(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Structured Loop Cutpoint Validator ([CertValidator.McLoop])

    Implements Milestone M3b of Phase 8.3a for single-header structured loops
    on RV64IM+RVC and AArch64:
    1. Cutpoint variable naming ([!cut_k], [!mc_hi_rk], [!mc_ur_r], [!mc_us_i]
       — never [$]-prefixed), let-free substitution ([subst_cert_expr]), and
       32-bit upper-half recombination ([combine_hi32_expr]).
    2. General pure-SSA IR segment reification ([ir_seg_tree], [reify_ir_seg])
       supporting rotated loops, entry guards, exit-block phis, LICM, and
       self-loops.
    3. Single-CNF multi-obligation SAT/LRAT refinement discharger
       ([check_mc_loop_obls]) where [ml_inv] guards ONLY Body obligations
       (never asserted as a global unit clause).
    4. Cutpoint & skeleton state construction and leaf-pair obligation
       collection for RV64 and AArch64.
    5. End-to-end validators & CNF emitters ([validate_mc_loop_rv64],
       [validate_mc_loop_a64], [emit_mc_loop_cnf_rv64], [emit_mc_loop_cnf_a64]).
    6. Backward partial-correctness and arbitrary-depth forward progress
       soundness theorems ([validate_mc_loop_rv64_sound],
       [validate_mc_loop_a64_sound]) with [0 Admitted] and zero custom axioms. *)

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
  McFormat.

From CertValidator Require Export
  McOblDischarger
  McLoopIrSpec
  McLoopCheck.

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

(** ** 6. Backward Partial Correctness & Arbitrary-Depth Forward Progress Proofs *)

Lemma dummy_freeze_oracle_const : forall w x y,
  dummy_freeze_oracle w x = dummy_freeze_oracle w y.
Proof. intros w x y; reflexivity. Qed.

Lemma wf_mc_loop_spec_sp_bounds : forall arch ls,
  wf_mc_loop_spec arch ls = true -> (- mc_frame_cap <= ml_sp_off ls <= 0)%Z.
Proof.
  intros arch ls Hwf; unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & Hsp) & _) & _) & _) & _) & _) & _).
  exact (mc_sp_aligned16_bounds _ Hsp).
Qed.

Lemma mc_skel_reg_slot_disjoint : forall r i,
  mc_skel_reg_name r <> mc_skel_slot_name i.
Proof.
  intros r i Heq; unfold mc_skel_reg_name, mc_skel_slot_name in Heq; discriminate Heq.
Qed.

Lemma mc_cut_hi_disjoint : forall k r,
  mc_cut_var_name k <> mc_hi_var_name r.
Proof.
  intros k r Heq; unfold mc_cut_var_name, mc_hi_var_name in Heq; discriminate Heq.
Qed.

Lemma mc_skel_reg_bang : forall r, mc_starts_with_bang (mc_skel_reg_name r) = true.
Proof. intro r; reflexivity. Qed.

Lemma mc_skel_slot_bang : forall i, mc_starts_with_bang (mc_skel_slot_name i) = true.
Proof. intro i; reflexivity. Qed.

Lemma mc_cut_var_bang : forall k, mc_starts_with_bang (mc_cut_var_name k) = true.
Proof. intro k; reflexivity. Qed.

Lemma mc_hi_var_bang : forall r, mc_starts_with_bang (mc_hi_var_name r) = true.
Proof. intro r; reflexivity. Qed.

Lemma rv_unspilled_preserved_nonzero : forall ls r,
  In r (mc_unspilled_preserved EA_Riscv64 ls) -> r <> 0%N.
Proof.
  intros ls r Hin; unfold mc_unspilled_preserved, mc_preserved_regs in Hin.
  apply filter_In in Hin as [Hrv _].
  cbn [rv_preserved_non_sp_regs In] in Hrv; repeat destruct Hrv as [<- | Hrv]; try lia; contradiction.
Qed.

Lemma a64_unspilled_preserved_lt31 : forall ls r,
  In r (mc_unspilled_preserved EA_AArch64 ls) -> (N.leb 31%N r = false).
Proof.
  intros ls r Hin; unfold mc_unspilled_preserved, mc_preserved_regs, a64_callee_saved_list in Hin.
  apply filter_In in Hin as [Ha64 _].
  cbn [In] in Ha64; repeat destruct Ha64 as [<- | Ha64]; try reflexivity; contradiction.
Qed.

Definition skel_reg_binds {Pa : Params}
  (read_reg : N -> @Integers.bit_int 64%positive) (rbs : list mc_loop_reg_bind)
  : list (string * @dvalue Pa) :=
  List.map (fun rb => (mc_skel_reg_name (mlr_reg rb), DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb))))) rbs.

Fixpoint skel_slot_binds {Pa : Params}
  (mstk : mc_stack_mem) (idx : nat) (sbs : list mc_loop_slot_bind)
  {struct sbs} : list (string * @dvalue Pa) :=
  match sbs with
  | [] => []
  | MLS_Expr o s _ :: rest =>
      (mc_skel_slot_name idx, DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false))) ::
      skel_slot_binds mstk (S idx) rest
  | MLS_SavedReg _ _ :: rest =>
      skel_slot_binds mstk (S idx) rest
  end.

Lemma skel_slot_binds_ge {Pa : Params} :
  forall mstk idx sbs nm,
    In nm (List.map fst (@skel_slot_binds Pa mstk idx sbs)) ->
    exists j, (idx <= j)%nat /\ nm = mc_skel_slot_name j.
Proof.
  intros mstk idx sbs; revert idx; induction sbs as [| [o s e | o r] rest IH]; intros idx nm Hin;
    cbn [skel_slot_binds List.map fst] in Hin; [contradiction | |].
  - destruct Hin as [Heq | Hr].
    + exists idx; split; [lia | symmetry; exact Heq].
    + destruct (IH (S idx) nm Hr) as [j [Hle Hnm]]; exists j; split; [lia | exact Hnm].
  - destruct (IH (S idx) nm Hin) as [j [Hle Hnm]]; exists j; split; [lia | exact Hnm].
Qed.

Lemma skel_binds_nodup {Pa : Params} :
  forall (read_reg : N -> @Integers.bit_int 64%positive) mstk ls,
    NoDup (List.map mlr_reg (ml_regs ls)) ->
    NoDup (List.map fst (@skel_reg_binds Pa read_reg (ml_regs ls) ++ skel_slot_binds mstk 0%nat (ml_slots ls))).
Proof.
  intros read_reg mstk ls Hnd; rewrite List.map_app; apply NoDup_app_intro.
  - clear mstk; induction (ml_regs ls) as [| rb rest IH]; cbn in *; [constructor |].
    inversion Hnd as [| ? ? Hnin Hnr]; subst; constructor; [| exact (IH Hnr)].
    intro Hin; apply in_map_iff in Hin as [[x dv] [Hfx Hin]].
    cbn in Hfx; subst x; apply in_map_iff in Hin as [rb0 [Heq0 Hrb0]].
    apply (f_equal fst) in Heq0; cbn in Heq0; apply mc_skel_reg_name_inj in Heq0.
    apply Hnin; rewrite <- Heq0; apply in_map_iff; exists rb0; split; [reflexivity | exact Hrb0].
  - clear read_reg Hnd; generalize 0%nat as idx; induction (ml_slots ls) as [| [o s e | o r] rest IH];
      intro idx; cbn [skel_slot_binds List.map]; [constructor | | exact (IH (S idx))].
    constructor; [| exact (IH (S idx))].
    intro Hin; apply skel_slot_binds_ge in Hin as [j [Hle Heq]]; apply mc_skel_slot_name_inj in Heq; lia.
  - intros x Hxr Hxs.
    apply in_map_iff in Hxr as [[x0 dv] [Hfx Hinr]]; cbn in Hfx; subst x0.
    apply in_map_iff in Hinr as [rb [Heq0 _]]; inversion Heq0 as [Hxr]; clear Heq0.
    apply skel_slot_binds_ge in Hxs as [j [_ Hxs]]; rewrite <- Hxr in Hxs.
    exact (mc_skel_reg_slot_disjoint (mlr_reg rb) j Hxs).
Qed.

Lemma skel_slot_binds_nth {Pa : Params} :
  forall mstk idx sbs i o s e,
    nth_error sbs i = Some (MLS_Expr o s e) ->
    In (mc_skel_slot_name (idx + i), DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))
       (skel_slot_binds mstk idx sbs).
Proof.
  intros mstk idx sbs; revert idx; induction sbs as [| [o0 s0 e0 | o0 r0] rest IH];
    intros idx i o s e Hnth; [destruct i; discriminate Hnth | |].
  - destruct i as [| i']; cbn in Hnth.
    + inversion Hnth; subst; rewrite Nat.add_0_r; left; reflexivity.
    + right; replace (idx + S i')%nat with (S idx + i')%nat by lia; exact (IH (S idx) i' o s e Hnth).
  - destruct i as [| i']; cbn in Hnth; [discriminate Hnth |].
    replace (idx + S i')%nat with (S idx + i')%nat by lia; exact (IH (S idx) i' o s e Hnth).
Qed.

Definition rv_at_cut (ls : mc_loop_spec) (rf0 rf : rv_regfile) (mstk : mc_stack_mem) : Prop :=
  rf 2%N = @Integers.add 64%positive (rv_read_reg 2%N rf0) (@Integers.repr 64%positive (ml_sp_off ls)) /\
  (forall r, In r (mc_unspilled_preserved EA_Riscv64 ls) -> rf r = rf0 r) /\
  (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
     mc_stk_load mstk off MS_8 false = rv_read_reg r rf0).

Definition a64_at_cut (ls : mc_loop_spec) (sp0 : @Integers.bit_int 64%positive)
  (rf0 rf : a64_regfile) (sp : @Integers.bit_int 64%positive) (mstk : mc_stack_mem) : Prop :=
  sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive (ml_sp_off ls)) /\
  (forall r, In r (mc_unspilled_preserved EA_AArch64 ls) -> a64_read_reg r rf = a64_read_reg r rf0) /\
  (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
     mc_stk_load mstk off MS_8 false = a64_read_reg r rf0).

Lemma rv_skel_step {Pa : Params} :
  forall seg_name insts ret_w ls seg_skel rf0 rf mstk,
    wf_mc_loop_spec EA_Riscv64 ls = true ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    summarize_rv64_seg seg_name (S (2 * List.length insts)) insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
      (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w = inr seg_skel ->
    mc_skel_tree_ok EA_Riscv64 ls (rv_seg_to_mc_seg seg_skel) = true ->
    rv_at_cut ls rf0 rf mstk ->
    (exists fuel_end rf_end mstk_end,
       rv_exec_mem fuel_end insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
       rv_callee_saved_preserved rf0 rf_end /\
       rf_end 1%N = rf0 1%N) \/
    (exists n rf' mstk',
       (1 <= n)%nat /\
       rv_exec_steps n insts (rv_read_reg 2%N rf0) (ml_mc_pc ls) rf mstk = Some (ml_mc_pc ls, rf', mstk') /\
       rv_at_cut ls rf0 rf' mstk').
Proof.
  intros seg_name insts ret_w ls seg_skel rf0 rf mstk Hwf Hrw Hnmul Hsp0 Hsum Hok [Hsp [Hunsp Hsav]].
  pose proof (wf_mc_loop_spec_sp_bounds _ _ Hwf) as Hrng.
  assert (Hnd : NoDup (List.map mlr_reg (ml_regs ls))).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
    destruct Hwf as (((((((_ & _) & _) & Hnd_b) & _) & _) & _) & _); rewrite mc_map_tr_eq in Hnd_b; exact (no_dup_N_to_NoDup _ Hnd_b). }
  set (binds := @skel_reg_binds Pa (fun r => rv_read_reg r rf) (ml_regs ls) ++ skel_slot_binds mstk 0%nat (ml_slots ls)).
  set (penv_s := overlay_penv binds (fun _ => None)).
  assert (Hnd_b : NoDup (List.map fst binds)) by exact (skel_binds_nodup _ mstk ls Hnd).
  assert (Hregs : forall rb, In rb (ml_regs ls) ->
    penv_s (mc_skel_reg_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf)))).
  { intros rb Hrb; unfold penv_s; apply overlay_penv_lookup_in; [exact Hnd_b |].
    unfold binds; apply in_or_app; left; unfold skel_reg_binds; apply in_map_iff; exists rb; split; [reflexivity | exact Hrb]. }
  assert (Hslots : forall i o s e, nth_error (ml_slots ls) i = Some (MLS_Expr o s e) ->
    penv_s (mc_skel_slot_name (0%nat + i)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))).
  { intros i o s e Hnth; unfold penv_s; apply overlay_penv_lookup_in; [exact Hnd_b |].
    unfold binds; apply in_or_app; right; exact (skel_slot_binds_nth mstk 0%nat (ml_slots ls) i o s e Hnth). }
  pose proof (rv_skel_vrf_agrees penv_s dummy_freeze_oracle ls rf0 rf Hwf Hsp Hrng Hunsp Hregs) as Hag.
  pose proof (build_skel_astk_agrees penv_s dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) 0%nat (ml_slots ls) mstk Hslots Hsav) as Hastk.
  assert (Hwfb : forallb (wf_mc_loop_reg_bind EA_Riscv64) (ml_regs ls) = true).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf; destruct Hwf as (((((((_ & _) & _) & _) & Hwbr) & _) & _) & _); exact Hwbr. }
  pose proof (summarize_rv64_seg_sound seg_name _ insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w seg_skel
                penv_s dummy_freeze_oracle rf0 rf mstk Hrw Hnmul Hsp0 Hrng (rv_skel_vrf_sp ls Hwfb) Hag Hastk Hsum) as Hexec.
  apply rv_seg_exec_to_mc in Hexec.
  destruct (mc_skel_tree_ok_extract EA_Riscv64 ls penv_s dummy_freeze_oracle _ _ _ Hok Hexec)
    as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & mstk' & Hn & Hsteps & _ & Hsp2' & Hag' & Hastk'))
       | (ret_e & (fuel_end & rf_end & mstk_end & Hmem & Hcs & Hra & _))].
  - right; exists n, rf', mstk'; split; [exact (Hn eq_refl) | split; [exact Hsteps |]].
    repeat split.
    + specialize (Hag' 2%N); rewrite Hsp2' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
    + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
      pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
      unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
    + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_s dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                  off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
      cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
  - left; exists fuel_end, rf_end, mstk_end; repeat split; assumption.
Qed.

Lemma rv_skel_backward_sound {Pa : Params} :
  forall seg_name insts ret_w ls seg_skel rf0 n_max fuel rf mstk rf_end mstk_end,
    (fuel <= n_max)%nat ->
    wf_mc_loop_spec EA_Riscv64 ls = true ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    summarize_rv64_seg seg_name (S (2 * List.length insts)) insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
      (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w = inr seg_skel ->
    mc_skel_tree_ok EA_Riscv64 ls (rv_seg_to_mc_seg seg_skel) = true ->
    rv_at_cut ls rf0 rf mstk ->
    rv_exec_mem fuel insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) ->
    rv_callee_saved_preserved rf0 rf_end /\ rf_end 1%N = rf0 1%N.
Proof.
  intros seg_name insts ret_w ls seg_skel rf0 n_max; induction n_max as [| n_max' IH];
    intros fuel rf mstk rf_end mstk_end Hle Hwf Hrw Hnmul Hsp0 Hsum Hok Hat Hmem.
  - assert (Hf0 : fuel = 0%nat) by lia; subst fuel; cbn [rv_exec_mem] in Hmem; discriminate Hmem.
  - destruct (@rv_skel_step Pa seg_name insts ret_w ls seg_skel rf0 rf mstk Hwf Hrw Hnmul Hsp0 Hsum Hok Hat)
      as [(fuel_e & rf_e & mstk_e & Hme & Hcs & Hra) | (n1 & rf1 & mstk1 & Hn1 & Hst1 & Hat1)].
    + pose proof (rv_exec_mem_det fuel fuel_e insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk _ _ Hmem Hme) as Heq.
      inversion Heq; subst rf_e mstk_e; split; assumption.
    + destruct (rv_exec_mem_split_steps n1 fuel insts (rv_read_reg 2%N rf0) (ml_mc_pc ls) rf mstk
                  (ml_mc_pc ls) rf1 mstk1 (rf_end, mstk_end) Hmem Hst1) as [Hlt Hrem].
      exact (IH (fuel - n1)%nat rf1 mstk1 rf_end mstk_end ltac:(lia) Hwf Hrw Hnmul Hsp0 Hsum Hok Hat1 Hrem).
Qed.

Lemma a64_skel_step {Pa : Params} :
  forall seg_name insts ret_w ls seg_skel rf0 sp0 rf sp fl mstk,
    wf_mc_loop_spec EA_AArch64 ls = true ->
    rv_supported_arg_width ret_w = true ->
    forallb a64_inst_valid insts = true ->
    mc_valid_sp0 sp0 ->
    summarize_a64_seg seg_name (S (2 * List.length insts)) insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
      (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w = inr seg_skel ->
    mc_skel_tree_ok EA_AArch64 ls (a64_seg_to_mc_seg seg_skel) = true ->
    a64_at_cut ls sp0 rf0 rf sp mstk ->
    (exists fuel_end rf_end fl_end mstk_end,
       a64_exec_mem fuel_end insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
       a64_callee_saved_preserved rf0 rf_end) \/
    (exists n rf' sp' fl' mstk',
       (1 <= n)%nat /\
       a64_exec_steps n insts sp0 (ml_mc_pc ls) rf sp fl mstk = Some (ml_mc_pc ls, rf', sp', fl', mstk') /\
       a64_at_cut ls sp0 rf0 rf' sp' mstk').
Proof.
  intros seg_name insts ret_w ls seg_skel rf0 sp0 rf sp fl mstk Hwf Hrw Hval Hsp0 Hsum Hok [Hsp [Hunsp Hsav]].
  pose proof (wf_mc_loop_spec_sp_bounds _ _ Hwf) as Hrng.
  assert (Hnd : NoDup (List.map mlr_reg (ml_regs ls))).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
    destruct Hwf as (((((((_ & _) & _) & Hnd_b) & _) & _) & _) & _); rewrite mc_map_tr_eq in Hnd_b; exact (no_dup_N_to_NoDup _ Hnd_b). }
  set (binds := @skel_reg_binds Pa (fun r => a64_read_reg r rf) (ml_regs ls) ++ skel_slot_binds mstk 0%nat (ml_slots ls)).
  set (penv_s := overlay_penv binds (fun _ => None)).
  assert (Hnd_b : NoDup (List.map fst binds)) by exact (skel_binds_nodup _ mstk ls Hnd).
  assert (Hregs : forall rb, In rb (ml_regs ls) ->
    penv_s (mc_skel_reg_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf)))).
  { intros rb Hrb; unfold penv_s; apply overlay_penv_lookup_in; [exact Hnd_b |].
    unfold binds; apply in_or_app; left; unfold skel_reg_binds; apply in_map_iff; exists rb; split; [reflexivity | exact Hrb]. }
  assert (Hslots : forall i o s e, nth_error (ml_slots ls) i = Some (MLS_Expr o s e) ->
    penv_s (mc_skel_slot_name (0%nat + i)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))).
  { intros i o s e Hnth; unfold penv_s; apply overlay_penv_lookup_in; [exact Hnd_b |].
    unfold binds; apply in_or_app; right; exact (skel_slot_binds_nth mstk 0%nat (ml_slots ls) i o s e Hnth). }
  pose proof (a64_skel_vrf_agrees penv_s dummy_freeze_oracle ls rf0 sp0 rf Hwf Hunsp Hregs) as Hag.
  pose proof (build_skel_astk_agrees penv_s dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0 0%nat (ml_slots ls) mstk Hslots Hsav) as Hastk.
  pose proof (summarize_a64_seg_sound seg_name _ insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w seg_skel
                penv_s dummy_freeze_oracle rf0 sp0 rf sp fl mstk Hrw Hval Hsp0 Hrng Hsp Hag Hastk (fun C => ltac:(discriminate C)) Hsum) as Hexec.
  apply a64_seg_exec_to_mc in Hexec.
  destruct (mc_skel_tree_ok_extract EA_AArch64 ls penv_s dummy_freeze_oracle _ _ _ Hok Hexec)
    as [(sp_off' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & sp' & fl' & mstk' & Hn & Hsteps & _ & Hsp' & Hag' & Hastk'))
       | (ret_e & (fuel_end & rf_end & fl_end & mstk_end & Hmem & Hcs & _))].
  - right; exists n, rf', sp', fl', mstk'; split; [exact (Hn eq_refl) | split; [exact Hsteps |]].
    repeat split; try assumption.
    + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
    + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_s dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                  off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
      cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
  - left; exists fuel_end, rf_end, fl_end, mstk_end; split; assumption.
Qed.

Lemma a64_skel_backward_sound {Pa : Params} :
  forall seg_name insts ret_w ls seg_skel rf0 sp0 n_max fuel rf sp fl mstk rf_end sp_end fl_end mstk_end,
    (fuel <= n_max)%nat ->
    wf_mc_loop_spec EA_AArch64 ls = true ->
    rv_supported_arg_width ret_w = true ->
    forallb a64_inst_valid insts = true ->
    mc_valid_sp0 sp0 ->
    summarize_a64_seg seg_name (S (2 * List.length insts)) insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
      (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w = inr seg_skel ->
    mc_skel_tree_ok EA_AArch64 ls (a64_seg_to_mc_seg seg_skel) = true ->
    a64_at_cut ls sp0 rf0 rf sp mstk ->
    a64_exec_mem fuel insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp_end, fl_end, mstk_end) ->
    sp_end = sp0 /\ a64_callee_saved_preserved rf0 rf_end.
Proof.
  intros seg_name insts ret_w ls seg_skel rf0 sp0 n_max; induction n_max as [| n_max' IH];
    intros fuel rf sp fl mstk rf_end sp_end fl_end mstk_end Hle Hwf Hrw Hval Hsp0 Hsum Hok Hat Hmem.
  - assert (Hf0 : fuel = 0%nat) by lia; subst fuel; cbn [a64_exec_mem] in Hmem; discriminate Hmem.
  - destruct (@a64_skel_step Pa seg_name insts ret_w ls seg_skel rf0 sp0 rf sp fl mstk Hwf Hrw Hval Hsp0 Hsum Hok Hat)
      as [(fuel_e & rf_e & fl_e & mstk_e & Hme & Hcs) | (n1 & rf1 & sp1 & fl1 & mstk1 & Hn1 & Hst1 & Hat1)].
    + pose proof (a64_exec_mem_det fuel fuel_e insts (ml_mc_pc ls) sp0 rf sp fl mstk _ _ Hmem Hme) as Heq.
      inversion Heq; subst; split; [reflexivity | exact Hcs].
    + destruct (a64_exec_mem_split_steps n1 fuel insts sp0 (ml_mc_pc ls) rf sp fl mstk
                  (ml_mc_pc ls) rf1 sp1 fl1 mstk1 (rf_end, sp_end, fl_end, mstk_end) Hmem Hst1) as [Hlt Hrem].
      exact (IH (fuel - n1)%nat rf1 sp1 fl1 mstk1 rf_end sp_end fl_end mstk_end ltac:(lia) Hwf Hrw Hval Hsp0 Hsum Hok Hat1 Hrem).
Qed.

(** Helpers for [ir_at_cut] and [lmap_base] *)

Definition ir_at_cut {Pa : Params}
  (bmap : rmap (block dtyp)) (init_id hdr_id : block_id)
  (env0 env_c : rmap (@dvalue Pa)) (bid_c : block_id) : Prop :=
  (env_c = env0 /\ bid_c = init_id /\ init_id = hdr_id) \/
  pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (init_id, init_id))
    env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id)).

Lemma ir_at_cut_ub {Pa : Params} :
  forall bmap init_id hdr_id env0 env_c bid_c (sigma : @draw_strat Pa),
    ir_at_cut bmap init_id hdr_id env0 env_c bid_c ->
    cfg_steps_to_ub sigma env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id)) ->
    cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (init_id, init_id)).
Proof.
  intros bmap init_id hdr_id env0 env_c bid_c sigma Hcut Hub.
  destruct Hcut as [[-> [-> ->]] | Htau]; [exact Hub | exact (pure_cfg_steps_to_tau_then_ub sigma _ _ _ _ Htau Hub)].
Qed.

Lemma ir_at_cut_ret {Pa : Params} :
  forall bmap init_id hdr_id env0 env_c bid_c env_out (dv : @dvalue Pa),
    ir_at_cut bmap init_id hdr_id env0 env_c bid_c ->
    pure_cfg_steps env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id)) env_out dv ->
    pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (init_id, init_id)) env_out dv.
Proof.
  intros bmap init_id hdr_id env0 env_c bid_c env_out dv Hcut Hst.
  destruct Hcut as [[-> [-> ->]] | Htau]; [exact Hst | exact (pure_cfg_steps_to_tau_then_ret _ _ _ _ _ _ Htau Hst)].
Qed.

Lemma ir_at_cut_step {Pa : Params} :
  forall bmap init_id hdr_id env0 env_c bid_c env_c' bid_c',
    ir_at_cut bmap init_id hdr_id env0 env_c bid_c ->
    ((env_c' = env_c /\ bid_c' = bid_c /\ hdr_id = hdr_id) \/
     pure_cfg_steps_to_tau env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))
       env_c' (@denote_cfg_from Pa bmap None (bid_c', hdr_id))) ->
    ir_at_cut bmap init_id hdr_id env0 env_c' bid_c'.
Proof.
  intros bmap init_id hdr_id env0 env_c bid_c env_c' bid_c' Hcut Hstep.
  destruct Hstep as [[-> [-> _]] | Htau2]; [exact Hcut |].
  right; destruct Hcut as [[-> [-> ->]] | Htau1];
    [exact Htau2 | exact (pure_cfg_steps_to_tau_trans _ _ _ _ _ _ Htau1 Htau2)].
Qed.

Lemma common_cut_lmap_wf : forall allowed base lms,
  wf_pure_lmap allowed base ->
  (forall lm, In lm lms -> wf_pure_lmap allowed lm) ->
  wf_pure_lmap allowed (common_cut_lmap base lms).
Proof.
  intros allowed base lms Hbase Hlms; destruct lms as [| lm0 rest]; cbn [common_cut_lmap]; [exact Hbase |].
  intros r w ce Hf.
  pose proof (common_cut_lmap_in base (lm0 :: rest) lm0 (or_introl eq_refl) r w ce Hf) as Hf0.
  exact (Hlms lm0 (or_introl eq_refl) r w ce Hf0).
Qed.

Lemma lmap_matches_env_penv_agree {Pa : Params} :
  forall allowed (penv1 penv2 : param_env Pa) lm env,
    wf_pure_lmap allowed lm ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    lmap_matches_env penv1 lm env ->
    lmap_matches_env penv2 lm env.
Proof.
  intros allowed penv1 penv2 lm env Hwf Hag Hlm r w ce Hf.
  destruct (Hlm r w ce Hf) as (dv & Hev & Hsc & Hrm).
  destruct (Hwf r w ce Hf) as (_ & _ & Hlf & Hfv).
  exists dv; repeat split; try assumption.
  rewrite <- Hsc; symmetry; apply eval_cert_expr_penv_eq_if_vars; [exact Hlf |].
  intros nm wn Hin; exact (Hag nm wn (Hfv _ Hin)).
Qed.

Lemma wrap_cut_mc_at_matches {Pa : Params} :
  forall (penv : param_env Pa) lmap_base idx hspecs dvs env,
    lmap_matches_env penv lmap_base env ->
    NoDup (List.map fst hspecs) ->
    Forall2 (fun '(id, _) '(id', _) => id' = id) hspecs dvs ->
    (forall r, In r (lmap_keys lmap_base) -> ~ In r (List.map fst hspecs)) ->
    (forall j id w dv,
       nth_error hspecs j = Some (id, w) ->
       nth_error dvs j = Some (id, dv) ->
       penv (mc_cut_var_name (idx + j)) = Some dv /\ wf_scalar_dvalue w dv) ->
    lmap_matches_env penv (wrap_cut_mc_at idx lmap_base hspecs) (apply_phi_env env dvs).
Proof.
  intros penv lmap_base idx hspecs; revert idx;
    induction hspecs as [| [id w] rest IH]; intros idx [| [id' dv'] rdvs] env Hlm Hnd Hids Hdisj Hp;
    try (inversion Hids; fail); cbn [wrap_cut_mc_at apply_phi_env].
  - exact Hlm.
  - cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin_rest Hnd_rest]; subst.
    assert (Hids_rest : Forall2 (fun '(id0, _) '(id'0, _) => id'0 = id0) rest rdvs)
      by (inversion Hids; assumption).
    assert (Hid : id' = id) by (inversion Hids; assumption).
    subst id'.
    intros r wr cer Hf.
    destruct (RawIDOrd.eq_dec id r) as [Heqr | Hneqr].
    + subst r; rewrite RMF.F.add_eq_o in Hf by reflexivity; inversion Hf; subst wr cer.
      destruct (Hp 0%nat id w dv' eq_refl eq_refl) as [Hpv Hsc].
      rewrite Nat.add_0_r in Hpv; exists dv'; repeat split; try assumption.
      * rewrite apply_phi_env_preserves_not_in;
          [rewrite RMF.F.add_eq_o by reflexivity; reflexivity
          | intro Hin; apply Hnin_rest; clear -Hids_rest Hin;
            revert rdvs Hids_rest Hin; induction rest as [| [i0 w0] rr IHr]; intros rdvs H2 Hin;
            destruct rdvs as [| [i1 d1] r2]; try inversion H2; cbn in Hin; [contradiction |];
            subst; destruct Hin as [Heq | Hr]; [cbn in *; left; congruence | right; exact (IHr _ H5 Hr)]].
      * unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hpv.
        destruct Hsc as [-> | [v ->]]; cbn [check_scalar_width]; [reflexivity | rewrite Pos.eqb_refl; reflexivity].
    + rewrite RMF.F.add_neq_o in Hf by exact Hneqr.
      assert (Hlm_add : lmap_matches_env penv lmap_base (RM.add id dv' env)).
      { intros r0 w0 ce0 Hf0; destruct (Hlm r0 w0 ce0 Hf0) as (d0 & He0 & Hs0 & Hr0).
        exists d0; repeat split; try assumption.
        rewrite RMF.F.add_neq_o; [exact He0 | intro Heq; subst r0; apply (Hdisj id (proj2 (in_lmap_keys_iff lmap_base id) (ex_intro _ _ Hf0))); left; reflexivity]. }
      assert (Hp_sub : forall j0 id0 w0 dv0,
        nth_error rest j0 = Some (id0, w0) ->
        nth_error rdvs j0 = Some (id0, dv0) ->
        penv (mc_cut_var_name (S idx + j0)) = Some dv0 /\ wf_scalar_dvalue w0 dv0).
      { intros j0 id0 w0 dv0 Hn1 Hn2; replace (S idx + j0)%nat with (idx + S j0)%nat by lia; exact (Hp (S j0) id0 w0 dv0 Hn1 Hn2). }
      exact (IH (S idx) rdvs (RM.add id dv' env) Hlm_add Hnd_rest Hids_rest
               (fun r0 Hr0 Hin => Hdisj r0 Hr0 (or_intror Hin)) Hp_sub r wr cer Hf).
Qed.

(** Constructive Cutpoint [penv] Construction *)


Lemma is_exact_cut_var_inj_k : forall k1 w1 k2 w2 e,
  is_exact_cut_var k1 w1 e = true ->
  is_exact_cut_var k2 w2 e = true ->
  k1 = k2 /\ w1 = w2.
Proof.
  intros k1 w1 k2 w2 e H1 H2; destruct e; cbn in H1, H2; try discriminate H1.
  apply andb_true_iff in H1 as [Hn1 Hw1]; apply andb_true_iff in H2 as [Hn2 Hw2].
  apply String.eqb_eq in Hn1; apply String.eqb_eq in Hn2; apply Pos.eqb_eq in Hw1; apply Pos.eqb_eq in Hw2.
  subst; split; [apply mc_cut_var_name_inj; exact Hn2 | reflexivity].
Qed.

Lemma length_filter_ge1 : forall {A : Type} (f : A -> bool) (xs : list A) (x : A),
  f x = true -> In x xs -> (1 <= List.length (List.filter f xs))%nat.
Proof.
  intros A f xs; induction xs as [| y rest IH]; intros x Hfx Hin; cbn in Hin; [contradiction |].
  cbn [List.filter]; destruct Hin as [-> | Hr].
  - rewrite Hfx; cbn [List.length]; lia.
  - destruct (f y); cbn [List.length]; pose proof (IH x Hfx Hr); lia.
Qed.

Fixpoint find_ptol_reg (k : nat) (w : positive) (rbs : list mc_loop_reg_bind) {struct rbs} : option N :=
  match rbs with
  | [] => None
  | rb :: rest => if is_exact_cut_var k w (mlr_expr rb) then Some (mlr_reg rb) else find_ptol_reg k w rest
  end.

Fixpoint find_ptol_slot (k : nat) (w : positive) (sbs : list mc_loop_slot_bind) {struct sbs} : option (Z * mc_mem_size) :=
  match sbs with
  | [] => None
  | MLS_Expr off sz e :: rest =>
      if is_exact_cut_var k w e then Some (off, sz) else find_ptol_slot k w rest
  | MLS_SavedReg _ _ :: rest =>
      find_ptol_slot k w rest
  end.

Lemma find_ptol_reg_spec : forall k w rbs rb,
  (List.length (List.filter (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) rbs) <= 1)%nat ->
  In rb rbs ->
  is_exact_cut_var k w (mlr_expr rb) = true ->
  find_ptol_reg k w rbs = Some (mlr_reg rb).
Proof.
  intros k w rbs; induction rbs as [| rb0 rest IH]; intros rb Hle Hin Hex; cbn in *; [contradiction |].
  pose proof (is_exact_cut_var_has_var k w (mlr_expr rb) Hex) as Hhv.
  destruct (is_exact_cut_var k w (mlr_expr rb0)) eqn:Ex0.
  - rewrite (is_exact_cut_var_has_var k w _ Ex0) in Hle; cbn [List.length] in Hle.
    destruct Hin as [<- | Hinr]; [reflexivity |].
    pose proof (length_filter_ge1 (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) rest rb Hhv Hinr); lia.
  - destruct (expr_has_var (mc_cut_var_name k) (mlr_expr rb0)) in Hle; cbn [List.length] in Hle;
      destruct Hin as [-> | Hinr]; [rewrite Ex0 in Hex; discriminate Hex | apply (IH rb ltac:(lia) Hinr Hex) | rewrite Ex0 in Hex; discriminate Hex | apply (IH rb ltac:(lia) Hinr Hex)].
Qed.

Lemma find_ptol_reg_none_when_zero : forall k w rbs,
  List.length (List.filter (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) rbs) = 0%nat ->
  find_ptol_reg k w rbs = None.
Proof.
  intros k w rbs; induction rbs as [| rb0 rest IH]; intro Hz; cbn in *; [reflexivity |].
  destruct (is_exact_cut_var k w (mlr_expr rb0)) eqn:Ex0.
  - rewrite (is_exact_cut_var_has_var k w _ Ex0) in Hz; cbn [List.length] in Hz; discriminate Hz.
  - destruct (expr_has_var (mc_cut_var_name k) (mlr_expr rb0)) in Hz; cbn [List.length] in Hz; [discriminate Hz | exact (IH Hz)].
Qed.

Lemma find_ptol_slot_spec : forall k w sbs off sz e,
  (List.length (List.filter (fun sb => match sb with MLS_Expr _ _ e0 => expr_has_var (mc_cut_var_name k) e0 | MLS_SavedReg _ _ => false end) sbs) <= 1)%nat ->
  In (MLS_Expr off sz e) sbs ->
  is_exact_cut_var k w e = true ->
  find_ptol_slot k w sbs = Some (off, sz).
Proof.
  intros k w sbs; induction sbs as [| [o0 s0 e0 | o0 r0] rest IH];
    intros off sz e Hle Hin Hex; cbn in *; [contradiction | |].
  - pose proof (is_exact_cut_var_has_var k w e Hex) as Hhv.
    destruct (is_exact_cut_var k w e0) eqn:Ex0.
    + rewrite (is_exact_cut_var_has_var k w e0 Ex0) in Hle; cbn [List.length] in Hle.
      destruct Hin as [Heq | Hinr]; [inversion Heq; reflexivity |].
      pose proof (length_filter_ge1 (fun sb => match sb with MLS_Expr _ _ e0 => expr_has_var (mc_cut_var_name k) e0 | MLS_SavedReg _ _ => false end) rest (MLS_Expr off sz e) Hhv Hinr); lia.
    + destruct (expr_has_var (mc_cut_var_name k) e0) in Hle; cbn [List.length] in Hle;
        destruct Hin as [Heq | Hinr]; try (inversion Heq; subst; rewrite Ex0 in Hex; discriminate Hex);
        apply (IH off sz e ltac:(lia) Hinr Hex).
  - destruct Hin as [Hc | Hinr]; [discriminate Hc | exact (IH off sz e Hle Hinr Hex)].
Qed.

Lemma cut_var_ptol_count_split : forall ls k w,
  cut_var_ptol ls k w = true ->
  (List.length (List.filter (fun rb => expr_has_var (mc_cut_var_name k) (mlr_expr rb)) (ml_regs ls)) +
   List.length (List.filter (fun sb => match sb with MLS_Expr _ _ e => expr_has_var (mc_cut_var_name k) e | MLS_SavedReg _ _ => false end) (ml_slots ls)) <= 1)%nat.
Proof.
  intros ls k w H; rewrite cut_var_ptol_spec in H; rewrite !andb_true_iff in H.
  destruct H as [[[_ Hcnt] _] _]; unfold cut_var_bind_count in Hcnt; rewrite !mc_count_tr_eq in Hcnt.
  apply Nat.leb_le in Hcnt; exact Hcnt.
Qed.

Lemma cut_var_ptol_inv_not_in : forall ls k w inv_e,
  cut_var_ptol ls k w = true ->
  ml_inv ls = Some inv_e ->
  forall w0, ~ In (mc_cut_var_name k, w0) (collect_free_vars [] inv_e).
Proof.
  intros ls k w inv_e Hpt Hmi w0.
  rewrite cut_var_ptol_spec in Hpt; rewrite Hmi, !andb_true_iff in Hpt.
  destruct Hpt as [[[Hneg _] _] _]; apply negb_true_iff in Hneg; exact (expr_has_var_false_not_in _ _ Hneg w0).
Qed.

Lemma cut_var_ptol_reg_uses : forall ls k w rb,
  cut_var_ptol ls k w = true -> In rb (ml_regs ls) -> reg_slot_uses_cut_var_ok k w (mlr_expr rb) = true.
Proof.
  intros ls k w rb Hpt Hrb; rewrite cut_var_ptol_spec in Hpt; rewrite !andb_true_iff in Hpt.
  destruct Hpt as [[[_ _] Hregs] _]; rewrite forallb_forall in Hregs; exact (Hregs rb Hrb).
Qed.

Lemma cut_var_ptol_slot_uses : forall ls k w off sz e,
  cut_var_ptol ls k w = true -> In (MLS_Expr off sz e) (ml_slots ls) -> reg_slot_uses_cut_var_ok k w e = true.
Proof.
  intros ls k w off sz e Hpt Hs; rewrite cut_var_ptol_spec in Hpt; rewrite !andb_true_iff in Hpt.
  destruct Hpt as [_ Hslts]; rewrite forallb_forall in Hslts; exact (Hslts (MLS_Expr off sz e) Hs).
Qed.

Fixpoint build_cut_ir_binds {Pa : Params}
  (idx : nat) (hdr_ws : list positive) (dvs : list (raw_id * @dvalue Pa))
  {struct hdr_ws} : list (string * @dvalue Pa) :=
  match hdr_ws, dvs with
  | _ :: rw, (_, dv) :: rd => (mc_cut_var_name idx, dv) :: build_cut_ir_binds (S idx) rw rd
  | _, _ => []
  end.

Fixpoint build_cut_mc_binds {Pa : Params}
  (ls : mc_loop_spec) (penv_mc_prev : param_env Pa)
  (read_reg : N -> @Integers.bit_int 64%positive) (mstk : mc_stack_mem)
  (idx : nat) (hdr_ws : list positive) (phis_ir : list (positive * cert_expr))
  (dvs : list (raw_id * @dvalue Pa)) {struct hdr_ws} : list (string * @dvalue Pa) :=
  match hdr_ws, phis_ir, dvs with
  | w :: rw, (_, ce) :: rp, (_, dv) :: rd =>
      let dv_bind :=
        if cut_var_ptol ls idx w then
          match find_ptol_reg idx w (ml_regs ls) with
          | Some r =>
              DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive (read_reg r))))
          | None =>
              match find_ptol_slot idx w (ml_slots ls) with
              | Some (off, sz) =>
                  DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))
              | None =>
                  match dv with
                  | DVALUE_Base (@DVALUE_I _ wp' vi) =>
                      if Pos.eqb wp' w then DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned wp' vi)))
                      else DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
                  | _ => DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
                  end
              end
          end
        else
          match eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle ce with
          | raise_ret (DVALUE_Base (@DVALUE_I _ wp' vi)) =>
              if Pos.eqb wp' w then DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned wp' vi)))
              else DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
          | _ => DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
          end
      in
      (mc_cut_var_name idx, dv_bind) :: build_cut_mc_binds ls penv_mc_prev read_reg mstk (S idx) rw rp rd
  | _, _, _ => []
  end.

Definition build_hi32_binds {Pa : Params}
  (read_reg : N -> @Integers.bit_int 64%positive) (rbs : list mc_loop_reg_bind)
  : list (string * @dvalue Pa) :=
  List.flat_map (fun rb =>
    if Pos.eqb (mlr_width rb) 32%positive then
      [(mc_hi_var_name (mlr_reg rb), DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb))))]
    else []) rbs.

Lemma build_cut_ir_binds_ge {Pa : Params} :
  forall idx hdr_ws dvs nm,
    In nm (List.map fst (@build_cut_ir_binds Pa idx hdr_ws dvs)) ->
    exists j, (idx <= j)%nat /\ nm = mc_cut_var_name j.
Proof.
  intros idx hdr_ws; revert idx; induction hdr_ws as [| w rw IH]; intros idx [| [id dv] rd] nm Hin;
    cbn in Hin; try contradiction.
  destruct Hin as [<- | Hr]; [exists idx; split; [lia | reflexivity] |].
  destruct (IH (S idx) rd nm Hr) as [j [Hle ->]]; exists j; split; [lia | reflexivity].
Qed.

Lemma build_cut_ir_binds_nodup {Pa : Params} :
  forall idx hdr_ws dvs, NoDup (List.map fst (@build_cut_ir_binds Pa idx hdr_ws dvs)).
Proof.
  intros idx hdr_ws; revert idx; induction hdr_ws as [| w rw IH]; intros idx [| [id dv] rd]; cbn; [constructor | constructor | constructor |].
  constructor; [| exact (IH (S idx) rd)].
  intro Hin; apply build_cut_ir_binds_ge in Hin as [j [Hle Heq]]; apply mc_cut_var_name_inj in Heq; lia.
Qed.

Lemma build_cut_ir_binds_bang {Pa : Params} :
  forall idx hdr_ws dvs nm,
    In nm (List.map fst (@build_cut_ir_binds Pa idx hdr_ws dvs)) -> mc_starts_with_bang nm = true.
Proof.
  intros idx hdr_ws dvs nm Hin; apply build_cut_ir_binds_ge in Hin as [j [_ ->]]; apply mc_cut_var_bang.
Qed.

Lemma build_cut_mc_binds_ge {Pa : Params} :
  forall ls penv_prev rr mstk idx hdr_ws phis_ir dvs nm,
    In nm (List.map fst (@build_cut_mc_binds Pa ls penv_prev rr mstk idx hdr_ws phis_ir dvs)) ->
    exists j, (idx <= j)%nat /\ nm = mc_cut_var_name j.
Proof.
  intros ls penv_prev rr mstk idx hdr_ws; revert idx;
    induction hdr_ws as [| w rw IH]; intros idx [| [wp ce] rp] [| [id dv] rd] nm Hin;
    cbn [build_cut_mc_binds List.map fst] in Hin; try contradiction.
  destruct Hin as [<- | Hr]; [exists idx; split; [lia | reflexivity] |].
  destruct (IH (S idx) rp rd nm Hr) as [j [Hle ->]]; exists j; split; [lia | reflexivity].
Qed.

Lemma build_hi32_binds_nodup {Pa : Params} :
  forall rr rbs,
    NoDup (List.map mlr_reg rbs) ->
    NoDup (List.map fst (@build_hi32_binds Pa rr rbs)).
Proof.
  intros rr rbs; induction rbs as [| rb rest IH]; intro Hnd; cbn in *; [constructor |].
  inversion Hnd as [| ? ? Hnin Hnr]; subst.
  destruct (Pos.eqb (mlr_width rb) 32%positive); cbn [app List.map]; [| exact (IH Hnr)].
  constructor; [| exact (IH Hnr)].
  intro Hin; apply in_map_iff in Hin as [[nm dv] [Hfx Hfl]]; cbn in Hfx; subst nm.
  unfold build_hi32_binds in Hfl; apply in_flat_map in Hfl as [rb0 [Hrb0 Hin0]].
  destruct (Pos.eqb (mlr_width rb0) 32%positive); cbn in Hin0; [| contradiction].
  destruct Hin0 as [Heq | []]; apply (f_equal fst) in Heq; cbn in Heq; apply mc_hi_var_name_inj in Heq.
  apply Hnin; rewrite <- Heq; apply in_map_iff; exists rb0; split; [reflexivity | exact Hrb0].
Qed.

Lemma build_cut_mc_hi_nodup {Pa : Params} :
  forall ls penv_prev rr mstk idx hdr_ws phis_ir dvs,
    NoDup (List.map mlr_reg (ml_regs ls)) ->
    NoDup (List.map fst (@build_cut_mc_binds Pa ls penv_prev rr mstk idx hdr_ws phis_ir dvs ++ build_hi32_binds rr (ml_regs ls))).
Proof.
  intros ls penv_prev rr mstk idx hdr_ws phis_ir dvs Hnd; rewrite List.map_app; apply NoDup_app_intro.
  - clear -idx; revert idx phis_ir dvs; induction hdr_ws as [| w rw IH]; intros idx [| [wp ce] rp] [| [id dv] rd]; cbn;
      try (constructor; fail).
    constructor; [| exact (IH (S idx) rp rd)].
    intro Hin; apply build_cut_mc_binds_ge in Hin as [j [Hle Heq]]; apply mc_cut_var_name_inj in Heq; lia.
  - exact (build_hi32_binds_nodup rr (ml_regs ls) Hnd).
  - intros x Hxc Hxh; apply build_cut_mc_binds_ge in Hxc as [j [_ ->]].
    apply in_map_iff in Hxh as [[nm dv] [Hfx Hfl]]; cbn in Hfx; subst nm.
    unfold build_hi32_binds in Hfl; apply in_flat_map in Hfl as [rb0 [_ Hin0]].
    destruct (Pos.eqb (mlr_width rb0) 32%positive); cbn in Hin0; [| contradiction].
    destruct Hin0 as [Heq | []]; inversion Heq as [Hnm]; exact (mc_cut_hi_disjoint j (mlr_reg rb0) Hnm).
Qed.

Lemma build_cut_mc_hi_bang {Pa : Params} :
  forall ls penv_prev rr mstk idx hdr_ws phis_ir dvs nm,
    In nm (List.map fst (@build_cut_mc_binds Pa ls penv_prev rr mstk idx hdr_ws phis_ir dvs ++ build_hi32_binds rr (ml_regs ls))) ->
    mc_starts_with_bang nm = true.
Proof.
  intros ls penv_prev rr mstk idx hdr_ws phis_ir dvs nm Hin; rewrite List.map_app in Hin; apply in_app_iff in Hin as [Hc | Hh].
  - apply build_cut_mc_binds_ge in Hc as [j [_ ->]]; apply mc_cut_var_bang.
  - apply in_map_iff in Hh as [[x dv] [<- Hfl]]; unfold build_hi32_binds in Hfl; apply in_flat_map in Hfl as [rb [_ Hr]].
    destruct (Pos.eqb (mlr_width rb) 32%positive); cbn in Hr; [| contradiction]; destruct Hr as [Heq | []]; inversion Heq; reflexivity.
Qed.

Fixpoint cut_vars_from_ws (idx : nat) (ws : list positive) {struct ws}
  : list (string * positive) :=
  match ws with
  | [] => []
  | w :: rest => (mc_cut_var_name idx, w) :: cut_vars_from_ws (S idx) rest
  end.

Lemma cut_vars_from_eq_ws : forall idx hspecs,
  cut_vars_from idx hspecs = cut_vars_from_ws idx (extract_hdr_phi_widths hspecs).
Proof.
  intros idx hspecs; revert idx; induction hspecs as [| [id w] rest IH];
    intro idx; cbn; [reflexivity | f_equal; exact (IH (S idx))].
Qed.

Lemma Forall2_nth_error_l_ex : forall {A B : Type} (R : A -> B -> Prop) xs ys k x,
  Forall2 R xs ys ->
  nth_error xs k = Some x ->
  exists y, nth_error ys k = Some y /\ R x y.
Proof.
  intros A B R xs ys k x Hfa; revert k; induction Hfa as [| x0 y0 rx ry Hxy Hrest IH];
    intros [| k'] Hnth; cbn in Hnth; try discriminate Hnth.
  - inversion Hnth; subst x0; exists y0; split; [reflexivity | exact Hxy].
  - exact (IH k' Hnth).
Qed.

Lemma Forall2_nth_error_r : forall {A B : Type} (R : A -> B -> Prop) xs ys k y,
  Forall2 R xs ys ->
  nth_error ys k = Some y ->
  exists x, nth_error xs k = Some x /\ R x y.
Proof.
  intros A B R xs ys k y Hfa; revert k; induction Hfa as [| x0 y0 rx ry Hxy Hrest IH];
    intros [| k'] Hnth; cbn in Hnth; try discriminate Hnth.
  - inversion Hnth; subst y0; exists x0; split; [reflexivity | exact Hxy].
  - exact (IH k' Hnth).
Qed.

Lemma build_cut_ir_binds_nth {Pa : Params} :
  forall idx hdr_ws dvs k w id dv,
    nth_error hdr_ws k = Some w ->
    nth_error dvs k = Some (id, dv) ->
    In (mc_cut_var_name (idx + k), dv) (@build_cut_ir_binds Pa idx hdr_ws dvs).
Proof.
  intros idx hdr_ws; revert idx; induction hdr_ws as [| w0 rw IH];
    intros idx [| [id0 dv0] rd] [| k'] w id dv Hnw Hndv; cbn in Hnw, Hndv;
    try discriminate Hnw; try discriminate Hndv; cbn [build_cut_ir_binds].
  - inversion Hndv; subst; rewrite Nat.add_0_r; left; reflexivity.
  - right; replace (idx + S k')%nat with (S idx + k')%nat by lia; exact (IH (S idx) rd k' w id dv Hnw Hndv).
Qed.

Lemma build_cut_mc_binds_nth {Pa : Params} :
  forall ls penv_prev rr mstk idx hdr_ws phis_ir dvs k w wp ce id dv,
    nth_error hdr_ws k = Some w ->
    nth_error phis_ir k = Some (wp, ce) ->
    nth_error dvs k = Some (id, dv) ->
    let dv_bind :=
      if cut_var_ptol ls (idx + k) w then
        match find_ptol_reg (idx + k) w (ml_regs ls) with
        | Some r =>
            DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive (rr r))))
        | None =>
            match find_ptol_slot (idx + k) w (ml_slots ls) with
            | Some (off, sz) =>
                DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))
            | None =>
                match dv with
                | DVALUE_Base (@DVALUE_I _ wp' vi) =>
                    if Pos.eqb wp' w then DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned wp' vi)))
                    else DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
                | _ => DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
                end
            end
        end
      else
        match eval_closed_cert_expr penv_prev dummy_freeze_oracle ce with
        | raise_ret (DVALUE_Base (@DVALUE_I _ wp' vi)) =>
            if Pos.eqb wp' w then DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned wp' vi)))
            else DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
        | _ => DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
        end in
    In (mc_cut_var_name (idx + k), dv_bind)
       (@build_cut_mc_binds Pa ls penv_prev rr mstk idx hdr_ws phis_ir dvs).
Proof.
  intros ls penv_prev rr mstk idx hdr_ws; revert idx;
    induction hdr_ws as [| w0 rw IH];
    intros idx [| [wp0 ce0] rp] [| [id0 dv0] rd] [| k'] w wp ce id dv Hnw Hnp Hndv;
    cbn in Hnw, Hnp, Hndv; try discriminate Hnw; try discriminate Hnp; try discriminate Hndv;
    cbn [build_cut_mc_binds].
  - inversion Hnw; inversion Hnp; inversion Hndv; subst; rewrite Nat.add_0_r; left; reflexivity.
  - right; replace (idx + S k')%nat with (S idx + k')%nat by lia; exact (IH (S idx) rp rd k' w wp ce id dv Hnw Hnp Hndv).
Qed.

Lemma build_hi32_binds_in {Pa : Params} :
  forall (rr : N -> @Integers.bit_int 64%positive) rbs rb,
    In rb rbs ->
    mlr_width rb = 32%positive ->
    In (mc_hi_var_name (mlr_reg rb), DVALUE_Base (@DVALUE_I Pa 64%positive (rr (mlr_reg rb))))
       (build_hi32_binds rr rbs).
Proof.
  intros rr rbs rb Hin Hw32; unfold build_hi32_binds; apply in_flat_map; exists rb; split; [exact Hin |].
  rewrite Hw32, Pos.eqb_refl; left; reflexivity.
Qed.

Lemma find_ptol_reg_In : forall k w rbs r,
  find_ptol_reg k w rbs = Some r ->
  exists rb, In rb rbs /\ mlr_reg rb = r /\ is_exact_cut_var k w (mlr_expr rb) = true.
Proof.
  intros k w rbs; induction rbs as [| rb rest IH]; intros r H; cbn in H; [discriminate H |].
  destruct (is_exact_cut_var k w (mlr_expr rb)) eqn:Ex.
  - inversion H; subst; exists rb; repeat split; [left; reflexivity | exact Ex].
  - destruct (IH r H) as (rb0 & Hin & Heqr & Ex0); exists rb0; repeat split; [right; exact Hin | exact Heqr | exact Ex0].
Qed.

Lemma find_ptol_slot_In : forall k w sbs off sz,
  find_ptol_slot k w sbs = Some (off, sz) ->
  exists e, In (MLS_Expr off sz e) sbs /\ is_exact_cut_var k w e = true.
Proof.
  intros k w sbs; induction sbs as [| [o0 s0 e0 | o0 r0] rest IH]; intros off sz H; cbn in H; [discriminate H | |].
  - destruct (is_exact_cut_var k w e0) eqn:Ex.
    + inversion H; subst; exists e0; split; [left; reflexivity | exact Ex].
    + destruct (IH off sz H) as [e [Hin Ex0]]; exists e; split; [right; exact Hin | exact Ex0].
  - destruct (IH off sz H) as [e [Hin Ex0]]; exists e; split; [right; exact Hin | exact Ex0].
Qed.

Lemma trunc_mc_expr_to_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle w e64 (v64 : @Integers.bit_int 64%positive),
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (trunc_mc_expr_to w e64) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive v64)))).
Proof.
  intros penv foracle w e64 v64 [-> | ->] He; unfold trunc_mc_expr_to; cbn [Pos.eqb].
  - apply eval_ce_trunc; [reflexivity | exact He].
  - rewrite (@Integers.repr_unsigned 64%positive); exact He.
Qed.

Lemma trunc_mc_slot_expr_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle sz e64 (v64 : @Integers.bit_int 64%positive),
    eval_closed_cert_expr penv foracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (trunc_mc_slot_expr sz e64) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive v64)))).
Proof.
  intros penv foracle sz e64 v64 He; destruct sz; unfold trunc_mc_slot_expr; cbn [mc_mem_bits].
  - apply eval_ce_trunc; [reflexivity | exact He].
  - apply eval_ce_trunc; [reflexivity | exact He].
  - apply eval_ce_trunc; [reflexivity | exact He].
  - rewrite (@Integers.repr_unsigned 64%positive); exact He.
Qed.

Lemma cut_vars_from_ws_In : forall idx ws nm w,
  In (nm, w) (cut_vars_from_ws idx ws) ->
  exists k, nm = mc_cut_var_name (idx + k) /\ nth_error ws k = Some w.
Proof.
  intros idx ws; revert idx; induction ws as [| w0 rest IH]; intros idx nm w Hin;
    cbn [cut_vars_from_ws] in Hin; [contradiction |].
  destruct Hin as [Heq | Hr].
  - inversion Heq; subst; exists 0%nat; rewrite Nat.add_0_r; split; reflexivity.
  - destruct (IH (S idx) nm w Hr) as [k [Hnm Hnth]]; exists (S k);
      split; [rewrite Hnm; f_equal; lia | exact Hnth].
Qed.

Lemma hi32_vars_In : forall ls nm w,
  In (nm, w) (hi32_vars ls) ->
  exists rb, In rb (ml_regs ls) /\ mlr_width rb = 32%positive /\ nm = mc_hi_var_name (mlr_reg rb) /\ w = 64%positive.
Proof.
  intros ls nm w Hin; unfold hi32_vars in Hin; apply in_flat_map in Hin as [rb [Hrb Hhere]].
  destruct (Pos.eqb (mlr_width rb) 32%positive) eqn:Ew; cbn in Hhere; [| contradiction].
  destruct Hhere as [Heq | []]; inversion Heq; subst; apply Pos.eqb_eq in Ew.
  exists rb; repeat split; assumption.
Qed.

Lemma wf_mc_loop_reg_bind_props : forall arch ls rb,
  wf_mc_loop_spec arch ls = true -> In rb (ml_regs ls) ->
  (mlr_width rb = 32%positive \/ mlr_width rb = 64%positive) /\
  wt_cert_expr [] (mlr_expr rb) = true /\
  cert_expr_bit_width (mlr_expr rb) = mlr_width rb /\
  is_let_free_expr (mlr_expr rb) = true /\
  ub_free_expr (mlr_expr rb) = true.
Proof.
  intros arch ls rb Hwf Hrb; unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & _) & Hwbr) & _) & _) & _).
  rewrite forallb_forall in Hwbr; pose proof (Hwbr rb Hrb) as Hwrb.
  unfold wf_mc_loop_reg_bind in Hwrb; rewrite !andb_true_iff in Hwrb.
  destruct Hwrb as (((((_ & Hw) & Hwt) & Hbw) & Hlf) & Hub).
  apply orb_true_iff in Hw; apply Pos.eqb_eq in Hbw.
  split; [destruct Hw as [H32 | H64]; [left; apply Pos.eqb_eq; exact H32 | right; apply Pos.eqb_eq; exact H64] |].
  repeat split; assumption.
Qed.

Lemma wf_mc_loop_slot_bind_props : forall arch ls off sz e,
  wf_mc_loop_spec arch ls = true -> In (MLS_Expr off sz e) (ml_slots ls) ->
  wt_cert_expr [] e = true /\
  cert_expr_bit_width e = mc_mem_bits sz /\
  is_let_free_expr e = true /\
  ub_free_expr e = true.
Proof.
  intros arch ls off sz e Hwf Hs; unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & _) & _) & Hwbs) & _) & _).
  rewrite forallb_forall in Hwbs; pose proof (Hwbs (MLS_Expr off sz e) Hs) as Hwsb.
  unfold wf_mc_loop_slot_bind in Hwsb; rewrite !andb_true_iff in Hwsb.
  destruct Hwsb as ((((_ & Hwt) & Hbw) & Hlf) & Hub); apply Pos.eqb_eq in Hbw.
  repeat split; assumption.
Qed.

Lemma build_next_cut_penvs_sound {Pa : Params} :
  forall arch ls allowed0 mc_init_ctx (penv0 penv_ir_prev penv_mc_prev : param_env Pa)
         hdr_ws phis_ir dvs (read_reg : N -> @Integers.bit_int 64%positive) mstk opt_inv is_body path,
    wf_mc_loop_spec arch ls = true ->
    (forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall nm, mc_starts_with_bang nm = false -> penv_ir_prev nm = penv0 nm /\ penv_mc_prev nm = penv0 nm) ->
    vars_subset_b (collect_free_vars [] (match ml_inv ls with None => CE_BvConst 1%positive 1%N | Some inv => inv end)) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) = true ->
    (forall rb, In rb (ml_regs ls) -> vars_subset_b (collect_free_vars [] (mlr_expr rb)) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) = true) ->
    (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) -> vars_subset_b (collect_free_vars [] e) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) = true) ->
    Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir ->
    Forall2 (fun '(wp, ce) '(_, dv) =>
      eval_closed_cert_expr penv_ir_prev dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue wp dv) phis_ir dvs ->
    (is_body = true ->
     match opt_inv with
     | None => True
     | Some inv_e => eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle inv_e = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end) ->
    (forall (b : bool) (c : cert_expr), In (b, c) path ->
       eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (fun '(wp, ce) =>
      wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
      is_let_free_expr ce = true /\ ub_free_expr ce = true /\
      expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) (allowed0 ++ cut_vars_from_ws 0%nat (if is_body then hdr_ws else []))) phis_ir ->
    (forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat (if is_body then hdr_ws else [])) ->
       exists d1 d2 : @dvalue Pa, penv_ir_prev nm = Some d1 /\ penv_mc_prev nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) ->
    (forall k w ce,
       nth_error phis_ir k = Some (w, ce) ->
       cut_var_ptol ls k w = false ->
       exists vi, eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) ->
    (forall rb, In rb (ml_regs ls) ->
       exists e_mc64,
         eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb)))) /\
         mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
           (MLO_Refine is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
         (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false ->
          mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
            (MLO_Defined is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))) ->
    (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) ->
       exists e_mc64,
         eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk off sz false))) /\
         mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
           (MLO_Refine is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
         (expr_is_ptol_var ls hdr_ws e_s = false ->
          mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
            (MLO_Defined is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))) ->
    match ml_inv ls with
    | None => True
    | Some inv_e =>
        mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
          (MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e))
    end ->
    let ir_binds := build_cut_ir_binds 0%nat hdr_ws dvs in
    let mc_binds := build_cut_mc_binds ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs ++ build_hi32_binds read_reg (ml_regs ls) in
    let penv_ir_next := overlay_penv ir_binds penv0 in
    let penv_mc_next := overlay_penv mc_binds penv0 in
    (forall nm, mc_starts_with_bang nm = false -> penv_ir_next nm = penv0 nm /\ penv_mc_next nm = penv0 nm) /\
    wf_param_env_for (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls) penv_mc_next /\
    ub_ctx_holds penv_mc_next dummy_freeze_oracle
      (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) /\
    (forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) ->
       exists d1 d2 : @dvalue Pa, penv_ir_next nm = Some d1 /\ penv_mc_next nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) /\
    (forall k id w dv,
       nth_error hdr_ws k = Some w ->
       nth_error dvs k = Some (id, dv) ->
       penv_ir_next (mc_cut_var_name k) = Some dv /\ wf_scalar_dvalue w dv) /\
    mc_cut_obl_inv_holds ls penv_mc_next dummy_freeze_oracle /\
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv_mc_next dummy_freeze_oracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (read_reg (mlr_reg rb)))))) /\
       (mlr_width rb = 32%positive ->
          penv_mc_next (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb)))))) /\
    (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) ->
       eval_closed_cert_expr penv_mc_next dummy_freeze_oracle e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false)))))).
Proof.
  intros arch ls allowed0 mc_init_ctx penv0 penv_ir_prev penv_mc_prev hdr_ws phis_ir dvs read_reg mstk opt_inv is_body path.
  intros Hwf Hnb_al Hpenv0 Hctx0 Hprev Hinv_sub Hreg_sub Hslt_sub Hws Hph Hinv_p Hpath_p Hph_wf Href_p Hphi_d Hregs Hslts Hmi.
  intros ir_binds mc_binds penv_ir_next penv_mc_next.
  assert (Hnd_r : NoDup (List.map mlr_reg (ml_regs ls))).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
    destruct Hwf as (((((((_ & _) & _) & Hnd_b) & _) & _) & _) & _); rewrite mc_map_tr_eq in Hnd_b; exact (no_dup_N_to_NoDup _ Hnd_b). }
  assert (Hnd_ir : NoDup (List.map fst ir_binds)) by exact (build_cut_ir_binds_nodup 0%nat hdr_ws dvs).
  assert (Hnd_mc : NoDup (List.map fst mc_binds)) by exact (build_cut_mc_hi_nodup ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs Hnd_r).
  assert (Hnb_next : forall nm, mc_starts_with_bang nm = false -> penv_ir_next nm = penv0 nm /\ penv_mc_next nm = penv0 nm).
  { intros nm Hnb; split.
    - apply overlay_penv_non_bang; [| exact Hnb]; intros y Hy; exact (build_cut_ir_binds_bang _ _ _ _ Hy).
    - apply overlay_penv_non_bang; [| exact Hnb]; intros y Hy; exact (build_cut_mc_hi_bang _ _ _ _ _ _ _ _ _ Hy). }
  assert (Hcut_facts : forall k w, nth_error hdr_ws k = Some w ->
    exists id dv_ir ce vi_mc,
      nth_error phis_ir k = Some (w, ce) /\
      nth_error dvs k = Some (id, dv_ir) /\
      penv_ir_next (mc_cut_var_name k) = Some dv_ir /\
      wf_scalar_dvalue w dv_ir /\
      penv_mc_next (mc_cut_var_name k) = Some (DVALUE_Base (@DVALUE_I Pa w vi_mc)) /\
      dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa w vi_mc)) /\
      (cut_var_ptol ls k w = false ->
       eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi_mc)))).
  { intros k w Hnw.
    destruct (Forall2_nth_error_l_ex _ _ _ k w Hws Hnw) as [[wp ce] [Hnp Hweq]]; subst wp.
    destruct (Forall2_nth_error_l_ex _ _ _ k (w, ce) Hph Hnp) as [[id dv_ir] [Hndv [Hev_ir Hsc_ir]]].
    assert (Hir_k : penv_ir_next (mc_cut_var_name k) = Some dv_ir).
    { unfold penv_ir_next; apply overlay_penv_lookup_in; [exact Hnd_ir |].
      unfold ir_binds; replace k with (0%nat + k)%nat by lia; exact (build_cut_ir_binds_nth 0%nat hdr_ws dvs k w id dv_ir Hnw Hndv). }
    pose proof (build_cut_mc_binds_nth ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs k w w ce id dv_ir Hnw Hnp Hndv) as Hin_mc.
    rewrite Nat.add_0_l in Hin_mc; set (dv_b := if cut_var_ptol ls k w then _ else _) in Hin_mc.
    assert (Hmc_k : penv_mc_next (mc_cut_var_name k) = Some dv_b).
    { unfold penv_mc_next; apply overlay_penv_lookup_in; [exact Hnd_mc | unfold mc_binds; apply in_or_app; left; exact Hin_mc]. }
    assert (Hce_wf : wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = w /\ is_let_free_expr ce = true /\
      ub_free_expr ce = true /\ expr_has_freeze ce = false /\
      incl (collect_free_vars [] ce) (allowed0 ++ cut_vars_from_ws 0%nat (if is_body then hdr_ws else []))).
    { rewrite Forall_forall in Hph_wf; exact (Hph_wf (w, ce) (nth_error_In _ k Hnp)). }
    destruct Hce_wf as (Hwt_c & Hbw_c & Hlf_c & Hub_c & Hnf_c & Hfv_c).
    destruct (eval_cert_expr_refine_mono penv_ir_prev penv_mc_prev dummy_freeze_oracle ce Hwt_c Hlf_c Hub_c Hnf_c
                (fun x wx Hx => Href_p x wx (Hfv_c (x, wx) Hx)))
      as (v1 & v2 & Ev1 & Ev2 & _ & W2 & R12).
    rewrite Hev_ir in Ev1; inversion Ev1; subst v1; rewrite Hbw_c in W2.
    unfold dv_b in Hmc_k; destruct (cut_var_ptol ls k w) eqn:Ept.
    - destruct (find_ptol_reg k w (ml_regs ls)) as [r |] eqn:Epr.
      + apply find_ptol_reg_In in Epr as [rb [Hrb [<- Hex_rb]]].
        destruct rb as [r0 w0 e0]; cbn in Hex_rb; destruct e0 as [| | nm_rb w_rb | | | | | |]; try discriminate Hex_rb.
        cbn in Hex_rb; apply andb_true_iff in Hex_rb as [Hnm Hw0]; apply String.eqb_eq in Hnm; apply Pos.eqb_eq in Hw0.
        destruct (wf_mc_loop_reg_bind_props arch ls _ Hwf Hrb) as (Hw32_64 & _ & Hbw_rb & _ & _); cbn in Hbw_rb.
        rewrite Hbw_rb in Hw0; subst w0; cbn [mlr_width mlr_expr mlr_reg] in *.
        eexists id, dv_ir, ce, (@Integers.repr w (@Integers.unsigned 64%positive (read_reg r0))).
        repeat split; try assumption; [| intro C; discriminate C].
        destruct Hsc_ir as [-> | [vi_ir ->]]; [apply dvalue_refines_poison_l |].
        assert (Hv2_eq : v2 = DVALUE_Base (@DVALUE_I Pa w vi_ir)).
        { destruct R12 as [Hc | ->]; [discriminate Hc | reflexivity]. }
        subst v2; destruct (Hregs _ Hrb) as (e_mc64 & Ev_mc & Ho_r & _).
        pose proof (Ho_r eq_refl Hinv_p Hpath_p) as Href_o; cbn [mlr_width mlr_expr mlr_reg] in *.
        assert (Hsub_ce : subst_cert_expr (build_phi_subst 0%nat phis_ir) (CE_Var nm_rb w_rb) = ce).
        { cbn [subst_cert_expr]; rewrite Hnm, Hbw_rb.
          replace k with (0%nat + k)%nat by lia; rewrite (lookup_phi_subst_some 0%nat phis_ir k w ce Hnp), Pos.eqb_refl; reflexivity. }
        cbn [refine_eou_dvalue] in Href_o; rewrite Hsub_ce, Ev2, (trunc_mc_expr_to_sound _ _ w e_mc64 _ Hw32_64 Ev_mc) in Href_o.
        destruct Href_o as [Hc | Href_o]; [discriminate Hc | right; exact Href_o].
      + destruct (find_ptol_slot k w (ml_slots ls)) as [[off sz] |] eqn:Eps.
        * apply find_ptol_slot_In in Eps as [e0 [Hs0 Hex_s]].
          destruct e0 as [| | nm_s w_s | | | | | |]; try discriminate Hex_s; cbn in Hex_s; apply andb_true_iff in Hex_s as [Hnm Hw0].
          apply String.eqb_eq in Hnm; apply Pos.eqb_eq in Hw0.
          destruct (wf_mc_loop_slot_bind_props arch ls off sz _ Hwf Hs0) as (_ & Hbw_s & _ & _); cbn in Hbw_s.
          rewrite Hbw_s in Hw0; subst w.
          eexists id, dv_ir, ce, (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))).
          repeat split; try assumption; [| intro C; discriminate C].
          destruct Hsc_ir as [-> | [vi_ir ->]]; [apply dvalue_refines_poison_l |].
          assert (Hv2_eq : v2 = DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) vi_ir)).
          { destruct R12 as [Hc | ->]; [discriminate Hc | reflexivity]. }
          subst v2; destruct (Hslts off sz _ Hs0) as (e_mc64 & Ev_mc & Ho_r & _).
          assert (Hsub_ce : subst_cert_expr (build_phi_subst 0%nat phis_ir) (CE_Var nm_s w_s) = ce).
          { cbn [subst_cert_expr]; rewrite Hnm, Hbw_s.
            replace k with (0%nat + k)%nat by lia; rewrite (lookup_phi_subst_some 0%nat phis_ir k (mc_mem_bits sz) ce Hnp), Pos.eqb_refl; reflexivity. }
          cbn [refine_eou_dvalue] in Ho_r; pose proof (Ho_r eq_refl Hinv_p Hpath_p) as Href_o.
          rewrite Hsub_ce, Ev2, (trunc_mc_slot_expr_sound _ _ sz e_mc64 _ Ev_mc) in Href_o.
          destruct Href_o as [Hc | Href_o]; [discriminate Hc | right; exact Href_o].
        * destruct Hsc_ir as [-> | [vi_ir ->]].
          -- eexists id, (DVALUE_Base DVALUE_Poison), ce, (@Integers.zero w); repeat split; try assumption;
               [left; reflexivity | apply dvalue_refines_poison_l | intro C; discriminate C].
          -- rewrite Pos.eqb_refl, (@Integers.repr_unsigned w vi_ir) in Hmc_k; eexists id, (DVALUE_Base (@DVALUE_I Pa w vi_ir)), ce, vi_ir;
               repeat split; try assumption; [right; exists vi_ir; reflexivity | apply dvalue_refines_refl | intro C; discriminate C].
    - destruct (Hphi_d k w ce Hnp Ept) as [vi_d Hev_d].
      rewrite Hev_d in Hmc_k, Ev2; inversion Ev2; subst v2; rewrite Pos.eqb_refl, (@Integers.repr_unsigned w vi_d) in Hmc_k.
      eexists id, dv_ir, ce, vi_d; repeat split; try assumption; intros _; exact Hev_d. }
  assert (Hcut_ref : forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) ->
    exists d1 d2 : @dvalue Pa, penv_ir_next nm = Some d1 /\ penv_mc_next nm = Some d2 /\
      wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2).
  { intros nm w Hin; apply in_app_iff in Hin as [Hal | Hcut].
    - destruct (Hpenv0 nm w Hal) as [d0 [Hp0 Hwf0]].
      destruct (Hnb_next nm (Hnb_al nm w Hal)) as [-> ->].
      exists d0, d0; repeat split; try assumption; apply dvalue_refines_refl.
    - apply cut_vars_from_ws_In in Hcut as [k [-> Hnw]].
      destruct (Hcut_facts k w Hnw) as (id & dv_ir & ce & vi_mc & _ & _ & Hir_k & Hsc_ir & Hmc_k & Href_k & _).
      rewrite Nat.add_0_l; exists dv_ir, (DVALUE_Base (@DVALUE_I Pa w vi_mc)); repeat split; try assumption.
      right; exists vi_mc; reflexivity. }
  assert (Hhi_lookup : forall rb, In rb (ml_regs ls) -> mlr_width rb = 32%positive ->
    penv_mc_next (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb))))).
  { intros rb Hrb Hw32; unfold penv_mc_next; apply overlay_penv_lookup_in; [exact Hnd_mc |].
    unfold mc_binds; apply in_or_app; right; exact (build_hi32_binds_in read_reg (ml_regs ls) rb Hrb Hw32). }
  assert (Hmc_wf : wf_param_env_for (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls) penv_mc_next).
  { intros nm w Hin; apply in_app_iff in Hin as [Hal | Hgh].
    - destruct (Hcut_ref nm w (in_or_app _ _ _ (or_introl Hal))) as (_ & d2 & _ & Hmc_n & _ & Hw2 & _); exists d2; split; assumption.
    - apply in_app_iff in Hgh as [Hcut | Hhi].
      + destruct (Hcut_ref nm w (in_or_app _ _ _ (or_intror Hcut))) as (_ & d2 & _ & Hmc_n & _ & Hw2 & _); exists d2; split; assumption.
      + apply hi32_vars_In in Hhi as (rb & Hrb & Hw32 & -> & ->).
        eexists; split; [exact (Hhi_lookup rb Hrb Hw32) | right; eexists; reflexivity]. }
  assert (Hctx_next : ub_ctx_holds penv_mc_next dummy_freeze_oracle
    (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls))).
  { apply Forall_app; split; [apply Hctx0; intros nm Hnb; exact (proj2 (Hnb_next nm Hnb)) |].
    apply Forall_forall; intros ua Hin; apply in_map_iff in Hin as [[nm w] [<- Hgh]].
    apply in_app_iff in Hgh as [Hcut | Hhi].
    - apply cut_vars_from_ws_In in Hcut as [k [-> Hnw]]; rewrite Nat.add_0_l.
      destruct (Hcut_facts k w Hnw) as (_ & _ & _ & vi_mc & _ & _ & _ & _ & Hmc_k & _).
      cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hmc_k in Hdv; inversion Hdv; discriminate.
    - apply hi32_vars_In in Hhi as (rb & Hrb & Hw32 & -> & ->).
      cbn [ub_assumption_holds]; intros dv Hdv; rewrite (Hhi_lookup rb Hrb Hw32) in Hdv; inversion Hdv; discriminate. }
  assert (Hsubst_non_ptol : forall e,
    is_let_free_expr e = true ->
    vars_subset_b (collect_free_vars [] e) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) = true ->
    (forall k w, nth_error hdr_ws k = Some w -> cut_var_ptol ls k w = true ->
       forall w0, ~ In (mc_cut_var_name k, w0) (collect_free_vars [] e)) ->
    eval_closed_cert_expr penv_mc_next dummy_freeze_oracle e =
    eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle (subst_cert_expr (build_phi_subst 0%nat phis_ir) e)).
  { intros e Hlf Hsub Hav; apply subst_cert_expr_eval; [exact dummy_freeze_oracle_const | exact Hlf |].
    intros nm wn Hfn.
    pose proof (vars_subset_b_incl _ _ Hsub _ Hfn) as Hin_all.
    apply in_app_iff in Hin_all as [Hal | Hcut].
    - pose proof (Hnb_al nm wn Hal) as Hnb.
      rewrite (lookup_phi_subst_none_non_bang 0%nat phis_ir nm Hnb).
      rewrite (proj2 (Hnb_next nm Hnb)), (proj2 (Hprev nm Hnb)); reflexivity.
    - apply cut_vars_from_ws_In in Hcut as [k [Heqn Hnw]]; rewrite Nat.add_0_l in Heqn; subst nm.
      destruct (Hcut_facts k wn Hnw) as (_ & _ & ce & vi_mc & Hnp & _ & _ & _ & Hmc_k & _ & Hprev_k).
      replace k with (0%nat + k)%nat by lia; rewrite (lookup_phi_subst_some 0%nat phis_ir k wn ce Hnp).
      destruct (cut_var_ptol ls k wn) eqn:Ept; [exfalso; exact (Hav k wn Hnw Ept wn Hfn) |].
      split; [reflexivity | exists (DVALUE_Base (@DVALUE_I Pa wn vi_mc)); split; [exact Hmc_k | split; [right; eexists; reflexivity | exact (Hprev_k eq_refl)]]]. }
  assert (Hinv_next : mc_cut_obl_inv_holds ls penv_mc_next dummy_freeze_oracle).
  { unfold mc_cut_obl_inv_holds; destruct (ml_inv ls) as [inv_e |] eqn:Emi; [| exact I].
    unfold wf_mc_loop_spec in Hwf; rewrite Emi, !andb_true_iff in Hwf.
    destruct Hwf as (((((((_ & _) & _) & _) & _) & _) & _) & ((_ & _) & Hlf_i) & _).
    rewrite (Hsubst_non_ptol inv_e Hlf_i Hinv_sub (fun k w _ Hpt => cut_var_ptol_inv_not_in ls k w inv_e Hpt Emi)).
    pose proof (Hmi eq_refl Hinv_p Hpath_p) as Href_i.
    cbn [refine_eou_dvalue eval_closed_cert_expr eval_cert_expr] in Href_i; rewrite repr_one_N in Href_i.
    destruct (eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e))
      as [| | | dv_i] eqn:Evi; try contradiction.
    destruct Href_i as [Hc | <-]; [discriminate Hc | reflexivity]. }
  assert (Hregs_next : forall rb, In rb (ml_regs ls) ->
    eval_closed_cert_expr penv_mc_next dummy_freeze_oracle (mlr_expr rb) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (read_reg (mlr_reg rb)))))) /\
    (mlr_width rb = 32%positive ->
       penv_mc_next (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb)))))).
  { intros rb Hrb; split; [| exact (Hhi_lookup rb Hrb)].
    destruct (wf_mc_loop_reg_bind_props arch ls rb Hwf Hrb) as (Hw32_64 & _ & Hbw_rb & Hlf_rb & _).
    destruct (expr_is_ptol_var ls hdr_ws (mlr_expr rb)) eqn:Eptv.
    - apply expr_is_ptol_var_at_spec in Eptv as (k & w & _ & Hnw & He_eq & Hpt).
      rewrite Nat.sub_0_r in Hnw; rewrite He_eq in Hbw_rb |- *; cbn [cert_expr_bit_width] in Hbw_rb; subst w.
      pose proof (cut_var_ptol_count_split ls k (mlr_width rb) Hpt) as Hcnt.
      assert (Hle1 : (List.length (List.filter (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) (ml_regs ls)) <= 1)%nat) by lia.
      pose proof (find_ptol_reg_spec k (mlr_width rb) (ml_regs ls) rb Hle1 Hrb ltac:(rewrite He_eq; cbn; rewrite String.eqb_refl, Pos.eqb_refl; reflexivity)) as Efnd.
      destruct (Forall2_nth_error_l_ex _ _ _ k (mlr_width rb) Hws Hnw) as [[wp ce] [Hnp <-]].
      destruct (Forall2_nth_error_l_ex _ _ _ k (mlr_width rb, ce) Hph Hnp) as [[id dv_ir] [Hndv _]].
      pose proof (build_cut_mc_binds_nth ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs k (mlr_width rb) (mlr_width rb) ce id dv_ir Hnw Hnp Hndv) as Hin_mc.
      rewrite Nat.add_0_l, Hpt, Efnd in Hin_mc.
      assert (Hpv : penv_mc_next (mc_cut_var_name k) = Some (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (read_reg (mlr_reg rb))))))).
      { unfold penv_mc_next; apply overlay_penv_lookup_in; [exact Hnd_mc | unfold mc_binds; apply in_or_app; left; exact Hin_mc]. }
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hpv; cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    - rewrite (Hsubst_non_ptol (mlr_expr rb) Hlf_rb (Hreg_sub rb Hrb)
                 (fun k w Hnw Hpt => expr_not_ptol_var_avoids_ptol ls hdr_ws (mlr_expr rb) k w Eptv Hnw Hpt (cut_var_ptol_reg_uses ls k w rb Hpt Hrb))).
      destruct (Hregs rb Hrb) as (e_mc64 & Ev_mc & Ho_r & Ho_d).
      destruct (Ho_d Eptv eq_refl Hinv_p Hpath_p) as [v_def Ev_def].
      pose proof (Ho_r eq_refl Hinv_p Hpath_p) as Href_o.
      cbn [refine_eou_dvalue] in Href_o; rewrite Ev_def, (trunc_mc_expr_to_sound _ _ (mlr_width rb) e_mc64 _ Hw32_64 Ev_mc) in Href_o.
      destruct Href_o as [Hpois | Heqv]; [discriminate Hpois | rewrite Heqv; exact Ev_def]. }
  assert (Hslts_next : forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) ->
    eval_closed_cert_expr penv_mc_next dummy_freeze_oracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false)))))).
  { intros off sz e Hs; destruct (wf_mc_loop_slot_bind_props arch ls off sz e Hwf Hs) as (_ & Hbw_s & Hlf_s & _).
    destruct (expr_is_ptol_var ls hdr_ws e) eqn:Eptv.
    - apply expr_is_ptol_var_at_spec in Eptv as (k & w & _ & Hnw & He_eq & Hpt).
      rewrite Nat.sub_0_r in Hnw; rewrite He_eq in Hbw_s |- *; cbn [cert_expr_bit_width] in Hbw_s; subst w.
      pose proof (cut_var_ptol_count_split ls k (mc_mem_bits sz) Hpt) as Hcnt.
      assert (Hreg0 : List.length (List.filter (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) (ml_regs ls)) = 0%nat).
      { pose proof (length_filter_ge1 (fun sb : mc_loop_slot_bind => match sb with MLS_Expr _ _ e0 => expr_has_var (mc_cut_var_name k) e0 | MLS_SavedReg _ _ => false end) (ml_slots ls) (MLS_Expr off sz e)
                      ltac:(rewrite He_eq; cbn; rewrite String.eqb_refl; reflexivity) Hs) as Hgt; lia. }
      assert (Hle1 : (List.length (List.filter (fun sb => match sb with MLS_Expr _ _ e0 => expr_has_var (mc_cut_var_name k) e0 | MLS_SavedReg _ _ => false end) (ml_slots ls)) <= 1)%nat) by lia.
      pose proof (find_ptol_reg_none_when_zero k (mc_mem_bits sz) (ml_regs ls) Hreg0) as Enr.
      pose proof (find_ptol_slot_spec k (mc_mem_bits sz) (ml_slots ls) off sz e Hle1 Hs
                    ltac:(rewrite He_eq; cbn; rewrite String.eqb_refl, Pos.eqb_refl; reflexivity)) as Efs.
      destruct (Forall2_nth_error_l_ex _ _ _ k (mc_mem_bits sz) Hws Hnw) as [[wp ce] [Hnp <-]].
      destruct (Forall2_nth_error_l_ex _ _ _ k (mc_mem_bits sz, ce) Hph Hnp) as [[id dv_ir] [Hndv _]].
      pose proof (build_cut_mc_binds_nth ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs k (mc_mem_bits sz) (mc_mem_bits sz) ce id dv_ir Hnw Hnp Hndv) as Hin_mc.
      rewrite Nat.add_0_l, Hpt, Enr, Efs in Hin_mc.
      assert (Hpv : penv_mc_next (mc_cut_var_name k) = Some (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false)))))).
      { unfold penv_mc_next; apply overlay_penv_lookup_in; [exact Hnd_mc | unfold mc_binds; apply in_or_app; left; exact Hin_mc]. }
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hpv; cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    - rewrite (Hsubst_non_ptol e Hlf_s (Hslt_sub off sz e Hs)
                 (fun k w Hnw Hpt => expr_not_ptol_var_avoids_ptol ls hdr_ws e k w Eptv Hnw Hpt (cut_var_ptol_slot_uses ls k w off sz e Hpt Hs))).
      destruct (Hslts off sz e Hs) as (e_mc64 & Ev_mc & Ho_r & Ho_d).
      destruct (Ho_d Eptv eq_refl Hinv_p Hpath_p) as [v_def Ev_def].
      pose proof (Ho_r eq_refl Hinv_p Hpath_p) as Href_o.
      cbn [refine_eou_dvalue] in Href_o; rewrite Ev_def, (trunc_mc_slot_expr_sound _ _ sz e_mc64 _ Ev_mc) in Href_o.
      destruct Href_o as [Hpois | Heqv]; [discriminate Hpois | rewrite Heqv; exact Ev_def]. }
  split; [exact Hnb_next |].
  split; [exact Hmc_wf |].
  split; [exact Hctx_next |].
  split; [exact Hcut_ref |].
  split.
  { intros k id w dv Hnw Hndv; destruct (Hcut_facts k w Hnw) as (id0 & dv0 & _ & _ & _ & Hndv0 & Hir_k & Hsc_k & _).
    rewrite Hndv in Hndv0; inversion Hndv0; subst; split; assumption. }
  split; [exact Hinv_next |].
  split; [exact Hregs_next | exact Hslts_next].
Qed.

Lemma lmap_base_matches_next {Pa : Params} :
  forall allowed0 (penv0 penv_ir_prev penv_ir_next : param_env Pa)
         lmap_base lmap_cut dvs env_c hdr_phis wr_body,
    wf_pure_lmap allowed0 lmap_base ->
    (forall r w ce, RM.find r lmap_base = Some (w, ce) -> RM.find r lmap_cut = Some (w, ce)) ->
    lmap_matches_env penv_ir_prev lmap_cut env_c ->
    (forall nm w, In (nm, w) allowed0 -> penv_ir_next nm = penv_ir_prev nm) ->
    NoDup (List.map fst hdr_phis) ->
    Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs ->
    disjoint_raw_ids (lmap_keys lmap_base) (List.map fst hdr_phis ++ wr_body) = true ->
    (forall k id w dv,
       nth_error hdr_phis k = Some (id, w) ->
       nth_error dvs k = Some (id, dv) ->
       penv_ir_next (mc_cut_var_name k) = Some dv /\ wf_scalar_dvalue w dv) ->
    lmap_matches_env penv_ir_next (wrap_cut_mc lmap_base hdr_phis) (apply_phi_env env_c dvs).
Proof.
  intros allowed0 penv0 penv_ir_prev penv_ir_next lmap_base lmap_cut dvs env_c hdr_phis wr_body
         Hwf_b Hsub Hlm Hagree Hnd_h Hids Hdisj Hphi.
  assert (Hlm_b : lmap_matches_env penv_ir_next lmap_base env_c).
  { apply (lmap_matches_env_penv_agree allowed0 penv_ir_prev penv_ir_next lmap_base env_c Hwf_b (fun nm w H => Logic.eq_sym (Hagree nm w H))).
    intros r w ce Hf; exact (Hlm r w ce (Hsub r w ce Hf)). }
  assert (Hdisj_h : forall r, In r (lmap_keys lmap_base) -> ~ In r (List.map fst hdr_phis)).
  { intros r Hr Hin; pose proof (disjoint_raw_ids_spec _ _ r Hdisj Hr) as Hn; apply Hn, in_or_app; left; exact Hin. }
  exact (wrap_cut_mc_at_matches penv_ir_next lmap_base 0%nat hdr_phis dvs env_c Hlm_b Hnd_h Hids Hdisj_h Hphi).
Qed.

(** Zero-ghost-var initialization helper for initial Entry obligations *)

Definition zero_ghost_binds {Pa : Params} (vs : list (string * positive))
  : list (string * @dvalue Pa) :=
  List.map (fun '(nm, w) => (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w)))) vs.

Lemma zero_ghost_binds_nodup {Pa : Params} :
  forall (ls : mc_loop_spec) (ws : list positive),
    NoDup (List.map mlr_reg (ml_regs ls)) ->
    NoDup (List.map fst (@zero_ghost_binds Pa (cut_vars_from_ws 0%nat ws ++ hi32_vars ls))).
Proof.
  intros ls ws Hnd; unfold zero_ghost_binds.
  replace (List.map fst (List.map (fun '(nm, w) => (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w)))) (cut_vars_from_ws 0%nat ws ++ hi32_vars ls)))
    with (List.map fst (cut_vars_from_ws 0%nat ws ++ hi32_vars ls))
    by (clear; induction (cut_vars_from_ws 0%nat ws ++ hi32_vars ls) as [| [nm w] rest IH]; cbn; [reflexivity | f_equal; exact IH]).
  rewrite List.map_app; apply NoDup_app_intro.
  - clear; generalize 0%nat as idx; induction ws as [| w rw IH]; intro idx; cbn; [constructor |].
    constructor; [| exact (IH (S idx))].
    intro Hin; apply in_map_iff in Hin as [[nm w0] [Hfx Hc]]; cbn in Hfx; subst nm.
    apply cut_vars_from_ws_In in Hc as [k [Heq _]]; apply mc_cut_var_name_inj in Heq; lia.
  - clear ws; unfold hi32_vars in *; generalize dependent (ml_regs ls); intros rbs Hnd.
    induction rbs as [| rb rest IH]; cbn in *; [constructor |].
    inversion Hnd as [| ? ? Hnin Hnr]; subst; destruct (Pos.eqb (mlr_width rb) 32%positive); cbn [app List.map]; [| exact (IH Hnr)].
    constructor; [| exact (IH Hnr)].
    intro Hin; cbn [fst] in Hin; apply in_map_iff in Hin as [[nm w0] [Hfx Hfl]]; cbn [fst] in Hfx; subst nm.
    apply in_flat_map in Hfl as [rb0 [Hrb0 Hhere]].
    destruct (Pos.eqb (mlr_width rb0) 32%positive); cbn in Hhere; [| contradiction].
    destruct Hhere as [Heq | []]; apply (f_equal fst) in Heq; cbn in Heq; apply mc_hi_var_name_inj in Heq.
    apply Hnin; rewrite <- Heq; apply in_map_iff; exists rb0; split; [reflexivity | exact Hrb0].
  - intros x Hxc Hxh.
    apply in_map_iff in Hxc as [[nm w] [Hfx Hc]]; cbn [fst] in Hfx; subst x.
    apply cut_vars_from_ws_In in Hc as [k [Heqc _]]; cbn [Nat.add] in Heqc; subst nm.
    apply in_map_iff in Hxh as [[nm0 w0] [Heq Hh]]; cbn [fst] in Heq; subst nm0.
    apply hi32_vars_In in Hh as [rb [_ [_ [Hdisj _]]]]; exact (mc_cut_hi_disjoint k (mlr_reg rb) Hdisj).
Qed.

Lemma zero_ghost_binds_bang {Pa : Params} :
  forall vs nm,
    In nm (List.map fst (@zero_ghost_binds Pa vs)) ->
    (forall x w, In (x, w) vs -> mc_starts_with_bang x = true) ->
    mc_starts_with_bang nm = true.
Proof.
  intros vs nm Hin Hvs; apply in_map_iff in Hin as [[x dv] [<- Hzm]].
  unfold zero_ghost_binds in Hzm; apply in_map_iff in Hzm as [[x0 w0] [Heq Hxin]]; inversion Heq; subst; exact (Hvs _ _ Hxin).
Qed.

Lemma zero_ghost_binds_wf_ctx {Pa : Params} :
  forall ls ws (penv0 : param_env Pa) allowed0 mc_init_ctx,
    wf_mc_loop_spec EA_Riscv64 ls = true \/ wf_mc_loop_spec EA_AArch64 ls = true ->
    (forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    let ghost := cut_vars_from_ws 0%nat ws ++ hi32_vars ls in
    let penv_ext := overlay_penv (@zero_ghost_binds Pa ghost) penv0 in
    (forall nm, mc_starts_with_bang nm = false -> penv_ext nm = penv0 nm) /\
    wf_param_env_for (allowed0 ++ ghost) penv_ext /\
    ub_ctx_holds penv_ext dummy_freeze_oracle (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) ghost).
Proof.
  intros ls ws penv0 allowed0 mc_init_ctx Hwf Hnb Hpenv0 Hctx0 ghost penv_ext.
  assert (Hnd_r : NoDup (List.map mlr_reg (ml_regs ls))).
  { destruct Hwf as [Hw | Hw]; unfold wf_mc_loop_spec in Hw; rewrite !andb_true_iff in Hw;
      destruct Hw as (((((((_ & _) & _) & Hnd_b) & _) & _) & _) & _); rewrite mc_map_tr_eq in Hnd_b; exact (no_dup_N_to_NoDup _ Hnd_b). }
  assert (Hnd_g : NoDup (List.map fst (@zero_ghost_binds Pa ghost))) by exact (zero_ghost_binds_nodup ls ws Hnd_r).
  assert (Hgb : forall nm w, In (nm, w) ghost -> mc_starts_with_bang nm = true).
  { intros nm w Hg; unfold ghost in Hg; apply in_app_iff in Hg as [Hc | Hh].
    - apply cut_vars_from_ws_In in Hc as [k [-> _]]; reflexivity.
    - apply hi32_vars_In in Hh as (rb & _ & _ & -> & _); reflexivity. }
  assert (Hnb_ext : forall nm, mc_starts_with_bang nm = false -> penv_ext nm = penv0 nm).
  { intros nm Hnbm; apply overlay_penv_non_bang; [| exact Hnbm]; intros y Hy; exact (zero_ghost_binds_bang ghost y Hy Hgb). }
  assert (Hg_lk : forall nm w, In (nm, w) ghost -> penv_ext nm = Some (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w)))).
  { intros nm w Hg; unfold penv_ext; apply overlay_penv_lookup_in; [exact Hnd_g |].
    unfold zero_ghost_binds; apply in_map_iff; exists (nm, w); split; [reflexivity | exact Hg]. }
  repeat split; [exact Hnb_ext | |].
  - intros nm w Hin; apply in_app_iff in Hin as [Hal | Hg].
    + rewrite (Hnb_ext nm (Hnb nm w Hal)); exact (Hpenv0 nm w Hal).
    + exists (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))); split; [exact (Hg_lk nm w Hg) | right; eexists; reflexivity].
  - apply Forall_app; split; [exact (Hctx0 penv_ext Hnb_ext) |].
    apply Forall_forall; intros ua Hin; apply in_map_iff in Hin as [[nm w] [<- Hg]].
    cbn [ub_assumption_holds]; intros dv Hdv; rewrite (Hg_lk nm w Hg) in Hdv; inversion Hdv; discriminate.
Qed.

(** Common Loop Invariant Helper Checks on [prepare_mc_loop_ir] & [check_ls_exprs_vars] *)

Lemma check_ls_exprs_vars_split : forall allowed ls,
  check_ls_exprs_vars allowed ls = true ->
  vars_subset_b (collect_free_vars [] (match ml_inv ls with None => CE_BvConst 1%positive 1%N | Some inv => inv end)) allowed = true /\
  (forall rb, In rb (ml_regs ls) -> vars_subset_b (collect_free_vars [] (mlr_expr rb)) allowed = true) /\
  (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) -> vars_subset_b (collect_free_vars [] e) allowed = true).
Proof.
  intros allowed ls H; unfold check_ls_exprs_vars in H; rewrite !andb_true_iff in H; destruct H as [[Hr Hs] Hi].
  repeat split.
  - destruct (ml_inv ls); [exact Hi | reflexivity].
  - intros rb Hrb; rewrite forallb_forall in Hr; exact (Hr rb Hrb).
  - intros off sz e Hsl; rewrite forallb_forall in Hs; exact (Hs (MLS_Expr off sz e) Hsl).
Qed.

Definition rv_loop_sound_spec {Pa : Params}
  (ir_cfg : CFG.cfg dtyp) (insts : list decoded_rv_inst) (ret_w : positive)
  (ls : mc_loop_spec) (vs : list (@dvalue Pa)) (rf0 : rv_regfile) (mstk0 : mc_stack_mem) : Prop :=
  (forall fuel rf_end mstk_end,
     rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) ->
     rv_callee_saved_preserved rf0 rf_end /\
     rf_end 1%N = rf0 1%N /\
     exists sigma_ir,
       wf_draw_strat sigma_ir /\
       (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
        exists sigma_ir' env_out dv_ir,
          cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
            sigma_ir' env_out dv_ir /\
          dvalue_refines dv_ir
            (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))))) /\
  (forall k : nat,
     (exists fuel rf_end mstk_end,
        rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end)) \/
     (exists n rf_k mstk_k,
        (k <= n)%nat /\
        rv_exec_steps n insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 = Some (ml_mc_pc ls, rf_k, mstk_k) /\
        rv_at_cut ls rf0 rf_k mstk_k)).

Definition a64_loop_sound_spec {Pa : Params}
  (ir_cfg : CFG.cfg dtyp) (insts : list decoded_a64_inst) (ret_w : positive)
  (ls : mc_loop_spec) (vs : list (@dvalue Pa))
  (rf0 : a64_regfile) (sp0 : @Integers.bit_int 64%positive) (fl0 : a64_flags) (mstk0 : mc_stack_mem) : Prop :=
  (forall fuel rf_end sp_end fl_end mstk_end,
     a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end) ->
     sp_end = sp0 /\
     a64_callee_saved_preserved rf0 rf_end /\
     exists sigma_ir,
       wf_draw_strat sigma_ir /\
       (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
        exists sigma_ir' env_out dv_ir,
          cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
            sigma_ir' env_out dv_ir /\
          dvalue_refines dv_ir
            (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))) /\
  (forall k : nat,
     (exists fuel rf_end sp_end fl_end mstk_end,
        a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end)) \/
     (exists n rf_k sp_k fl_k mstk_k,
        (k <= n)%nat /\
        a64_exec_steps n insts sp0 0%N rf0 sp0 fl0 mstk0 = Some (ml_mc_pc ls, rf_k, sp_k, fl_k, mstk_k) /\
        a64_at_cut ls sp0 rf0 rf_k sp_k mstk_k)).

Theorem validate_mc_loop_rv64_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
         (insts : list decoded_rv_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
         (ls : mc_loop_spec) (opt_pf : option (list lrat_step))
         arg_dtys vs (penv0 : param_env Pa) rf0 mstk0,
    validate_mc_loop_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls opt_pf = inr tt ->
    forallb inst_no_word_mulh insts = true ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    cfg_param_dtyp_compatible ir_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (param_idx_uses_cfg ir_cfg) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed0) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv0 nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed0) ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    rv_rf_matches_args penv0 arg_specs rf0 ->
    rv_loop_sound_spec ir_cfg insts ret_w ls vs rf0 mstk0.
Proof.
  intros ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls opt_pf arg_dtys vs penv0 rf0 mstk0
         Hval Hnmul Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp Hty Hpu Hpenv_eq Hpenv0 Hctx0 Hargs_al Hsp0 Hm.
  unfold validate_mc_loop_rv64, build_mc_loop_bundle_rv64 in Hval.
  destruct (check_mc_loop_spec_diag EA_Riscv64 ls) as [| []] eqn:Hwf_d; [discriminate Hval |].
  pose proof (check_mc_loop_spec_diag_sound _ _ Hwf_d) as Hwf.
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hval; [| discriminate Hval].
  rewrite Hnmul in Hval; cbn [negb] in Hval.
  destruct (Nat.leb (List.length arg_specs) 8) eqn:Hlen_args; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (prepare_mc_loop_ir ir_cfg allowed0 ls) as [| prep] eqn:Eprep; [discriminate Hval |].
  rewrite elf_length_tr_eq in Hval; set (mc_fuel := S (2 * List.length insts)) in *.
  set (hdr_ws := extract_hdr_phi_widths (mlip_hdr_phis prep)) in *.
  destruct (summarize_rv64_seg "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z (rv_build_init_val_regs 10%N arg_specs) [] ret_w)
    as [| seg_ent] eqn:Es_ent; [discriminate Hval |].
  destruct (summarize_rv64_seg "body" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls) (rv_cut_vrf ls) (build_cut_astk (ml_slots ls)) ret_w)
    as [| seg_body] eqn:Es_body; [discriminate Hval |].
  destruct (summarize_rv64_seg "skel" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls) (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w)
    as [| seg_skel] eqn:Es_skel; [discriminate Hval |].
  destruct (check_mc_skel_tree_diag "entry" EA_Riscv64 ls (rv_seg_to_mc_seg seg_ent)) as [| []] eqn:Hok_ent_d;
    cbn [bind_err] in Hval; [discriminate Hval |].
  destruct (check_mc_skel_tree_diag "skel" EA_Riscv64 ls (rv_seg_to_mc_seg seg_skel)) as [| []] eqn:Hok_skel_d;
    [discriminate Hval |].
  pose proof (check_mc_skel_tree_diag_sound _ _ _ _ Hok_ent_d) as Hok_ent.
  pose proof (check_mc_skel_tree_diag_sound _ _ _ _ Hok_skel_d) as Hok_skel.
  destruct (collect_mc_ir_obls_acc EA_Riscv64 ls ret_w hdr_ws true [] (mlip_t_ir_body prep) (rv_seg_to_mc_seg seg_body) [])
    as [| obls_body] eqn:Eob_b; [discriminate Hval |].
  destruct (collect_mc_ir_obls_acc EA_Riscv64 ls ret_w hdr_ws false [] (mlip_t_ir_entry prep) (rv_seg_to_mc_seg seg_ent) obls_body)
    as [| obls_all] eqn:Eob_e; [discriminate Hval |].
  rename Hval into Hchk.
  (* Unpack prepare_mc_loop_ir *)
  unfold prepare_mc_loop_ir in Eprep.
  destruct (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) eqn:Hnb_al_b;
    cbn [negb] in Eprep; [| discriminate Eprep].
  assert (Hnb_al : forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false).
  { intros nm w Hin; rewrite forallb_forall in Hnb_al_b; pose proof (Hnb_al_b (nm, w) Hin) as Hn; apply negb_true_iff in Hn; exact Hn. }
  set (bmap := ocfg_map (blks ir_cfg)) in *.
  destruct (find_hdr_block_id (ml_ir_header ls) (blks ir_cfg)) as [hdr_id |] eqn:Ehid; [| discriminate Eprep].
  destruct (RM.find hdr_id bmap) as [b_hdr |] eqn:Ebh; [| discriminate Eprep].
  destruct (extract_hdr_phis (blk_phis b_hdr)) as [| hdr_phis] eqn:Ehp; [discriminate Eprep |].
  destruct (no_dup_raw_ids (List.map fst hdr_phis)) eqn:Hnd_hp_b; cbn [negb] in Eprep; [| discriminate Eprep].
  apply no_dup_raw_ids_spec in Hnd_hp_b.
  set (ir_pnames := List.map cert_reg_name (args ir_cfg)) in *.
  set (lmap_init := init_param_lmap (args ir_cfg) ir_pnames (param_idx_uses_cfg ir_cfg)) in *.
  set (ir_fuel := S (List.length (blks ir_cfg) + 1)) in *.
  destruct (ir_seg_written_ids "entry" ir_fuel bmap hdr_id false [] (init ir_cfg)) as [| wr_ent] eqn:Ewre; [discriminate Eprep |].
  destruct (reify_ir_seg "entry" ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init)
    as [| t_ir_ent] eqn:Ere_ent; [discriminate Eprep |].
  set (lmap_base := common_cut_lmap lmap_init (collect_entry_cut_lmaps t_ir_ent)) in *.
  set (lmap_cut := wrap_cut_mc lmap_base hdr_phis) in *.
  destruct (ir_seg_written_ids "body" ir_fuel bmap hdr_id true [] hdr_id) as [| wr_body] eqn:Ewrb; [discriminate Eprep |].
  destruct (reify_ir_seg "body" ir_fuel bmap hdr_id hdr_phis true [] hdr_id hdr_id lmap_cut)
    as [| t_ir_body] eqn:Ere_body; [discriminate Eprep |].
  destruct (disjoint_raw_ids (lmap_keys lmap_base) (List.map fst hdr_phis ++ wr_body)) eqn:Hdisj_b;
    cbn [negb] in Eprep; [| discriminate Eprep].
  destruct (ir_seg_freeze_free t_ir_ent) eqn:Hnf_ent; cbn [negb] in Eprep; [| discriminate Eprep].
  destruct (ir_seg_freeze_free t_ir_body) eqn:Hnf_bdy; cbn [negb] in Eprep; [| discriminate Eprep].
  destruct (check_ls_exprs_vars_diag (allowed0 ++ cut_vars_from 0%nat hdr_phis) ls) as [| []] eqn:Hls_vars_d;
    [discriminate Eprep |].
  pose proof (check_ls_exprs_vars_diag_sound _ _ Hls_vars_d) as Hls_vars.
  inversion Eprep; subst prep; clear Eprep; cbn [mlip_hdr_phis mlip_t_ir_entry mlip_t_ir_body] in *.
  rewrite cut_vars_from_eq_ws in Hls_vars; change (extract_hdr_phi_widths hdr_phis) with hdr_ws in Hls_vars.
  destruct (check_ls_exprs_vars_split _ _ Hls_vars) as (Hinv_sub & Hreg_sub & Hslt_sub).
  (* Typing & agreement for lmap_init and lmap_base *)
  assert (Hwf_li : wf_pure_lmap allowed0 lmap_init) by exact (init_param_lmap_typing _ _ _ _ Hpu).
  assert (Hwf_te : ir_seg_wf allowed0 hdr_ws t_ir_ent) by exact (reify_ir_seg_wf _ _ _ _ _ _ _ _ _ _ _ _ Hwf_li Ere_ent).
  assert (Hwf_lb : wf_pure_lmap allowed0 lmap_base) by exact (common_cut_lmap_wf _ _ _ Hwf_li (proj1 Hwf_te)).
  assert (Hwf_lc : wf_pure_lmap (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) lmap_cut).
  { change hdr_ws with (extract_hdr_phi_widths hdr_phis); rewrite <- (cut_vars_from_eq_ws 0%nat hdr_phis); exact (wrap_cut_mc_at_wf 0%nat allowed0 lmap_base hdr_phis Hwf_lb). }
  assert (Hwf_tb : ir_seg_wf (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) hdr_ws t_ir_body)
    by exact (reify_ir_seg_wf _ _ _ _ _ _ _ _ _ _ _ _ Hwf_lc Ere_body).
  (* Initial entry ghost extension & obligations *)
  destruct (zero_ghost_binds_wf_ctx ls hdr_ws penv0 allowed0 mc_init_ctx (or_introl Hwf) Hnb_al Hpenv0 Hctx0)
    as (Hnb_ext & Hpenv_ext & Hctx_ext).
  set (penv_ext := overlay_penv (@zero_ghost_binds Pa (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) penv0) in *.
  cbn [mlcb_ctx mlcb_known mlcb_obls] in Hchk; rewrite cut_vars_from_eq_ws in Hchk; change (extract_hdr_phi_widths hdr_phis) with hdr_ws in Hchk.
  pose proof (check_mc_loop_obls_sound _ _ _ _ _ _ penv_ext dummy_freeze_oracle false Hchk Hpenv_ext Hctx_ext) as Hobls_ent.
  assert (Hpenv_ext_ref : forall nm w, In (nm, w) allowed0 ->
    exists d1 d2 : @dvalue Pa, penv_ext nm = Some d1 /\ penv_ext nm = Some d2 /\ wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2).
  { intros nm w Hin; destruct (Hpenv0 nm w Hin) as [d0 [Hp0 Hw0]]; rewrite (Hnb_ext nm (Hnb_al nm w Hin)).
    exists d0, d0; repeat split; try assumption; apply dvalue_refines_refl. }
  assert (Hinit_len : List.length (args ir_cfg) = List.length vs).
  { pose proof (Forall2_length Hty); lia. }
  assert (Hcomp_n : forall idx dt, In (idx, dt) (param_idx_uses_cfg ir_cfg) -> nth_error arg_dtys idx = Some dt)
    by (intros idx dt Hin; exact (cfg_param_dtyp_compatible_nth _ _ idx dt Hcomp Hin)).
  assert (Hlm_init_dom : forall r w ce, RM.find r lmap_init = Some (w, ce) ->
    exists pnm, ce = CE_Var pnm w /\ In pnm ir_pnames)
    by (intros r w ce Hf; exact (init_param_lmap_dom _ _ _ _ _ _ Hf)).
  assert (Hlm_init_ext : lmap_matches_env penv_ext lmap_init (init_cfg_locals (args ir_cfg) vs)).
  { pose proof (init_param_lmap_matches (param_idx_uses_cfg ir_cfg) (args ir_cfg) ir_pnames arg_dtys vs
                  Hnd_a Hnd_s Hinit_len (eq_trans Hlen_s Hinit_len) Hty Hcomp_n) as Hbase.
    intros r w ce Hf; destruct (Hbase r w ce Hf) as (dv & Hev & Hsc & Hrm).
    destruct (Hlm_init_dom r w ce Hf) as [pnm [-> Hinp]].
    destruct (Hwf_li r w (CE_Var pnm w) Hf) as (_ & _ & _ & Hfv).
    pose proof (Hfv (pnm, w) (or_introl eq_refl)) as Hal.
    exists dv; repeat split; try assumption.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr lookup_let_val] in *.
    rewrite (Hnb_ext pnm (Hnb_al pnm w Hal)), (Hpenv_eq pnm Hinp); exact Hsc. }
  assert (Hm_ext : rv_rf_matches_args penv_ext arg_specs rf0).
  { intros k sp Hlt Hnth; destruct (Hm k sp Hlt Hnth) as [v [Hp Hmt]].
    pose proof (Hargs_al sp (nth_error_In arg_specs k Hnth)) as Hal_sp.
    exists v; split; [rewrite (Hnb_ext _ (Hnb_al _ _ Hal_sp)); exact Hp | exact Hmt]. }
  assert (Hwfb : forallb (wf_mc_loop_reg_bind EA_Riscv64) (ml_regs ls) = true).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf; destruct Hwf as (((((((_ & _) & _) & _) & Hwbr) & _) & _) & _); exact Hwbr. }
  assert (Hrng : (- mc_frame_cap <= ml_sp_off ls <= 0)%Z) by exact (wf_mc_loop_spec_sp_bounds _ _ Hwf).
  assert (Hdisj_b_wr : disjoint_raw_ids (lmap_keys lmap_base) wr_body = true).
  { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
    pose proof (Hdisj_b x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
    destruct (raw_id_in_list x wr_body) eqn:Exb; [| reflexivity].
    rewrite raw_id_in_list_spec in Exb.
    assert (Htru : raw_id_in_list x (List.map fst hdr_phis ++ wr_body) = true)
      by (apply raw_id_in_list_spec, in_or_app; right; exact Exb).
    rewrite Htru in Hnx; discriminate Hnx. }
  assert (Hdisj_e_nil : disjoint_raw_ids (@nil raw_id) wr_ent = true) by reflexivity.
  assert (Hsp2_init : rv_val_read 2%N (rv_build_init_val_regs 10%N arg_specs) = MSV_StackPtr 0%Z).
  { unfold rv_val_read; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity. }
  assert (Hskel_bwd : forall fuel rf mstk rf_end mstk_end,
    rv_at_cut ls rf0 rf mstk ->
    rv_exec_mem fuel insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) ->
    rv_callee_saved_preserved rf0 rf_end /\ rf_end 1%N = rf0 1%N).
  { intros fuel rf mstk rf_end mstk_end Hat Hmem.
    exact (@rv_skel_backward_sound Pa "skel" insts ret_w ls seg_skel rf0 fuel fuel rf mstk rf_end mstk_end
             (Nat.le_refl fuel) Hwf Hrw Hnmul Hsp0 Es_skel Hok_skel Hat Hmem). }
  assert (Hentry_skel_bwd : forall fuel rf_end mstk_end,
    rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) ->
    rv_callee_saved_preserved rf0 rf_end /\ rf_end 1%N = rf0 1%N).
  { intros fuel rf_end mstk_end Hmem.
    pose proof (summarize_rv64_seg_sound "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (rv_build_init_val_regs 10%N arg_specs) [] ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 rf0 mstk0 Hrw Hnmul Hsp0 ltac:(unfold mc_frame_cap; lia)
                  Hsp2_init (rv_init_val_regs_agrees penv_ext dummy_freeze_oracle arg_specs rf0 Hws Hm_ext)
                  (mc_sym_stack_agrees_empty _ _ _ _ _) Es_ent) as Hs_ent.
    apply rv_seg_exec_to_mc in Hs_ent.
    destruct (mc_skel_tree_ok_extract EA_Riscv64 ls penv_ext dummy_freeze_oracle _ _ _ Hok_ent Hs_ent)
      as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & mstk' & _ & Hsteps & _ & Hsp2' & Hag' & Hastk'))
         | (ret_e & (fuel_end & rf_e & mstk_e & Hme & Hcs & Hra & _))].
    - destruct (rv_exec_mem_split_steps n fuel insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0
                  (ml_mc_pc ls) rf' mstk' (rf_end, mstk_end) Hmem Hsteps) as [_ Hrem].
      apply (Hskel_bwd (fuel - n)%nat rf' mstk' rf_end mstk_end); [| exact Hrem].
      repeat split.
      + specialize (Hag' 2%N); rewrite Hsp2' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
      + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
        unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
      + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                    off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
    - pose proof (rv_exec_mem_det fuel fuel_end insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 _ _ Hmem Hme) as Heq.
      inversion Heq; subst; split; assumption. }
  assert (Hentry_skel_fwd :
    (exists fuel rf_end mstk_end, rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end)) \/
    (exists n rf' mstk', rv_exec_steps n insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 = Some (ml_mc_pc ls, rf', mstk') /\ rv_at_cut ls rf0 rf' mstk')).
  { pose proof (summarize_rv64_seg_sound "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (rv_build_init_val_regs 10%N arg_specs) [] ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 rf0 mstk0 Hrw Hnmul Hsp0 ltac:(unfold mc_frame_cap; lia)
                  Hsp2_init (rv_init_val_regs_agrees penv_ext dummy_freeze_oracle arg_specs rf0 Hws Hm_ext)
                  (mc_sym_stack_agrees_empty _ _ _ _ _) Es_ent) as Hs_ent.
    apply rv_seg_exec_to_mc in Hs_ent.
    destruct (mc_skel_tree_ok_extract EA_Riscv64 ls penv_ext dummy_freeze_oracle _ _ _ Hok_ent Hs_ent)
      as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & mstk' & _ & Hsteps & _ & Hsp2' & Hag' & Hastk'))
         | (ret_e & (fuel_end & rf_e & mstk_e & Hme & _))].
    - right; exists n, rf', mstk'; split; [exact Hsteps | repeat split].
      + specialize (Hag' 2%N); rewrite Hsp2' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
      + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
        unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
      + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                    off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
    - left; exists fuel_end, rf_e, mstk_e; exact Hme. }
  set (rv_cut_inv := fun (env_c : rmap (@dvalue Pa)) (bid_c : block_id) (dvs : list (raw_id * @dvalue Pa))
                         (penv_ir penv_mc : param_env Pa) (rf : rv_regfile) (mstk : mc_stack_mem) =>
    ir_at_cut bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c /\
    pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
    lmap_matches_env penv_ir lmap_cut (apply_phi_env env_c dvs) /\
    Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
    rv_at_cut ls rf0 rf mstk /\
    (forall nm, mc_starts_with_bang nm = false -> penv_ir nm = penv0 nm /\ penv_mc nm = penv0 nm) /\
    wf_param_env_for (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls) penv_mc /\
    ub_ctx_holds penv_mc dummy_freeze_oracle
      (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) /\
    (forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) ->
       exists d1 d2 : @dvalue Pa, penv_ir nm = Some d1 /\ penv_mc nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) /\
    mc_cut_obl_inv_holds ls penv_mc dummy_freeze_oracle /\
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (rv_read_reg (mlr_reg rb) rf))))) /\
       (mlr_width rb = 32%positive ->
          penv_mc (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf))))) /\
    (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))))).
  assert (Hentry_step :
    cfg_steps_to_ub default_draw_strat (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
    (exists fuel_end rf_end mstk_end env_out dv_ir,
       rv_exec_mem fuel_end insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) /\
       rv_callee_saved_preserved rf0 rf_end /\
       rf_end 1%N = rf0 1%N /\
       pure_cfg_steps (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end))))) \/
    (exists n rf1 mstk1 env_c bid_c dvs penv_ir1 penv_mc1,
       rv_exec_steps n insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 = Some (ml_mc_pc ls, rf1, mstk1) /\
       rv_cut_inv env_c bid_c dvs penv_ir1 penv_mc1 rf1 mstk1)).
  { pose proof (reify_ir_seg_sound "entry" ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init
                  [] wr_ent penv_ext (init_cfg_locals (args ir_cfg) vs) (init_cfg_locals (args ir_cfg) vs)
                  t_ir_ent Ewre Hdisj_e_nil (conj eq_refl Hlm_init_ext) Ere_ent) as Hir_ent.
    pose proof (summarize_rv64_seg_sound "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (rv_build_init_val_regs 10%N arg_specs) [] ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 rf0 mstk0 Hrw Hnmul Hsp0 ltac:(unfold mc_frame_cap; lia)
                  Hsp2_init (rv_init_val_regs_agrees penv_ext dummy_freeze_oracle arg_specs rf0 Hws Hm_ext)
                  (mc_sym_stack_agrees_empty _ _ _ _ _) Es_ent) as Hmc_ent.
    apply rv_seg_exec_to_mc in Hmc_ent.
    destruct (collect_mc_ir_obls_acc_sound EA_Riscv64 ls ret_w hdr_ws allowed0 false penv_ext penv_ext
                bmap hdr_id hdr_phis [] (init_cfg_locals (args ir_cfg) vs) (init ir_cfg) (init ir_cfg) t_ir_ent
                _ _ (rv_seg_to_mc_seg seg_ent) (ml_inv ls) [] obls_body obls_all
                eq_refl Hwf_te Hnf_ent Hpenv_ext_ref
                Hir_ent Hmc_ent (fun C => ltac:(discriminate C)) (fun _ _ Hin => ltac:(contradiction Hin)) Eob_e Hobls_ent)
      as [_ [Hub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & (fuel_e & rf_e & mstk_e & Hme & Hcs & Hra & Hev_mc) & Hev_mc2 & Href_d)
                | (env_c & bid_c & b_hdr0 & dvs & lmap_cut0 & phis_ir & sp' & rr' & astk' &
                   Htau & Ebh0 & Hin_lm & Hlm_m & _ & Hstp & Hids & Hws_m & Hpwf_m & Hph_m & Hsp' &
                   (n & rf1 & mstk1 & _ & Hst_mc & _ & Hsp2' & Hag' & Hastk') &
                   Hunsp & Hphi_d & Hregs_o & Hsav & Hslts_o & Hmi_o)]]].
    - left; change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)); exact (Hub default_draw_strat).
    - right; left; exists fuel_e, rf_e, mstk_e, env_out, dv_ir.
      split; [exact Hme | split; [exact Hcs | split; [exact Hra | split]]].
      + change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)); exact Hst.
      + rewrite Hev_mc in Hev_mc2; inversion Hev_mc2; subst dv_mc; exact Href_d.
    - rewrite Ebh in Ebh0; inversion Ebh0; subst b_hdr0.
      assert (Hat1 : rv_at_cut ls rf0 rf1 mstk1).
      { repeat split.
        - specialize (Hag' 2%N); rewrite Hsp2', Hsp' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
        - intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hunsp r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
          pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
          unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
        - intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                      off MS_8 false astk' mstk1 (MSV_SavedReg r) Hastk' (Hsav off r Hr)) as Hsld.
          cbn [mc_sym_val_agrees] in Hsld; exact Hsld. }
      assert (Hregs_ev : forall rb, In rb (ml_regs ls) -> exists e_mc64,
        eval_closed_cert_expr penv_ext dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf1))) /\
        mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Refine false [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Defined false [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))).
      { intros rb Hrb; destruct (Hregs_o rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d).
        pose proof (Hag' (mlr_reg rb)) as Hagr; rewrite Err in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        exists e_mc64; split; [exact Hagr | split; assumption]. }
      assert (Hslts_ev : forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64,
        eval_closed_cert_expr penv_ext dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk1 off sz false))) /\
        mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Refine false [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Defined false [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))).
      { intros off sz e_s Hs; destruct (Hslts_o off sz e_s Hs) as (e_mc64 & Eld & Ho_r & Ho_d).
        pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                      off sz false astk' mstk1 (MSV_Expr e_mc64) Hastk' Eld) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exists e_mc64; split; [exact Hsld | split; assumption]. }
      destruct (@build_next_cut_penvs_sound Pa EA_Riscv64 ls allowed0 mc_init_ctx penv0 penv_ext penv_ext
                  hdr_ws phis_ir dvs (fun r => rv_read_reg r rf1) mstk1 (ml_inv ls) false []
                  Hwf Hnb_al Hpenv0 Hctx0 (fun nm Hnb => conj (Hnb_ext nm Hnb) (Hnb_ext nm Hnb))
                  Hinv_sub Hreg_sub Hslt_sub Hws_m Hph_m (fun C => ltac:(discriminate C)) (fun _ _ Hin => ltac:(contradiction Hin))
                  ltac:(cbn [cut_vars_from_ws]; rewrite app_nil_r; exact Hpwf_m)
                  ltac:(cbn [cut_vars_from_ws]; rewrite app_nil_r; exact Hpenv_ext_ref) Hphi_d Hregs_ev Hslts_ev Hmi_o)
        as (Hnb_1 & Hwf_mc1 & Hctx1 & Href1 & Hphi1 & Hmi1 & Hregs1 & Hslts1).
      set (penv_ir1 := overlay_penv (build_cut_ir_binds 0%nat hdr_ws dvs) penv0) in *.
      set (penv_mc1 := overlay_penv (build_cut_mc_binds ls penv_ext (fun r => rv_read_reg r rf1) mstk1 0%nat hdr_ws phis_ir dvs ++ build_hi32_binds (fun r => rv_read_reg r rf1) (ml_regs ls)) penv0) in *.
      assert (Hlm_next1 : lmap_matches_env penv_ir1 lmap_cut (apply_phi_env env_c dvs)).
      { apply (lmap_base_matches_next allowed0 penv0 penv_ext penv_ir1 lmap_base lmap_cut0 dvs env_c hdr_phis wr_body
                 Hwf_lb (fun r w ce Hf => common_cut_lmap_in lmap_init (collect_entry_cut_lmaps t_ir_ent) lmap_cut0 Hin_lm r w ce Hf)
                 Hlm_m (fun nm w Hal => eq_trans (proj1 (Hnb_1 nm (Hnb_al nm w Hal))) (Logic.eq_sym (Hnb_ext nm (Hnb_al nm w Hal))))
                 Hnd_hp_b Hids Hdisj_b).
        intros k id w dv Hnh Hndv; assert (Hnw : nth_error hdr_ws k = Some w) by (unfold hdr_ws, extract_hdr_phi_widths; rewrite nth_error_map, Hnh; reflexivity); exact (Hphi1 k id w dv Hnw Hndv). }
      right; right; exists n, rf1, mstk1, env_c, bid_c, dvs, penv_ir1, penv_mc1.
      split; [exact Hst_mc |].
      unfold rv_cut_inv.
      split; [destruct Htau as [[-> [-> ->]] | Htau]; [left; repeat split; reflexivity | right; exact Htau] |].
      split; [exact Hstp | split; [exact Hlm_next1 | split; [exact Hids | split; [exact Hat1 |]]]].
      split; [exact Hnb_1 | split; [exact Hwf_mc1 | split; [exact Hctx1 | split; [exact Href1 | split; [exact Hmi1 | split; [exact Hregs1 | exact Hslts1]]]]]]. }
  assert (Hbody_step : forall env_c bid_c dvs penv_ir penv_mc rf mstk,
    rv_cut_inv env_c bid_c dvs penv_ir penv_mc rf mstk ->
    (cfg_steps_to_ub default_draw_strat (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)) \/
    (exists fuel_end rf_end mstk_end env_out dv_ir,
       rv_exec_mem fuel_end insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
       rv_callee_saved_preserved rf0 rf_end /\
       rf_end 1%N = rf0 1%N /\
       pure_cfg_steps (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end))))) \/
    (exists n rf' mstk' env_c' bid_c' dvs' penv_ir' penv_mc',
       (1 <= n)%nat /\
       rv_exec_steps n insts (rv_read_reg 2%N rf0) (ml_mc_pc ls) rf mstk = Some (ml_mc_pc ls, rf', mstk') /\
       rv_cut_inv env_c' bid_c' dvs' penv_ir' penv_mc' rf' mstk')).
  { intros env_c bid_c dvs penv_ir penv_mc rf mstk
           (Hcut & Hstp_p & Hlm_c & Hids & Hat & Hnb_c & Hwf_mc & Hctx_c & Href_c & Hmi_c & Hregs_c & Hslts_c).
    assert (Hpres_phi : forall r, In r (lmap_keys lmap_base) -> RM.find r (apply_phi_env env_c dvs) = RM.find r env_c).
    { intros r Hr; apply apply_phi_env_preserves_not_in.
      intro Hin; apply (disjoint_raw_ids_spec _ _ r Hdisj_b Hr), in_or_app; left.
      clear -Hids Hin; revert dvs Hids Hin; induction hdr_phis as [| [i0 w0] rp IH];
        intros [| [i1 d1] rd] H2 Hin; cbn in *; try inversion H2; [contradiction |].
      destruct Hin as [Heq | Hr]; [left; subst; congruence | right; exact (IH rd H5 Hr)]. }
    assert (Hre_body_c : reify_ir_seg "body" ir_fuel bmap hdr_id hdr_phis true [] bid_c hdr_id lmap_cut = inr t_ir_body)
      by exact (reify_ir_seg_req_step_bid_from_irrel "body" ir_fuel bmap hdr_id hdr_phis [] hdr_id bid_c hdr_id lmap_cut t_ir_body Ere_body).
    pose proof (reify_ir_seg_sound "body" ir_fuel bmap hdr_id hdr_phis true [] bid_c hdr_id lmap_cut
                  (lmap_keys lmap_base) wr_body penv_ir env_c (apply_phi_env env_c dvs) t_ir_body
                  Ewrb Hdisj_b_wr (ex_intro _ b_hdr (conj Ebh (conj Hstp_p (conj Hpres_phi Hlm_c)))) Hre_body_c) as Hir_body.
    destruct Hat as [Hsp_r [Hunsp_r Hsav_r]].
    pose proof (summarize_rv64_seg_sound "body" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                  (rv_cut_vrf ls) (build_cut_astk (ml_slots ls)) ret_w seg_body
                  penv_mc dummy_freeze_oracle rf0 rf mstk Hrw Hnmul Hsp0 Hrng (rv_cut_vrf_sp ls Hwfb)
                  (rv_cut_vrf_agrees penv_mc dummy_freeze_oracle ls rf0 rf Hwf Hsp_r Hrng Hunsp_r Hregs_c)
                  (build_cut_astk_agrees penv_mc dummy_freeze_oracle (fun k => rv_read_reg k rf0) (rv_read_reg 2%N rf0) (ml_slots ls) mstk Hslts_c Hsav_r)
                  Es_body) as Hmc_body.
    apply rv_seg_exec_to_mc in Hmc_body.
    pose proof (check_mc_loop_obls_sound _ _ _ _ _ _ penv_mc dummy_freeze_oracle true Hchk Hwf_mc Hctx_c) as Hobls_all_b.
    pose proof (collect_mc_ir_obls_acc_sub _ _ _ _ _ _ _ _ _ _ _ Eob_e Hobls_all_b) as Hobls_b.
    destruct (collect_mc_ir_obls_acc_sound EA_Riscv64 ls ret_w hdr_ws (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) true penv_ir penv_mc
                bmap hdr_id hdr_phis (lmap_keys lmap_base) env_c bid_c hdr_id t_ir_body
                _ _ (rv_seg_to_mc_seg seg_body) (ml_inv ls) [] [] obls_body eq_refl Hwf_tb Hnf_bdy Href_c
                Hir_body Hmc_body (fun _ => Hmi_c) (fun _ _ Hin => ltac:(contradiction Hin)) Eob_b Hobls_b)
      as [_ [Hub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & (fuel_e & rf_e & mstk_e & Hme & Hcs & Hra & Hev_mc) & Hev_mc2 & Href_d)
                | (env_c' & bid_c' & b_hdr0 & dvs' & lmap_cut' & phis_ir & sp' & rr' & astk' &
                   Htau & Ebh0 & _ & Hlm_m & Hkp_lb & Hstp & Hids' & Hws_m & Hpwf_m & Hph_m & Hsp' &
                   (n & rf' & mstk' & Hn & Hst_mc & _ & Hsp2' & Hag' & Hastk') &
                   Hunsp & Hphi_d & Hregs_o & Hsav & Hslts_o & Hmi_o)]]].
    - left; change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)).
      exact (ir_at_cut_ub bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c default_draw_strat Hcut (Hub default_draw_strat)).
    - right; left; exists fuel_e, rf_e, mstk_e, env_out, dv_ir; repeat split; try assumption.
      + change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)).
        exact (ir_at_cut_ret bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c env_out dv_ir Hcut Hst).
      + rewrite Hev_mc in Hev_mc2; inversion Hev_mc2; subst dv_mc; exact Href_d.
    - rewrite Ebh in Ebh0; inversion Ebh0; subst b_hdr0.
      assert (Hat' : rv_at_cut ls rf0 rf' mstk').
      { repeat split.
        - specialize (Hag' 2%N); rewrite Hsp2', Hsp' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
        - intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hunsp r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
          pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
          unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
        - intros off r Hr; pose proof (mc_sym_stk_load_sound penv_mc dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                      off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hsav off r Hr)) as Hsld.
          cbn [mc_sym_val_agrees] in Hsld; exact Hsld. }
      assert (Hregs_ev : forall rb, In rb (ml_regs ls) -> exists e_mc64,
        eval_closed_cert_expr penv_mc dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf'))) /\
        mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Refine true [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Defined true [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))).
      { intros rb Hrb; destruct (Hregs_o rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d).
        pose proof (Hag' (mlr_reg rb)) as Hagr; rewrite Err in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        exists e_mc64; split; [exact Hagr | split; assumption]. }
      assert (Hslts_ev : forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64,
        eval_closed_cert_expr penv_mc dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk' off sz false))) /\
        mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Refine true [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Defined true [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))).
      { intros off sz e_s Hs; destruct (Hslts_o off sz e_s Hs) as (e_mc64 & Eld & Ho_r & Ho_d).
        pose proof (mc_sym_stk_load_sound penv_mc dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                      off sz false astk' mstk' (MSV_Expr e_mc64) Hastk' Eld) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exists e_mc64; split; [exact Hsld | split; assumption]. }
      destruct (@build_next_cut_penvs_sound Pa EA_Riscv64 ls allowed0 mc_init_ctx penv0 penv_ir penv_mc
                  hdr_ws phis_ir dvs' (fun r => rv_read_reg r rf') mstk' (ml_inv ls) true []
                  Hwf Hnb_al Hpenv0 Hctx0 Hnb_c
                  Hinv_sub Hreg_sub Hslt_sub Hws_m Hph_m (fun _ => Hmi_c) (fun _ _ Hin => ltac:(contradiction Hin))
                  Hpwf_m Href_c Hphi_d Hregs_ev Hslts_ev Hmi_o)
        as (Hnb' & Hwf_mc' & Hctx' & Href' & Hphi' & Hmi' & Hregs' & Hslts').
      set (penv_ir' := overlay_penv (build_cut_ir_binds 0%nat hdr_ws dvs') penv0) in *.
      set (penv_mc' := overlay_penv (build_cut_mc_binds ls penv_mc (fun r => rv_read_reg r rf') mstk' 0%nat hdr_ws phis_ir dvs' ++ build_hi32_binds (fun r => rv_read_reg r rf') (ml_regs ls)) penv0) in *.
      assert (Hlm_env_c' : lmap_matches_env penv_ir lmap_base env_c').
      { intros r w ce Hf; assert (Hr_k : In r (lmap_keys lmap_base)) by (apply in_lmap_keys_iff; eexists; exact Hf).
        assert (Hnf_h : ~ In r (List.map fst hdr_phis)) by (intro Hin; apply (disjoint_raw_ids_spec _ _ r Hdisj_b Hr_k), in_or_app; left; exact Hin).
        assert (Hf_cut : RM.find r lmap_cut = Some (w, ce)) by (unfold lmap_cut, wrap_cut_mc; rewrite wrap_cut_mc_at_preserves by exact Hnf_h; exact Hf).
        destruct (Hlm_c r w ce Hf_cut) as (dv0 & He0 & Hs0 & Hrm0); exists dv0; repeat split; try assumption.
        rewrite (Hkp_lb r Hr_k), <- Hpres_phi by exact Hr_k; exact He0. }
      assert (Hlm_next' : lmap_matches_env penv_ir' lmap_cut (apply_phi_env env_c' dvs')).
      { apply (lmap_base_matches_next allowed0 penv0 penv_ir penv_ir' lmap_base lmap_base dvs' env_c' hdr_phis wr_body
                 Hwf_lb (fun r w ce H => H) Hlm_env_c'
                 (fun nm w Hal => eq_trans (proj1 (Hnb' nm (Hnb_al nm w Hal))) (Logic.eq_sym (proj1 (Hnb_c nm (Hnb_al nm w Hal)))))
                 Hnd_hp_b Hids' Hdisj_b).
        intros k id w dv Hnh Hndv; assert (Hnw : nth_error hdr_ws k = Some w) by (unfold hdr_ws, extract_hdr_phi_widths; rewrite nth_error_map, Hnh; reflexivity); exact (Hphi' k id w dv Hnw Hndv). }
      right; right; exists n, rf', mstk', env_c', bid_c', dvs', penv_ir', penv_mc'.
      split; [exact (Hn eq_refl) | split; [exact Hst_mc |]].
      unfold rv_cut_inv.
      split; [exact (ir_at_cut_step bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c env_c' bid_c' Hcut Htau) |].
      split; [exact Hstp | split; [exact Hlm_next' | split; [exact Hids' | split; [exact Hat' |]]]].
      split; [exact Hnb' | split; [exact Hwf_mc' | split; [exact Hctx' | split; [exact Href' | split; [exact Hmi' | split; [exact Hregs' | exact Hslts']]]]]]. }
  split.
  - (* Part 1: Backward partial correctness *)
    assert (Hbwd_cut : forall n_max fuel rf mstk env_c bid_c dvs penv_ir penv_mc rf_end mstk_end,
      (fuel <= n_max)%nat ->
      rv_cut_inv env_c bid_c dvs penv_ir penv_mc rf mstk ->
      rv_exec_mem fuel insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) ->
      rv_callee_saved_preserved rf0 rf_end /\ rf_end 1%N = rf0 1%N /\
      exists sigma_ir,
        wf_draw_strat sigma_ir /\
        (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
         exists sigma_ir' env_out dv_ir,
           cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
             sigma_ir' env_out dv_ir /\
           dvalue_refines dv_ir
             (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))))).
    { intros n_max; induction n_max as [| n_max' IH];
        intros fuel rf mstk env_c bid_c dvs penv_ir penv_mc rf_end mstk_end Hle Hinv Hmem.
      - assert (Hf0 : fuel = 0%nat) by lia; subst fuel; cbn [rv_exec_mem] in Hmem; discriminate Hmem.
      - destruct (Hbody_step env_c bid_c dvs penv_ir penv_mc rf mstk Hinv)
          as [Hub | [(fuel_e & rf_e & mstk_e & env_out & dv_ir & Hme & Hcs & Hra & Hst & Href)
                    | (n1 & rf1 & mstk1 & env_c1 & bid_c1 & dvs1 & penv_ir1 & penv_mc1 & Hn1 & Hst1 & Hinv1)]].
        + destruct (Hskel_bwd fuel rf mstk rf_end mstk_end (proj1 (proj2 (proj2 (proj2 (proj2 Hinv))))) Hmem) as [Hcs Hra].
          split; [exact Hcs | split; [exact Hra | exists default_draw_strat; split; [exact default_draw_strat_wf | left; exact Hub]]].
        + pose proof (rv_exec_mem_det fuel fuel_e insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk _ _ Hmem Hme) as Heq.
          inversion Heq; subst rf_e mstk_e.
          split; [exact Hcs | split; [exact Hra | exists default_draw_strat; split; [exact default_draw_strat_wf | right; exists default_draw_strat, env_out, dv_ir; split; [apply pure_cfg_to_cfg_ret; exact Hst | exact Href]]]].
        + destruct (rv_exec_mem_split_steps n1 fuel insts (rv_read_reg 2%N rf0) (ml_mc_pc ls) rf mstk
                      (ml_mc_pc ls) rf1 mstk1 (rf_end, mstk_end) Hmem Hst1) as [Hlt Hrem].
          exact (IH (fuel - n1)%nat rf1 mstk1 env_c1 bid_c1 dvs1 penv_ir1 penv_mc1 rf_end mstk_end ltac:(lia) Hinv1 Hrem). }
    intros fuel rf_end mstk_end Hmem.
    destruct (Hentry_skel_bwd fuel rf_end mstk_end Hmem) as [Hcs0 Hra0].
    destruct Hentry_step as [Hub | [(fuel_e & rf_e & mstk_e & env_out & dv_ir & Hme & Hcs & Hra & Hst & Href)
                                  | (n1 & rf1 & mstk1 & env_c1 & bid_c1 & dvs1 & penv_ir1 & penv_mc1 & Hst1 & Hinv1)]].
    + split; [exact Hcs0 | split; [exact Hra0 | exists default_draw_strat; split; [exact default_draw_strat_wf | left; exact Hub]]].
    + pose proof (rv_exec_mem_det fuel fuel_e insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 _ _ Hmem Hme) as Heq.
      inversion Heq; subst rf_e mstk_e.
      split; [exact Hcs0 | split; [exact Hra0 | exists default_draw_strat; split; [exact default_draw_strat_wf | right; exists default_draw_strat, env_out, dv_ir; split; [apply pure_cfg_to_cfg_ret; exact Hst | exact Href]]]].
    + destruct (rv_exec_mem_split_steps n1 fuel insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0
                  (ml_mc_pc ls) rf1 mstk1 (rf_end, mstk_end) Hmem Hst1) as [_ Hrem].
      exact (Hbwd_cut (fuel - n1)%nat (fuel - n1)%nat rf1 mstk1 env_c1 bid_c1 dvs1 penv_ir1 penv_mc1 rf_end mstk_end (Nat.le_refl _) Hinv1 Hrem).
  - (* Part 2: Arbitrary-depth forward progress *)
    assert (Hfwd_aux : forall k : nat,
      (exists fuel rf_end mstk_end, rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end)) \/
      (exists n rf_k mstk_k, (k <= n)%nat /\ rv_exec_steps n insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 = Some (ml_mc_pc ls, rf_k, mstk_k) /\ rv_at_cut ls rf0 rf_k mstk_k)).
    { induction k as [| k' IH].
      - destruct Hentry_skel_fwd as [(f0 & rfe & me & Hmem) | (n0 & rf1 & mstk1 & Hst1 & Hat1)].
        + left; exists f0, rfe, me; exact Hmem.
        + right; exists n0, rf1, mstk1; split; [lia | split; assumption].
      - destruct IH as [(f0 & rfe & me & Hmem) | (n0 & rfk & mstkk & Hle & Hst0 & Hatk)];
          [left; exists f0, rfe, me; exact Hmem |].
        destruct (@rv_skel_step Pa "skel" insts ret_w ls seg_skel rf0 rfk mstkk Hwf Hrw Hnmul Hsp0 Es_skel Hok_skel Hatk)
          as [(fe & rfe & me & Hme & _ & _) | (n1 & rf1 & mstk1 & Hn1 & Hst1 & Hat1)].
        + left; exists (n0 + fe)%nat, rfe, me; exact (rv_exec_steps_to_exec_mem n0 fe insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 (ml_mc_pc ls) rfk mstkk (rfe, me) Hst0 Hme).
        + right; exists (n0 + n1)%nat, rf1, mstk1; split; [lia | split; [exact (rv_exec_steps_trans n0 n1 insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 (ml_mc_pc ls) rfk mstkk (ml_mc_pc ls, rf1, mstk1) Hst0 Hst1) | exact Hat1]]. }
    exact Hfwd_aux.
Qed.

Theorem validate_mc_loop_a64_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
         (insts : list decoded_a64_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
         (ls : mc_loop_spec) (opt_pf : option (list lrat_step))
         arg_dtys vs (penv0 : param_env Pa) rf0 sp0 fl0 mstk0,
    validate_mc_loop_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls opt_pf = inr tt ->
    forallb a64_inst_valid insts = true ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    cfg_param_dtyp_compatible ir_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (param_idx_uses_cfg ir_cfg) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed0) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv0 nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    (forall sp, In sp arg_specs ->
       penv0 (a64_hi_var_name (ras_name sp)) =
       a64_extend_penv_with_hi (build_param_env (List.map cert_reg_name (args ir_cfg)) vs) arg_specs rf0 (a64_hi_var_name (ras_name sp))) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed0) ->
    (forall nv, In nv (a64_hi_vars arg_specs) -> In nv allowed0) ->
    NoDup (List.map ras_name arg_specs) ->
    (forall sp, In sp arg_specs -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name arg_specs)) ->
    (forall sp, In sp arg_specs -> penv0 (ras_name sp) = build_param_env (List.map cert_reg_name (args ir_cfg)) vs (ras_name sp)) ->
    mc_valid_sp0 sp0 ->
    a64_rf_matches_args (build_param_env (List.map cert_reg_name (args ir_cfg)) vs) arg_specs rf0 ->
    a64_loop_sound_spec ir_cfg insts ret_w ls vs rf0 sp0 fl0 mstk0.
Proof.
  intros ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls opt_pf arg_dtys vs penv0 rf0 sp0 fl0 mstk0
         Hval Hval_a64 Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp Hty Hpu Hpenv_eq Hhi_eq Hpenv0 Hctx0 Hargs_al Hhi_al Hnd_mc Hdis_args Hnames_p Hsp0 Hm.
  unfold validate_mc_loop_a64, build_mc_loop_bundle_a64 in Hval.
  destruct (check_mc_loop_spec_diag EA_AArch64 ls) as [| []] eqn:Hwf_d; [discriminate Hval |].
  pose proof (check_mc_loop_spec_diag_sound _ _ Hwf_d) as Hwf.
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hval; [| discriminate Hval].
  rewrite Hval_a64 in Hval; cbn [negb] in Hval.
  destruct (Nat.leb (List.length arg_specs) 8) eqn:Hlen_args; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb a64_valid_arg_spec arg_specs) eqn:Hws; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (prepare_mc_loop_ir ir_cfg allowed0 ls) as [| prep] eqn:Eprep; [discriminate Hval |].
  rewrite elf_length_tr_eq in Hval; set (mc_fuel := S (2 * List.length insts)) in *.
  set (hdr_ws := extract_hdr_phi_widths (mlip_hdr_phis prep)) in *.
  destruct (summarize_a64_seg "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w)
    as [| seg_ent] eqn:Es_ent; [discriminate Hval |].
  destruct (summarize_a64_seg "body" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls) (a64_cut_vrf ls) (build_cut_astk (ml_slots ls)) a64_init_sym_flags false ret_w)
    as [| seg_body] eqn:Es_body; [discriminate Hval |].
  destruct (summarize_a64_seg "skel" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls) (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w)
    as [| seg_skel] eqn:Es_skel; [discriminate Hval |].
  destruct (check_mc_skel_tree_diag "entry" EA_AArch64 ls (a64_seg_to_mc_seg seg_ent)) as [| []] eqn:Hok_ent_d;
    cbn [bind_err] in Hval; [discriminate Hval |].
  destruct (check_mc_skel_tree_diag "skel" EA_AArch64 ls (a64_seg_to_mc_seg seg_skel)) as [| []] eqn:Hok_skel_d;
    [discriminate Hval |].
  pose proof (check_mc_skel_tree_diag_sound _ _ _ _ Hok_ent_d) as Hok_ent.
  pose proof (check_mc_skel_tree_diag_sound _ _ _ _ Hok_skel_d) as Hok_skel.
  destruct (collect_mc_ir_obls_acc EA_AArch64 ls ret_w hdr_ws true [] (mlip_t_ir_body prep) (a64_seg_to_mc_seg seg_body) [])
    as [| obls_body] eqn:Eob_b; [discriminate Hval |].
  destruct (collect_mc_ir_obls_acc EA_AArch64 ls ret_w hdr_ws false [] (mlip_t_ir_entry prep) (a64_seg_to_mc_seg seg_ent) obls_body)
    as [| obls_all] eqn:Eob_e; [discriminate Hval |].
  rename Hval into Hchk.
  unfold prepare_mc_loop_ir in Eprep.
  destruct (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) eqn:Hnb_al_b;
    cbn [negb] in Eprep; [| discriminate Eprep].
  assert (Hnb_al : forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false).
  { intros nm w Hin; rewrite forallb_forall in Hnb_al_b; pose proof (Hnb_al_b (nm, w) Hin) as Hn; apply negb_true_iff in Hn; exact Hn. }
  set (bmap := ocfg_map (blks ir_cfg)) in *.
  destruct (find_hdr_block_id (ml_ir_header ls) (blks ir_cfg)) as [hdr_id |] eqn:Ehid; [| discriminate Eprep].
  destruct (RM.find hdr_id bmap) as [b_hdr |] eqn:Ebh; [| discriminate Eprep].
  destruct (extract_hdr_phis (blk_phis b_hdr)) as [| hdr_phis] eqn:Ehp; [discriminate Eprep |].
  destruct (no_dup_raw_ids (List.map fst hdr_phis)) eqn:Hnd_hp_b; cbn [negb] in Eprep; [| discriminate Eprep].
  apply no_dup_raw_ids_spec in Hnd_hp_b.
  set (ir_pnames := List.map cert_reg_name (args ir_cfg)) in *.
  set (lmap_init := init_param_lmap (args ir_cfg) ir_pnames (param_idx_uses_cfg ir_cfg)) in *.
  set (ir_fuel := S (List.length (blks ir_cfg) + 1)) in *.
  destruct (ir_seg_written_ids "entry" ir_fuel bmap hdr_id false [] (init ir_cfg)) as [| wr_ent] eqn:Ewre; [discriminate Eprep |].
  destruct (reify_ir_seg "entry" ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init)
    as [| t_ir_ent] eqn:Ere_ent; [discriminate Eprep |].
  set (lmap_base := common_cut_lmap lmap_init (collect_entry_cut_lmaps t_ir_ent)) in *.
  set (lmap_cut := wrap_cut_mc lmap_base hdr_phis) in *.
  destruct (ir_seg_written_ids "body" ir_fuel bmap hdr_id true [] hdr_id) as [| wr_body] eqn:Ewrb; [discriminate Eprep |].
  destruct (reify_ir_seg "body" ir_fuel bmap hdr_id hdr_phis true [] hdr_id hdr_id lmap_cut)
    as [| t_ir_body] eqn:Ere_body; [discriminate Eprep |].
  destruct (disjoint_raw_ids (lmap_keys lmap_base) (List.map fst hdr_phis ++ wr_body)) eqn:Hdisj_b;
    cbn [negb] in Eprep; [| discriminate Eprep].
  destruct (ir_seg_freeze_free t_ir_ent) eqn:Hnf_ent; cbn [negb] in Eprep; [| discriminate Eprep].
  destruct (ir_seg_freeze_free t_ir_body) eqn:Hnf_bdy; cbn [negb] in Eprep; [| discriminate Eprep].
  destruct (check_ls_exprs_vars_diag (allowed0 ++ cut_vars_from 0%nat hdr_phis) ls) as [| []] eqn:Hls_vars_d;
    [discriminate Eprep |].
  pose proof (check_ls_exprs_vars_diag_sound _ _ Hls_vars_d) as Hls_vars.
  inversion Eprep; subst prep; clear Eprep; cbn [mlip_hdr_phis mlip_t_ir_entry mlip_t_ir_body] in *.
  rewrite cut_vars_from_eq_ws in Hls_vars; change (extract_hdr_phi_widths hdr_phis) with hdr_ws in Hls_vars.
  destruct (check_ls_exprs_vars_split _ _ Hls_vars) as (Hinv_sub & Hreg_sub & Hslt_sub).
  assert (Hwf_li : wf_pure_lmap allowed0 lmap_init) by exact (init_param_lmap_typing _ _ _ _ Hpu).
  assert (Hwf_te : ir_seg_wf allowed0 hdr_ws t_ir_ent) by exact (reify_ir_seg_wf _ _ _ _ _ _ _ _ _ _ _ _ Hwf_li Ere_ent).
  assert (Hwf_lb : wf_pure_lmap allowed0 lmap_base) by exact (common_cut_lmap_wf _ _ _ Hwf_li (proj1 Hwf_te)).
  assert (Hwf_lc : wf_pure_lmap (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) lmap_cut).
  { change hdr_ws with (extract_hdr_phi_widths hdr_phis); rewrite <- (cut_vars_from_eq_ws 0%nat hdr_phis); exact (wrap_cut_mc_at_wf 0%nat allowed0 lmap_base hdr_phis Hwf_lb). }
  assert (Hwf_tb : ir_seg_wf (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) hdr_ws t_ir_body)
    by exact (reify_ir_seg_wf _ _ _ _ _ _ _ _ _ _ _ _ Hwf_lc Ere_body).
  destruct (zero_ghost_binds_wf_ctx ls hdr_ws penv0 allowed0 mc_init_ctx (or_intror Hwf) Hnb_al Hpenv0 Hctx0)
    as (Hnb_ext & Hpenv_ext & Hctx_ext).
  set (penv_ext := overlay_penv (@zero_ghost_binds Pa (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) penv0) in *.
  cbn [mlcb_ctx mlcb_known mlcb_obls] in Hchk; rewrite cut_vars_from_eq_ws in Hchk; change (extract_hdr_phi_widths hdr_phis) with hdr_ws in Hchk.
  pose proof (check_mc_loop_obls_sound _ _ _ _ _ _ penv_ext dummy_freeze_oracle false Hchk Hpenv_ext Hctx_ext) as Hobls_ent.
  assert (Hpenv_ext_ref : forall nm w, In (nm, w) allowed0 ->
    exists d1 d2 : @dvalue Pa, penv_ext nm = Some d1 /\ penv_ext nm = Some d2 /\ wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2).
  { intros nm w Hin; destruct (Hpenv0 nm w Hin) as [d0 [Hp0 Hw0]]; rewrite (Hnb_ext nm (Hnb_al nm w Hin)).
    exists d0, d0; repeat split; try assumption; apply dvalue_refines_refl. }
  assert (Hinit_len : List.length (args ir_cfg) = List.length vs) by (pose proof (Forall2_length Hty); lia).
  assert (Hcomp_n : forall idx dt, In (idx, dt) (param_idx_uses_cfg ir_cfg) -> nth_error arg_dtys idx = Some dt)
    by (intros idx dt Hin; exact (cfg_param_dtyp_compatible_nth _ _ idx dt Hcomp Hin)).
  assert (Hlm_init_dom : forall r w ce, RM.find r lmap_init = Some (w, ce) -> exists pnm, ce = CE_Var pnm w /\ In pnm ir_pnames)
    by (intros r w ce Hf; exact (init_param_lmap_dom _ _ _ _ _ _ Hf)).
  assert (Hlm_init_ext : lmap_matches_env penv_ext lmap_init (init_cfg_locals (args ir_cfg) vs)).
  { pose proof (init_param_lmap_matches (param_idx_uses_cfg ir_cfg) (args ir_cfg) ir_pnames arg_dtys vs
                  Hnd_a Hnd_s Hinit_len (eq_trans Hlen_s Hinit_len) Hty Hcomp_n) as Hbase.
    intros r w ce Hf; destruct (Hbase r w ce Hf) as (dv & Hev & Hsc & Hrm).
    destruct (Hlm_init_dom r w ce Hf) as [pnm [-> Hinp]].
    destruct (Hwf_li r w (CE_Var pnm w) Hf) as (_ & _ & _ & Hfv).
    pose proof (Hfv (pnm, w) (or_introl eq_refl)) as Hal.
    exists dv; repeat split; try assumption.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr lookup_let_val] in *.
    rewrite (Hnb_ext pnm (Hnb_al pnm w Hal)), (Hpenv_eq pnm Hinp); exact Hsc. }
  assert (Ha64_init_agrees :
    a64_val_regs_agrees penv_ext dummy_freeze_oracle rf0 sp0 (a64_build_init_val_regs 0%N arg_specs) rf0).
  { set (penv_hi := a64_extend_penv_with_hi (build_param_env ir_pnames vs) arg_specs rf0).
    pose proof (a64_init_val_regs_agrees (build_param_env ir_pnames vs) dummy_freeze_oracle arg_specs rf0 sp0 Hws Hnd_mc Hdis_args Hm) as Hbase.
    fold penv_hi in Hbase.
    intro r; pose proof (Hbase r) as Hr; destruct (a64_val_read r (a64_build_init_val_regs 0%N arg_specs)) as [| e_arg | |] eqn:Erd;
      try exact Hr.
    cbn [mc_sym_val_agrees] in Hr |- *.
    rewrite <- Hr; symmetry; apply eval_cert_expr_penv_eq_if_vars;
      destruct (a64_build_init_val_regs_vars 0%N arg_specs r e_arg Erd) as [Hlf Hfv]; [exact Hlf |].
    intros nm wn Hfn.
    destruct (Hfv nm wn Hfn) as [sp [Hin [[-> ->] | [Hw64 [-> ->]]]]].
    - pose proof (Hargs_al sp Hin) as Hal.
      rewrite (Hnb_ext _ (Hnb_al _ _ Hal)), (Hnames_p sp Hin).
      unfold penv_hi, a64_extend_penv_with_hi; apply a64_extend_penv_at_orig.
      intros sp1 Hin1 Heq; apply (Hdis_args sp1 Hin1); rewrite Heq; apply in_map_iff; exists sp; split; [reflexivity | exact Hin].
    - assert (Hhi_in : In (a64_hi_var_name (ras_name sp), 64%positive) (a64_hi_vars arg_specs))
        by (unfold a64_hi_vars; apply in_flat_map; exists sp; split; [exact Hin | rewrite Hw64; left; reflexivity]).
      pose proof (Hhi_al _ Hhi_in) as Hal.
      rewrite (Hnb_ext _ (Hnb_al _ _ Hal)), (Hhi_eq sp Hin); reflexivity. }
  assert (Hsp0_eq : sp0 = @Integers.add 64%positive sp0 (@Integers.repr 64%positive 0%Z))
    by (change (@Integers.repr 64%positive 0%Z) with (@Integers.zero 64%positive); rewrite Integers.add_zero; reflexivity).
  assert (Hwfb : forallb (wf_mc_loop_reg_bind EA_AArch64) (ml_regs ls) = true).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf; destruct Hwf as (((((((_ & _) & _) & _) & Hwbr) & _) & _) & _); exact Hwbr. }
  assert (Hrng : (- mc_frame_cap <= ml_sp_off ls <= 0)%Z) by exact (wf_mc_loop_spec_sp_bounds _ _ Hwf).
  assert (Hdisj_b_wr : disjoint_raw_ids (lmap_keys lmap_base) wr_body = true).
  { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
    pose proof (Hdisj_b x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
    destruct (raw_id_in_list x wr_body) eqn:Exb; [| reflexivity].
    rewrite raw_id_in_list_spec in Exb.
    assert (Htru : raw_id_in_list x (List.map fst hdr_phis ++ wr_body) = true)
      by (apply raw_id_in_list_spec, in_or_app; right; exact Exb).
    rewrite Htru in Hnx; discriminate Hnx. }
  assert (Hdisj_e_nil : disjoint_raw_ids (@nil raw_id) wr_ent = true) by reflexivity.
  assert (Hskel_bwd : forall fuel rf sp fl mstk rf_end sp_end fl_end mstk_end,
    a64_at_cut ls sp0 rf0 rf sp mstk ->
    a64_exec_mem fuel insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp_end, fl_end, mstk_end) ->
    sp_end = sp0 /\ a64_callee_saved_preserved rf0 rf_end).
  { intros fuel rf sp fl mstk rf_end sp_end fl_end mstk_end Hat Hmem.
    exact (@a64_skel_backward_sound Pa "skel" insts ret_w ls seg_skel rf0 sp0 fuel fuel rf sp fl mstk rf_end sp_end fl_end mstk_end
             (Nat.le_refl fuel) Hwf Hrw Hval_a64 Hsp0 Es_skel Hok_skel Hat Hmem). }
  assert (Hentry_skel_bwd : forall fuel rf_end sp_end fl_end mstk_end,
    a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end) ->
    sp_end = sp0 /\ a64_callee_saved_preserved rf0 rf_end).
  { intros fuel rf_end sp_end fl_end mstk_end Hmem.
    pose proof (summarize_a64_seg_sound "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 sp0 rf0 sp0 fl0 mstk0 Hrw Hval_a64 Hsp0
                  ltac:(unfold mc_frame_cap; lia) Hsp0_eq Ha64_init_agrees (mc_sym_stack_agrees_empty _ _ _ _ _)
                  (fun C => ltac:(discriminate C)) Es_ent) as Hs_ent.
    apply a64_seg_exec_to_mc in Hs_ent.
    destruct (mc_skel_tree_ok_extract EA_AArch64 ls penv_ext dummy_freeze_oracle _ _ _ Hok_ent Hs_ent)
      as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & sp_c & fl_c & mstk' & _ & Hsteps & _ & Hsp_c & Hag' & Hastk'))
         | (ret_e & (fuel_end & rf_e & fl_e & mstk_e & Hme & Hcs & _))].
    - destruct (a64_exec_mem_split_steps n fuel insts sp0 0%N rf0 sp0 fl0 mstk0
                  (ml_mc_pc ls) rf' sp_c fl_c mstk' (rf_end, sp_end, fl_end, mstk_end) Hmem Hsteps) as [_ Hrem].
      apply (Hskel_bwd (fuel - n)%nat rf' sp_c fl_c mstk' rf_end sp_end fl_end mstk_end); [| exact Hrem].
      repeat split; [exact Hsp_c | |].
      + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
      + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                    off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
    - pose proof (a64_exec_mem_det fuel fuel_end insts 0%N sp0 rf0 sp0 fl0 mstk0 _ _ Hmem Hme) as Heq.
      inversion Heq; subst; split; [reflexivity | exact Hcs]. }
  assert (Hentry_skel_fwd :
    (exists fuel rf_end sp_end fl_end mstk_end, a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end)) \/
    (exists n rf' sp' fl' mstk', a64_exec_steps n insts sp0 0%N rf0 sp0 fl0 mstk0 = Some (ml_mc_pc ls, rf', sp', fl', mstk') /\ a64_at_cut ls sp0 rf0 rf' sp' mstk')).
  { pose proof (summarize_a64_seg_sound "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 sp0 rf0 sp0 fl0 mstk0 Hrw Hval_a64 Hsp0
                  ltac:(unfold mc_frame_cap; lia) Hsp0_eq Ha64_init_agrees (mc_sym_stack_agrees_empty _ _ _ _ _)
                  (fun C => ltac:(discriminate C)) Es_ent) as Hs_ent.
    apply a64_seg_exec_to_mc in Hs_ent.
    destruct (mc_skel_tree_ok_extract EA_AArch64 ls penv_ext dummy_freeze_oracle _ _ _ Hok_ent Hs_ent)
      as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & sp_c & fl_c & mstk' & _ & Hsteps & _ & Hsp_c & Hag' & Hastk'))
         | (ret_e & (fuel_end & rf_e & fl_e & mstk_e & Hme & _))].
    - right; exists n, rf', sp_c, fl_c, mstk'; split; [exact Hsteps | repeat split; try assumption].
      + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
      + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                    off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
    - left; exists fuel_end, rf_e, sp0, fl_e, mstk_e; exact Hme. }
  set (a64_cut_inv := fun (env_c : rmap (@dvalue Pa)) (bid_c : block_id) (dvs : list (raw_id * @dvalue Pa))
                          (penv_ir penv_mc : param_env Pa) (rf : a64_regfile) (sp : @Integers.bit_int 64%positive) (mstk : mc_stack_mem) =>
    ir_at_cut bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c /\
    pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
    lmap_matches_env penv_ir lmap_cut (apply_phi_env env_c dvs) /\
    Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
    a64_at_cut ls sp0 rf0 rf sp mstk /\
    (forall nm, mc_starts_with_bang nm = false -> penv_ir nm = penv0 nm /\ penv_mc nm = penv0 nm) /\
    wf_param_env_for (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls) penv_mc /\
    ub_ctx_holds penv_mc dummy_freeze_oracle
      (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) /\
    (forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) ->
       exists d1 d2 : @dvalue Pa, penv_ir nm = Some d1 /\ penv_mc nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) /\
    mc_cut_obl_inv_holds ls penv_mc dummy_freeze_oracle /\
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (a64_read_reg (mlr_reg rb) rf))))) /\
       (mlr_width rb = 32%positive ->
          penv_mc (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf))))) /\
    (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))))).
  assert (Hentry_step :
    cfg_steps_to_ub default_draw_strat (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
    (exists fuel_end rf_end fl_end mstk_end env_out dv_ir,
       a64_exec_mem fuel_end insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp0, fl_end, mstk_end) /\
       a64_callee_saved_preserved rf0 rf_end /\
       pure_cfg_steps (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end))))) \/
    (exists n rf1 sp1 fl1 mstk1 env_c bid_c dvs penv_ir1 penv_mc1,
       a64_exec_steps n insts sp0 0%N rf0 sp0 fl0 mstk0 = Some (ml_mc_pc ls, rf1, sp1, fl1, mstk1) /\
       a64_cut_inv env_c bid_c dvs penv_ir1 penv_mc1 rf1 sp1 mstk1)).
  { pose proof (reify_ir_seg_sound "entry" ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init
                  [] wr_ent penv_ext (init_cfg_locals (args ir_cfg) vs) (init_cfg_locals (args ir_cfg) vs)
                  t_ir_ent Ewre Hdisj_e_nil (conj eq_refl Hlm_init_ext) Ere_ent) as Hir_ent.
    pose proof (summarize_a64_seg_sound "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 sp0 rf0 sp0 fl0 mstk0 Hrw Hval_a64 Hsp0
                  ltac:(unfold mc_frame_cap; lia) Hsp0_eq Ha64_init_agrees (mc_sym_stack_agrees_empty _ _ _ _ _)
                  (fun C => ltac:(discriminate C)) Es_ent) as Hmc_ent.
    apply a64_seg_exec_to_mc in Hmc_ent.
    destruct (collect_mc_ir_obls_acc_sound EA_AArch64 ls ret_w hdr_ws allowed0 false penv_ext penv_ext
                bmap hdr_id hdr_phis [] (init_cfg_locals (args ir_cfg) vs) (init ir_cfg) (init ir_cfg) t_ir_ent
                _ _ (a64_seg_to_mc_seg seg_ent) (ml_inv ls) [] obls_body obls_all
                eq_refl Hwf_te Hnf_ent Hpenv_ext_ref
                Hir_ent Hmc_ent (fun C => ltac:(discriminate C)) (fun _ _ Hin => ltac:(contradiction Hin)) Eob_e Hobls_ent)
      as [_ [Hub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & (fuel_e & rf_e & fl_e & mstk_e & Hme & Hcs & Hev_mc) & Hev_mc2 & Href_d)
                | (env_c & bid_c & b_hdr0 & dvs & lmap_cut0 & phis_ir & sp' & rr' & astk' &
                   Htau & Ebh0 & Hin_lm & Hlm_m & _ & Hstp & Hids & Hws_m & Hpwf_m & Hph_m & Hsp' &
                   (n & rf1 & sp1 & fl1 & mstk1 & _ & Hst_mc & _ & Hsp_c & Hag' & Hastk') &
                   Hunsp & Hphi_d & Hregs_o & Hsav & Hslts_o & Hmi_o)]]].
    - left; change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)); exact (Hub default_draw_strat).
    - right; left; exists fuel_e, rf_e, fl_e, mstk_e, env_out, dv_ir.
      split; [exact Hme | split; [exact Hcs | split]].
      + change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)); exact Hst.
      + rewrite Hev_mc in Hev_mc2; inversion Hev_mc2; subst dv_mc; exact Href_d.
    - rewrite Ebh in Ebh0; inversion Ebh0; subst b_hdr0.
      assert (Hat1 : a64_at_cut ls sp0 rf0 rf1 sp1 mstk1).
      { repeat split.
        - rewrite Hsp_c, Hsp'; reflexivity.
        - intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hunsp r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
        - intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                      off MS_8 false astk' mstk1 (MSV_SavedReg r) Hastk' (Hsav off r Hr)) as Hsld.
          cbn [mc_sym_val_agrees] in Hsld; exact Hsld. }
      assert (Hregs_ev : forall rb, In rb (ml_regs ls) -> exists e_mc64,
        eval_closed_cert_expr penv_ext dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf1))) /\
        mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Refine false [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Defined false [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))).
      { intros rb Hrb; destruct (Hregs_o rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d).
        pose proof (Hag' (mlr_reg rb)) as Hagr; rewrite Err in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        exists e_mc64; split; [exact Hagr | split; assumption]. }
      assert (Hslts_ev : forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64,
        eval_closed_cert_expr penv_ext dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk1 off sz false))) /\
        mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Refine false [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Defined false [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))).
      { intros off sz e_s Hs; destruct (Hslts_o off sz e_s Hs) as (e_mc64 & Eld & Ho_r & Ho_d).
        pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                      off sz false astk' mstk1 (MSV_Expr e_mc64) Hastk' Eld) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exists e_mc64; split; [exact Hsld | split; assumption]. }
      destruct (@build_next_cut_penvs_sound Pa EA_AArch64 ls allowed0 mc_init_ctx penv0 penv_ext penv_ext
                  hdr_ws phis_ir dvs (fun r => a64_read_reg r rf1) mstk1 (ml_inv ls) false []
                  Hwf Hnb_al Hpenv0 Hctx0 (fun nm Hnb => conj (Hnb_ext nm Hnb) (Hnb_ext nm Hnb))
                  Hinv_sub Hreg_sub Hslt_sub Hws_m Hph_m (fun C => ltac:(discriminate C)) (fun _ _ Hin => ltac:(contradiction Hin))
                  ltac:(cbn [cut_vars_from_ws]; rewrite app_nil_r; exact Hpwf_m)
                  ltac:(cbn [cut_vars_from_ws]; rewrite app_nil_r; exact Hpenv_ext_ref) Hphi_d Hregs_ev Hslts_ev Hmi_o)
        as (Hnb_1 & Hwf_mc1 & Hctx1 & Href1 & Hphi1 & Hmi1 & Hregs1 & Hslts1).
      set (penv_ir1 := overlay_penv (build_cut_ir_binds 0%nat hdr_ws dvs) penv0) in *.
      set (penv_mc1 := overlay_penv (build_cut_mc_binds ls penv_ext (fun r => a64_read_reg r rf1) mstk1 0%nat hdr_ws phis_ir dvs ++ build_hi32_binds (fun r => a64_read_reg r rf1) (ml_regs ls)) penv0) in *.
      assert (Hlm_next1 : lmap_matches_env penv_ir1 lmap_cut (apply_phi_env env_c dvs)).
      { apply (lmap_base_matches_next allowed0 penv0 penv_ext penv_ir1 lmap_base lmap_cut0 dvs env_c hdr_phis wr_body
                 Hwf_lb (fun r w ce Hf => common_cut_lmap_in lmap_init (collect_entry_cut_lmaps t_ir_ent) lmap_cut0 Hin_lm r w ce Hf)
                 Hlm_m (fun nm w Hal => eq_trans (proj1 (Hnb_1 nm (Hnb_al nm w Hal))) (Logic.eq_sym (Hnb_ext nm (Hnb_al nm w Hal))))
                 Hnd_hp_b Hids Hdisj_b).
        intros k id w dv Hnh Hndv; assert (Hnw : nth_error hdr_ws k = Some w) by (unfold hdr_ws, extract_hdr_phi_widths; rewrite nth_error_map, Hnh; reflexivity); exact (Hphi1 k id w dv Hnw Hndv). }
      right; right; exists n, rf1, sp1, fl1, mstk1, env_c, bid_c, dvs, penv_ir1, penv_mc1.
      split; [exact Hst_mc |].
      unfold a64_cut_inv.
      split; [destruct Htau as [[-> [-> ->]] | Htau]; [left; repeat split; reflexivity | right; exact Htau] |].
      split; [exact Hstp | split; [exact Hlm_next1 | split; [exact Hids | split; [exact Hat1 |]]]].
      split; [exact Hnb_1 | split; [exact Hwf_mc1 | split; [exact Hctx1 | split; [exact Href1 | split; [exact Hmi1 | split; [exact Hregs1 | exact Hslts1]]]]]]. }
  assert (Hbody_step : forall env_c bid_c dvs penv_ir penv_mc rf sp fl mstk,
    a64_cut_inv env_c bid_c dvs penv_ir penv_mc rf sp mstk ->
    (cfg_steps_to_ub default_draw_strat (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)) \/
    (exists fuel_end rf_end fl_end mstk_end env_out dv_ir,
       a64_exec_mem fuel_end insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
       a64_callee_saved_preserved rf0 rf_end /\
       pure_cfg_steps (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end))))) \/
    (exists n rf' sp' fl' mstk' env_c' bid_c' dvs' penv_ir' penv_mc',
       (1 <= n)%nat /\
       a64_exec_steps n insts sp0 (ml_mc_pc ls) rf sp fl mstk = Some (ml_mc_pc ls, rf', sp', fl', mstk') /\
       a64_cut_inv env_c' bid_c' dvs' penv_ir' penv_mc' rf' sp' mstk')).
  { intros env_c bid_c dvs penv_ir penv_mc rf sp fl mstk
           (Hcut & Hstp_p & Hlm_c & Hids & Hat & Hnb_c & Hwf_mc & Hctx_c & Href_c & Hmi_c & Hregs_c & Hslts_c).
    assert (Hpres_phi : forall r, In r (lmap_keys lmap_base) -> RM.find r (apply_phi_env env_c dvs) = RM.find r env_c).
    { intros r Hr; apply apply_phi_env_preserves_not_in.
      intro Hin; apply (disjoint_raw_ids_spec _ _ r Hdisj_b Hr), in_or_app; left.
      clear -Hids Hin; revert dvs Hids Hin; induction hdr_phis as [| [i0 w0] rp IH];
        intros [| [i1 d1] rd] H2 Hin; cbn in *; try inversion H2; [contradiction |].
      destruct Hin as [Heq | Hr]; [left; subst; congruence | right; exact (IH rd H5 Hr)]. }
    assert (Hre_body_c : reify_ir_seg "body" ir_fuel bmap hdr_id hdr_phis true [] bid_c hdr_id lmap_cut = inr t_ir_body)
      by exact (reify_ir_seg_req_step_bid_from_irrel "body" ir_fuel bmap hdr_id hdr_phis [] hdr_id bid_c hdr_id lmap_cut t_ir_body Ere_body).
    pose proof (reify_ir_seg_sound "body" ir_fuel bmap hdr_id hdr_phis true [] bid_c hdr_id lmap_cut
                  (lmap_keys lmap_base) wr_body penv_ir env_c (apply_phi_env env_c dvs) t_ir_body
                  Ewrb Hdisj_b_wr (ex_intro _ b_hdr (conj Ebh (conj Hstp_p (conj Hpres_phi Hlm_c)))) Hre_body_c) as Hir_body.
    destruct Hat as [Hsp_r [Hunsp_r Hsav_r]].
    pose proof (summarize_a64_seg_sound "body" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                  (a64_cut_vrf ls) (build_cut_astk (ml_slots ls)) a64_init_sym_flags false ret_w seg_body
                  penv_mc dummy_freeze_oracle rf0 sp0 rf sp fl mstk Hrw Hval_a64 Hsp0 Hrng Hsp_r
                  (a64_cut_vrf_agrees penv_mc dummy_freeze_oracle ls rf0 sp0 rf Hwf Hunsp_r Hregs_c)
                  (build_cut_astk_agrees penv_mc dummy_freeze_oracle (fun k => a64_read_reg k rf0) sp0 (ml_slots ls) mstk Hslts_c Hsav_r)
                  (fun C => ltac:(discriminate C)) Es_body) as Hmc_body.
    apply a64_seg_exec_to_mc in Hmc_body.
    pose proof (check_mc_loop_obls_sound _ _ _ _ _ _ penv_mc dummy_freeze_oracle true Hchk Hwf_mc Hctx_c) as Hobls_all_b.
    pose proof (collect_mc_ir_obls_acc_sub _ _ _ _ _ _ _ _ _ _ _ Eob_e Hobls_all_b) as Hobls_b.
    destruct (collect_mc_ir_obls_acc_sound EA_AArch64 ls ret_w hdr_ws (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) true penv_ir penv_mc
                bmap hdr_id hdr_phis (lmap_keys lmap_base) env_c bid_c hdr_id t_ir_body
                _ _ (a64_seg_to_mc_seg seg_body) (ml_inv ls) [] [] obls_body eq_refl Hwf_tb Hnf_bdy Href_c
                Hir_body Hmc_body (fun _ => Hmi_c) (fun _ _ Hin => ltac:(contradiction Hin)) Eob_b Hobls_b)
      as [_ [Hub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & (fuel_e & rf_e & fl_e & mstk_e & Hme & Hcs & Hev_mc) & Hev_mc2 & Href_d)
                | (env_c' & bid_c' & b_hdr0 & dvs' & lmap_cut' & phis_ir & sp' & rr' & astk' &
                   Htau & Ebh0 & _ & Hlm_m & Hkp_lb & Hstp & Hids' & Hws_m & Hpwf_m & Hph_m & Hsp' &
                   (n & rf' & sp_c' & fl_c' & mstk' & Hn & Hst_mc & _ & Hsp_c' & Hag' & Hastk') &
                   Hunsp & Hphi_d & Hregs_o & Hsav & Hslts_o & Hmi_o)]]].
    - left; change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)).
      exact (ir_at_cut_ub bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c default_draw_strat Hcut (Hub default_draw_strat)).
    - right; left; exists fuel_e, rf_e, fl_e, mstk_e, env_out, dv_ir; repeat split; try assumption.
      + change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)).
        exact (ir_at_cut_ret bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c env_out dv_ir Hcut Hst).
      + rewrite Hev_mc in Hev_mc2; inversion Hev_mc2; subst dv_mc; exact Href_d.
    - rewrite Ebh in Ebh0; inversion Ebh0; subst b_hdr0.
      assert (Hat' : a64_at_cut ls sp0 rf0 rf' sp_c' mstk').
      { repeat split.
        - rewrite Hsp_c', Hsp'; reflexivity.
        - intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hunsp r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
        - intros off r Hr; pose proof (mc_sym_stk_load_sound penv_mc dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                      off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hsav off r Hr)) as Hsld.
          cbn [mc_sym_val_agrees] in Hsld; exact Hsld. }
      assert (Hregs_ev : forall rb, In rb (ml_regs ls) -> exists e_mc64,
        eval_closed_cert_expr penv_mc dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf'))) /\
        mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Refine true [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Defined true [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))).
      { intros rb Hrb; destruct (Hregs_o rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d).
        pose proof (Hag' (mlr_reg rb)) as Hagr; rewrite Err in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        exists e_mc64; split; [exact Hagr | split; assumption]. }
      assert (Hslts_ev : forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64,
        eval_closed_cert_expr penv_mc dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk' off sz false))) /\
        mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Refine true [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Defined true [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))).
      { intros off sz e_s Hs; destruct (Hslts_o off sz e_s Hs) as (e_mc64 & Eld & Ho_r & Ho_d).
        pose proof (mc_sym_stk_load_sound penv_mc dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                      off sz false astk' mstk' (MSV_Expr e_mc64) Hastk' Eld) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exists e_mc64; split; [exact Hsld | split; assumption]. }
      destruct (@build_next_cut_penvs_sound Pa EA_AArch64 ls allowed0 mc_init_ctx penv0 penv_ir penv_mc
                  hdr_ws phis_ir dvs' (fun r => a64_read_reg r rf') mstk' (ml_inv ls) true []
                  Hwf Hnb_al Hpenv0 Hctx0 Hnb_c
                  Hinv_sub Hreg_sub Hslt_sub Hws_m Hph_m (fun _ => Hmi_c) (fun _ _ Hin => ltac:(contradiction Hin))
                  Hpwf_m Href_c Hphi_d Hregs_ev Hslts_ev Hmi_o)
        as (Hnb' & Hwf_mc' & Hctx' & Href' & Hphi' & Hmi' & Hregs' & Hslts').
      set (penv_ir' := overlay_penv (build_cut_ir_binds 0%nat hdr_ws dvs') penv0) in *.
      set (penv_mc' := overlay_penv (build_cut_mc_binds ls penv_mc (fun r => a64_read_reg r rf') mstk' 0%nat hdr_ws phis_ir dvs' ++ build_hi32_binds (fun r => a64_read_reg r rf') (ml_regs ls)) penv0) in *.
      assert (Hlm_env_c' : lmap_matches_env penv_ir lmap_base env_c').
      { intros r w ce Hf; assert (Hr_k : In r (lmap_keys lmap_base)) by (apply in_lmap_keys_iff; eexists; exact Hf).
        assert (Hnf_h : ~ In r (List.map fst hdr_phis)) by (intro Hin; apply (disjoint_raw_ids_spec _ _ r Hdisj_b Hr_k), in_or_app; left; exact Hin).
        assert (Hf_cut : RM.find r lmap_cut = Some (w, ce)) by (unfold lmap_cut, wrap_cut_mc; rewrite wrap_cut_mc_at_preserves by exact Hnf_h; exact Hf).
        destruct (Hlm_c r w ce Hf_cut) as (dv0 & He0 & Hs0 & Hrm0); exists dv0; repeat split; try assumption.
        rewrite (Hkp_lb r Hr_k), <- Hpres_phi by exact Hr_k; exact He0. }
      assert (Hlm_next' : lmap_matches_env penv_ir' lmap_cut (apply_phi_env env_c' dvs')).
      { apply (lmap_base_matches_next allowed0 penv0 penv_ir penv_ir' lmap_base lmap_base dvs' env_c' hdr_phis wr_body
                 Hwf_lb (fun r w ce H => H) Hlm_env_c'
                 (fun nm w Hal => eq_trans (proj1 (Hnb' nm (Hnb_al nm w Hal))) (Logic.eq_sym (proj1 (Hnb_c nm (Hnb_al nm w Hal)))))
                 Hnd_hp_b Hids' Hdisj_b).
        intros k id w dv Hnh Hndv; assert (Hnw : nth_error hdr_ws k = Some w) by (unfold hdr_ws, extract_hdr_phi_widths; rewrite nth_error_map, Hnh; reflexivity); exact (Hphi' k id w dv Hnw Hndv). }
      right; right; exists n, rf', sp_c', fl_c', mstk', env_c', bid_c', dvs', penv_ir', penv_mc'.
      split; [exact (Hn eq_refl) | split; [exact Hst_mc |]].
      unfold a64_cut_inv.
      split; [exact (ir_at_cut_step bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c env_c' bid_c' Hcut Htau) |].
      split; [exact Hstp | split; [exact Hlm_next' | split; [exact Hids' | split; [exact Hat' |]]]].
      split; [exact Hnb' | split; [exact Hwf_mc' | split; [exact Hctx' | split; [exact Href' | split; [exact Hmi' | split; [exact Hregs' | exact Hslts']]]]]]. }
  split.
  - assert (Hbwd_cut : forall n_max fuel rf sp fl mstk env_c bid_c dvs penv_ir penv_mc rf_end sp_end fl_end mstk_end,
      (fuel <= n_max)%nat ->
      a64_cut_inv env_c bid_c dvs penv_ir penv_mc rf sp mstk ->
      a64_exec_mem fuel insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp_end, fl_end, mstk_end) ->
      sp_end = sp0 /\ a64_callee_saved_preserved rf0 rf_end /\
      exists sigma_ir,
        wf_draw_strat sigma_ir /\
        (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
         exists sigma_ir' env_out dv_ir,
           cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
             sigma_ir' env_out dv_ir /\
           dvalue_refines dv_ir
             (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))).
    { intros n_max; induction n_max as [| n_max' IH];
        intros fuel rf sp fl mstk env_c bid_c dvs penv_ir penv_mc rf_end sp_end fl_end mstk_end Hle Hinv Hmem.
      - assert (Hf0 : fuel = 0%nat) by lia; subst fuel; cbn [a64_exec_mem] in Hmem; discriminate Hmem.
      - destruct (Hbody_step env_c bid_c dvs penv_ir penv_mc rf sp fl mstk Hinv)
          as [Hub | [(fuel_e & rf_e & fl_e & mstk_e & env_out & dv_ir & Hme & Hcs & Hst & Href)
                    | (n1 & rf1 & sp1 & fl1 & mstk1 & env_c1 & bid_c1 & dvs1 & penv_ir1 & penv_mc1 & Hn1 & Hst1 & Hinv1)]].
        + destruct (Hskel_bwd fuel rf sp fl mstk rf_end sp_end fl_end mstk_end (proj1 (proj2 (proj2 (proj2 (proj2 Hinv))))) Hmem) as [Hspe Hcs].
          split; [exact Hspe | split; [exact Hcs | exists default_draw_strat; split; [exact default_draw_strat_wf | left; exact Hub]]].
        + pose proof (a64_exec_mem_det fuel fuel_e insts (ml_mc_pc ls) sp0 rf sp fl mstk _ _ Hmem Hme) as Heq.
          inversion Heq; subst; split; [reflexivity | split; [exact Hcs | exists default_draw_strat; split; [exact default_draw_strat_wf | right; exists default_draw_strat, env_out, dv_ir; split; [apply pure_cfg_to_cfg_ret; exact Hst | exact Href]]]].
        + destruct (a64_exec_mem_split_steps n1 fuel insts sp0 (ml_mc_pc ls) rf sp fl mstk
                      (ml_mc_pc ls) rf1 sp1 fl1 mstk1 (rf_end, sp_end, fl_end, mstk_end) Hmem Hst1) as [Hlt Hrem].
          exact (IH (fuel - n1)%nat rf1 sp1 fl1 mstk1 env_c1 bid_c1 dvs1 penv_ir1 penv_mc1 rf_end sp_end fl_end mstk_end ltac:(lia) Hinv1 Hrem). }
    intros fuel rf_end sp_end fl_end mstk_end Hmem.
    destruct (Hentry_skel_bwd fuel rf_end sp_end fl_end mstk_end Hmem) as [Hspe0 Hcs0].
    destruct Hentry_step as [Hub | [(fuel_e & rf_e & fl_e & mstk_e & env_out & dv_ir & Hme & Hcs & Hst & Href)
                                  | (n1 & rf1 & sp1 & fl1 & mstk1 & env_c1 & bid_c1 & dvs1 & penv_ir1 & penv_mc1 & Hst1 & Hinv1)]].
    + split; [exact Hspe0 | split; [exact Hcs0 | exists default_draw_strat; split; [exact default_draw_strat_wf | left; exact Hub]]].
    + pose proof (a64_exec_mem_det fuel fuel_e insts 0%N sp0 rf0 sp0 fl0 mstk0 _ _ Hmem Hme) as Heq.
      inversion Heq; subst; split; [reflexivity | split; [exact Hcs | exists default_draw_strat; split; [exact default_draw_strat_wf | right; exists default_draw_strat, env_out, dv_ir; split; [apply pure_cfg_to_cfg_ret; exact Hst | exact Href]]]].
    + destruct (a64_exec_mem_split_steps n1 fuel insts sp0 0%N rf0 sp0 fl0 mstk0
                  (ml_mc_pc ls) rf1 sp1 fl1 mstk1 (rf_end, sp_end, fl_end, mstk_end) Hmem Hst1) as [_ Hrem].
      exact (Hbwd_cut (fuel - n1)%nat (fuel - n1)%nat rf1 sp1 fl1 mstk1 env_c1 bid_c1 dvs1 penv_ir1 penv_mc1 rf_end sp_end fl_end mstk_end (Nat.le_refl _) Hinv1 Hrem).
  - assert (Hfwd_aux : forall k : nat,
      (exists fuel rf_end sp_end fl_end mstk_end, a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end)) \/
      (exists n rf_k sp_k fl_k mstk_k, (k <= n)%nat /\ a64_exec_steps n insts sp0 0%N rf0 sp0 fl0 mstk0 = Some (ml_mc_pc ls, rf_k, sp_k, fl_k, mstk_k) /\ a64_at_cut ls sp0 rf0 rf_k sp_k mstk_k)).
    { induction k as [| k' IH].
      - destruct Hentry_skel_fwd as [(f0 & rfe & spe & fle & me & Hmem) | (n0 & rf1 & sp1 & fl1 & mstk1 & Hst1 & Hat1)].
        + left; exists f0, rfe, spe, fle, me; exact Hmem.
        + right; exists n0, rf1, sp1, fl1, mstk1; split; [lia | split; assumption].
      - destruct IH as [(f0 & rfe & spe & fle & me & Hmem) | (n0 & rfk & spk & flk & mstkk & Hle & Hst0 & Hatk)];
          [left; exists f0, rfe, spe, fle, me; exact Hmem |].
        destruct (@a64_skel_step Pa "skel" insts ret_w ls seg_skel rf0 sp0 rfk spk flk mstkk Hwf Hrw Hval_a64 Hsp0 Es_skel Hok_skel Hatk)
          as [(fe & rfe & fle & me & Hme & _) | (n1 & rf1 & sp1 & fl1 & mstk1 & Hn1 & Hst1 & Hat1)].
        + left; exists (n0 + fe)%nat, rfe, sp0, fle, me; exact (a64_exec_steps_to_exec_mem n0 fe insts sp0 0%N rf0 sp0 fl0 mstk0 (ml_mc_pc ls) rfk spk flk mstkk (rfe, sp0, fle, me) Hst0 Hme).
        + right; exists (n0 + n1)%nat, rf1, sp1, fl1, mstk1; split; [lia | split; [exact (a64_exec_steps_trans n0 n1 insts sp0 0%N rf0 sp0 fl0 mstk0 (ml_mc_pc ls) rfk spk flk mstkk (ml_mc_pc ls, rf1, sp1, fl1, mstk1) Hst0 Hst1) | exact Hat1]]. }
    exact Hfwd_aux.
Qed.


