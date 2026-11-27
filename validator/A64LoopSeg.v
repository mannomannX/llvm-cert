(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified AArch64 (A64) Loop-Segment Symbolic Summarizer ([CertValidator.A64LoopSeg])

    Purpose:
      Provides multi-step concrete non-ret execution lemmas ([a64_exec_steps]), the A64
      loop-segment symbolic summarizer ([summarize_a64_seg]) backed by [summarize_a64_seg_wf]
      and [summarize_a64_seg_sound], and initial argument variable tracking.

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml directly. [summarize_a64_seg] fails closed
      ([inl err]) on missing instructions, invalid branches/cutpoints, undefined reads, or fuel
      exhaustion; accepted [a64_seg_tree] trees satisfy [a64_seg_wf] and concrete soundness.

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{CertFormat,AigLrat,
      AlgRules,CfgDag,Elf64Spec,McFrameMem,McIsaCommon,A64Decode,A64ExecSym,A64DagProof}];
      zero custom axioms.

    Section Outline:
      8. Multi-step execution lemmas ([a64_exec_steps]), [a64_seg_tree], [a64_sym_step_one],
      [summarize_a64_seg], [summarize_a64_seg_wf] / [summarize_a64_seg_sound], and init vars. *)

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
  A64ExecSym
  A64DagProof.

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

(** ** 8. Loop-Segment Symbolic Summarizer & Multi-Step Concrete Lemmas (M3b) *)

Definition a64_exec_one_nonret
  (dec : decoded_a64_inst) (sp0 : @Integers.bit_int 64%positive)
  (pc : N) (rf : a64_regfile) (sp : @Integers.bit_int 64%positive)
  (fl : a64_flags) (mstk : mc_stack_mem)
  : option (N * a64_regfile * @Integers.bit_int 64%positive * a64_flags * mc_stack_mem) :=
  let next_pc := (pc + 4%N)%N in
  match dai_inst dec with
  | A64_Nop => Some (next_pc, rf, sp, fl, mstk)
  | A64_AddSubImm sf is_sub sfl rd rn imm =>
      if sf && negb sfl then
        let lhs := a64_read_reg_sp rn rf sp in
        let rhs := @Integers.repr 64%positive (Z.of_N imm) in
        let res := if is_sub then @Integers.sub 64%positive lhs rhs else @Integers.add 64%positive lhs rhs in
        let '(rf', sp') := a64_write_reg_sp rd res rf sp in
        Some (next_pc, rf', sp', fl, mstk)
      else
        let lhs := a64_read_w sf rn rf in
        let rhs := @Integers.repr (a64_w sf) (Z.of_N imm) in
        let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
        Some (next_pc, a64_write_w sf rd res rf, sp, (if sfl then fl' else fl), mstk)
  | A64_AddSubShift sf is_sub sfl rd rn rm sh amt =>
      let lhs := a64_read_w sf rn rf in
      let rhs := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt in
      let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
      Some (next_pc, a64_write_w sf rd res rf, sp, (if sfl then fl' else fl), mstk)
  | A64_AddSubExt sf is_sub sfl rd rn rm ext amt =>
      let lhs := a64_read_w sf rn rf in
      let rhs := a64_eval_extend (a64_w sf) (a64_read_reg rm rf) ext amt in
      let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
      Some (next_pc, a64_write_w sf rd res rf, sp, (if sfl then fl' else fl), mstk)
  | A64_LogicalImm sf op sfl rd rn mask =>
      let lhs := a64_read_w sf rn rf in
      let rhs := @Integers.repr (a64_w sf) (Z.of_N mask) in
      let res := a64_eval_logic_op (a64_w sf) op lhs rhs in
      let fl' := if sfl then a64_eval_logic_flags (a64_w sf) res else fl in
      Some (next_pc, a64_write_w sf rd res rf, sp, fl', mstk)
  | A64_LogicalShift sf op inv_rm sfl rd rn rm sh amt =>
      let lhs := a64_read_w sf rn rf in
      let shv := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt in
      let rhs := if inv_rm then @Integers.not (a64_w sf) shv else shv in
      let res := a64_eval_logic_op (a64_w sf) op lhs rhs in
      let fl' := if sfl then a64_eval_logic_flags (a64_w sf) res else fl in
      Some (next_pc, a64_write_w sf rd res rf, sp, fl', mstk)
  | A64_MoveWide sf kind rd imm16 shift =>
      let w := a64_w sf in
      let imm_sh := N.shiftl imm16 shift in
      let res :=
        match kind with
        | AMW_Movz => @Integers.repr w (Z.of_N imm_sh)
        | AMW_Movn => @Integers.not w (@Integers.repr w (Z.of_N imm_sh))
        | AMW_Movk =>
            let cur := a64_read_w sf rd rf in
            let clr := @Integers.not w (@Integers.repr w (Z.of_N (N.shiftl 65535%N shift))) in
            @Integers.or w (@Integers.and w cur clr) (@Integers.repr w (Z.of_N imm_sh))
        end
      in
      Some (next_pc, a64_write_w sf rd res rf, sp, fl, mstk)
  | A64_Bitfield sf kind rd rn immr imms =>
      let res := a64_eval_bitfield (a64_w sf) kind
                   (a64_read_w sf rn rf) (a64_read_w sf rd rf) immr imms in
      Some (next_pc, a64_write_w sf rd res rf, sp, fl, mstk)
  | A64_Extr sf rd rn rm lsb =>
      let res := a64_eval_extr (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf) lsb in
      Some (next_pc, a64_write_w sf rd res rf, sp, fl, mstk)
  | A64_MulAddSub sf is_sub rd rn rm ra =>
      let w := a64_w sf in
      let p := @Integers.mul w (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
      let a := a64_read_w sf ra rf in
      let res := if is_sub then @Integers.sub w a p else @Integers.add w a p in
      Some (next_pc, a64_write_w sf rd res rf, sp, fl, mstk)
  | A64_MulWidening sgn is_sub rd rn rm ra =>
      let n32 := a64_read_w false rn rf in
      let m32 := a64_read_w false rm rf in
      let n64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive n32
                                             else @Integers.unsigned 32%positive n32) in
      let m64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive m32
                                             else @Integers.unsigned 32%positive m32) in
      let p := @Integers.mul 64%positive n64 m64 in
      let a := a64_read_reg ra rf in
      let res := if is_sub then @Integers.sub 64%positive a p else @Integers.add 64%positive a p in
      Some (next_pc, a64_write_reg rd res rf, sp, fl, mstk)
  | A64_DataProc2 sf op rd rn rm =>
      let res := a64_eval_dp2 (a64_w sf) op (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
      Some (next_pc, a64_write_w sf rd res rf, sp, fl, mstk)
  | A64_CondSelect sf kind cond rd rn rm =>
      let res := a64_eval_csel (a64_w sf) kind cond fl
                   (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
      Some (next_pc, a64_write_w sf rd res rf, sp, fl, mstk)
  | A64_CondCompareReg sf is_sub cond rn rm nzcv =>
      let lhs := a64_read_w sf rn rf in
      let rhs := a64_read_w sf rm rf in
      let '(_, cfl) := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
      let fl' := if a64_eval_cond cond fl then cfl else a64_flags_of_imm4 nzcv in
      Some (next_pc, rf, sp, fl', mstk)
  | A64_CondCompareImm sf is_sub cond rn imm5 nzcv =>
      let lhs := a64_read_w sf rn rf in
      let rhs := @Integers.repr (a64_w sf) (Z.of_N imm5) in
      let '(_, cfl) := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
      let fl' := if a64_eval_cond cond fl then cfl else a64_flags_of_imm4 nzcv in
      Some (next_pc, rf, sp, fl', mstk)
  | A64_LdStImm is_load is_signed sf_dst sz mode rt rn imm =>
      if (if N.eqb rn 31%N then negb (mc_sp_aligned16 (mc_addr_to_off sp0 sp)) else false)
      then None
      else
        let base := a64_read_reg_sp rn rf sp in
        let wb_addr := @Integers.add 64%positive base (@Integers.repr 64%positive imm) in
        let '(addr, sp_chk) :=
          match mode with
          | AAM_SignedOffset => (wb_addr, sp)
          | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp)
          | AAM_PostIndex => (base, sp)
          end
        in
        let off := mc_addr_to_off sp0 addr in
        if mc_slot_in_frame (mc_addr_to_off sp0 sp_chk) off sz then
          let '(rf1, mstk1) :=
            if is_load then
              (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk)
            else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf))
          in
          let '(rf2, sp2) :=
            match mode with
            | AAM_SignedOffset => (rf1, sp)
            | AAM_PreIndex | AAM_PostIndex => a64_write_reg_sp rn wb_addr rf1 sp
            end
          in
          Some (next_pc, rf2, sp2, fl, mstk1)
        else None
  | A64_LdStPair is_load sf mode rt1 rt2 rn imm =>
      if (if N.eqb rn 31%N then negb (mc_sp_aligned16 (mc_addr_to_off sp0 sp)) else false)
      then None
      else
        let base := a64_read_reg_sp rn rf sp in
        let wb_addr := @Integers.add 64%positive base (@Integers.repr 64%positive imm) in
        let '(addr, sp_chk) :=
          match mode with
          | AAM_SignedOffset => (wb_addr, sp)
          | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp)
          | AAM_PostIndex => (base, sp)
          end
        in
        let off := mc_addr_to_off sp0 addr in
        let sz := if sf then MS_8 else MS_4 in
        let delta := mc_mem_bytes_Z sz in
        if mc_slot_in_frame (mc_addr_to_off sp0 sp_chk) off sz &&
           mc_slot_in_frame (mc_addr_to_off sp0 sp_chk) (off + delta) sz
        then
          let '(rf1, mstk1) :=
            if is_load then
              (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false)
                 (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk)
            else
              (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf))
                                (off + delta) sz (a64_read_reg rt2 rf))
          in
          let '(rf2, sp2) :=
            match mode with
            | AAM_SignedOffset => (rf1, sp)
            | AAM_PreIndex | AAM_PostIndex => a64_write_reg_sp rn wb_addr rf1 sp
            end
          in
          Some (next_pc, rf2, sp2, fl, mstk1)
        else None
  | A64_B rel =>
      match add_rel_off pc rel with
      | None => None
      | Some tgt_pc => Some (tgt_pc, rf, sp, fl, mstk)
      end
  | A64_BCond cond rel =>
      if a64_eval_cond cond fl then
        match add_rel_off pc rel with
        | None => None
        | Some tgt_pc => Some (tgt_pc, rf, sp, fl, mstk)
        end
      else Some (next_pc, rf, sp, fl, mstk)
  | A64_Cbz sf is_nz rt rel =>
      let v := a64_read_w sf rt rf in
      let eq0 := @Integers.eq (a64_w sf) v (@Integers.zero (a64_w sf)) in
      let taken := if is_nz then negb eq0 else eq0 in
      if taken then
        match add_rel_off pc rel with
        | None => None
        | Some tgt_pc => Some (tgt_pc, rf, sp, fl, mstk)
        end
      else Some (next_pc, rf, sp, fl, mstk)
  | A64_Tbz is_nz rt bit rel =>
      let v := a64_read_reg rt rf in
      let tb := Z.testbit (@Integers.unsigned 64%positive v) (Z.of_N bit) in
      let taken := if is_nz then tb else negb tb in
      if taken then
        match add_rel_off pc rel with
        | None => None
        | Some tgt_pc => Some (tgt_pc, rf, sp, fl, mstk)
        end
      else Some (next_pc, rf, sp, fl, mstk)
  | A64_Ret => None
  end.

Fixpoint a64_exec_steps
  (n : nat) (insts : list decoded_a64_inst) (sp0 : @Integers.bit_int 64%positive)
  (pc : N) (rf : a64_regfile) (sp : @Integers.bit_int 64%positive)
  (fl : a64_flags) (mstk : mc_stack_mem)
  {struct n} : option (N * a64_regfile * @Integers.bit_int 64%positive * a64_flags * mc_stack_mem) :=
  match n with
  | O => Some (pc, rf, sp, fl, mstk)
  | S n' =>
      match lookup_a64_inst insts pc with
      | None => None
      | Some dec =>
          match a64_exec_one_nonret dec sp0 pc rf sp fl mstk with
          | None => None
          | Some (pc1, rf1, sp1, fl1, m1) => a64_exec_steps n' insts sp0 pc1 rf1 sp1 fl1 m1
          end
      end
  end.

Lemma a64_exec_mem_step_nonret :
  forall fuel' insts sp0 pc rf sp fl mstk dec pc1 rf1 sp1 fl1 m1,
    lookup_a64_inst insts pc = Some dec ->
    a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (pc1, rf1, sp1, fl1, m1) ->
    a64_exec_mem (S fuel') insts pc sp0 rf sp fl mstk = a64_exec_mem fuel' insts pc1 sp0 rf1 sp1 fl1 m1.
Proof.
  intros fuel' insts sp0 pc rf sp fl mstk dec pc1 rf1 sp1 fl1 m1 Hlk Hstep.
  cbn [a64_exec_mem]; rewrite Hlk.
  unfold a64_exec_one_nonret in Hstep.
  destruct (dai_inst dec) as
    [ | sf ? ? ? ? ? | | | | | | | | | | | | |
      | ? ? ? ? ? ? ? | ? ? ? ? ? ? ? | rel | cond rel | ? ? ? rel | ? ? ? rel | ];
    try (cbv zeta in Hstep;
         repeat match type of Hstep with
         | (if ?c then _ else _) = _ => destruct c
         | (match ?x with Some _ => _ | None => _ end) = _ => destruct x
         | (let '(_, _) := ?x in _) = _ => destruct x
         end;
         inversion Hstep; subst; reflexivity).
Qed.

Lemma a64_exec_mem_mono :
  forall f1 f2 insts pc sp0 rf sp fl mstk res,
    (f1 <= f2)%nat ->
    a64_exec_mem f1 insts pc sp0 rf sp fl mstk = Some res ->
    a64_exec_mem f2 insts pc sp0 rf sp fl mstk = Some res.
Proof.
  intros f1; induction f1 as [| f1' IH]; intros f2 insts pc sp0 rf sp fl mstk res Hle H;
    [cbn [a64_exec_mem] in H; discriminate H |].
  destruct f2 as [| f2']; [lia |].
  cbn [a64_exec_mem] in H |- *.
  destruct (lookup_a64_inst insts pc) as [dec |]; [| discriminate H].
  destruct (dai_inst dec) as
    [ | sf ? ? ? ? ? | | | | | | | | | | | | |
      | ? ? ? ? ? ? ? | ? ? ? ? ? ? ? | rel | cond rel | ? ? ? rel | ? ? ? rel | ];
    try (cbv zeta in *;
         repeat match type of H with
         | a64_exec_mem f1' _ _ _ _ _ _ _ = Some res => eapply IH; [lia | exact H]
         | (if ?c then _ else _) = _ => destruct c
         | (match ?x with Some _ => _ | None => _ end) = _ => destruct x
         | (let '(_, _) := ?x in _) = _ => destruct x
         end;
         try discriminate H; exact H).
Qed.

Lemma a64_exec_steps_trans :
  forall n1 n2 insts sp0 pc0 rf0 sp_a fl0 m0 pc1 rf1 sp_b fl1 m1 res,
    a64_exec_steps n1 insts sp0 pc0 rf0 sp_a fl0 m0 = Some (pc1, rf1, sp_b, fl1, m1) ->
    a64_exec_steps n2 insts sp0 pc1 rf1 sp_b fl1 m1 = Some res ->
    a64_exec_steps (n1 + n2) insts sp0 pc0 rf0 sp_a fl0 m0 = Some res.
Proof.
  intros n1; induction n1 as [| n1' IH]; intros n2 insts sp0 pc0 rf0 sp_a fl0 m0 pc1 rf1 sp_b fl1 m1 res H1 H2;
    cbn [a64_exec_steps] in *.
  - inversion H1; subst; exact H2.
  - destruct (lookup_a64_inst insts pc0) as [d |] eqn:El; [| discriminate H1].
    destruct (a64_exec_one_nonret d sp0 pc0 rf0 sp_a fl0 m0)
      as [[[[[pc' rf'] sp'] fl'] m'] |] eqn:Hs; [| discriminate H1].
    cbn [Nat.add a64_exec_steps]; rewrite El, Hs; exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2).
Qed.

Lemma a64_exec_steps_to_exec_mem :
  forall n1 f2 insts sp0 pc0 rf0 sp_a fl0 m0 pc1 rf1 sp_b fl1 m1 res,
    a64_exec_steps n1 insts sp0 pc0 rf0 sp_a fl0 m0 = Some (pc1, rf1, sp_b, fl1, m1) ->
    a64_exec_mem f2 insts pc1 sp0 rf1 sp_b fl1 m1 = Some res ->
    a64_exec_mem (n1 + f2) insts pc0 sp0 rf0 sp_a fl0 m0 = Some res.
Proof.
  intros n1; induction n1 as [| n1' IH]; intros f2 insts sp0 pc0 rf0 sp_a fl0 m0 pc1 rf1 sp_b fl1 m1 res H1 H2;
    cbn [a64_exec_steps] in H1.
  - inversion H1; subst; exact H2.
  - destruct (lookup_a64_inst insts pc0) as [dec |] eqn:Hlk; [| discriminate H1].
    destruct (a64_exec_one_nonret dec sp0 pc0 rf0 sp_a fl0 m0)
      as [[[[[pc' rf'] sp'] fl'] m'] |] eqn:Hs; [| discriminate H1].
    cbn [Nat.add].
    rewrite (a64_exec_mem_step_nonret (n1' + f2) insts sp0 pc0 rf0 sp_a fl0 m0 dec pc' rf' sp' fl' m' Hlk Hs).
    exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2).
Qed.

Lemma a64_exec_mem_split_steps :
  forall n1 fuel insts sp0 pc0 rf0 sp_a fl0 m0 pc1 rf1 sp_b fl1 m1 res,
    a64_exec_mem fuel insts pc0 sp0 rf0 sp_a fl0 m0 = Some res ->
    a64_exec_steps n1 insts sp0 pc0 rf0 sp_a fl0 m0 = Some (pc1, rf1, sp_b, fl1, m1) ->
    (n1 < fuel)%nat /\ a64_exec_mem (fuel - n1) insts pc1 sp0 rf1 sp_b fl1 m1 = Some res.
Proof.
  intros n1; induction n1 as [| n1' IH]; intros fuel insts sp0 pc0 rf0 sp_a fl0 m0 pc1 rf1 sp_b fl1 m1 res Hm Hs.
  - cbn [a64_exec_steps] in Hs; inversion Hs; subst; clear Hs.
    destruct fuel; [cbn [a64_exec_mem] in Hm; discriminate Hm |].
    split; [lia | rewrite Nat.sub_0_r; exact Hm].
  - cbn [a64_exec_steps] in Hs.
    destruct (lookup_a64_inst insts pc0) as [dec |] eqn:Hlk; [| discriminate Hs].
    destruct (a64_exec_one_nonret dec sp0 pc0 rf0 sp_a fl0 m0)
      as [[[[[pc' rf'] sp'] fl'] m'] |] eqn:Hst; [| discriminate Hs].
    destruct fuel as [| fuel']; [cbn [a64_exec_mem] in Hm; discriminate Hm |].
    rewrite (a64_exec_mem_step_nonret fuel' insts sp0 pc0 rf0 sp_a fl0 m0 dec pc' rf' sp' fl' m' Hlk Hst) in Hm.
    destruct (IH fuel' insts sp0 pc' rf' sp' fl' m' pc1 rf1 sp_b fl1 m1 res Hm Hs) as [Hlt Hrem].
    split; [lia | exact Hrem].
Qed.

Inductive a64_seg_tree : Type :=
| AST_Cut (sp_off : Z) (vrf : a64_val_regs) (astk : mc_sym_stack)
| AST_Ret (ret_e : cert_expr)
| AST_Branch (cond : cert_expr) (t_br f_br : a64_seg_tree).

Fixpoint a64_seg_wf (allowed : list (string * positive)) (ret_w : positive) (t : a64_seg_tree) {struct t} : Prop :=
  match t with
  | AST_Cut sp_off vrf astk =>
      (- mc_frame_cap <= sp_off <= 0)%Z /\
      wf_a64_val_regs allowed vrf /\
      mc_sym_stack_wf allowed sp_off astk
  | AST_Ret ret_e =>
      wf_sym_expr allowed ret_w ret_e
  | AST_Branch cond dt df =>
      wf_sym_expr allowed 1%positive cond /\
      a64_seg_wf allowed ret_w dt /\
      a64_seg_wf allowed ret_w df
  end.

Variant a64_sym_step_res : Type :=
| ASSR_Next (next_pc : N) (sp_off' : Z) (vrf' : a64_val_regs)
            (astk' : mc_sym_stack) (sfl' : a64_sym_flags) (fl_def' : bool)
| ASSR_Branch (cond : cert_expr) (tgt_pc next_pc : N) (fl_def' : bool)
| ASSR_Ret (ret_e : cert_expr).

Definition a64_sym_step_one
  (dec : decoded_a64_inst) (pc : N) (sp_off : Z) (vrf : a64_val_regs)
  (astk : mc_sym_stack) (sfl : a64_sym_flags) (fl_def : bool) (ret_w : positive)
  : option a64_sym_step_res :=
  let next_pc := (pc + 4%N)%N in
  match dai_inst dec with
  | A64_Nop => Some (ASSR_Next next_pc sp_off vrf astk sfl fl_def)
  | A64_AddSubImm sf is_sub set_fl rd rn imm =>
      if sf && negb set_fl then
        let sv_opt :=
          match a64_val_read_sp rn vrf sp_off with
          | MSV_StackPtr base_off =>
              let off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z in
              if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
          | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
          | MSV_Expr e =>
              Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
          | MSV_Undef => None
          end
        in
        match sv_opt with
        | None => None
        | Some sv =>
            match a64_val_write_sp rd sv sp_off vrf astk with
            | None => None
            | Some (sp_off', vrf', astk') => Some (ASSR_Next next_pc sp_off' vrf' astk' sfl fl_def)
            end
        end
      else if N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N) then None
      else
        match a64_val_read_expr_w sf rn vrf with
        | None => None
        | Some lhs =>
            let rhs := ce_bv_z (a64_w sf) (Z.of_N imm) in
            let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
            Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk
                   (if set_fl then sfl' else sfl) (set_fl || fl_def))
        end
  | A64_AddSubShift sf is_sub set_fl rd rn rm sh amt =>
      match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
      | Some lhs, Some rm_e =>
          let rhs := a64_sym_shift (a64_w sf) rm_e sh amt in
          let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
          Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk
                 (if set_fl then sfl' else sfl) (set_fl || fl_def))
      | _, _ => None
      end
  | A64_AddSubExt sf is_sub set_fl rd rn rm ext amt =>
      if N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N) then None
      else
        match a64_val_read_expr_w sf rn vrf, a64_val_read rm vrf with
        | Some lhs, MSV_Expr rm64 =>
            let rhs := a64_sym_extend (a64_w sf) rm64 ext amt in
            let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
            Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk
                   (if set_fl then sfl' else sfl) (set_fl || fl_def))
        | _, _ => None
        end
  | A64_LogicalImm sf op set_fl rd rn mask =>
      if negb set_fl && N.eqb rd 31%N then None
      else
        match a64_val_read_expr_w sf rn vrf with
        | None => None
        | Some lhs =>
            let rhs := ce_bv_z (a64_w sf) (Z.of_N mask) in
            let res := a64_sym_logic_op (a64_w sf) op lhs rhs in
            let sfl' := if set_fl then a64_sym_logic_flags (a64_w sf) res else sfl in
            Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk sfl' (set_fl || fl_def))
        end
  | A64_LogicalShift sf op inv_rm set_fl rd rn rm sh amt =>
      if a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt then
        match a64_val_read rm vrf with
        | MSV_Undef => None
        | sv => Some (ASSR_Next next_pc sp_off (a64_val_write rd sv vrf) astk sfl fl_def)
        end
      else
        match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
        | Some lhs, Some rm_e =>
            let shv := a64_sym_shift (a64_w sf) rm_e sh amt in
            let rhs := if inv_rm then a64_sym_not (a64_w sf) shv else shv in
            let res := a64_sym_logic_op (a64_w sf) op lhs rhs in
            let sfl' := if set_fl then a64_sym_logic_flags (a64_w sf) res else sfl in
            Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk sfl' (set_fl || fl_def))
        | _, _ => None
        end
  | A64_MoveWide sf kind rd imm16 shift =>
      let w := a64_w sf in
      let imm_e := ce_bv_z w (Z.of_N (N.shiftl imm16 shift)) in
      match kind with
      | AMW_Movz => Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd imm_e vrf) astk sfl fl_def)
      | AMW_Movn => Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd (a64_sym_not w imm_e) vrf) astk sfl fl_def)
      | AMW_Movk =>
          match a64_val_read_expr_w sf rd vrf with
          | None => None
          | Some cur =>
              let clr := a64_sym_not w (ce_bv_z w (Z.of_N (N.shiftl 65535%N shift))) in
              let res := CE_BinOp CB_Or w no_binop_flags (CE_BinOp CB_And w no_binop_flags cur clr) imm_e in
              Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk sfl fl_def)
          end
      end
  | A64_Bitfield sf kind rd rn immr imms =>
      let dst_opt :=
        match kind with
        | ABF_Bfm => a64_val_read_expr_w sf rd vrf
        | _ => Some (CE_BvConst (a64_w sf) 0%N)
        end in
      match a64_val_read_expr_w sf rn vrf, dst_opt with
      | Some src_e, Some dst_e =>
          let res := a64_sym_bitfield (a64_w sf) kind src_e dst_e immr imms in
          Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk sfl fl_def)
      | _, _ => None
      end
  | A64_Extr sf rd rn rm lsb =>
      match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
      | Some hi_e, Some lo_e =>
          let res := a64_sym_extr (a64_w sf) hi_e lo_e lsb in
          Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk sfl fl_def)
      | _, _ => None
      end
  | A64_MulAddSub sf is_sub rd rn rm ra =>
      match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf, a64_val_read_expr_w sf ra vrf with
      | Some en, Some em, Some ea =>
          let w := a64_w sf in
          let p := CE_BinOp CB_Mul w no_binop_flags en em in
          let res := CE_BinOp (if is_sub then CB_Sub else CB_Add) w no_binop_flags ea p in
          Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk sfl fl_def)
      | _, _, _ => None
      end
  | A64_MulWidening sgn is_sub rd rn rm ra =>
      match a64_val_read_expr_w false rn vrf, a64_val_read_expr_w false rm vrf, a64_val_read ra vrf with
      | Some en, Some em, MSV_Expr ea =>
          let ck := if sgn then CCK_SExt else CCK_ZExt in
          let n64 := CE_Cast ck 32%positive 64%positive no_cast_flags en in
          let m64 := CE_Cast ck 32%positive 64%positive no_cast_flags em in
          let p := CE_BinOp CB_Mul 64%positive no_binop_flags n64 m64 in
          let res := CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags ea p in
          Some (ASSR_Next next_pc sp_off (a64_val_write rd (MSV_Expr res) vrf) astk sfl fl_def)
      | _, _, _ => None
      end
  | A64_DataProc2 sf op rd rn rm =>
      match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
      | Some en, Some em =>
          let res := a64_sym_dp2 (a64_w sf) op en em in
          Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk sfl fl_def)
      | _, _ => None
      end
  | A64_CondSelect sf kind cond rd rn rm =>
      if negb fl_def then None
      else
        match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
        | Some en, Some em =>
            let res := a64_sym_csel (a64_w sf) kind cond sfl en em in
            Some (ASSR_Next next_pc sp_off (a64_val_write_w sf rd res vrf) astk sfl fl_def)
        | _, _ => None
        end
  | A64_CondCompareReg sf is_sub cond rn rm nzcv =>
      if negb fl_def then None
      else
        match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
        | Some en, Some em =>
            let '(_, csfl) := a64_sym_add_sub (a64_w sf) is_sub en em in
            let sfl' := a64_sym_ite_flags (a64_sym_cond cond sfl) csfl (a64_sym_flags_of_imm4 nzcv) in
            Some (ASSR_Next next_pc sp_off vrf astk sfl' true)
        | _, _ => None
        end
  | A64_CondCompareImm sf is_sub cond rn imm5 nzcv =>
      if negb fl_def then None
      else
        match a64_val_read_expr_w sf rn vrf with
        | None => None
        | Some en =>
            let '(_, csfl) := a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5)) in
            let sfl' := a64_sym_ite_flags (a64_sym_cond cond sfl) csfl (a64_sym_flags_of_imm4 nzcv) in
            Some (ASSR_Next next_pc sp_off vrf astk sfl' true)
        end
  | A64_LdStImm is_load is_signed sf_dst sz mode rt rn imm =>
      if (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false)
      then None
      else
        match a64_val_read_sp rn vrf sp_off with
        | MSV_StackPtr base_off =>
            let wb_off := (base_off + imm)%Z in
            let wb_ok :=
              match mode with
              | AAM_SignedOffset => true
              | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z
              end in
            if negb wb_ok then None
            else
              let '(off, sp_chk) :=
                match mode with
                | AAM_SignedOffset => (wb_off, sp_off)
                | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                | AAM_PostIndex => (base_off, sp_off)
                end
              in
              if mc_slot_in_frame sp_chk off sz then
                let st_opt :=
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
                    let sv := a64_val_read rt vrf in
                    if a64_ldst_store_sym_ok sz sv then Some (vrf, mc_sym_stk_store off sz sv astk) else None
                in
                match st_opt with
                | None => None
                | Some (vrf1, astk1) =>
                    let '(sp_off2, vrf2, astk2) :=
                      match mode with
                      | AAM_SignedOffset => (sp_off, vrf1, astk1)
                      | AAM_PreIndex | AAM_PostIndex =>
                          if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
                          else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
                      end
                    in
                    Some (ASSR_Next next_pc sp_off2 vrf2 astk2 sfl fl_def)
                end
              else None
        | _ => None
        end
  | A64_LdStPair is_load sf mode rt1 rt2 rn imm =>
      if (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false)
      then None
      else
        match a64_val_read_sp rn vrf sp_off with
        | MSV_StackPtr base_off =>
            let wb_off := (base_off + imm)%Z in
            let wb_ok :=
              match mode with
              | AAM_SignedOffset => true
              | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z
              end in
            if negb wb_ok then None
            else
              let '(off, sp_chk) :=
                match mode with
                | AAM_SignedOffset => (wb_off, sp_off)
                | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                | AAM_PostIndex => (base_off, sp_off)
                end
              in
              let sz := if sf then MS_8 else MS_4 in
              let delta := mc_mem_bytes_Z sz in
              if mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz then
                let st_opt :=
                  if is_load then
                    match mc_sym_stk_load off sz false astk, mc_sym_stk_load (off + delta) sz false astk with
                    | Some sv1, Some sv2 => Some (a64_val_write rt2 sv2 (a64_val_write rt1 sv1 vrf), astk)
                    | _, _ => None
                    end
                  else
                    let sv1 := a64_val_read rt1 vrf in
                    let sv2 := a64_val_read rt2 vrf in
                    if a64_ldst_store_sym_ok sz sv1 && a64_ldst_store_sym_ok sz sv2 then
                      Some (vrf, mc_sym_stk_store (off + delta) sz sv2 (mc_sym_stk_store off sz sv1 astk))
                    else None
                in
                match st_opt with
                | None => None
                | Some (vrf1, astk1) =>
                    let '(sp_off2, vrf2, astk2) :=
                      match mode with
                      | AAM_SignedOffset => (sp_off, vrf1, astk1)
                      | AAM_PreIndex | AAM_PostIndex =>
                          if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
                          else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
                      end
                    in
                    Some (ASSR_Next next_pc sp_off2 vrf2 astk2 sfl fl_def)
                end
              else None
        | _ => None
        end
  | A64_B rel =>
      match add_rel_off pc rel with
      | None => None
      | Some tgt_pc => Some (ASSR_Next tgt_pc sp_off vrf astk sfl fl_def)
      end
  | A64_BCond cond rel =>
      if negb fl_def then None
      else
        match add_rel_off pc rel with
        | None => None
        | Some tgt_pc => Some (ASSR_Branch (a64_sym_cond cond sfl) tgt_pc next_pc true)
        end
  | A64_Cbz sf is_nz rt rel =>
      match a64_val_read_expr_w sf rt vrf with
      | None => None
      | Some rt_e =>
          match add_rel_off pc rel with
          | None => None
          | Some tgt_pc =>
              let cond_e :=
                CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false (a64_w sf) rt_e
                  (CE_BvConst (a64_w sf) 0%N) in
              Some (ASSR_Branch cond_e tgt_pc next_pc fl_def)
          end
      end
  | A64_Tbz is_nz rt bit rel =>
      match a64_val_read rt vrf with
      | MSV_Expr rt_e =>
          match add_rel_off pc rel with
          | None => None
          | Some tgt_pc =>
              let masked :=
                CE_BinOp CB_And 64%positive no_binop_flags rt_e
                  (CE_BvConst 64%positive (N.shiftl 1%N bit)) in
              let cond_e :=
                CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false 64%positive masked
                  (CE_BvConst 64%positive 0%N) in
              Some (ASSR_Branch cond_e tgt_pc next_pc fl_def)
          end
      | _ => None
      end
  | A64_Ret =>
      if a64_sym_epilogue_ok sp_off vrf then
        match a64_val_read 0%N vrf with
        | MSV_Expr e_ret => Some (ASSR_Ret (rv_trunc_ret_expr ret_w e_ret))
        | _ => None
        end
      else None
  end.

Lemma wf_a64_sym_logic_op : forall allowed w op l r,
  wf_sym_expr allowed w l ->
  wf_sym_expr allowed w r ->
  wf_sym_expr allowed w (a64_sym_logic_op w op l r).
Proof.
  intros allowed w op l r Hl Hr; destruct op; apply a64_wf_sym_binop; assumption.
Qed.

Local Lemma a64_sym_step_addsub_imm_wf :
  forall allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sf is_sub set_fl rd rn imm,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    dai_inst dec = A64_AddSubImm sf is_sub set_fl rd rn imm ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next _ sp_off' vrf' astk' sfl' fl_def' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        wf_a64_val_regs allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk' /\
        (fl_def' = true -> wf_sym_flags allowed sfl')
    | ASSR_Branch cond _ _ fl_def' =>
        wf_sym_expr allowed 1%positive cond /\ (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sf is_sub set_fl rd rn imm Hrng Hwf Hstk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
  destruct (sf && negb set_fl).
  - set (sv_opt :=
      match a64_val_read_sp rn vrf sp_off with
      | MSV_StackPtr base_off =>
          let off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z in
          if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
      | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
      | MSV_Expr e =>
          Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
      | MSV_Undef => None
      end) in *.
    destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hstep].
    destruct (a64_val_write_sp rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
      [| discriminate Hstep].
    inversion Hstep; subst res; clear Hstep.
    assert (Hsv : mc_sym_val_wf allowed sv).
    { subst sv_opt; destruct (a64_val_read_sp rn vrf sp_off) as [| e | r0 | base_off] eqn:Ern;
        try discriminate Esv.
      - inversion Esv.
        pose proof (wf_a64_val_read_sp allowed vrf sp_off rn _ Hrng Hwf Ern) as Hwfe.
        cbn [mc_sym_val_wf] in Hwfe |- *.
        exact (proj1 (wf_a64_sym_add_sub allowed 64%positive is_sub _ _ Hwfe (wf_sym_bv_z _ _ _))).
      - destruct (N.eqb imm 0%N); [inversion Esv; exact I | discriminate Esv].
      - cbv zeta in Esv.
        destruct (Z.leb (- mc_frame_cap) _ && Z.leb _ 0%Z) eqn:Eb; [| discriminate Esv].
        apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
        inversion Esv; cbn [mc_sym_val_wf]; lia. }
    destruct (a64_val_write_sp_wf allowed rd sv sp_off vrf astk _ _ _ Hrng Hsv Hwf Hstk Est)
      as (Hr & Hw & Hs).
    split; [exact Hr | split; [exact Hw | split; [exact Hs | exact Hfl]]].
  - destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub lhs (ce_bv_z (a64_w sf) (Z.of_N imm)))
      as [se sfl'] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z _ _ (Z.of_N imm))) as Hwe.
    rewrite Esas in Hwe; destruct Hwe as [Hse Hsfl].
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w; assumption |].
    split; [exact Hstk |].
    intro Hfs; destruct set_fl; [exact Hsfl | exact (Hfl Hfs)].
Qed.

Local Lemma a64_sym_step_ldst_wb_wf :
  forall allowed sp_off sp_chk wb_off rn mode vrf1 astk1,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end ->
    sp_chk =
      (match mode with
       | AAM_SignedOffset => sp_off
       | AAM_PreIndex => if N.eqb rn 31%N then wb_off else sp_off
       | AAM_PostIndex => sp_off
       end) ->
    wf_a64_val_regs allowed vrf1 ->
    mc_sym_stack_wf allowed (Z.min sp_off sp_chk) astk1 ->
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
  intros allowed sp_off sp_chk wb_off rn mode vrf1 astk1 Hrng Hwb_rng Hspchk Hwf1 Hstk1.
  subst sp_chk.
  destruct mode.
  - replace (Z.min sp_off sp_off) with sp_off in Hstk1 by lia.
    split; [exact Hrng | split; [exact Hwf1 | exact Hstk1]].
  - destruct (N.eqb rn 31%N).
    + split; [exact Hwb_rng |].
      split; [exact Hwf1 |].
      eapply mc_sym_stk_prune_wf; [lia | exact Hstk1].
    + replace (Z.min sp_off sp_off) with sp_off in Hstk1 by lia.
      split; [exact Hrng |].
      split; [apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1].
  - destruct (N.eqb rn 31%N).
    + split; [exact Hwb_rng |].
      split; [exact Hwf1 |].
      eapply mc_sym_stk_prune_wf; [lia | exact Hstk1].
    + replace (Z.min sp_off sp_off) with sp_off in Hstk1 by lia.
      split; [exact Hrng |].
      split; [apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1].
Qed.

Local Lemma a64_sym_step_ldst_imm_wf :
  forall allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         is_load is_signed sf_dst sz mode rt rn imm,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    dai_inst dec = A64_LdStImm is_load is_signed sf_dst sz mode rt rn imm ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next _ sp_off' vrf' astk' sfl' fl_def' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        wf_a64_val_regs allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk' /\
        (fl_def' = true -> wf_sym_flags allowed sfl')
    | ASSR_Branch cond _ _ fl_def' =>
        wf_sym_expr allowed 1%positive cond /\ (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         is_load is_signed sf_dst sz mode rt rn imm Hrng Hwf Hstk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
  destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hstep |].
  destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off]; try discriminate Hstep.
  set (wb_off := (base_off + imm)%Z) in *.
  set (wb_ok :=
    match mode with
    | AAM_SignedOffset => true
    | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z
    end) in *.
  destruct wb_ok eqn:Ewb; cbn [negb] in Hstep; [| discriminate Hstep].
  assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
  { destruct mode; [exact I | |];
      apply andb_true_iff in Ewb as [E1 E2];
      apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
  set (pair_off :=
    match mode with
    | AAM_SignedOffset => (wb_off, sp_off)
    | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
    | AAM_PostIndex => (base_off, sp_off)
    end).
  destruct pair_off as [off sp_chk] eqn:Epo; cbv zeta in Hstep.
  assert (Hpo_eq :
    match mode with
    | AAM_SignedOffset => (wb_off, sp_off)
    | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
    | AAM_PostIndex => (base_off, sp_off)
    end = (off, sp_chk)) by exact Epo.
  rewrite Hpo_eq in Hstep; cbv iota in Hstep.
  destruct (mc_slot_in_frame sp_chk off sz) eqn:Eslot; [| discriminate Hstep].
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
      if a64_ldst_store_sym_ok sz (a64_val_read rt vrf)
      then Some (vrf, mc_sym_stk_store off sz (a64_val_read rt vrf) astk)
      else None) in *.
  destruct st_opt as [[vrf1 astk1] |] eqn:Est;
    [try (rewrite Est in Hstep; cbv iota in Hstep) | try rewrite Est in Hstep; discriminate Hstep].
  assert (Hstep1 : wf_a64_val_regs allowed vrf1 /\ mc_sym_stack_wf allowed sp_min astk1).
  { destruct is_load; unfold st_opt in Est.
    - destruct (mc_sym_stk_load off sz is_signed astk) as [sv0 |] eqn:Esl0; [| discriminate Est].
      destruct (a64_ldst_sym_load is_signed sf_dst sv0) as [sv1 |] eqn:Esl1; [| discriminate Est].
      inversion Est; subst vrf1 astk1.
      split; [| exact Hstk_min].
      apply wf_a64_val_write;
        [exact Hwf | exact (a64_ldst_sym_load_wf _ _ _ _ _ (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl0) Esl1)].
    - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt vrf)); [| discriminate Est].
      inversion Est; subst vrf1 astk1.
      split; [exact Hwf | exact (mc_sym_stk_store_wf _ _ _ _ _ _ Hslot_min (Hwf rt) Hstk_min)]. }
  destruct Hstep1 as [Hwf1 Hstk1].
  assert (Hspchk : sp_chk =
    match mode with
    | AAM_SignedOffset => sp_off
    | AAM_PreIndex => if N.eqb rn 31%N then wb_off else sp_off
    | AAM_PostIndex => sp_off
    end) by (destruct mode; inversion Epo; reflexivity).
  pose proof (a64_sym_step_ldst_wb_wf allowed sp_off sp_chk wb_off rn mode vrf1 astk1
    Hrng Hwb_rng Hspchk Hwf1 Hstk1) as Hwb2.
  destruct
    (match mode with
     | AAM_SignedOffset => (sp_off, vrf1, astk1)
     | AAM_PreIndex | AAM_PostIndex =>
         if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
         else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
     end) as [[sp_off2 vrf2] astk2] eqn:Ewbs.
  try rewrite Ewbs in Hwb2; cbv iota in Hwb2.
  inversion Hstep; subst; clear Hstep.
  destruct Hwb2 as (Hr2 & Hw2 & Hs2).
  split; [exact Hr2 | split; [exact Hw2 | split; [exact Hs2 | exact Hfl]]].
Qed.

Local Lemma a64_sym_step_ldst_pair_wf :
  forall allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         is_load sf mode rt1 rt2 rn imm,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    dai_inst dec = A64_LdStPair is_load sf mode rt1 rt2 rn imm ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next _ sp_off' vrf' astk' sfl' fl_def' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        wf_a64_val_regs allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk' /\
        (fl_def' = true -> wf_sym_flags allowed sfl')
    | ASSR_Branch cond _ _ fl_def' =>
        wf_sym_expr allowed 1%positive cond /\ (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         is_load sf mode rt1 rt2 rn imm Hrng Hwf Hstk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
  destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hstep |].
  destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off]; try discriminate Hstep.
  set (wb_off := (base_off + imm)%Z) in *.
  set (wb_ok :=
    match mode with
    | AAM_SignedOffset => true
    | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z
    end) in *.
  destruct wb_ok eqn:Ewb; cbn [negb] in Hstep; [| discriminate Hstep].
  assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
  { destruct mode; [exact I | |];
      apply andb_true_iff in Ewb as [E1 E2];
      apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
  set (pair_off :=
    match mode with
    | AAM_SignedOffset => (wb_off, sp_off)
    | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
    | AAM_PostIndex => (base_off, sp_off)
    end).
  destruct pair_off as [off sp_chk] eqn:Epo; cbv zeta in Hstep.
  assert (Hpo_eq :
    match mode with
    | AAM_SignedOffset => (wb_off, sp_off)
    | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
    | AAM_PostIndex => (base_off, sp_off)
    end = (off, sp_chk)) by exact Epo.
  rewrite Hpo_eq in Hstep; cbv iota in Hstep.
  set (sz := if sf then MS_8 else MS_4) in *.
  set (delta := mc_mem_bytes_Z sz) in *.
  destruct (mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz)
    eqn:Eslots; [| discriminate Hstep].
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
      if a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) &&
         a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf)
      then Some (vrf, mc_sym_stk_store (off + delta) sz (a64_val_read rt2 vrf)
                        (mc_sym_stk_store off sz (a64_val_read rt1 vrf) astk))
      else None) in *.
  destruct st_opt as [[vrf1 astk1] |] eqn:Est;
    [try (rewrite Est in Hstep; cbv iota in Hstep) | try rewrite Est in Hstep; discriminate Hstep].
  assert (Hstep1 : wf_a64_val_regs allowed vrf1 /\ mc_sym_stack_wf allowed sp_min astk1).
  { destruct is_load; unfold st_opt in Est.
    - destruct (mc_sym_stk_load off sz false astk) as [sv1 |] eqn:Esl_1; [| discriminate Est].
      destruct (mc_sym_stk_load (off + delta) sz false astk) as [sv2 |] eqn:Esl_2; [| discriminate Est].
      inversion Est; subst vrf1 astk1.
      split; [| exact Hstk_min].
      apply wf_a64_val_write;
        [apply wf_a64_val_write; [exact Hwf | exact (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl_1)]
        | exact (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl_2)].
    - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) &&
                a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf)); [| discriminate Est].
      inversion Est; subst vrf1 astk1.
      split; [exact Hwf |].
      apply mc_sym_stk_store_wf; [exact Hslot2_min | exact (Hwf rt2) |].
      apply mc_sym_stk_store_wf; [exact Hslot1_min | exact (Hwf rt1) | exact Hstk_min]. }
  destruct Hstep1 as [Hwf1 Hstk1].
  assert (Hspchk : sp_chk =
    match mode with
    | AAM_SignedOffset => sp_off
    | AAM_PreIndex => if N.eqb rn 31%N then wb_off else sp_off
    | AAM_PostIndex => sp_off
    end) by (destruct mode; inversion Epo; reflexivity).
  pose proof (a64_sym_step_ldst_wb_wf allowed sp_off sp_chk wb_off rn mode vrf1 astk1
    Hrng Hwb_rng Hspchk Hwf1 Hstk1) as Hwb2.
  destruct
    (match mode with
     | AAM_SignedOffset => (sp_off, vrf1, astk1)
     | AAM_PreIndex | AAM_PostIndex =>
         if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
         else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
     end) as [[sp_off2 vrf2] astk2] eqn:Ewbs.
  try rewrite Ewbs in Hwb2; cbv iota in Hwb2.
  inversion Hstep; subst; clear Hstep.
  destruct Hwb2 as (Hr2 & Hw2 & Hs2).
  split; [exact Hr2 | split; [exact Hw2 | split; [exact Hs2 | exact Hfl]]].
Qed.

Local Lemma a64_sym_step_logic_shift_wf :
  forall allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sf op inv_rm set_fl rd rn rm sh amt,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    dai_inst dec = A64_LogicalShift sf op inv_rm set_fl rd rn rm sh amt ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next _ sp_off' vrf' astk' sfl' fl_def' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        wf_a64_val_regs allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk' /\
        (fl_def' = true -> wf_sym_flags allowed sfl')
    | ASSR_Branch cond _ _ fl_def' =>
        wf_sym_expr allowed 1%positive cond /\ (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sf op inv_rm set_fl rd rn rm sh amt Hrng Hwf Hstk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
  destruct (a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt).
  - destruct (a64_val_read rm vrf) eqn:Erm; try discriminate Hstep;
      match goal with |- _ =>
        inversion Hstep; subst; clear Hstep;
        split; [exact Hrng |];
        split;
          [apply wf_a64_val_write;
            [exact Hwf | pose proof (Hwf rm) as Hm; rewrite Erm in Hm; exact Hm]
          |];
        split; [exact Hstk | exact Hfl]
      end.
  - destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_shift allowed (a64_w sf) rm_e sh amt
      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)) as Hsh.
    assert (Hrhs :
      wf_sym_expr allowed (a64_w sf)
        (if inv_rm then a64_sym_not (a64_w sf) (a64_sym_shift (a64_w sf) rm_e sh amt)
         else a64_sym_shift (a64_w sf) rm_e sh amt)).
    { destruct inv_rm;
        [unfold a64_sym_not; apply a64_wf_sym_binop; [exact Hsh | apply wf_sym_bv_const] | exact Hsh]. }
    pose proof (wf_a64_sym_logic_op allowed (a64_w sf) op _ _
      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) Hrhs) as Hres.
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w; assumption |].
    split; [exact Hstk | intro Hfs; destruct set_fl; [apply wf_a64_sym_logic_flags; exact Hres | exact (Hfl Hfs)]].
Qed.

Local Lemma a64_sym_step_move_wide_wf :
  forall allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sf kind rd imm16 shift,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    dai_inst dec = A64_MoveWide sf kind rd imm16 shift ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next _ sp_off' vrf' astk' sfl' fl_def' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        wf_a64_val_regs allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk' /\
        (fl_def' = true -> wf_sym_flags allowed sfl')
    | ASSR_Branch cond _ _ fl_def' =>
        wf_sym_expr allowed 1%positive cond /\ (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sf kind rd imm16 shift Hrng Hwf Hstk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
  destruct kind.
  - inversion Hstep; subst.
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; apply wf_sym_bv_const] |].
    split; [exact Hstk | exact Hfl].
  - inversion Hstep; subst.
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w; [exact Hwf | apply wf_sym_bv_const] |].
    split; [exact Hstk | exact Hfl].
  - destruct (a64_val_read_expr_w sf rd vrf) as [cur |] eqn:Erd; [| discriminate Hstep].
    inversion Hstep; subst.
    split; [exact Hrng |].
    split.
    + apply wf_a64_val_write_w; [exact Hwf |].
      apply a64_wf_sym_binop; [| apply wf_sym_bv_const].
      apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erd) |].
      unfold a64_sym_not; apply a64_wf_sym_binop; apply wf_sym_bv_const.
    + split; [exact Hstk | exact Hfl].
Qed.

Local Lemma a64_sym_step_bitfield_wf :
  forall allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sf kind rd rn immr imms,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    dai_inst dec = A64_Bitfield sf kind rd rn immr imms ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next _ sp_off' vrf' astk' sfl' fl_def' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        wf_a64_val_regs allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk' /\
        (fl_def' = true -> wf_sym_flags allowed sfl')
    | ASSR_Branch cond _ _ fl_def' =>
        wf_sym_expr allowed 1%positive cond /\ (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sf kind rd rn immr imms Hrng Hwf Hstk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
  set (dst_opt :=
    match kind with
    | ABF_Bfm => a64_val_read_expr_w sf rd vrf
    | _ => Some (CE_BvConst (a64_w sf) 0%N)
    end) in *.
  destruct (a64_val_read_expr_w sf rn vrf) as [src_e |] eqn:Ern; [| discriminate Hstep].
  destruct dst_opt as [dst_e |] eqn:Edst; [| discriminate Hstep].
  inversion Hstep; subst; clear Hstep.
  assert (Hdst : wf_sym_expr allowed (a64_w sf) dst_e).
  { unfold dst_opt in Edst; destruct kind;
      [inversion Edst; subst; apply wf_sym_bv_const
      | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Edst)
      | inversion Edst; subst; apply wf_sym_bv_const]. }
  split; [exact Hrng |].
  split; [apply wf_a64_val_write_w;
    [exact Hwf | apply wf_a64_sym_bitfield; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact Hdst]] |].
  split; [exact Hstk | exact Hfl].
Qed.

Local Lemma a64_sym_step_mul_widening_wf :
  forall allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sgn is_sub rd rn rm ra,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    dai_inst dec = A64_MulWidening sgn is_sub rd rn rm ra ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next _ sp_off' vrf' astk' sfl' fl_def' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        wf_a64_val_regs allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk' /\
        (fl_def' = true -> wf_sym_flags allowed sfl')
    | ASSR_Branch cond _ _ fl_def' =>
        wf_sym_expr allowed 1%positive cond /\ (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk sfl fl_def ret_w res
         sgn is_sub rd rn rm ra Hrng Hwf Hstk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
  destruct (a64_val_read_expr_w false rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
  destruct (a64_val_read_expr_w false rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
  destruct (a64_val_read ra vrf) as [| ea | |] eqn:Era; try discriminate Hstep.
  inversion Hstep; subst; clear Hstep.
  pose proof (Hwf ra) as Hra; rewrite Era in Hra; cbn [mc_sym_val_wf] in Hra.
  split; [exact Hrng |].
  split.
  - apply wf_a64_val_write; [exact Hwf | cbn [mc_sym_val_wf]].
    destruct is_sub;
      (apply a64_wf_sym_binop;
        [exact Hra
        | apply a64_wf_sym_binop; destruct sgn;
          (apply wf_sym_cast;
            [reflexivity
            | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) ||
              exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)])]).
  - split; [exact Hstk | exact Hfl].
Qed.

Lemma a64_sym_step_one_wf :
  forall allowed dec pc sp_off vrf astk sfl fl_def ret_w res,
    rv_supported_arg_width ret_w = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next _ sp_off' vrf' astk' sfl' fl_def' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        wf_a64_val_regs allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk' /\
        (fl_def' = true -> wf_sym_flags allowed sfl')
    | ASSR_Branch cond _ _ fl_def' => wf_sym_expr allowed 1%positive cond /\ (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk sfl fl_def ret_w res Hrw Hrng Hwf Hstk Hfl Hstep.
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
      | rel | cond rel | sf is_nz rt rel | is_nz rt bit rel | ] eqn:Ed.
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv zeta iota in Hstep.
    inversion Hstep; subst.
    split; [exact Hrng | split; [exact Hwf | split; [exact Hstk | exact Hfl]]].
  - exact (a64_sym_step_addsub_imm_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res
      sf is_sub set_fl rd rn imm Hrng Hwf Hstk Hfl Ed Hstep).
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
      (wf_a64_sym_shift _ _ _ sh amt (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm))) as Hwe.
    rewrite Esas in Hwe; destruct Hwe as [Hse Hsfl].
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w; assumption |].
    split; [exact Hstk | intro Hfs; destruct set_fl; [exact Hsfl | exact (Hfl Hfs)]].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read rm vrf) as [| rm64 | |] eqn:Erm; try discriminate Hstep.
    destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (Hwf rm) as Hm64; rewrite Erm in Hm64; cbn [mc_sym_val_wf] in Hm64.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
      (wf_a64_sym_extend _ _ _ ext amt (a64_w_32_64 sf) Hm64)) as Hwe.
    rewrite Esas in Hwe; destruct Hwe as [Hse Hsfl].
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w; assumption |].
    split; [exact Hstk | intro Hfs; destruct set_fl; [exact Hsfl | exact (Hfl Hfs)]].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct (negb set_fl && N.eqb rd 31%N); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_logic_op allowed (a64_w sf) op _ _
      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z _ _ (Z.of_N mask))) as Hres.
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w; assumption |].
    split; [exact Hstk | intro Hfs; destruct set_fl; [apply wf_a64_sym_logic_flags; assumption | exact (Hfl Hfs)]].
  - exact (a64_sym_step_logic_shift_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res
      sf op inv_rm set_fl rd rn rm sh amt Hrng Hwf Hstk Hfl Ed Hstep).
  - exact (a64_sym_step_move_wide_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res
      sf kind rd imm16 shift Hrng Hwf Hstk Hfl Ed Hstep).
  - exact (a64_sym_step_bitfield_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res
      sf kind rd rn immr imms Hrng Hwf Hstk Hfl Ed Hstep).
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct (a64_val_read_expr_w sf rn vrf) as [hi_e |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [lo_e |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    split; [exact Hrng |].
    split.
    + apply wf_a64_val_write_w; [exact Hwf |].
      unfold a64_sym_extr; destruct (N.eqb (N.modulo lsb (N.pos (a64_w sf))) 0%N).
      * exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm).
      * apply a64_wf_sym_binop; apply a64_wf_sym_binop;
          first [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
                | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)
                | apply wf_sym_bv_const].
    + split; [exact Hstk | exact Hfl].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf ra vrf) as [ea |] eqn:Era; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    split; [exact Hrng |].
    split.
    + apply wf_a64_val_write_w; [exact Hwf |].
      destruct is_sub; apply a64_wf_sym_binop; try apply a64_wf_sym_binop;
        exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Era) ||
        exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) ||
        exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm).
    + split; [exact Hstk | exact Hfl].
  - exact (a64_sym_step_mul_widening_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res
      sgn is_sub rd rn rm ra Hrng Hwf Hstk Hfl Ed Hstep).
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w;
      [exact Hwf
      | apply wf_a64_sym_dp2;
        [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
        | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)]] |].
    split; [exact Hstk | exact Hfl].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    split; [exact Hrng |].
    split; [apply wf_a64_val_write_w;
      [exact Hwf
      | apply wf_a64_sym_csel;
        [exact (Hfl eq_refl)
        | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
        | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)]] |].
    split; [exact Hstk | exact Hfl].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub en em) as [csres csfl] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)) as [_ Hcsfl].
    rewrite Esas in Hcsfl.
    split; [exact Hrng | split; [exact Hwf | split; [exact Hstk |]]].
    intro; apply wf_a64_sym_ite_flags;
      [exact (wf_a64_sym_cond allowed cond sfl (Hfl eq_refl)) | exact Hcsfl | apply wf_a64_sym_flags_imm4].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv iota in Hstep.
    destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5))) as [csres csfl] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z _ _ (Z.of_N imm5))) as [_ Hcsfl].
    rewrite Esas in Hcsfl.
    split; [exact Hrng | split; [exact Hwf | split; [exact Hstk |]]].
    intro; apply wf_a64_sym_ite_flags;
      [exact (wf_a64_sym_cond allowed cond sfl (Hfl eq_refl)) | exact Hcsfl | apply wf_a64_sym_flags_imm4].
  - exact (a64_sym_step_ldst_imm_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res
      is_load is_signed sf_dst sz mode rt rn imm Hrng Hwf Hstk Hfl Ed Hstep).
  - exact (a64_sym_step_ldst_pair_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res
      is_load sf mode rt1 rt2 rn imm Hrng Hwf Hstk Hfl Ed Hstep).
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv zeta iota in Hstep.
    destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst.
    split; [exact Hrng | split; [exact Hwf | split; [exact Hstk | exact Hfl]]].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv zeta iota in Hstep.
    destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst.
    split; [exact (wf_a64_sym_cond allowed cond sfl (Hfl eq_refl)) | intro Hf; exact Hf].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv zeta iota in Hstep.
    destruct (a64_val_read_expr_w sf rt vrf) as [rt_e |] eqn:Ert; [| discriminate Hstep].
    destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst.
    split; [apply wf_sym_icmp; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ert) | apply wf_sym_bv_const] |].
    intro Hf; exact Hf.
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv zeta iota in Hstep.
    destruct (a64_val_read rt vrf) as [| rt_e | |] eqn:Ert; try discriminate Hstep.
    destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst.
    pose proof (Hwf rt) as Hrt; rewrite Ert in Hrt; cbn [mc_sym_val_wf] in Hrt.
    split; [apply wf_sym_icmp; [apply a64_wf_sym_binop; [exact Hrt | apply wf_sym_bv_const] | apply wf_sym_bv_const] |].
    intro Hf; exact Hf.
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv zeta iota in Hstep.
    destruct (a64_sym_epilogue_ok sp_off vrf); [| discriminate Hstep].
    destruct (a64_val_read 0%N vrf) as [| e_ret | |] eqn:Er0; try discriminate Hstep.
    inversion Hstep; subst.
    pose proof (Hwf 0%N) as Ha0; rewrite Er0 in Ha0; cbn [mc_sym_val_wf] in Ha0.
    unfold rv_trunc_ret_expr; destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
    + apply Pos.eqb_eq in Ew64; subst ret_w; exact Ha0.
    + apply wf_sym_cast; [exact (rv_supported_arg_width_lt64 _ Hrw Ew64) | exact Ha0].
Qed.

Local Lemma a64_tbz_bit_test_eq :
  forall (v : @Integers.bit_int 64%positive) (bit : N),
    (bit < 64)%N ->
    negb (@Integers.eq 64%positive
      (@Integers.and 64%positive v (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))
      (@Integers.zero 64%positive)) =
    Z.testbit (@Integers.unsigned 64%positive v) (Z.of_N bit).
Proof.
  intros v bit Hbit.
  pose proof (integers_eq_zero_iff 64%positive
    (@Integers.and 64%positive v (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) as Hiz.
  destruct (@Integers.eq 64%positive _ _) eqn:Ez,
           (Z.testbit (@Integers.unsigned 64%positive v) (Z.of_N bit)) eqn:Etb;
    try reflexivity.
  - exfalso; pose proof (proj1 Hiz eq_refl) as Hz.
    assert (Hb :
      Z.testbit (@Integers.unsigned 64%positive
        (@Integers.and 64%positive v (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))))
        (Z.of_N bit) = false)
      by (rewrite Hz; apply Z.testbit_0_l).
    change (Z.testbit (@Integers.unsigned 64%positive
      (@Integers.and 64%positive v (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))))
      (Z.of_N bit))
      with (@Integers.testbit 64%positive
        (@Integers.and 64%positive v (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))
        (Z.of_N bit)) in Hb.
    rewrite Integers.bits_and, (@Integers.testbit_repr 64%positive _ (Z.of_N bit)) in Hb
      by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
    rewrite N.shiftl_1_l, N2Z.inj_pow, Z.pow2_bits_true in Hb by lia.
    unfold Integers.testbit in Hb; rewrite Etb in Hb; discriminate Hb.
  - exfalso.
    assert (Hnz :
      @Integers.and 64%positive v (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))) =
      @Integers.zero 64%positive).
    { apply Integers.same_bits_eq; intros i Hi; rewrite Integers.bits_zero, Integers.bits_and by exact Hi.
      rewrite (@Integers.testbit_repr 64%positive _ i Hi).
      change (@Integers.zwordsize 64%positive) with 64%Z in Hi.
      rewrite N.shiftl_1_l, N2Z.inj_pow.
      destruct (Z.eq_dec i (Z.of_N bit)) as [-> | Hne].
      - unfold Integers.testbit; rewrite Etb; reflexivity.
      - rewrite Z.pow2_bits_false by (try lia; exact Hne); rewrite andb_false_r; reflexivity. }
    pose proof (proj2 Hiz ltac:(rewrite Hnz, (@Integers.unsigned_zero 64%positive); reflexivity)) as Htru.
    discriminate Htru.
Qed.

Local Lemma a64_sym_step_addsub_imm_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn imm,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_AddSubImm sf is_sub set_fl rd rn imm ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn imm
         Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct (sf && negb set_fl) eqn:E64n.
  - set (sv_opt :=
      match a64_val_read_sp rn vrf sp_off with
      | MSV_StackPtr base_off =>
          let off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z in
          if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
      | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
      | MSV_Expr e =>
          Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
      | MSV_Undef => None
      end) in *.
    destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hstep].
    destruct (a64_val_write_sp rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
      [| discriminate Hstep].
    inversion Hstep; subst res; clear Hstep.
    assert (Hsv_ag :
      mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv
        (if is_sub
         then @Integers.sub 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive (Z.of_N imm))
         else @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive (Z.of_N imm)))).
    { pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag eq_refl) as Hrn.
      subst sv_opt; destruct (a64_val_read_sp rn vrf sp_off) as [| e | r0 | base_off] eqn:Ern;
        try discriminate Esv.
      - inversion Esv; subst sv; clear Esv; cbn [mc_sym_val_agrees] in Hrn |- *.
        pose proof (eval_a64_sym_add_sub_sound penv foracle 64%positive is_sub _ _ _ _ Hrn
          (eval_ce_bv_z _ _ 64%positive (Z.of_N imm))) as [Hres _]; exact Hres.
      - destruct (N.eqb imm 0%N) eqn:Ez; [| discriminate Esv].
        apply N.eqb_eq in Ez; subst imm; inversion Esv; subst sv; clear Esv.
        cbn [mc_sym_val_agrees] in Hrn |- *; destruct is_sub.
        + unfold Integers.sub; change (Z.of_N 0%N) with 0%Z.
          rewrite (@Integers.unsigned_repr 64%positive 0%Z) by (compute; split; discriminate).
          rewrite Z.sub_0_r, Integers.repr_unsigned; exact Hrn.
        + rewrite Hrn, mc_add_ptr_zero; reflexivity.
      - cbv zeta in Esv; destruct (Z.leb (- mc_frame_cap) _ && Z.leb _ 0%Z) eqn:Erng; [| discriminate Esv].
        apply andb_true_iff in Erng as [Er1 Er2]; apply Z.leb_le in Er1; apply Z.leb_le in Er2.
        inversion Esv; subst sv; clear Esv.
        cbn [mc_sym_val_agrees] in Hrn |- *; destruct Hrn as [_ Hptr]; split; [lia |].
        rewrite Hptr; destruct is_sub; [apply mc_sub_ptr_off | apply mc_add_ptr_off]. }
    pose proof (a64_val_write_sp_bounds _ _ _ _ _ _ _ _ Hrng Est) as Hrng'.
    pose proof (a64_val_write_sp_sound penv foracle rf0 sp0 rd sv _ sp_off vrf astk rf sp mstk
      sp_off' vrf' astk' Hsp Hag Hastk Hsv_ag Est) as Hwr.
    destruct (a64_write_reg_sp rd _ rf sp) as [rf' sp'] eqn:Ewr.
    destruct Hwr as (Hsp' & Hag' & Hastk').
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng' | split; [exact Hsp' | split; [exact Hag' | split; [exact Hastk' | exact Hfl]]]].
  - destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub lhs (ce_bv_z (a64_w sf) (Z.of_N imm))) as [se sfl'] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm)))
      as [vr fl'] eqn:Eeas.
    inversion Hstep; subst; clear Hstep.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
      (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
      (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm))) as [Hres Hfl'].
    rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split; [apply a64_val_regs_agrees_write_w; assumption |].
    split; [exact Hastk | intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]].
Qed.

Local Lemma a64_sym_step_logic_shift_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf op inv_rm set_fl rd rn rm sh amt,
    a64_inst_valid dec = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_LogicalShift sf op inv_rm set_fl rd rn rm sh amt ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf op inv_rm set_fl rd rn rm sh amt
         Hdec_val Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct (a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt) eqn:Emov.
  - unfold a64_is_orr_mov64 in Emov; rewrite !andb_true_iff in Emov.
    destruct Emov as ((((((Esf & Hninv) & Hnsfl) & Hrn) & Hamt) & Hop) & Hsh).
    apply negb_true_iff in Hninv; apply negb_true_iff in Hnsfl.
    apply N.eqb_eq in Hrn; apply N.eqb_eq in Hamt.
    subst sf inv_rm set_fl rn amt; destruct op; try discriminate Hop; destruct sh; try discriminate Hsh.
    pose proof (Hag rm) as Hrm.
    destruct (a64_val_read rm vrf) eqn:Erm; try discriminate Hstep;
      match goal with |- _ =>
        inversion Hstep; subst; clear Hstep;
        cbn [a64_w a64_read_w a64_eval_logic_op a64_write_w];
        replace (a64_read_reg 31%N rf) with (@Integers.zero 64%positive) by reflexivity;
        rewrite a64_orr_xzr_lsl0;
        eexists _, _, _, _;
        split; [reflexivity | split; [exact Hrng | split; [reflexivity |]]];
        split; [apply a64_val_regs_agrees_write; assumption | split; [exact Hastk | exact Hfl]]
      end.
  - destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.ltb_lt in Hdec_val.
    pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf)
      ltac:(destruct sf; exact Hdec_val) (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hsh.
    assert (Hrhs :
      eval_closed_cert_expr penv foracle
        (if inv_rm then a64_sym_not (a64_w sf) (a64_sym_shift (a64_w sf) rm_e sh amt)
         else a64_sym_shift (a64_w sf) rm_e sh amt) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (if inv_rm then @Integers.not (a64_w sf) (a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt)
         else a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt))))
      by (destruct inv_rm; [exact (eval_ce_not _ _ _ _ _ Hsh) | exact Hsh]).
    assert (Hres :
      eval_closed_cert_expr penv foracle
        (a64_sym_logic_op (a64_w sf) op lhs
          (if inv_rm then a64_sym_not (a64_w sf) (a64_sym_shift (a64_w sf) rm_e sh amt)
           else a64_sym_shift (a64_w sf) rm_e sh amt)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf)
          (if inv_rm then @Integers.not (a64_w sf) (a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt)
           else a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt))))).
    { unfold a64_sym_logic_op, a64_eval_logic_op.
      rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), Hrhs.
      cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split; [apply a64_val_regs_agrees_write_w; assumption |].
    split; [exact Hastk | intro Hs; destruct set_fl;
      [exact (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) | exact (Hfl Hs)]].
Qed.

Local Lemma a64_sym_step_move_wide_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf kind rd imm16 shift,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_MoveWide sf kind rd imm16 shift ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf kind rd imm16 shift
         Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct kind.
  - inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split; [apply a64_val_regs_agrees_write_w; [exact Hag | exact (eval_ce_not _ _ _ _ _ (eval_ce_bv_z _ _ _ _))] |].
    split; [exact Hastk | exact Hfl].
  - inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split; [apply a64_val_regs_agrees_write_w; [exact Hag | exact (eval_ce_bv_z _ _ _ _)] |].
    split; [exact Hastk | exact Hfl].
  - destruct (a64_val_read_expr_w sf rd vrf) as [cur |] eqn:Erd; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split; [| split; [exact Hastk | exact Hfl]].
    apply a64_val_regs_agrees_write_w; [exact Hag |].
    change (Z.pos (Pos.shiftl 65535 shift)) with (Z.of_N (N.shiftl 65535%N shift)).
    assert (Hand :
      eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And (a64_w sf) no_binop_flags cur
          (a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl 65535%N shift))))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (@Integers.and (a64_w sf) (a64_read_w sf rd rf)
          (@Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))))).
    { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erd),
              (eval_ce_not _ _ _ _ _ (eval_ce_bv_z _ _ _ _)).
      cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
    rewrite eval_ce_binop, Hand, eval_ce_bv_z.
    cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
Qed.

Local Lemma a64_sym_step_bitfield_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf kind rd rn immr imms,
    a64_inst_valid dec = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_Bitfield sf kind rd rn immr imms ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf kind rd rn immr imms
         Hdec_val Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  set (dst_opt :=
    match kind with
    | ABF_Bfm => a64_val_read_expr_w sf rd vrf
    | _ => Some (CE_BvConst (a64_w sf) 0%N)
    end) in *.
  destruct (a64_val_read_expr_w sf rn vrf) as [src_e |] eqn:Ern; [| discriminate Hstep].
  destruct dst_opt as [dst_e |] eqn:Edst; [| discriminate Hstep].
  inversion Hstep; subst; clear Hstep.
  unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val.
  apply andb_true_iff in Hdec_val as [Hr1 Hs1]; apply N.ltb_lt in Hr1; apply N.ltb_lt in Hs1.
  assert (Hres :
    eval_closed_cert_expr penv foracle (a64_sym_bitfield (a64_w sf) kind src_e dst_e immr imms) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
      (a64_eval_bitfield (a64_w sf) kind (a64_read_w sf rn rf) (a64_read_w sf rd rf) immr imms)))).
  { destruct kind.
    - subst dst_opt; inversion Edst; subst dst_e.
      epose proof (eval_a64_sym_bitfield_sound penv foracle sf ABF_Sbfm src_e (CE_BvConst (a64_w sf) 0%N)
        _ (@Integers.zero (a64_w sf)) immr imms Hr1 Hs1
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
        ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hbf.
      cbn [a64_sym_bitfield a64_eval_bitfield] in Hbf |- *; destruct (N.leb immr imms); exact Hbf.
    - subst dst_opt; exact (eval_a64_sym_bitfield_sound _ _ sf ABF_Bfm _ _ _ _ _ _ Hr1 Hs1
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Edst)).
    - subst dst_opt; inversion Edst; subst dst_e.
      epose proof (eval_a64_sym_bitfield_sound penv foracle sf ABF_Ubfm src_e (CE_BvConst (a64_w sf) 0%N)
        _ (@Integers.zero (a64_w sf)) immr imms Hr1 Hs1
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
        ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hbf.
      cbn [a64_sym_bitfield a64_eval_bitfield] in Hbf |- *; destruct (N.leb immr imms); exact Hbf. }
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng | split; [reflexivity |]].
  split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | exact Hfl]].
Qed.

Local Lemma a64_sym_step_mul_addsub_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub rd rn rm ra,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_MulAddSub sf is_sub rd rn rm ra ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub rd rn rm ra
         Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
  destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
  destruct (a64_val_read_expr_w sf ra vrf) as [ea |] eqn:Era; [| discriminate Hstep].
  inversion Hstep; subst; clear Hstep.
  assert (Hmul :
    eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul (a64_w sf) no_binop_flags en em) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
      (@Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf))))).
  { rewrite eval_ce_binop,
            (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern),
            (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm).
    cbn [eou_bind]; destruct sf; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
      cbn - [Integers.mul a64_read_w]; reflexivity. }
  assert (Hres :
    eval_closed_cert_expr penv foracle
      (CE_BinOp (if is_sub then CB_Sub else CB_Add) (a64_w sf) no_binop_flags ea
        (CE_BinOp CB_Mul (a64_w sf) no_binop_flags en em)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
      (let p := @Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
       if is_sub then @Integers.sub (a64_w sf) (a64_read_w sf ra rf) p
       else @Integers.add (a64_w sf) (a64_read_w sf ra rf) p)))).
  { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Era), Hmul.
    cbn [eou_bind]; destruct sf, is_sub; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
      cbn - [Integers.mul Integers.add Integers.sub a64_read_w]; reflexivity. }
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng | split; [reflexivity |]].
  split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | exact Hfl]].
Qed.

Local Lemma a64_sym_step_mul_widening_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sgn is_sub rd rn rm ra,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_MulWidening sgn is_sub rd rn rm ra ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sgn is_sub rd rn rm ra
         Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct (a64_val_read_expr_w false rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
  destruct (a64_val_read_expr_w false rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
  destruct (a64_val_read ra vrf) as [| ea | |] eqn:Era; try discriminate Hstep.
  inversion Hstep; subst; clear Hstep.
  pose proof (Hag ra) as Hra; rewrite Era in Hra; cbn [mc_sym_val_agrees] in Hra.
  set (n64 :=
    @Integers.repr 64%positive
      (if sgn then @Integers.signed 32%positive (a64_read_w false rn rf)
       else @Integers.unsigned 32%positive (a64_read_w false rn rf))).
  set (m64 :=
    @Integers.repr 64%positive
      (if sgn then @Integers.signed 32%positive (a64_read_w false rm rf)
       else @Integers.unsigned 32%positive (a64_read_w false rm rf))).
  assert (Hn64 :
    eval_closed_cert_expr penv foracle
      (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags en) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive n64))).
  { unfold n64; destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity;
      exact (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern). }
  assert (Hm64 :
    eval_closed_cert_expr penv foracle
      (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags em) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive m64))).
  { unfold m64; destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity;
      exact (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm). }
  assert (Hmul :
    eval_closed_cert_expr penv foracle
      (CE_BinOp CB_Mul 64%positive no_binop_flags
        (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags en)
        (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags em)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.mul 64%positive n64 m64)))).
  { rewrite eval_ce_binop, Hn64, Hm64.
    cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.mul n64 m64]; reflexivity. }
  assert (Hres :
    eval_closed_cert_expr penv foracle
      (CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags ea
        (CE_BinOp CB_Mul 64%positive no_binop_flags
          (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags en)
          (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags em))) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
      (if is_sub then @Integers.sub 64%positive (a64_read_reg ra rf) (@Integers.mul 64%positive n64 m64)
       else @Integers.add 64%positive (a64_read_reg ra rf) (@Integers.mul 64%positive n64 m64))))).
  { rewrite eval_ce_binop, Hra, Hmul.
    cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct is_sub; cbn - [Integers.mul Integers.add Integers.sub n64 m64 a64_read_reg]; reflexivity. }
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng | split; [reflexivity |]].
  split; [apply a64_val_regs_agrees_write; assumption | split; [exact Hastk | exact Hfl]].
Qed.

Local Lemma a64_sym_step_ldst_imm_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk is_load is_signed sf_dst sz mode rt rn imm,
    mc_valid_sp0 sp0 ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_LdStImm is_load is_signed sf_dst sz mode rt rn imm ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk is_load is_signed sf_dst sz mode rt rn imm
         Hsp0 Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct Hsp0 as [Hsp0_cap Hsp0_al].
  assert (Hsp_to_off : mc_addr_to_off sp0 sp = sp_off)
    by (rewrite Hsp; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
  rewrite Hsp_to_off.
  destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hstep |].
  destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off] eqn:Ern; try discriminate Hstep.
  pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag Ern) as Hrn_ag.
  cbn [mc_sym_val_agrees] in Hrn_ag; destruct Hrn_ag as [Hbase_rng Hbase_ptr].
  set (wb_off := (base_off + imm)%Z) in *.
  set (wb_addr := @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive imm)) in *.
  assert (Hwb_ptr : wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off))
    by (unfold wb_addr, wb_off; rewrite Hbase_ptr, mc_add_ptr_off; reflexivity).
  set (wb_ok :=
    match mode with
    | AAM_SignedOffset => true
    | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z
    end) in *.
  destruct wb_ok eqn:Ewb; cbn [negb] in Hstep; [| discriminate Hstep].
  assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
  { destruct mode; [exact I | |];
      apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
  set (pair_off :=
    match mode with
    | AAM_SignedOffset => (wb_off, sp_off)
    | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
    | AAM_PostIndex => (base_off, sp_off)
    end).
  destruct pair_off as [off sp_chk] eqn:Epo; cbv zeta in Hstep.
  assert (Hpo_eq :
    match mode with
    | AAM_SignedOffset => (wb_off, sp_off)
    | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
    | AAM_PostIndex => (base_off, sp_off)
    end = (off, sp_chk)) by exact Epo.
  rewrite Hpo_eq in Hstep; cbv iota in Hstep.
  destruct (mc_slot_in_frame sp_chk off sz) eqn:Eslot; [| discriminate Hstep].
  pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
  assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
  assert (Hc_eq :
    mc_addr_to_off sp0
      (match mode with
       | AAM_SignedOffset | AAM_PreIndex => wb_addr
       | AAM_PostIndex => a64_read_reg_sp rn rf sp
       end) = off /\
    mc_addr_to_off sp0
      (match mode with
       | AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp
       | _ => sp
       end) = sp_chk).
  { unfold pair_off in Epo; destruct mode; inversion Epo; subst off sp_chk; split.
    - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
    - exact Hsp_to_off.
    - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
    - destruct (N.eqb rn 31%N);
        [rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia] | exact Hsp_to_off].
    - rewrite Hbase_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hbase_rng].
    - exact Hsp_to_off. }
  destruct Hc_eq as [Hoff_c Hspchk_c].
  replace
    (match mode with
     | AAM_SignedOffset => (wb_addr, sp)
     | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp)
     | AAM_PostIndex => (a64_read_reg_sp rn rf sp, sp)
     end)
    with
    ((match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end),
     (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end))
    by (destruct mode; reflexivity).
  cbn [fst snd]; rewrite Hoff_c, Hspchk_c, Eslot.
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
      if a64_ldst_store_sym_ok sz (a64_val_read rt vrf)
      then Some (vrf, mc_sym_stk_store off sz (a64_val_read rt vrf) astk)
      else None) in *.
  destruct st_opt as [[vrf1 astk1] |] eqn:Est;
    [try (rewrite Est in Hstep; cbv iota in Hstep) | try rewrite Est in Hstep; discriminate Hstep].
  assert (Hstep1 :
    let '(rf1, mstk1) :=
      if is_load
      then (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk)
      else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf)) in
    a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1).
  { destruct is_load; unfold st_opt in Est.
    - destruct (mc_sym_stk_load off sz is_signed astk) as [sv0 |] eqn:Esl0; [| discriminate Est].
      destruct (a64_ldst_sym_load is_signed sf_dst sv0) as [sv1 |] eqn:Esl1; [| discriminate Est].
      inversion Est; subst vrf1 astk1; split; [| exact Hastk].
      apply a64_val_regs_agrees_write;
        [exact Hag
        | exact (a64_ldst_sym_load_sound _ _ _ _ _ _ _ _ _
            (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl0) Esl1)].
    - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt vrf)) eqn:Eok; [| discriminate Est].
      inversion Est; subst vrf1 astk1.
      assert (Hszm : match a64_val_read rt vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
        by (destruct (a64_val_read rt vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok).
      split; [exact Hag | apply mc_sym_stk_store_agrees; [exact Hszm | exact (Hag rt) | exact Hastk]]. }
  set (rf1 :=
    if is_load
    then a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf
    else rf) in *.
  set (mstk1 := if is_load then mstk else mc_stk_store mstk off sz (a64_read_reg rt rf)) in *.
  assert (Hstep1' :
    a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1)
    by (destruct is_load; exact Hstep1).
  destruct Hstep1' as [Hag1 Hastk1].
  pose proof (a64_ldst_writeback_sound penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr
    Hrng Hsp Hwb_rng Hwb_ptr Hag1 Hastk1) as Hwb_s.
  destruct
    (match mode with
     | AAM_SignedOffset => (sp_off, vrf1, astk1)
     | AAM_PreIndex | AAM_PostIndex =>
         if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
         else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
     end) as [[sp_off2 vrf2] astk2] eqn:Ewbs.
  destruct
    (match mode with
     | AAM_SignedOffset => (rf1, sp)
     | AAM_PreIndex | AAM_PostIndex => a64_write_reg_sp rn wb_addr rf1 sp
     end) as [rf2 sp2] eqn:Ewbc.
  try rewrite Ewbs in Hwb_s; try rewrite Ewbc in Hwb_s; cbv iota in Hwb_s.
  inversion Hstep; subst res; clear Hstep.
  destruct Hwb_s as (Hrng2 & Hsp2 & Hag2 & Hastk2).
  replace
    (if is_load
     then (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk)
     else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf)))
    with (rf1, mstk1) by (destruct is_load; reflexivity).
  rewrite Ewbc.
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng2 | split; [exact Hsp2 | split; [exact Hag2 | split; [exact Hastk2 | exact Hfl]]]].
Qed.

Local Lemma a64_sym_step_ldst_pair_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk is_load sf mode rt1 rt2 rn imm,
    mc_valid_sp0 sp0 ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_LdStPair is_load sf mode rt1 rt2 rn imm ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk is_load sf mode rt1 rt2 rn imm
         Hsp0 Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct Hsp0 as [Hsp0_cap Hsp0_al].
  assert (Hsp_to_off : mc_addr_to_off sp0 sp = sp_off)
    by (rewrite Hsp; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
  rewrite Hsp_to_off.
  destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hstep |].
  destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off] eqn:Ern; try discriminate Hstep.
  pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag Ern) as Hrn_ag.
  cbn [mc_sym_val_agrees] in Hrn_ag; destruct Hrn_ag as [Hbase_rng Hbase_ptr].
  set (wb_off := (base_off + imm)%Z) in *.
  set (wb_addr := @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive imm)) in *.
  assert (Hwb_ptr : wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off))
    by (unfold wb_addr, wb_off; rewrite Hbase_ptr, mc_add_ptr_off; reflexivity).
  set (wb_ok :=
    match mode with
    | AAM_SignedOffset => true
    | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z
    end) in *.
  destruct wb_ok eqn:Ewb; cbn [negb] in Hstep; [| discriminate Hstep].
  assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
  { destruct mode; [exact I | |];
      apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
  set (pair_off :=
    match mode with
    | AAM_SignedOffset => (wb_off, sp_off)
    | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
    | AAM_PostIndex => (base_off, sp_off)
    end).
  destruct pair_off as [off sp_chk] eqn:Epo; cbv zeta in Hstep.
  assert (Hpo_eq :
    match mode with
    | AAM_SignedOffset => (wb_off, sp_off)
    | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
    | AAM_PostIndex => (base_off, sp_off)
    end = (off, sp_chk)) by exact Epo.
  rewrite Hpo_eq in Hstep; cbv iota in Hstep.
  set (sz := if sf then MS_8 else MS_4) in *; set (delta := mc_mem_bytes_Z sz) in *.
  destruct (mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz)
    eqn:Eslots; [| discriminate Hstep].
  apply andb_true_iff in Eslots as [Esl1 Esl2].
  pose proof (mc_slot_in_frame_bounds _ _ _ Esl1) as (Hb1 & Hb2 & Hb3 & _).
  pose proof (mc_slot_in_frame_bounds _ _ _ Esl2) as (_ & Hb2' & Hb3' & _).
  assert (Hsz_pos : (1 <= delta)%Z) by (unfold delta, sz; destruct sf; cbn; lia).
  assert (Hc_eq :
    mc_addr_to_off sp0
      (match mode with
       | AAM_SignedOffset | AAM_PreIndex => wb_addr
       | AAM_PostIndex => a64_read_reg_sp rn rf sp
       end) = off /\
    mc_addr_to_off sp0
      (match mode with
       | AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp
       | _ => sp
       end) = sp_chk).
  { unfold pair_off in Epo; destruct mode; inversion Epo; subst off sp_chk; split.
    - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
    - exact Hsp_to_off.
    - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
    - destruct (N.eqb rn 31%N);
        [rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia] | exact Hsp_to_off].
    - rewrite Hbase_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hbase_rng].
    - exact Hsp_to_off. }
  destruct Hc_eq as [Hoff_c Hspchk_c].
  replace
    (match mode with
     | AAM_SignedOffset => (wb_addr, sp)
     | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp)
     | AAM_PostIndex => (a64_read_reg_sp rn rf sp, sp)
     end)
    with
    ((match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end),
     (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end))
    by (destruct mode; reflexivity).
  cbn [fst snd]; rewrite Hoff_c, Hspchk_c, Esl1, Esl2; cbn [andb].
  set (st_opt :=
    if is_load then
      match mc_sym_stk_load off sz false astk, mc_sym_stk_load (off + delta) sz false astk with
      | Some sv1, Some sv2 => Some (a64_val_write rt2 sv2 (a64_val_write rt1 sv1 vrf), astk)
      | _, _ => None
      end
    else
      if a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) &&
         a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf)
      then Some (vrf, mc_sym_stk_store (off + delta) sz (a64_val_read rt2 vrf)
                        (mc_sym_stk_store off sz (a64_val_read rt1 vrf) astk))
      else None) in *.
  destruct st_opt as [[vrf1 astk1] |] eqn:Est;
    [try (rewrite Est in Hstep; cbv iota in Hstep) | try rewrite Est in Hstep; discriminate Hstep].
  assert (Hstep1 :
    let '(rf1, mstk1) :=
      if is_load
      then (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false)
              (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk)
      else (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf))
                  (off + delta) sz (a64_read_reg rt2 rf)) in
    a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1).
  { destruct is_load; unfold st_opt in Est.
    - destruct (mc_sym_stk_load off sz false astk) as [sv1 |] eqn:Esl_1; [| discriminate Est].
      destruct (mc_sym_stk_load (off + delta) sz false astk) as [sv2 |] eqn:Esl_2; [| discriminate Est].
      inversion Est; subst vrf1 astk1; split; [| exact Hastk].
      apply a64_val_regs_agrees_write;
        [apply a64_val_regs_agrees_write; [exact Hag | exact (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl_1)]
        | exact (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl_2)].
    - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) &&
                a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf)) eqn:Eok; [| discriminate Est].
      apply andb_true_iff in Eok as [Eok1 Eok2]; inversion Est; subst vrf1 astk1.
      assert (Hszm1 : match a64_val_read rt1 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
        by (destruct (a64_val_read rt1 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok1).
      assert (Hszm2 : match a64_val_read rt2 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
        by (destruct (a64_val_read rt2 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok2).
      split; [exact Hag |].
      apply mc_sym_stk_store_agrees; [exact Hszm2 | exact (Hag rt2) |].
      apply mc_sym_stk_store_agrees; [exact Hszm1 | exact (Hag rt1) | exact Hastk]. }
  set (rf1 :=
    if is_load
    then a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false)
           (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf)
    else rf) in *.
  set (mstk1 :=
    if is_load then mstk
    else mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)) in *.
  assert (Hstep1' :
    a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1)
    by (destruct is_load; exact Hstep1).
  destruct Hstep1' as [Hag1 Hastk1].
  pose proof (a64_ldst_writeback_sound penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr
    Hrng Hsp Hwb_rng Hwb_ptr Hag1 Hastk1) as Hwb_s.
  destruct
    (match mode with
     | AAM_SignedOffset => (sp_off, vrf1, astk1)
     | AAM_PreIndex | AAM_PostIndex =>
         if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
         else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
     end) as [[sp_off2 vrf2] astk2] eqn:Ewbs.
  destruct
    (match mode with
     | AAM_SignedOffset => (rf1, sp)
     | AAM_PreIndex | AAM_PostIndex => a64_write_reg_sp rn wb_addr rf1 sp
     end) as [rf2 sp2] eqn:Ewbc.
  try rewrite Ewbs in Hwb_s; try rewrite Ewbc in Hwb_s; cbv iota in Hwb_s.
  inversion Hstep; subst res; clear Hstep.
  destruct Hwb_s as (Hrng2 & Hsp2 & Hag2 & Hastk2).
  replace
    (if is_load
     then (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false)
             (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk)
     else (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf))
                 (off + delta) sz (a64_read_reg rt2 rf)))
    with (rf1, mstk1) by (destruct is_load; reflexivity).
  rewrite Ewbc.
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng2 | split; [exact Hsp2 | split; [exact Hag2 | split; [exact Hastk2 | exact Hfl]]]].
Qed.

Local Lemma a64_sym_step_tbz_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk is_nz rt bit rel,
    a64_inst_valid dec = true ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    dai_inst dec = A64_Tbz is_nz rt bit rel ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Branch cond tgt_pc next_pc fl_def' =>
        exists b : bool,
          eval_closed_cert_expr penv foracle cond =
            raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
              (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk =
            Some ((if b then tgt_pc else next_pc), rf, sp, fl, mstk) /\
          (fl_def' = true -> fl_def = true)
    | ASSR_Next _ _ _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk is_nz rt bit rel Hdec_val Hag Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct (a64_val_read rt vrf) as [| rt_e | |] eqn:Ert; try discriminate Hstep.
  destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep].
  inversion Hstep; subst; clear Hstep.
  unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.ltb_lt in Hdec_val.
  pose proof (Hag rt) as Hrt; rewrite Ert in Hrt; cbn [mc_sym_val_agrees] in Hrt.
  assert (Hm :
    eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit))) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
      (@Integers.and 64%positive (a64_read_reg rt rf)
        (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))))))
    by (rewrite eval_ce_binop, Hrt, eval_ce_const; cbn [eou_bind]; unfold eval_iop;
        rewrite eval_iop_integer_base_same_width; reflexivity).
  pose proof (a64_tbz_bit_test_eq (a64_read_reg rt rf) bit Hdec_val) as Heq_tb.
  set (b :=
    if is_nz
    then Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)
    else negb (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit))).
  exists b; split; [| split; [| intro Hf; exact Hf]].
  - unfold b; rewrite <- Heq_tb; destruct is_nz.
    + exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ Hm
        ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)).
    + rewrite negb_involutive.
      exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hm
        ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)).
  - cbv zeta iota; destruct b; try rewrite Erel; reflexivity.
Qed.

Local Lemma a64_sym_step_addsub_shift_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn rm sh amt,
    a64_inst_valid dec = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_AddSubShift sf is_sub set_fl rd rn rm sh amt ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn rm sh amt
         Hdec_val Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
  destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hstep].
  unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val.
  apply andb_true_iff in Hdec_val as [_ Hamt]; apply N.ltb_lt in Hamt.
  pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf)
    ltac:(destruct sf; exact Hamt) (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hsh.
  destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
  destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl'] eqn:Eeas.
  inversion Hstep; subst; clear Hstep.
  pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) Hsh) as [Hres Hfl'].
  rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng | split; [reflexivity |]].
  split; [apply a64_val_regs_agrees_write_w; assumption |].
  split; [exact Hastk | intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]].
Qed.

Local Lemma a64_sym_step_addsub_ext_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn rm ext amt,
    a64_inst_valid dec = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_AddSubExt sf is_sub set_fl rd rn rm ext amt ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn rm ext amt
         Hdec_val Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hstep |].
  destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
  destruct (a64_val_read rm vrf) as [| rm64 | |] eqn:Erm; try discriminate Hstep.
  unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.leb_le in Hdec_val.
  pose proof (Hag rm) as Hm64; rewrite Erm in Hm64; cbn [mc_sym_val_agrees] in Hm64.
  pose proof (eval_a64_sym_extend_sound _ _ (a64_w sf) _ _ ext amt (a64_w_32_64 sf) Hdec_val Hm64) as Hext.
  destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
  destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl'] eqn:Eeas.
  inversion Hstep; subst; clear Hstep.
  pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) Hext) as [Hres Hfl'].
  rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng | split; [reflexivity |]].
  split; [apply a64_val_regs_agrees_write_w; assumption |].
  split; [exact Hastk | intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]].
Qed.

Local Lemma a64_sym_step_ccmp_reg_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub cond rn rm nzcv,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_CondCompareReg sf is_sub cond rn rm nzcv ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub cond rn rm nzcv
         Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
  destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
  destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
  destruct (a64_sym_add_sub (a64_w sf) is_sub en em) as [csres csfl] eqn:Esas.
  destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (a64_read_w sf rm rf)) as [cvr cfl] eqn:Eeas.
  inversion Hstep; subst; clear Hstep.
  pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as [_ Hcsfl].
  rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng | split; [reflexivity |]].
  split; [exact Hag | split; [exact Hastk |]].
  intro; exact (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _
    (eval_a64_sym_cond_sound _ _ cond _ _ (Hfl eq_refl)) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv)).
Qed.

Local Lemma a64_sym_step_ccmp_imm_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub cond rn imm5 nzcv,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    dai_inst dec = A64_CondCompareImm sf is_sub cond rn imm5 nzcv ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch _ _ _ _ | ASSR_Ret _ => False
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res
         penv foracle rf0 sp0 rf sp fl mstk sf is_sub cond rn imm5 nzcv
         Hrng Hsp Hag Hastk Hfl Ed Hstep.
  unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
  destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
  destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
  destruct (a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5))) as [csres csfl] eqn:Esas.
  destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm5)))
    as [cvr cfl] eqn:Eeas.
  inversion Hstep; subst; clear Hstep.
  pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
    (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm5))) as [_ Hcsfl].
  rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
  eexists _, _, _, _; split; [reflexivity |].
  split; [exact Hrng | split; [reflexivity |]].
  split; [exact Hag | split; [exact Hastk |]].
  intro; exact (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _
    (eval_a64_sym_cond_sound _ _ cond _ _ (Hfl eq_refl)) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv)).
Qed.

Lemma a64_sym_step_one_sound :
  forall {Pa : Params} dec pc sp_off vrf astk sfl fl_def ret_w res penv foracle rf0 sp0 rf sp fl mstk,
    rv_supported_arg_width ret_w = true ->
    a64_inst_valid dec = true ->
    mc_valid_sp0 sp0 ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w = Some res ->
    match res with
    | ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def' =>
        exists rf' sp' fl' mstk',
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk = Some (next_pc, rf', sp', fl', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
          a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk' /\
          (fl_def' = true -> sym_flags_agree penv foracle sfl' fl')
    | ASSR_Branch cond tgt_pc next_pc fl_def' =>
        exists b : bool,
          eval_closed_cert_expr penv foracle cond =
            raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
              (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
          a64_exec_one_nonret dec sp0 pc rf sp fl mstk =
            Some ((if b then tgt_pc else next_pc), rf, sp, fl, mstk) /\
          (fl_def' = true -> fl_def = true)
    | ASSR_Ret ret_e =>
        dai_inst dec = A64_Ret /\
        sp = sp0 /\
        a64_callee_saved_preserved rf0 rf /\
        eval_closed_cert_expr penv foracle ret_e =
          raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf))))
    end.
Proof.
  intros Pa dec pc sp_off vrf astk sfl fl_def ret_w res penv foracle rf0 sp0 rf sp fl mstk
         Hrw Hdec_val Hsp0 Hrng Hsp Hag Hastk Hfl Hstep.
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
      | rel | cond rel | sf is_nz rt rel | is_nz rt bit rel | ] eqn:Ed.
  - unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv zeta iota in Hstep.
    inversion Hstep; subst.
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity | split; [exact Hag | split; [exact Hastk | exact Hfl]]]].
  - pose proof (a64_sym_step_addsub_imm_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn imm
      Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - pose proof (a64_sym_step_addsub_shift_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn rm sh amt
      Hdec_val Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - pose proof (a64_sym_step_addsub_ext_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf is_sub set_fl rd rn rm ext amt
      Hdec_val Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
    destruct (negb set_fl && N.eqb rd 31%N); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    assert (Hres :
      eval_closed_cert_expr penv foracle
        (a64_sym_logic_op (a64_w sf) op lhs (ce_bv_z (a64_w sf) (Z.of_N mask))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N mask)))))).
    { unfold a64_sym_logic_op, a64_eval_logic_op.
      rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), eval_ce_bv_z.
      cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split; [apply a64_val_regs_agrees_write_w; assumption |].
    split; [exact Hastk | intro Hs; destruct set_fl;
      [exact (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) | exact (Hfl Hs)]].
  - pose proof (a64_sym_step_logic_shift_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf op inv_rm set_fl rd rn rm sh amt
      Hdec_val Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - pose proof (a64_sym_step_move_wide_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf kind rd imm16 shift
      Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - pose proof (a64_sym_step_bitfield_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf kind rd rn immr imms
      Hdec_val Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
    destruct (a64_val_read_expr_w sf rn vrf) as [hi_e |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [lo_e |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split.
    + apply a64_val_regs_agrees_write_w; [exact Hag |].
      exact (eval_a64_sym_extr_sound _ _ (a64_w sf) _ _ _ _ lsb (a64_w_32_64 sf)
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)).
    + split; [exact Hastk | exact Hfl].
  - pose proof (a64_sym_step_mul_addsub_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf is_sub rd rn rm ra
      Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - pose proof (a64_sym_step_mul_widening_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sgn is_sub rd rn rm ra
      Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split.
    + apply a64_val_regs_agrees_write_w; [exact Hag |].
      exact (eval_a64_sym_dp2_sound _ _ (a64_w sf) op _ _ _ _ (a64_w_32_64 sf)
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)).
    + split; [exact Hastk | exact Hfl].
  - unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
    destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity |].
    split; [exact Hrng | split; [reflexivity |]].
    split.
    + apply a64_val_regs_agrees_write_w; [exact Hag |].
      exact (eval_a64_sym_csel_sound _ _ (a64_w sf) kind cond sfl fl _ _ _ _ (Hfl eq_refl)
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
        (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)).
    + split; [exact Hastk | exact Hfl].
  - pose proof (a64_sym_step_ccmp_reg_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf is_sub cond rn rm nzcv
      Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - pose proof (a64_sym_step_ccmp_imm_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk sf is_sub cond rn imm5 nzcv
      Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - pose proof (a64_sym_step_ldst_imm_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk is_load is_signed sf_dst sz mode rt rn imm
      Hsp0 Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - pose proof (a64_sym_step_ldst_pair_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk is_load sf mode rt1 rt2 rn imm
      Hsp0 Hrng Hsp Hag Hastk Hfl Ed Hstep) as Hr;
      destruct res; [exact Hr | contradiction | contradiction].
  - unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
    destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep].
    inversion Hstep; subst.
    eexists _, _, _, _; split; [cbv zeta iota; try rewrite Erel; reflexivity |].
    split; [exact Hrng | split; [reflexivity | split; [exact Hag | split; [exact Hastk | exact Hfl]]]].
  - unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
    destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    exists (a64_eval_cond cond fl).
    split; [exact (eval_a64_sym_cond_sound penv foracle cond sfl fl (Hfl eq_refl)) |].
    split.
    + cbv zeta iota; destruct (a64_eval_cond cond fl); try rewrite Erel; reflexivity.
    + intro; reflexivity.
  - unfold a64_sym_step_one in Hstep; unfold a64_exec_one_nonret; rewrite Ed in Hstep |- *; cbv iota in Hstep.
    destruct (a64_val_read_expr_w sf rt vrf) as [rt_e |] eqn:Ert; [| discriminate Hstep].
    destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    set (b :=
      if is_nz
      then negb (@Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf)))
      else @Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf))).
    exists b; split; [| split; [| intro Hf; exact Hf]].
    + unfold b; destruct is_nz.
      * exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _
          (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ert)
          ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)).
      * exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _
          (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ert)
          ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)).
    + cbv zeta iota; destruct b; try rewrite Erel; reflexivity.
  - pose proof (a64_sym_step_tbz_sound dec pc sp_off vrf astk sfl fl_def ret_w res
      penv foracle rf0 sp0 rf sp fl mstk is_nz rt bit rel Hdec_val Hag Ed Hstep) as Hr;
      destruct res; [contradiction | exact Hr | contradiction].
  - unfold a64_sym_step_one in Hstep; rewrite Ed in Hstep; cbv zeta iota in Hstep.
    destruct (a64_sym_epilogue_ok sp_off vrf) eqn:Hep; [| discriminate Hstep].
    destruct (a64_val_read 0%N vrf) as [| e_ret | |] eqn:Er0; try discriminate Hstep.
    inversion Hstep; subst res; clear Hstep.
    destruct (a64_sym_epilogue_ok_sound penv foracle rf0 sp0 sp_off vrf rf sp Hsp Hag Hep) as [Hsp_end Hcs].
    repeat split; try assumption; unfold rv_trunc_ret_expr, rv_trunc_ret_val.
    pose proof (Hag 0%N) as Ha0; rewrite Er0 in Ha0; cbn [mc_sym_val_agrees] in Ha0.
    destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
    + apply Pos.eqb_eq in Ew64; subst ret_w; rewrite Ha0, (@Integers.repr_unsigned 64%positive); reflexivity.
    + assert (Hlt64 : (ret_w <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hrw Ew64).
      rewrite (eval_ce_trunc penv foracle 64%positive ret_w _ _ Hlt64 Ha0); reflexivity.
Qed.

Fixpoint summarize_a64_seg_at
  (seg_name : string) (fuel : nat) (im : pos_trie decoded_a64_inst) (cut_pc : N)
  (req_step : bool) (visited : pos_trie unit)
  (pc : N) (sp_off : Z) (vrf : a64_val_regs) (astk : mc_sym_stack)
  (sfl : a64_sym_flags) (fl_def : bool) (ret_w : positive)
  {struct fuel} : string + a64_seg_tree :=
  let loc (_ : unit) : string :=
    ("aarch64 " ++ seg_name ++ " segment at pc=" ++ diag_N_hex pc ++
     " cut=" ++ diag_N_hex cut_pc ++ " sp-off=" ++ diag_Z_dec sp_off)%string
  in
  if negb req_step && N.eqb pc cut_pc then
    inr (AST_Cut sp_off vrf astk)
  else if pt_has_n pc visited then
    inl (diag "mc-loop-mc" ("cycle detected in " ++ loc tt))
  else
    match fuel with
    | O => inl (diag "mc-loop-mc" ("fuel exhausted summarizing " ++ loc tt))
    | S fuel' =>
        match pt_get (N.succ_pos pc) im with
        | None => inl (diag "mc-loop-mc" ("execution escaped function slice in " ++ loc tt))
        | Some dec =>
            let visited' := pt_add_n pc visited in
            match a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w with
            | None =>
                inl (diag "mc-loop-mc" ("unsupported instruction or invalid frame access in " ++ loc tt))
            | Some (ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def') =>
                summarize_a64_seg_at seg_name fuel' im cut_pc false visited'
                  next_pc sp_off' vrf' astk' sfl' fl_def' ret_w
            | Some (ASSR_Branch cond tgt_pc next_pc fl_def') =>
                match summarize_a64_seg_at seg_name fuel' im cut_pc false visited'
                        tgt_pc sp_off vrf astk sfl fl_def' ret_w with
                | inl err => inl err
                | inr dt =>
                    match summarize_a64_seg_at seg_name fuel' im cut_pc false visited'
                            next_pc sp_off vrf astk sfl fl_def' ret_w with
                    | inl err => inl err
                    | inr df => inr (AST_Branch cond dt df)
                    end
                end
            | Some (ASSR_Ret ret_e) => inr (AST_Ret ret_e)
            end
        end
    end.

Definition summarize_a64_seg
  (seg_name : string) (fuel : nat) (insts : list decoded_a64_inst) (cut_pc : N)
  (req_step : bool) (visited : list N)
  (pc : N) (sp_off : Z) (vrf : a64_val_regs) (astk : mc_sym_stack)
  (sfl : a64_sym_flags) (fl_def : bool) (ret_w : positive)
  : string + a64_seg_tree :=
  summarize_a64_seg_at seg_name fuel (pt_of_list_first dai_off insts) cut_pc req_step
    (pt_of_visited visited) pc sp_off vrf astk sfl fl_def ret_w.

Theorem summarize_a64_seg_at_wf :
  forall seg_name fuel insts im cut_pc req_step visited pc allowed sp_off vrf astk sfl fl_def ret_w seg,
    (forall q, pt_get (N.succ_pos q) im = lookup_a64_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    summarize_a64_seg_at seg_name fuel im cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w = inr seg ->
    a64_seg_wf allowed ret_w seg.
Proof.
  intros seg_name fuel insts im cut_pc req_step visited pc allowed sp_off vrf astk sfl fl_def ret_w seg Him.
  revert cut_pc req_step visited pc allowed sp_off vrf astk sfl fl_def ret_w seg.
  induction fuel as [| fuel' IH];
    intros cut_pc req_step visited pc allowed sp_off vrf astk sfl fl_def ret_w seg
           Hrw Hrng Hwf Hstk Hfl Hsum;
    cbn [summarize_a64_seg_at] in Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc).
    + inversion Hsum; subst; split; [exact Hrng | split; [exact Hwf | exact Hstk]].
    + destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc).
    + inversion Hsum; subst; split; [exact Hrng | split; [exact Hwf | exact Hstk]].
    + destruct (pt_has_n pc visited); [discriminate Hsum |].
      destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
      rewrite Him in Elook.
      destruct (a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w) as [res |] eqn:Est; [| discriminate Hsum].
      pose proof (a64_sym_step_one_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res
        Hrw Hrng Hwf Hstk Hfl Est) as Hres.
      destruct res.
      * destruct Hres as (Hrng' & Hwf' & Hstk' & Hfl').
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hrng' Hwf' Hstk' Hfl' Hsum).
      * destruct (summarize_a64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited)
                    tgt_pc sp_off vrf astk sfl fl_def' ret_w) as [| dt] eqn:Edt;
          [discriminate Hsum |].
        destruct (summarize_a64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited)
                    next_pc sp_off vrf astk sfl fl_def' ret_w) as [| df] eqn:Edf;
          [discriminate Hsum |].
        destruct Hres as [Hres Hfd]; inversion Hsum; subst; split;
          [exact Hres
          | split;
              [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk (fun Hf => Hfl (Hfd Hf)) Edt)
              | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk (fun Hf => Hfl (Hfd Hf)) Edf)]].
      * inversion Hsum; subst; exact Hres.
Qed.

Theorem summarize_a64_seg_wf :
  forall seg_name fuel insts cut_pc req_step visited pc allowed sp_off vrf astk sfl fl_def ret_w seg,
    rv_supported_arg_width ret_w = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    summarize_a64_seg seg_name fuel insts cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w = inr seg ->
    a64_seg_wf allowed ret_w seg.
Proof.
  intros seg_name fuel insts cut_pc req_step visited pc allowed sp_off vrf astk sfl fl_def ret_w seg
         Hrw Hrng Hwf Hstk Hfl Hsum.
  eapply summarize_a64_seg_at_wf with (insts := insts);
    [exact (pt_of_list_first_lookup_a64 insts)
    | exact Hrw | exact Hrng | exact Hwf | exact Hstk | exact Hfl | exact Hsum].
Qed.

Fixpoint a64_seg_exec_spec
  {Pa : Params} (penv : param_env Pa) (foracle : freeze_oracle)
  (insts : list decoded_a64_inst) (cut_pc : N) (req_step : bool)
  (pc : N) (rf0 : a64_regfile) (sp0 : @Integers.bit_int 64%positive)
  (rf : a64_regfile) (sp : @Integers.bit_int 64%positive)
  (fl : a64_flags) (mstk : mc_stack_mem) (ret_w : positive)
  (t : a64_seg_tree) {struct t} : Prop :=
  match t with
  | AST_Cut sp_off' vrf' astk' =>
      exists n rf' sp' fl' mstk',
        (req_step = true -> (1 <= n)%nat) /\
        a64_exec_steps n insts sp0 pc rf sp fl mstk = Some (cut_pc, rf', sp', fl', mstk') /\
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
        a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk'
  | AST_Ret ret_e =>
      exists fuel_end rf_end fl_end mstk_end,
        a64_exec_mem fuel_end insts pc sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
        a64_callee_saved_preserved rf0 rf_end /\
        eval_closed_cert_expr penv foracle ret_e =
          raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end))))
  | AST_Branch cond dt df =>
      exists b : bool,
        eval_closed_cert_expr penv foracle cond =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
            (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
        a64_seg_exec_spec penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w (if b then dt else df)
  end.

Lemma a64_seg_exec_spec_step_front :
  forall {Pa : Params} penv foracle insts cut_pc req_step pc0 pc1 rf0 sp0 rf_a sp_a fl_a m_a rf_b sp_b fl_b m_b ret_w t,
    a64_exec_steps 1 insts sp0 pc0 rf_a sp_a fl_a m_a = Some (pc1, rf_b, sp_b, fl_b, m_b) ->
    @a64_seg_exec_spec Pa penv foracle insts cut_pc false pc1 rf0 sp0 rf_b sp_b fl_b m_b ret_w t ->
    @a64_seg_exec_spec Pa penv foracle insts cut_pc req_step pc0 rf0 sp0 rf_a sp_a fl_a m_a ret_w t.
Proof.
  intros Pa penv foracle insts cut_pc req_step pc0 pc1 rf0 sp0 rf_a sp_a fl_a m_a rf_b sp_b fl_b m_b ret_w t H1 Hspec.
  induction t as [sp_off' vrf' astk' | ret_e | cond dt IHt df IHf]; cbn [a64_seg_exec_spec] in *.
  - destruct Hspec as (n & rf' & sp' & fl' & mstk' & _ & Hn & Hrng & Hsp' & Hag & Hastk).
    exists (1 + n)%nat, rf', sp', fl', mstk'.
    split; [intro; lia |].
    split; [exact (a64_exec_steps_trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 Hn) |].
    split; [exact Hrng | split; [exact Hsp' | split; [exact Hag | exact Hastk]]].
  - destruct Hspec as (fuel_end & rf_end & fl_end & mstk_end & Hm & Hcs & Hev).
    exists (1 + fuel_end)%nat, rf_end, fl_end, mstk_end;
      split; [exact (a64_exec_steps_to_exec_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 Hm) | split; [exact Hcs | exact Hev]].
  - destruct Hspec as [b [Hbc Hsub]]; exists b; split; [exact Hbc |];
      destruct b; [exact (IHt Hsub) | exact (IHf Hsub)].
Qed.

Theorem summarize_a64_seg_at_sound :
  forall {Pa : Params} seg_name fuel insts im cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w seg
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
    summarize_a64_seg_at seg_name fuel im cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w = inr seg ->
    a64_seg_exec_spec penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w seg.
Proof.
  intros Pa seg_name fuel insts im cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w seg
         penv foracle rf0 sp0 rf sp fl mstk Him.
  revert cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w seg penv foracle rf0 sp0 rf sp fl mstk.
  induction fuel as [| fuel' IH];
    intros cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w seg
           penv foracle rf0 sp0 rf sp fl mstk Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Hsum;
    cbn [summarize_a64_seg_at] in Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc) eqn:Ecut.
    + apply andb_true_iff in Ecut as [Hreq Hpc]; apply N.eqb_eq in Hpc; subst pc.
      destruct req_step; [discriminate Hreq |]; inversion Hsum; subst seg; clear Hsum.
      exists 0%nat, rf, sp, fl, mstk.
      split; [intro C; discriminate C | split; [reflexivity |]].
      split; [exact Hrng | split; [exact Hsp | split; [exact Hag | exact Hastk]]].
    + destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc) eqn:Ecut.
    + apply andb_true_iff in Ecut as [Hreq Hpc]; apply N.eqb_eq in Hpc; subst pc.
      destruct req_step; [discriminate Hreq |]; inversion Hsum; subst seg; clear Hsum.
      exists 0%nat, rf, sp, fl, mstk.
      split; [intro C; discriminate C | split; [reflexivity |]].
      split; [exact Hrng | split; [exact Hsp | split; [exact Hag | exact Hastk]]].
    + destruct (pt_has_n pc visited); [discriminate Hsum |].
      destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
      rewrite Him in Elook.
      assert (Hdec_val : a64_inst_valid dec = true).
      { clear -Elook Hval; induction insts as [| d rest IHl]; cbn in *; [discriminate |].
        apply andb_true_iff in Hval as [Hd Hr]; destruct (N.eqb (dai_off d) pc);
          [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
      destruct (a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w) as [res |] eqn:Est; [| discriminate Hsum].
      pose proof (a64_sym_step_one_sound dec pc sp_off vrf astk sfl fl_def ret_w res
        penv foracle rf0 sp0 rf sp fl mstk Hrw Hdec_val Hsp0 Hrng Hsp Hag Hastk Hfl Est) as Hres.
      destruct res.
      * destruct Hres as (rf1 & sp1 & fl1 & mstk1 & Hone & Hrng' & Hsp' & Hag' & Hastk' & Hfl').
        assert (H1 : a64_exec_steps 1 insts sp0 pc rf sp fl mstk = Some (next_pc, rf1, sp1, fl1, mstk1))
          by (cbn [a64_exec_steps]; rewrite Elook, Hone; reflexivity).
        eapply a64_seg_exec_spec_step_front; [exact H1 |].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng' Hsp' Hag' Hastk' Hfl' Hsum).
      * destruct (summarize_a64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited)
                    tgt_pc sp_off vrf astk sfl fl_def' ret_w) as [| dt] eqn:Edt;
          [discriminate Hsum |].
        destruct (summarize_a64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited)
                    next_pc sp_off vrf astk sfl fl_def' ret_w) as [| df] eqn:Edf;
          [discriminate Hsum |].
        inversion Hsum; subst seg; clear Hsum.
        destruct Hres as [b [Hbc [Hone Hfd]]].
        cbn [a64_seg_exec_spec]; exists b; split; [exact Hbc |].
        assert (H1 :
          a64_exec_steps 1 insts sp0 pc rf sp fl mstk =
          Some ((if b then tgt_pc else next_pc), rf, sp, fl, mstk))
          by (cbn [a64_exec_steps]; rewrite Elook, Hone; reflexivity).
        eapply a64_seg_exec_spec_step_front; [exact H1 |].
        assert (Hfl_sub : fl_def' = true -> sym_flags_agree penv foracle sfl fl) by (intro Hf; exact (Hfl (Hfd Hf))).
        destruct b;
          [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl_sub Edt)
          | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl_sub Edf)].
      * inversion Hsum; subst seg; clear Hsum.
        destruct Hres as (Hret & Hsp_end & Hcs & Hev).
        rewrite Hsp_end; exists 1%nat, rf, fl, mstk; split; [| split; [exact Hcs | exact Hev]].
        cbn [a64_exec_mem]; rewrite Elook, Hret; reflexivity.
Qed.

Theorem summarize_a64_seg_sound :
  forall {Pa : Params} seg_name fuel insts cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w seg
         penv foracle rf0 sp0 rf sp fl mstk,
    rv_supported_arg_width ret_w = true ->
    forallb a64_inst_valid insts = true ->
    mc_valid_sp0 sp0 ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    summarize_a64_seg seg_name fuel insts cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w = inr seg ->
    a64_seg_exec_spec penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w seg.
Proof.
  intros Pa seg_name fuel insts cut_pc req_step visited pc sp_off vrf astk sfl fl_def ret_w seg
         penv foracle rf0 sp0 rf sp fl mstk Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Hsum.
  eapply summarize_a64_seg_at_sound with (insts := insts);
    [exact (pt_of_list_first_lookup_a64 insts)
    | exact Hrw | exact Hval | exact Hsp0 | exact Hrng | exact Hsp | exact Hag | exact Hastk | exact Hfl | exact Hsum].
Qed.

Lemma a64_exec_mem_det :
  forall f1 f2 insts pc sp0 rf sp fl mstk r1 r2,
    a64_exec_mem f1 insts pc sp0 rf sp fl mstk = Some r1 ->
    a64_exec_mem f2 insts pc sp0 rf sp fl mstk = Some r2 ->
    r1 = r2.
Proof.
  intros f1 f2 insts pc sp0 rf sp fl mstk r1 r2 H1 H2.
  pose proof (a64_exec_mem_mono f1 (Nat.max f1 f2) insts pc sp0 rf sp fl mstk r1 (Nat.le_max_l f1 f2) H1) as Hm1.
  pose proof (a64_exec_mem_mono f2 (Nat.max f1 f2) insts pc sp0 rf sp fl mstk r2 (Nat.le_max_r f1 f2) H2) as Hm2.
  rewrite Hm1 in Hm2; inversion Hm2; reflexivity.
Qed.

Lemma a64_init_arg_expr_vars : forall sp,
  is_let_free_expr (a64_init_arg_expr sp) = true /\
  (forall nm w,
     In (nm, w) (collect_free_vars [] (a64_init_arg_expr sp)) ->
     (nm = ras_name sp /\ w = ras_width sp) \/
     ((ras_width sp =? 64)%positive = false /\ nm = a64_hi_var_name (ras_name sp) /\ w = 64%positive)).
Proof.
  intros sp; unfold a64_init_arg_expr.
  destruct (Pos.eqb (ras_width sp) 64%positive) eqn:E64.
  - cbn [is_let_free_expr collect_free_vars]; split; [reflexivity |].
    intros nm w [Heq | []]; inversion Heq; left; split; reflexivity.
  - destruct (Pos.eqb (ras_width sp) 32%positive) eqn:E32.
    + cbn [is_let_free_expr collect_free_vars]; split; [reflexivity |].
      intros nm w [Heq | [Heq | []]]; inversion Heq.
      * left; split; reflexivity.
      * right; repeat split; try assumption; reflexivity.
    + destruct (ras_ext sp); cbn [is_let_free_expr collect_free_vars]; split; try reflexivity;
        intros nm w [Heq | [Heq | []]]; inversion Heq.
      * left; split; reflexivity.
      * right; repeat split; try assumption; reflexivity.
      * left; split; reflexivity.
      * right; repeat split; try assumption; reflexivity.
      * left; split; reflexivity.
      * right; repeat split; try assumption; reflexivity.
Qed.

Lemma a64_build_init_val_regs_vars : forall idx specs r e,
  a64_val_read r (a64_build_init_val_regs idx specs) = MSV_Expr e ->
  is_let_free_expr e = true /\
  (forall nm w,
     In (nm, w) (collect_free_vars [] e) ->
     exists sp,
       In sp specs /\
       ((nm = ras_name sp /\ w = ras_width sp) \/
        ((ras_width sp =? 64)%positive = false /\ nm = a64_hi_var_name (ras_name sp) /\ w = 64%positive))).
Proof.
  intros idx specs; revert idx; induction specs as [| sp rest IH];
    intros idx r e Hrd; unfold a64_val_read in Hrd;
    destruct (N.leb 31%N r) eqn:Er31.
  - inversion Hrd; subst; split; [reflexivity | intros nm w []].
  - cbn [a64_build_init_val_regs] in Hrd; unfold a64_empty_val_regs in Hrd; rewrite Er31 in Hrd.
    destruct (a64_is_callee_saved r); discriminate Hrd.
  - inversion Hrd; subst; split; [reflexivity | intros nm w []].
  - cbn [a64_build_init_val_regs] in Hrd; destruct (N.eqb r idx) eqn:Eeq.
    + inversion Hrd; subst e; destruct (a64_init_arg_expr_vars sp) as [Hlf Hfv].
      split; [exact Hlf |].
      intros nm w Hin; exists sp; split; [left; reflexivity | exact (Hfv nm w Hin)].
    + assert (Hrd' : a64_val_read r (a64_build_init_val_regs (N.succ idx) rest) = MSV_Expr e)
        by (unfold a64_val_read; rewrite Er31; exact Hrd).
      destruct (IH (N.succ idx) r e Hrd') as [Hlf Hfv].
      split; [exact Hlf |].
      intros nm w Hin; destruct (Hfv nm w Hin) as [sp0 [Hin0 Hcase]].
      exists sp0; split; [right; exact Hin0 | exact Hcase].
Qed.
