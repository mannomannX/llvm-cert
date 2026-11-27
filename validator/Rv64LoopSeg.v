(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * RV64 Loop-Segment Symbolic Summarizer & Multi-Step Lemmas ([CertValidator.Rv64LoopSeg])

    Purpose:
      Provides multi-step concrete execution lemmas ([rv_exec_steps]) and the RV64 loop-segment
      symbolic summarizer ([summarize_rv64_seg]) producing [rv_seg_tree] trees backed by
      [summarize_rv64_seg_wf] and [summarize_rv64_seg_sound].

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml directly. [summarize_rv64_seg] fails closed
      ([inl err]) on missing instructions, invalid branches/cutpoints, undefined reads, or fuel
      exhaustion; accepted trees satisfy [rv_seg_wf] and multi-step execution soundness.

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{CertFormat,AigLrat,
      AlgRules,CfgDag,Elf64Spec,McFrameMem,McIsaCommon,Rv64Decode,Rv64ExecSym,Rv64DagProof}];
      zero custom axioms.

    Section Outline:
      8. Multi-step lemmas ([rv_exec_steps]), [rv_seg_tree], [rv_sym_step_one],
      [summarize_rv64_seg], and [summarize_rv64_seg_wf] / [summarize_rv64_seg_sound]. *)

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
  Rv64ExecSym
  Rv64DagProof.

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

(** ** 8. Loop-Segment Symbolic Summarizer & Multi-Step Concrete Lemmas (M3b) *)

Definition rv_exec_one_nonret
  (dec : decoded_rv_inst) (sp0 : @Integers.bit_int 64)
  (pc : N) (rf : rv_regfile) (mstk : mc_stack_mem)
  : option (N * rv_regfile * mc_stack_mem) :=
  let next_pc := (pc + dri_len dec)%N in
  match dri_inst dec with
  | RV_Nop => Some (next_pc, rf, mstk)
  | RV_Lui rd imm =>
      Some (next_pc, rv_write_reg rd (@Integers.repr 64 imm) rf, mstk)
  | RV_AluImm op is_word rd rs1 imm =>
      let v := rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm in
      Some (next_pc, rv_write_reg rd v rf, mstk)
  | RV_AluReg op is_word rd rs1 rs2 =>
      let v := rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) in
      Some (next_pc, rv_write_reg rd v rf, mstk)
  | RV_Load sz is_signed rd rs1 imm =>
      let addr := @Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm) in
      let off := mc_addr_to_off sp0 addr in
      let sp_off := mc_addr_to_off sp0 (rv_read_reg 2%N rf) in
      if mc_slot_in_frame sp_off off sz then
        Some (next_pc, rv_write_reg rd (mc_stk_load mstk off sz is_signed) rf, mstk)
      else None
  | RV_Store sz rs1 rs2 imm =>
      let addr := @Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm) in
      let off := mc_addr_to_off sp0 addr in
      let sp_off := mc_addr_to_off sp0 (rv_read_reg 2%N rf) in
      if mc_slot_in_frame sp_off off sz then
        Some (next_pc, rf, mc_stk_store mstk off sz (rv_read_reg rs2 rf))
      else None
  | RV_Jal0 rel =>
      match add_rel_off pc rel with
      | None => None
      | Some tgt_pc => Some (tgt_pc, rf, mstk)
      end
  | RV_Branch cond rs1 rs2 rel =>
      if rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) then
        match add_rel_off pc rel with
        | None => None
        | Some tgt_pc => Some (tgt_pc, rf, mstk)
        end
      else
        Some (next_pc, rf, mstk)
  | RV_Ret => None
  end.

Fixpoint rv_exec_steps
  (n : nat) (insts : list decoded_rv_inst) (sp0 : @Integers.bit_int 64)
  (pc : N) (rf : rv_regfile) (mstk : mc_stack_mem)
  {struct n} : option (N * rv_regfile * mc_stack_mem) :=
  match n with
  | O => Some (pc, rf, mstk)
  | S n' =>
      match lookup_rv_inst insts pc with
      | None => None
      | Some dec =>
          match rv_exec_one_nonret dec sp0 pc rf mstk with
          | None => None
          | Some (pc1, rf1, m1) => rv_exec_steps n' insts sp0 pc1 rf1 m1
          end
      end
  end.

Lemma rv_exec_mem_step_nonret :
  forall fuel' insts sp0 pc rf mstk dec pc1 rf1 m1,
    lookup_rv_inst insts pc = Some dec ->
    rv_exec_one_nonret dec sp0 pc rf mstk = Some (pc1, rf1, m1) ->
    rv_exec_mem (S fuel') insts pc sp0 rf mstk = rv_exec_mem fuel' insts pc1 sp0 rf1 m1.
Proof.
  intros fuel' insts sp0 pc rf mstk dec pc1 rf1 m1 Hlk Hstep.
  cbn [rv_exec_mem]; rewrite Hlk.
  unfold rv_exec_one_nonret in Hstep.
  destruct (dri_inst dec) as [| ? ? | ? ? ? ? ? | ? ? ? ? ? | ? ? ? ? ? | ? ? ? ? | ? ? ? rel | rel |];
    try (discriminate Hstep || (inversion Hstep; subst; reflexivity)).
  - destruct (mc_slot_in_frame _ _ _); [inversion Hstep; subst; reflexivity | discriminate Hstep].
  - destruct (mc_slot_in_frame _ _ _); [inversion Hstep; subst; reflexivity | discriminate Hstep].
  - destruct (rv_eval_br_cond _ _ _).
    + destruct (add_rel_off pc rel); [inversion Hstep; subst; reflexivity | discriminate Hstep].
    + inversion Hstep; subst; reflexivity.
  - destruct (add_rel_off pc rel); [inversion Hstep; subst; reflexivity | discriminate Hstep].
Qed.

Lemma rv_exec_mem_mono :
  forall f1 f2 insts pc sp0 rf mstk res,
    (f1 <= f2)%nat ->
    rv_exec_mem f1 insts pc sp0 rf mstk = Some res ->
    rv_exec_mem f2 insts pc sp0 rf mstk = Some res.
Proof.
  intros f1; induction f1 as [| f1' IH]; intros f2 insts pc sp0 rf mstk res Hle H;
    [cbn [rv_exec_mem] in H; discriminate H |].
  destruct f2 as [| f2']; [lia |].
  cbn [rv_exec_mem] in H |- *.
  destruct (lookup_rv_inst insts pc) as [dec |]; [| discriminate H].
  destruct (dri_inst dec) as [| ? ? | ? ? ? ? ? | ? ? ? ? ? | ? ? ? ? ? | ? ? ? ? | ? ? ? rel | rel |];
    try (eapply IH; [lia | exact H]).
  - destruct (mc_slot_in_frame _ _ _); [eapply IH; [lia | exact H] | discriminate H].
  - destruct (mc_slot_in_frame _ _ _); [eapply IH; [lia | exact H] | discriminate H].
  - destruct (rv_eval_br_cond _ _ _);
      [destruct (add_rel_off pc rel); [eapply IH; [lia | exact H] | discriminate H]
      | eapply IH; [lia | exact H]].
  - destruct (add_rel_off pc rel); [eapply IH; [lia | exact H] | discriminate H].
  - exact H.
Qed.

Lemma rv_exec_steps_trans :
  forall n1 n2 insts sp0 pc0 rf0 m0 pc1 rf1 m1 res,
    rv_exec_steps n1 insts sp0 pc0 rf0 m0 = Some (pc1, rf1, m1) ->
    rv_exec_steps n2 insts sp0 pc1 rf1 m1 = Some res ->
    rv_exec_steps (n1 + n2) insts sp0 pc0 rf0 m0 = Some res.
Proof.
  intros n1; induction n1 as [| n1' IH]; intros n2 insts sp0 pc0 rf0 m0 pc1 rf1 m1 res H1 H2;
    cbn [rv_exec_steps] in *.
  - inversion H1; subst; exact H2.
  - destruct (lookup_rv_inst insts pc0) as [d |] eqn:El; [| discriminate H1].
    destruct (rv_exec_one_nonret d sp0 pc0 rf0 m0) as [[[pc' rf'] m'] |] eqn:Hs; [| discriminate H1].
    cbn [Nat.add rv_exec_steps]; rewrite El, Hs; exact (IH _ _ _ _ _ _ _ _ _ _ H1 H2).
Qed.

Lemma rv_exec_steps_to_exec_mem :
  forall n1 f2 insts sp0 pc0 rf0 m0 pc1 rf1 m1 res,
    rv_exec_steps n1 insts sp0 pc0 rf0 m0 = Some (pc1, rf1, m1) ->
    rv_exec_mem f2 insts pc1 sp0 rf1 m1 = Some res ->
    rv_exec_mem (n1 + f2) insts pc0 sp0 rf0 m0 = Some res.
Proof.
  intros n1; induction n1 as [| n1' IH]; intros f2 insts sp0 pc0 rf0 m0 pc1 rf1 m1 res H1 H2;
    cbn [rv_exec_steps] in H1.
  - inversion H1; subst; exact H2.
  - destruct (lookup_rv_inst insts pc0) as [dec |] eqn:Hlk; [| discriminate H1].
    destruct (rv_exec_one_nonret dec sp0 pc0 rf0 m0) as [[[pc' rf'] m'] |] eqn:Hs; [| discriminate H1].
    cbn [Nat.add].
    rewrite (rv_exec_mem_step_nonret (n1' + f2) insts sp0 pc0 rf0 m0 dec pc' rf' m' Hlk Hs).
    exact (IH _ _ _ _ _ _ _ _ _ _ H1 H2).
Qed.

Lemma rv_exec_mem_split_steps :
  forall n1 fuel insts sp0 pc0 rf0 m0 pc1 rf1 m1 res,
    rv_exec_mem fuel insts pc0 sp0 rf0 m0 = Some res ->
    rv_exec_steps n1 insts sp0 pc0 rf0 m0 = Some (pc1, rf1, m1) ->
    (n1 < fuel)%nat /\ rv_exec_mem (fuel - n1) insts pc1 sp0 rf1 m1 = Some res.
Proof.
  intros n1; induction n1 as [| n1' IH]; intros fuel insts sp0 pc0 rf0 m0 pc1 rf1 m1 res Hm Hs.
  - cbn [rv_exec_steps] in Hs; inversion Hs; subst; clear Hs.
    destruct fuel; [cbn [rv_exec_mem] in Hm; discriminate Hm |].
    split; [lia | rewrite Nat.sub_0_r; exact Hm].
  - cbn [rv_exec_steps] in Hs.
    destruct (lookup_rv_inst insts pc0) as [dec |] eqn:Hlk; [| discriminate Hs].
    destruct (rv_exec_one_nonret dec sp0 pc0 rf0 m0) as [[[pc' rf'] m'] |] eqn:Hst; [| discriminate Hs].
    destruct fuel as [| fuel']; [cbn [rv_exec_mem] in Hm; discriminate Hm |].
    rewrite (rv_exec_mem_step_nonret fuel' insts sp0 pc0 rf0 m0 dec pc' rf' m' Hlk Hst) in Hm.
    destruct (IH fuel' insts sp0 pc' rf' m' pc1 rf1 m1 res Hm Hs) as [Hlt Hrem].
    split; [lia | exact Hrem].
Qed.

Inductive rv_seg_tree : Type :=
| RST_Cut (sp_off : Z) (vrf : rv_val_regs) (astk : mc_sym_stack)
| RST_Ret (ret_e : cert_expr)
| RST_Branch (cond : cert_expr) (t_br f_br : rv_seg_tree).

Fixpoint rv_seg_wf (allowed : list (string * positive)) (ret_w : positive) (t : rv_seg_tree) {struct t} : Prop :=
  match t with
  | RST_Cut sp_off vrf astk =>
      (- mc_frame_cap <= sp_off <= 0)%Z /\
      rv_val_read 2%N vrf = MSV_StackPtr sp_off /\
      rv_val_regs_wf allowed vrf /\
      mc_sym_stack_wf allowed sp_off astk
  | RST_Ret ret_e =>
      wf_sym_expr allowed ret_w ret_e
  | RST_Branch cond dt df =>
      wf_sym_expr allowed 1%positive cond /\
      rv_seg_wf allowed ret_w dt /\
      rv_seg_wf allowed ret_w df
  end.

Variant rv_sym_step_res : Type :=
| RSSR_Next (next_pc : N) (sp_off' : Z) (vrf' : rv_val_regs) (astk' : mc_sym_stack)
| RSSR_Branch (cond : cert_expr) (tgt_pc next_pc : N)
| RSSR_Ret (ret_e : cert_expr).

Definition rv_sym_step_one
  (dec : decoded_rv_inst) (pc : N) (sp_off : Z) (vrf : rv_val_regs)
  (astk : mc_sym_stack) (ret_w : positive) : option rv_sym_step_res :=
  let next_pc := (pc + dri_len dec)%N in
  match dri_inst dec with
  | RV_Nop => Some (RSSR_Next next_pc sp_off vrf astk)
  | RV_Lui rd imm =>
      match rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk with
      | None => None
      | Some (sp_off', vrf', astk') => Some (RSSR_Next next_pc sp_off' vrf' astk')
      end
  | RV_AluImm op is_word rd rs1 imm =>
      let sv_opt :=
        match op, is_word, rv_val_read rs1 vrf with
        | RAI_Addi, false, MSV_StackPtr base_off =>
            let off' := (base_off + imm)%Z in
            if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
        | RAI_Addi, false, MSV_SavedReg r0 =>
            if Z.eqb imm 0%Z then Some (MSV_SavedReg r0) else None
        | _, _, MSV_Expr e => Some (MSV_Expr (sym_alu_imm op is_word e imm))
        | _, _, _ => None
        end
      in
      match sv_opt with
      | None => None
      | Some sv =>
          match rv_sym_step_write rd sv sp_off vrf astk with
          | None => None
          | Some (sp_off', vrf', astk') => Some (RSSR_Next next_pc sp_off' vrf' astk')
          end
      end
  | RV_AluReg op is_word rd rs1 rs2 =>
      let sv_opt :=
        if (match op with RAR_Add => negb is_word | _ => false end) &&
           (N.eqb rs1 0%N || N.eqb rs2 0%N)
        then
          let sv := if N.eqb rs1 0%N then rv_val_read rs2 vrf else rv_val_read rs1 vrf in
          match sv with MSV_Undef => None | _ => Some sv end
        else
          match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
          | MSV_Expr e1, MSV_Expr e2 => Some (MSV_Expr (sym_alu_reg op is_word e1 e2))
          | _, _ => None
          end
      in
      match sv_opt with
      | None => None
      | Some sv =>
          match rv_sym_step_write rd sv sp_off vrf astk with
          | None => None
          | Some (sp_off', vrf', astk') => Some (RSSR_Next next_pc sp_off' vrf' astk')
          end
      end
  | RV_Load sz is_signed rd rs1 imm =>
      match rv_val_read rs1 vrf with
      | MSV_StackPtr base_off =>
          let off := (base_off + imm)%Z in
          if mc_slot_in_frame sp_off off sz then
            match mc_sym_stk_load off sz is_signed astk with
            | None => None
            | Some sv =>
                match rv_sym_step_write rd sv sp_off vrf astk with
                | None => None
                | Some (sp_off', vrf', astk') => Some (RSSR_Next next_pc sp_off' vrf' astk')
                end
            end
          else None
      | _ => None
      end
  | RV_Store sz rs1 rs2 imm =>
      match rv_val_read rs1 vrf with
      | MSV_StackPtr base_off =>
          let off := (base_off + imm)%Z in
          if mc_slot_in_frame sp_off off sz then
            let sv := rv_val_read rs2 vrf in
            let sv_ok :=
              match sv with
              | MSV_Undef => false
              | MSV_Expr _ => true
              | MSV_SavedReg _ | MSV_StackPtr _ => mc_mem_size_eqb sz MS_8
              end
            in
            if sv_ok then
              Some (RSSR_Next next_pc sp_off vrf (mc_sym_stk_store off sz sv astk))
            else None
          else None
      | _ => None
      end
  | RV_Jal0 rel =>
      match add_rel_off pc rel with
      | None => None
      | Some tgt_pc => Some (RSSR_Next tgt_pc sp_off vrf astk)
      end
  | RV_Branch cond rs1 rs2 rel =>
      match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
      | MSV_Expr e1, MSV_Expr e2 =>
          match add_rel_off pc rel with
          | None => None
          | Some tgt_pc => Some (RSSR_Branch (sym_br_cond cond e1 e2) tgt_pc next_pc)
          end
      | _, _ => None
      end
  | RV_Ret =>
      if rv_sym_epilogue_ok sp_off vrf then
        match rv_val_read 10%N vrf with
        | MSV_Expr e_ret => Some (RSSR_Ret (rv_trunc_ret_expr ret_w e_ret))
        | _ => None
        end
      else None
  end.

Lemma rv_sym_step_one_wf :
  forall allowed dec pc sp_off vrf astk ret_w res,
    rv_supported_arg_width ret_w = true ->
    inst_no_word_mulh dec = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_wf allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    rv_sym_step_one dec pc sp_off vrf astk ret_w = Some res ->
    match res with
    | RSSR_Next _ sp_off' vrf' astk' =>
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        rv_val_read 2%N vrf' = MSV_StackPtr sp_off' /\
        rv_val_regs_wf allowed vrf' /\
        mc_sym_stack_wf allowed sp_off' astk'
    | RSSR_Branch cond _ _ => wf_sym_expr allowed 1%positive cond
    | RSSR_Ret ret_e => wf_sym_expr allowed ret_w ret_e
    end.
Proof.
  intros allowed dec pc sp_off vrf astk ret_w res Hrw Hnmul Hrng Hsp2 Hwf Hstk Hstep.
  unfold rv_sym_step_one in Hstep.
  destruct (dri_inst dec) as [| rd imm | op is_word rd rs1 imm | op is_word rd rs1 rs2 | sz is_signed rd rs1 imm | sz rs1 rs2 imm | cond rs1 rs2 rel | rel |] eqn:Ed.
  - inversion Hstep; subst; split; [exact Hrng | split; [exact Hsp2 | split; [exact Hwf | exact Hstk]]].
  - destruct (rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk)
      as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
    unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N); [discriminate Est |].
    inversion Est; subst; split; [exact Hrng' | split; [exact Hsp2' | split; [apply rv_val_regs_wf_write; [exact Hwf | apply wf_sym_bv_z] | exact Hstk]]].
  - set (sv_opt := match op, is_word, rv_val_read rs1 vrf with
      | RAI_Addi, false, MSV_StackPtr base_off =>
          if Z.leb (- mc_frame_cap) (base_off + imm) && Z.leb (base_off + imm) 0%Z
          then Some (MSV_StackPtr (base_off + imm)) else None
      | RAI_Addi, false, MSV_SavedReg r0 => if Z.eqb imm 0%Z then Some (MSV_SavedReg r0) else None
      | _, _, MSV_Expr e => Some (MSV_Expr (sym_alu_imm op is_word e imm))
      | _, _, _ => None end) in *.
    destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hstep].
    destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    assert (Hsv_wf : mc_sym_val_wf allowed sv).
    { subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | r0 | base_off] eqn:Er1.
      - destruct op, is_word; discriminate Esv.
      - assert (He_eq : sv = MSV_Expr (sym_alu_imm op is_word e1 imm)) by (destruct op, is_word; inversion Esv; reflexivity).
        rewrite He_eq; apply wf_sym_alu_imm; pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1.
      - destruct op, is_word; try discriminate Esv; destruct (Z.eqb imm 0%Z); try discriminate Esv; inversion Esv; exact I.
      - destruct op, is_word; try discriminate Esv; cbv zeta in Esv.
        destruct (Z.leb (- mc_frame_cap) (base_off + imm) && Z.leb (base_off + imm) 0%Z) eqn:Eb; try discriminate Esv.
        apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; inversion Esv; cbn [mc_sym_val_wf]; lia. }
    destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
    split; [exact Hrng' | split; [exact Hsp2' | split]]; unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
    + destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z); try discriminate Est.
      inversion Est; subst; apply rv_val_regs_wf_write; assumption.
    + inversion Est; subst; apply rv_val_regs_wf_write; assumption.
    + destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z) eqn:Eb; try discriminate Est.
      apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
      inversion Est; subst; eapply mc_sym_stk_prune_wf; [lia | exact Hstk].
    + inversion Est; subst; exact Hstk.
  - set (is_mv := ((match op with RAR_Add => negb is_word | _ => false end) &&
                   (N.eqb rs1 0%N || N.eqb rs2 0%N))%bool) in *.
    set (sv_opt := if is_mv then
      let sv := if N.eqb rs1 0%N then rv_val_read rs2 vrf else rv_val_read rs1 vrf in
      match sv with MSV_Undef => None | _ => Some sv end
    else match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
         | MSV_Expr e1, MSV_Expr e2 => Some (MSV_Expr (sym_alu_reg op is_word e1 e2))
         | _, _ => None end) in *.
    destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hstep].
    destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    assert (Hsv_wf : mc_sym_val_wf allowed sv).
    { destruct is_mv eqn:Emv.
      - subst sv_opt; cbn [fst snd] in Esv; destruct (N.eqb rs1 0%N).
        + destruct (rv_val_read rs2 vrf) eqn:Er2; try discriminate Esv; inversion Esv; subst sv; pose proof (Hwf rs2) as H2; rewrite Er2 in H2; exact H2.
        + destruct (rv_val_read rs1 vrf) eqn:Er1; try discriminate Esv; inversion Esv; subst sv; pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1.
      - subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Esv.
        destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Esv; inversion Esv; subst sv; clear Esv.
        assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
        { destruct is_word; [| left; reflexivity].
          right; unfold inst_no_word_mulh in Hnmul; rewrite Ed in Hnmul.
          destruct op; repeat split; intro C; discriminate C || discriminate Hnmul. }
        apply wf_sym_alu_reg; [exact Hok_m | pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1 | pose proof (Hwf rs2) as H2; rewrite Er2 in H2; exact H2]. }
    destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
    split; [exact Hrng' | split; [exact Hsp2' | split]]; unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
    + destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z); try discriminate Est.
      inversion Est; subst; apply rv_val_regs_wf_write; assumption.
    + inversion Est; subst; apply rv_val_regs_wf_write; assumption.
    + destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z) eqn:Eb; try discriminate Est.
      apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
      inversion Est; subst; eapply mc_sym_stk_prune_wf; [lia | exact Hstk].
    + inversion Est; subst; exact Hstk.
  - destruct (rv_val_read rs1 vrf) as [| | | base_off]; try discriminate Hstep.
    destruct (mc_slot_in_frame sp_off (base_off + imm) sz); [| discriminate Hstep].
    destruct (mc_sym_stk_load (base_off + imm) sz is_signed astk) as [sv |] eqn:Eload; [| discriminate Hstep].
    destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Eload) as Hsv_wf.
    destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
    split; [exact Hrng' | split; [exact Hsp2' | split]]; unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
    + destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z); try discriminate Est.
      inversion Est; subst; apply rv_val_regs_wf_write; assumption.
    + inversion Est; subst; apply rv_val_regs_wf_write; assumption.
    + destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z) eqn:Eb; try discriminate Est.
      apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
      inversion Est; subst; eapply mc_sym_stk_prune_wf; [lia | exact Hstk].
    + inversion Est; subst; exact Hstk.
  - destruct (rv_val_read rs1 vrf) as [| | | base_off]; try discriminate Hstep.
    destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hstep].
    destruct (match rv_val_read rs2 vrf with MSV_Undef => false | MSV_Expr _ => true | MSV_SavedReg _ | MSV_StackPtr _ => mc_mem_size_eqb sz MS_8 end); [| discriminate Hstep].
    inversion Hstep; subst; split; [exact Hrng | split; [exact Hsp2 | split; [exact Hwf | exact (mc_sym_stk_store_wf _ _ _ _ _ _ Eslot (Hwf rs2) Hstk)]]].
  - destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Hstep.
    destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Hstep.
    destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    pose proof (Hwf rs1) as H1; rewrite Er1 in H1; pose proof (Hwf rs2) as H2; rewrite Er2 in H2.
    destruct cond; apply wf_sym_icmp; assumption.
  - destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst; split; [exact Hrng | split; [exact Hsp2 | split; [exact Hwf | exact Hstk]]].
  - destruct (rv_sym_epilogue_ok sp_off vrf); [| discriminate Hstep].
    destruct (rv_val_read 10%N vrf) as [| e_ret | |] eqn:Er10; try discriminate Hstep.
    inversion Hstep; subst; clear Hstep.
    pose proof (Hwf 10%N) as Ha10; rewrite Er10 in Ha10.
    unfold rv_trunc_ret_expr; destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
    + apply Pos.eqb_eq in Ew64; subst ret_w; exact Ha10.
    + apply wf_sym_cast; [exact (rv_supported_arg_width_lt64 _ Hrw Ew64) | exact Ha10].
Qed.

Lemma rv_sym_step_one_sound :
  forall {Pa : Params} dec pc sp_off vrf astk ret_w res penv foracle rf0 rf mstk,
    rv_supported_arg_width ret_w = true ->
    inst_no_word_mulh dec = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk mstk ->
    rv_sym_step_one dec pc sp_off vrf astk ret_w = Some res ->
    match res with
    | RSSR_Next next_pc sp_off' vrf' astk' =>
        exists rf' mstk',
          rv_exec_one_nonret dec (rv_read_reg 2%N rf0) pc rf mstk = Some (next_pc, rf', mstk') /\
          (- mc_frame_cap <= sp_off' <= 0)%Z /\
          rv_val_read 2%N vrf' = MSV_StackPtr sp_off' /\
          rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf' rf' /\
          mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk' mstk'
    | RSSR_Branch cond tgt_pc next_pc =>
        exists b : bool,
          eval_closed_cert_expr penv foracle cond =
            raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
              (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
          rv_exec_one_nonret dec (rv_read_reg 2%N rf0) pc rf mstk =
            Some ((if b then tgt_pc else next_pc), rf, mstk)
    | RSSR_Ret ret_e =>
        dri_inst dec = RV_Ret /\
        rv_callee_saved_preserved rf0 rf /\
        rf 1%N = rf0 1%N /\
        eval_closed_cert_expr penv foracle ret_e =
          raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rf 10%N))))
    end.
Proof.
  intros Pa dec pc sp_off vrf astk ret_w res penv foracle rf0 rf mstk
         Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hstep.
  unfold rv_sym_step_one in Hstep.
  destruct (dri_inst dec) as
    [| rd imm
     | op is_word rd rs1 imm
     | op is_word rd rs1 rs2
     | sz is_signed rd rs1 imm
     | sz rs1 rs2 imm
     | cond rs1 rs2 rel
     | rel
     | ] eqn:Ed;
    try (unfold rv_exec_one_nonret; rewrite Ed).
  - inversion Hstep; subst; exists rf, mstk; repeat split; try lia; assumption.
  - destruct (rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk)
      as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
    destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                rd (MSV_Expr (ce_bv_z 64%positive imm)) (@Integers.repr 64%positive imm)
                sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk (eval_ce_bv_z penv foracle 64%positive imm) Est)
      as [Hag' Hastk'].
    eexists _, _; repeat split; try lia; assumption.
  - set (sv_opt := match op, is_word, rv_val_read rs1 vrf with
      | RAI_Addi, false, MSV_StackPtr base_off =>
          if Z.leb (- mc_frame_cap) (base_off + imm) && Z.leb (base_off + imm) 0%Z
          then Some (MSV_StackPtr (base_off + imm)) else None
      | RAI_Addi, false, MSV_SavedReg r0 => if Z.eqb imm 0%Z then Some (MSV_SavedReg r0) else None
      | _, _, MSV_Expr e => Some (MSV_Expr (sym_alu_imm op is_word e imm))
      | _, _, _ => None end) in *.
    destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hstep].
    destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    assert (Hval_sv : mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                        sv (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm)).
    { subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | r0 | base_off] eqn:Er1.
      - destruct op, is_word; discriminate Esv.
      - assert (He_eq : sv = MSV_Expr (sym_alu_imm op is_word e1 imm)) by (destruct op, is_word; inversion Esv; reflexivity).
        rewrite He_eq; cbn [mc_sym_val_agrees]; apply eval_sym_alu_imm_sound; pose proof (Hag rs1) as H1; rewrite Er1 in H1; exact H1.
      - destruct op, is_word; try discriminate Esv; destruct (Z.eqb imm 0%Z) eqn:Ez0; [| discriminate Esv].
        apply Z.eqb_eq in Ez0; subst imm; inversion Esv; subst sv; clear Esv.
        pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1 |- *;
          cbn [rv_eval_alu_imm rv_eval_alu_imm_raw]; rewrite H1, mc_add_ptr_zero; reflexivity.
      - destruct op, is_word; try discriminate Esv; cbv zeta in Esv.
        destruct (Z.leb (- mc_frame_cap) (base_off + imm) && Z.leb (base_off + imm) 0%Z) eqn:Erng; [| discriminate Esv].
        apply andb_true_iff in Erng as [Er1' Er2']; apply Z.leb_le in Er1'; apply Z.leb_le in Er2'; inversion Esv; subst sv; clear Esv.
        pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1 |- *; destruct H1 as [_ Hptr]; split; [lia |].
        cbn [rv_eval_alu_imm rv_eval_alu_imm_raw]; rewrite Hptr, mc_add_ptr_off; reflexivity. }
    destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
    destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                rd sv (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm)
                sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est) as [Hag' Hastk'].
    eexists _, _; repeat split; try lia; assumption.
  - set (is_mv := ((match op with RAR_Add => negb is_word | _ => false end) &&
                   (N.eqb rs1 0%N || N.eqb rs2 0%N))%bool) in *.
    set (sv_opt := if is_mv then
      let sv := if N.eqb rs1 0%N then rv_val_read rs2 vrf else rv_val_read rs1 vrf in
      match sv with MSV_Undef => None | _ => Some sv end
    else match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
         | MSV_Expr e1, MSV_Expr e2 => Some (MSV_Expr (sym_alu_reg op is_word e1 e2))
         | _, _ => None end) in *.
    destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hstep].
    destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    assert (Hval_sv : mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                        sv (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf))).
    { destruct is_mv eqn:Emv.
      - subst is_mv; apply andb_true_iff in Emv as [Hopm Hz].
        destruct op; try discriminate Hopm; destruct is_word; try discriminate Hopm; cbn [rv_eval_alu_reg rv_eval_alu_reg_raw].
        destruct (N.eqb rs1 0%N) eqn:Ez1.
        + apply N.eqb_eq in Ez1; subst rs1; replace (rv_read_reg 0%N rf) with (@Integers.zero 64%positive) by reflexivity; rewrite (@Integers.add_zero_l 64%positive).
          destruct (rv_val_read rs2 vrf) eqn:Er2; try discriminate Esv; inversion Esv; subst sv; pose proof (Hag rs2) as H2; rewrite Er2 in H2; exact H2.
        + cbn [orb] in Hz; apply N.eqb_eq in Hz; subst rs2; replace (rv_read_reg 0%N rf) with (@Integers.zero 64%positive) by reflexivity; rewrite (@Integers.add_zero 64%positive).
          destruct (rv_val_read rs1 vrf) eqn:Er1; try discriminate Esv; inversion Esv; subst sv; pose proof (Hag rs1) as H1; rewrite Er1 in H1; exact H1.
      - subst sv_opt; cbn [fst snd] in Esv.
        destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Esv.
        destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Esv; inversion Esv; subst sv; clear Esv.
        pose proof (Hag rs1) as H1; rewrite Er1 in H1; pose proof (Hag rs2) as H2; rewrite Er2 in H2; cbn [mc_sym_val_agrees] in H1, H2 |- *.
        assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
        { destruct is_word; [| left; reflexivity].
          right; unfold inst_no_word_mulh in Hnmul; rewrite Ed in Hnmul.
          destruct op; repeat split; intro C; discriminate C || discriminate Hnmul. }
        apply eval_sym_alu_reg_sound; assumption. }
    destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
    destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                rd sv (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf))
                sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est) as [Hag' Hastk'].
    eexists _, _; repeat split; try lia; assumption.
  - destruct (rv_val_read rs1 vrf) as [| | | base_off] eqn:Er1; try discriminate Hstep.
    destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hstep].
    destruct (mc_sym_stk_load (base_off + imm) sz is_signed astk) as [sv |] eqn:Eload; [| discriminate Hstep].
    destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
    assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
    pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1; destruct H1 as [_ Hptr1].
    pose proof (Hag 2%N) as H2; rewrite Hsp2 in H2; cbn [mc_sym_val_agrees] in H2; destruct H2 as [_ Hptr2].
    destruct Hsp0 as [Hsp0_cap _].
    assert (Hoff_eq : mc_addr_to_off (rv_read_reg 2%N rf0)
                        (@Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm)) = (base_off + imm)%Z)
      by (rewrite Hptr1, mc_add_ptr_off; apply mc_addr_to_off_add; [exact Hsp0_cap | lia]).
    assert (Hsp_eq : mc_addr_to_off (rv_read_reg 2%N rf0) (rv_read_reg 2%N rf) = sp_off)
      by (rewrite Hptr2; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
    rewrite Hoff_eq, Hsp_eq, Eslot.
    pose proof (mc_sym_stk_load_sound penv foracle (fun r0 => rv_read_reg r0 rf0)
                  (rv_read_reg 2%N rf0) (base_off + imm) sz is_signed astk mstk sv Hastk Eload) as Hval_sv.
    destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
    destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                rd sv (mc_stk_load mstk (base_off + imm) sz is_signed)
                sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est) as [Hag' Hastk'].
    eexists _, _; repeat split; try lia; assumption.
  - destruct (rv_val_read rs1 vrf) as [| | | base_off] eqn:Er1; try discriminate Hstep.
    destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hstep].
    destruct (match rv_val_read rs2 vrf with MSV_Undef => false | MSV_Expr _ => true | MSV_SavedReg _ | MSV_StackPtr _ => mc_mem_size_eqb sz MS_8 end) eqn:Esvok; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
    assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
    pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1; destruct H1 as [_ Hptr1].
    pose proof (Hag 2%N) as H2; rewrite Hsp2 in H2; cbn [mc_sym_val_agrees] in H2; destruct H2 as [_ Hptr2].
    destruct Hsp0 as [Hsp0_cap _].
    assert (Hoff_eq : mc_addr_to_off (rv_read_reg 2%N rf0)
                        (@Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm)) = (base_off + imm)%Z)
      by (rewrite Hptr1, mc_add_ptr_off; apply mc_addr_to_off_add; [exact Hsp0_cap | lia]).
    assert (Hsp_eq : mc_addr_to_off (rv_read_reg 2%N rf0) (rv_read_reg 2%N rf) = sp_off)
      by (rewrite Hptr2; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
    rewrite Hoff_eq, Hsp_eq, Eslot.
    assert (Hsz_match : match rv_val_read rs2 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
      by (destruct (rv_val_read rs2 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Esvok).
    pose proof (mc_sym_stk_store_agrees penv foracle (fun r0 => rv_read_reg r0 rf0)
                  (rv_read_reg 2%N rf0) (base_off + imm) sz (rv_val_read rs2 vrf) (rv_read_reg rs2 rf)
                  astk mstk Hsz_match (Hag rs2) Hastk) as Hastk'.
    eexists _, _; repeat split; try lia; assumption.
  - destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Hstep.
    destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Hstep.
    destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1.
    pose proof (Hag rs2) as H2; rewrite Er2 in H2; cbn [mc_sym_val_agrees] in H2.
    exists (rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)); split.
    + exact (eval_sym_br_cond_sound penv foracle cond e1 e2 (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) H1 H2).
    + cbv zeta iota; destruct (rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)); try rewrite Erel; reflexivity.
  - destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    eexists _, _; repeat split; try lia; try (cbv zeta iota; try rewrite Erel; reflexivity); assumption.
  - destruct (rv_sym_epilogue_ok sp_off vrf) eqn:Eep; [| discriminate Hstep].
    destruct (rv_val_read 10%N vrf) as [| e_ret | |] eqn:Er10; try discriminate Hstep.
    inversion Hstep; subst; clear Hstep.
    destruct (rv_sym_epilogue_ok_sound penv foracle rf0 sp_off vrf rf Hag Eep) as [Hcs Hra].
    repeat split; try assumption.
    unfold rv_trunc_ret_expr, rv_trunc_ret_val.
    pose proof (Hag 10%N) as Ha10; rewrite Er10 in Ha10; cbn [mc_sym_val_agrees] in Ha10.
    destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
    + apply Pos.eqb_eq in Ew64; subst ret_w; rewrite Ha10, (@Integers.repr_unsigned 64%positive); reflexivity.
    + assert (Hlt64 : (ret_w <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hrw Ew64).
      rewrite (eval_ce_trunc penv foracle 64%positive ret_w _ _ Hlt64 Ha10); reflexivity.
Qed.

Fixpoint summarize_rv64_seg_at
  (seg_name : string) (fuel : nat) (im : pos_trie decoded_rv_inst) (cut_pc : N)
  (req_step : bool) (visited : pos_trie unit)
  (pc : N) (sp_off : Z) (vrf : rv_val_regs) (astk : mc_sym_stack) (ret_w : positive)
  {struct fuel} : string + rv_seg_tree :=
  let loc (_ : unit) : string :=
    ("rv64 " ++ seg_name ++ " segment at pc=" ++ diag_N_hex pc ++
     " cut=" ++ diag_N_hex cut_pc ++ " sp-off=" ++ diag_Z_dec sp_off)%string
  in
  if negb req_step && N.eqb pc cut_pc then
    inr (RST_Cut sp_off vrf astk)
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
            match rv_sym_step_one dec pc sp_off vrf astk ret_w with
            | None =>
                inl (diag "mc-loop-mc" ("unsupported instruction or invalid frame access in " ++ loc tt))
            | Some (RSSR_Next next_pc sp_off' vrf' astk') =>
                summarize_rv64_seg_at seg_name fuel' im cut_pc false visited' next_pc sp_off' vrf' astk' ret_w
            | Some (RSSR_Branch cond tgt_pc next_pc) =>
                match summarize_rv64_seg_at seg_name fuel' im cut_pc false visited' tgt_pc sp_off vrf astk ret_w with
                | inl err => inl err
                | inr dt =>
                    match summarize_rv64_seg_at seg_name fuel' im cut_pc false visited' next_pc sp_off vrf astk ret_w with
                    | inl err => inl err
                    | inr df => inr (RST_Branch cond dt df)
                    end
                end
            | Some (RSSR_Ret ret_e) => inr (RST_Ret ret_e)
            end
        end
    end.

Definition summarize_rv64_seg
  (seg_name : string) (fuel : nat) (insts : list decoded_rv_inst) (cut_pc : N)
  (req_step : bool) (visited : list N)
  (pc : N) (sp_off : Z) (vrf : rv_val_regs) (astk : mc_sym_stack) (ret_w : positive)
  : string + rv_seg_tree :=
  summarize_rv64_seg_at seg_name fuel (pt_of_list_first dri_off insts) cut_pc req_step
    (pt_of_visited visited) pc sp_off vrf astk ret_w.

Theorem summarize_rv64_seg_at_wf :
  forall seg_name fuel insts im cut_pc req_step visited pc allowed sp_off vrf astk ret_w seg,
    (forall q, pt_get (N.succ_pos q) im = lookup_rv_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_wf allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    summarize_rv64_seg_at seg_name fuel im cut_pc req_step visited pc sp_off vrf astk ret_w = inr seg ->
    rv_seg_wf allowed ret_w seg.
Proof.
  intros seg_name fuel insts im cut_pc req_step visited pc allowed sp_off vrf astk ret_w seg Him.
  revert cut_pc req_step visited pc allowed sp_off vrf astk ret_w seg.
  induction fuel as [| fuel' IH];
    intros cut_pc req_step visited pc allowed sp_off vrf astk ret_w seg
           Hrw Hnmul Hrng Hsp2 Hwf Hstk Hsum;
    cbn [summarize_rv64_seg_at] in Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc).
    + inversion Hsum; subst; split; [exact Hrng | split; [exact Hsp2 | split; [exact Hwf | exact Hstk]]].
    + destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc).
    + inversion Hsum; subst; split; [exact Hrng | split; [exact Hsp2 | split; [exact Hwf | exact Hstk]]].
    + destruct (pt_has_n pc visited); [discriminate Hsum |].
      destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
      rewrite Him in Elook.
      assert (Hdec_mulh : inst_no_word_mulh dec = true).
      { clear -Elook Hnmul; induction insts as [| d rest IHl]; cbn in *; [discriminate |].
        apply andb_true_iff in Hnmul as [Hd Hr]; destruct (N.eqb (dri_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
      destruct (rv_sym_step_one dec pc sp_off vrf astk ret_w) as [res |] eqn:Est; [| discriminate Hsum].
      pose proof (rv_sym_step_one_wf allowed dec pc sp_off vrf astk ret_w res Hrw Hdec_mulh Hrng Hsp2 Hwf Hstk Est) as Hres.
      destruct res.
      * destruct Hres as (Hrng' & Hsp2' & Hwf' & Hstk').
        exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' Hwf' Hstk' Hsum).
      * destruct (summarize_rv64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w) as [| dt] eqn:Edt; [discriminate Hsum |].
        destruct (summarize_rv64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited) next_pc sp_off vrf astk ret_w) as [| df] eqn:Edf; [discriminate Hsum |].
        inversion Hsum; subst; split;
          [exact Hres
          | split; [exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hnmul Hrng Hsp2 Hwf Hstk Edt)
                   | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hnmul Hrng Hsp2 Hwf Hstk Edf)]].
      * inversion Hsum; subst; exact Hres.
Qed.

Theorem summarize_rv64_seg_wf :
  forall seg_name fuel insts cut_pc req_step visited pc allowed sp_off vrf astk ret_w seg,
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_wf allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    summarize_rv64_seg seg_name fuel insts cut_pc req_step visited pc sp_off vrf astk ret_w = inr seg ->
    rv_seg_wf allowed ret_w seg.
Proof.
  intros seg_name fuel insts cut_pc req_step visited pc allowed sp_off vrf astk ret_w seg
         Hrw Hnmul Hrng Hsp2 Hwf Hstk Hsum.
  eapply summarize_rv64_seg_at_wf with (insts := insts);
    [exact (pt_of_list_first_lookup_rv insts)
    | exact Hrw | exact Hnmul | exact Hrng | exact Hsp2 | exact Hwf | exact Hstk | exact Hsum].
Qed.

Fixpoint rv_seg_exec_spec
  {Pa : Params} (penv : param_env Pa) (foracle : freeze_oracle)
  (insts : list decoded_rv_inst) (cut_pc : N) (req_step : bool)
  (pc : N) (rf0 rf : rv_regfile) (mstk : mc_stack_mem) (ret_w : positive)
  (t : rv_seg_tree) {struct t} : Prop :=
  match t with
  | RST_Cut sp_off' vrf' astk' =>
      exists n rf' mstk',
        (req_step = true -> (1 <= n)%nat) /\
        rv_exec_steps n insts (rv_read_reg 2%N rf0) pc rf mstk = Some (cut_pc, rf', mstk') /\
        (- mc_frame_cap <= sp_off' <= 0)%Z /\
        rv_val_read 2%N vrf' = MSV_StackPtr sp_off' /\
        rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf' rf' /\
        mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk' mstk'
  | RST_Ret ret_e =>
      exists fuel_end rf_end mstk_end,
        rv_exec_mem fuel_end insts pc (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
        rv_callee_saved_preserved rf0 rf_end /\
        rf_end 1%N = rf0 1%N /\
        eval_closed_cert_expr penv foracle ret_e =
          raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rf_end 10%N))))
  | RST_Branch cond dt df =>
      exists b : bool,
        eval_closed_cert_expr penv foracle cond =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
            (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
        rv_seg_exec_spec penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w (if b then dt else df)
  end.

Lemma rv_seg_exec_spec_step_front :
  forall {Pa : Params} penv foracle insts cut_pc req_step pc0 pc1 rf0 rf_a m_a rf_b m_b ret_w t,
    rv_exec_steps 1 insts (rv_read_reg 2%N rf0) pc0 rf_a m_a = Some (pc1, rf_b, m_b) ->
    @rv_seg_exec_spec Pa penv foracle insts cut_pc false pc1 rf0 rf_b m_b ret_w t ->
    @rv_seg_exec_spec Pa penv foracle insts cut_pc req_step pc0 rf0 rf_a m_a ret_w t.
Proof.
  intros Pa penv foracle insts cut_pc req_step pc0 pc1 rf0 rf_a m_a rf_b m_b ret_w t H1 Hspec.
  induction t as [sp_off' vrf' astk' | ret_e | cond dt IHt df IHf]; cbn [rv_seg_exec_spec] in *.
  - destruct Hspec as (n & rf' & mstk' & _ & Hn & Hrng & Hsp & Hag & Hastk).
    exists (1 + n)%nat, rf', mstk';
      split; [intro; lia | split; [exact (rv_exec_steps_trans _ _ _ _ _ _ _ _ _ _ _ H1 Hn) | split; [exact Hrng | split; [exact Hsp | split; [exact Hag | exact Hastk]]]]].
  - destruct Hspec as (fuel_end & rf_end & mstk_end & Hm & Hcs & Hra & Hev).
    exists (1 + fuel_end)%nat, rf_end, mstk_end;
      split; [exact (rv_exec_steps_to_exec_mem _ _ _ _ _ _ _ _ _ _ _ H1 Hm) | split; [exact Hcs | split; [exact Hra | exact Hev]]].
  - destruct Hspec as [b [Hbc Hsub]]; exists b; split; [exact Hbc |].
    destruct b; [exact (IHt Hsub) | exact (IHf Hsub)].
Qed.

Theorem summarize_rv64_seg_at_sound :
  forall {Pa : Params} seg_name fuel insts im cut_pc req_step visited pc sp_off vrf astk ret_w seg
         penv foracle rf0 rf mstk,
    (forall q, pt_get (N.succ_pos q) im = lookup_rv_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk mstk ->
    summarize_rv64_seg_at seg_name fuel im cut_pc req_step visited pc sp_off vrf astk ret_w = inr seg ->
    rv_seg_exec_spec penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w seg.
Proof.
  intros Pa seg_name fuel insts im cut_pc req_step visited pc sp_off vrf astk ret_w seg
         penv foracle rf0 rf mstk Him.
  revert cut_pc req_step visited pc sp_off vrf astk ret_w seg penv foracle rf0 rf mstk.
  induction fuel as [| fuel' IH];
    intros cut_pc req_step visited pc sp_off vrf astk ret_w seg
           penv foracle rf0 rf mstk Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hsum;
    cbn [summarize_rv64_seg_at] in Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc) eqn:Ecut.
    + apply andb_true_iff in Ecut as [Hreq Hpc]; apply N.eqb_eq in Hpc; subst pc.
      destruct req_step; [discriminate Hreq |].
      inversion Hsum; subst seg; clear Hsum.
      exists 0%nat, rf, mstk; split; [intro C; discriminate C | split; [reflexivity | split; [exact Hrng | split; [exact Hsp2 | split; [exact Hag | exact Hastk]]]]].
    + destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc) eqn:Ecut.
    + apply andb_true_iff in Ecut as [Hreq Hpc]; apply N.eqb_eq in Hpc; subst pc.
      destruct req_step; [discriminate Hreq |].
      inversion Hsum; subst seg; clear Hsum.
      exists 0%nat, rf, mstk; split; [intro C; discriminate C | split; [reflexivity | split; [exact Hrng | split; [exact Hsp2 | split; [exact Hag | exact Hastk]]]]].
    + destruct (pt_has_n pc visited); [discriminate Hsum |].
      destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
      rewrite Him in Elook.
      assert (Hdec_mulh : inst_no_word_mulh dec = true).
      { clear -Elook Hnmul; induction insts as [| d rest IHl]; cbn in *; [discriminate |].
        apply andb_true_iff in Hnmul as [Hd Hr]; destruct (N.eqb (dri_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
      destruct (rv_sym_step_one dec pc sp_off vrf astk ret_w) as [res |] eqn:Est; [| discriminate Hsum].
      pose proof (rv_sym_step_one_sound dec pc sp_off vrf astk ret_w res penv foracle rf0 rf mstk
                    Hrw Hdec_mulh Hsp0 Hrng Hsp2 Hag Hastk Est) as Hres.
      destruct res.
      * destruct Hres as (rf1 & mstk1 & Hone & Hrng' & Hsp2' & Hag' & Hastk').
        assert (H1 : rv_exec_steps 1 insts (rv_read_reg 2%N rf0) pc rf mstk = Some (next_pc, rf1, mstk1))
          by (cbn [rv_exec_steps]; rewrite Elook, Hone; reflexivity).
        exact (rv_seg_exec_spec_step_front _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1
                 (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hnmul Hsp0 Hrng' Hsp2' Hag' Hastk' Hsum)).
      * destruct (summarize_rv64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w) as [| dt] eqn:Edt; [discriminate Hsum |].
        destruct (summarize_rv64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited) next_pc sp_off vrf astk ret_w) as [| df] eqn:Edf; [discriminate Hsum |].
        inversion Hsum; subst seg; clear Hsum.
        destruct Hres as [b [Hbc Hone]].
        cbn [rv_seg_exec_spec]; exists b; split; [exact Hbc |].
        assert (H1 : rv_exec_steps 1 insts (rv_read_reg 2%N rf0) pc rf mstk = Some ((if b then tgt_pc else next_pc), rf, mstk))
          by (cbn [rv_exec_steps]; rewrite Elook, Hone; reflexivity).
        eapply rv_seg_exec_spec_step_front; [exact H1 |].
        destruct b;
          [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Edt)
          | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Edf)].
      * inversion Hsum; subst seg; clear Hsum.
        destruct Hres as (Hret & Hcs & Hra & Hev).
        exists 1%nat, rf, mstk; split; [| split; [exact Hcs | split; [exact Hra | exact Hev]]].
        cbn [rv_exec_mem]; rewrite Elook, Hret; reflexivity.
Qed.

Theorem summarize_rv64_seg_sound :
  forall {Pa : Params} seg_name fuel insts cut_pc req_step visited pc sp_off vrf astk ret_w seg
         penv foracle rf0 rf mstk,
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk mstk ->
    summarize_rv64_seg seg_name fuel insts cut_pc req_step visited pc sp_off vrf astk ret_w = inr seg ->
    rv_seg_exec_spec penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w seg.
Proof.
  intros Pa seg_name fuel insts cut_pc req_step visited pc sp_off vrf astk ret_w seg
         penv foracle rf0 rf mstk Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hsum.
  eapply summarize_rv64_seg_at_sound with (insts := insts);
    [exact (pt_of_list_first_lookup_rv insts)
    | exact Hrw | exact Hnmul | exact Hsp0 | exact Hrng | exact Hsp2
    | exact Hag | exact Hastk | exact Hsum].
Qed.

Lemma rv_exec_mem_det :
  forall f1 f2 insts pc sp0 rf mstk r1 r2,
    rv_exec_mem f1 insts pc sp0 rf mstk = Some r1 ->
    rv_exec_mem f2 insts pc sp0 rf mstk = Some r2 ->
    r1 = r2.
Proof.
  intros f1 f2 insts pc sp0 rf mstk r1 r2 H1 H2.
  pose proof (rv_exec_mem_mono f1 (Nat.max f1 f2) insts pc sp0 rf mstk r1 (Nat.le_max_l f1 f2) H1) as Hm1.
  pose proof (rv_exec_mem_mono f2 (Nat.max f1 f2) insts pc sp0 rf mstk r2 (Nat.le_max_r f1 f2) H2) as Hm2.
  rewrite Hm1 in Hm2; inversion Hm2; reflexivity.
Qed.



