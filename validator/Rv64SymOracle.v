(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * RV64 Concrete Oracle & Single-Step Symbolic Oracle ([CertValidator.Rv64SymOracle])

    Purpose:
      Provides Layer-3 differential oracle helpers ([rv_eval_bytes_concrete],
      [rv_decode_bytes_ok]), the single-step symbolic oracle ([rv_step_sym_oracle],
      [rv_step_sym_oracle_sound]), and 128-bit div/rem width-reduction lemmas.

    Trust Contract & Fail-Closed Boundary:
      [rv_step_sym_oracle] returns [None] on decode failure or non-single/unsupported
      instructions; [Some] outputs are proven sound by [rv_step_sym_oracle_sound]. Extracted to
      OCaml via [Extract.v].

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{CertFormat,AigLrat,
      AlgRules,CfgDag,Elf64Spec,McFrameMem,McIsaCommon,Rv64Decode,Rv64ExecSym,Rv64DagProof}];
      zero custom axioms.

    Section Outline:
      6. Concrete differential oracle helpers; 7. Single-step symbolic oracle
      ([rv_step_sym_oracle]), [rv_step_sym_oracle_sound], and [sail_divrem_128_width_reduce]. *)

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

(** ** 6. Concrete Extracted ISA Oracle Helpers (Layer-3 Differential Harness) *)

Definition rv_regfile_of_list (regs : list N) : rv_regfile :=
  fun r =>
    match List.nth_error regs (N.to_nat r) with
    | Some v => @Integers.repr 64%positive (Z.of_N v)
    | None => @Integers.zero 64%positive
    end.

Definition rv_regfile_to_list_aux : nat -> nat -> rv_regfile -> list N :=
  fix go idx count rf {struct count} :=
    match count with
    | O => []
    | S count' =>
        Z.to_N (@Integers.unsigned 64%positive (rv_read_reg (N.of_nat idx) rf))
        :: go (S idx) count' rf
    end.

Definition rv_regfile_to_list (rf : rv_regfile) : list N :=
  rv_regfile_to_list_aux 0%nat 32%nat rf.

Definition rv_decode_bytes_ok (rvc : bool) (code : list N) : bool :=
  match decode_rv64_bytes rvc code with
  | inr _ => true
  | inl _ => false
  end.

Definition rv_eval_bytes_concrete
  (rvc : bool) (fuel : nat) (code : list N) (init_regs : list N)
  : string + list N :=
  match decode_rv64_bytes rvc code with
  | inl err => inl err
  | inr insts =>
      match rv_exec fuel insts 0%N (rv_regfile_of_list init_regs) with
      | None => inl "rv_exec returned None"
      | Some rf_end => inr (rv_regfile_to_list rf_end)
      end
  end.

(** ** 7. Proven Single-Step Symbolic Oracle Export (Stage-2 Sail/SMT Reference) *)

Definition rv_oracle_reg_name (r : N) : string :=
  if N.eqb r 0%N then "x0" else if N.eqb r 1%N then "x1" else if N.eqb r 2%N then "x2"
  else if N.eqb r 3%N then "x3" else if N.eqb r 4%N then "x4" else if N.eqb r 5%N then "x5"
  else if N.eqb r 6%N then "x6" else if N.eqb r 7%N then "x7" else if N.eqb r 8%N then "x8"
  else if N.eqb r 9%N then "x9" else if N.eqb r 10%N then "x10" else if N.eqb r 11%N then "x11"
  else if N.eqb r 12%N then "x12" else if N.eqb r 13%N then "x13" else if N.eqb r 14%N then "x14"
  else if N.eqb r 15%N then "x15" else if N.eqb r 16%N then "x16" else if N.eqb r 17%N then "x17"
  else if N.eqb r 18%N then "x18" else if N.eqb r 19%N then "x19" else if N.eqb r 20%N then "x20"
  else if N.eqb r 21%N then "x21" else if N.eqb r 22%N then "x22" else if N.eqb r 23%N then "x23"
  else if N.eqb r 24%N then "x24" else if N.eqb r 25%N then "x25" else if N.eqb r 26%N then "x26"
  else if N.eqb r 27%N then "x27" else if N.eqb r 28%N then "x28" else if N.eqb r 29%N then "x29"
  else if N.eqb r 30%N then "x30" else "x31".

Definition rv_oracle_srf : rv_sym_regs :=
  fun r =>
    if N.eqb r 0%N then CE_BvConst 64%positive 0%N
    else CE_Var (rv_oracle_reg_name r) 64%positive.

Record rv_sym_step_out : Set := mk_rv_sym_step_out {
  rso_len : N;
  rso_rd_write : option (N * cert_expr);
  rso_pc_kind : N;
  rso_br_cond : option cert_expr;
  rso_rel_bytes : Z;
}.

Definition rv_oracle_wr (rd : N) (e : cert_expr) : option (N * cert_expr) :=
  if N.eqb rd 0%N then None else Some (rd, e).

Definition rv_step_sym_oracle (rvc : bool) (code : list N) : option rv_sym_step_out :=
  match decode_rv64_bytes rvc code with
  | inr [dec] =>
      let len := dri_len dec in
      match dri_inst dec with
      | RV_Nop => Some (mk_rv_sym_step_out len None 0%N None 0%Z)
      | RV_Lui rd imm =>
          Some (mk_rv_sym_step_out len (rv_oracle_wr rd (ce_bv_z 64%positive imm)) 0%N None 0%Z)
      | RV_AluImm op is_word rd rs1 imm =>
          let e := sym_alu_imm op is_word (rv_sym_read rs1 rv_oracle_srf) imm in
          Some (mk_rv_sym_step_out len (rv_oracle_wr rd e) 0%N None 0%Z)
      | RV_AluReg op is_word rd rs1 rs2 =>
          let e := sym_alu_reg op is_word (rv_sym_read rs1 rv_oracle_srf) (rv_sym_read rs2 rv_oracle_srf) in
          Some (mk_rv_sym_step_out len (rv_oracle_wr rd e) 0%N None 0%Z)
      | RV_Branch cond rs1 rs2 rel =>
          let ce := sym_br_cond cond (rv_sym_read rs1 rv_oracle_srf) (rv_sym_read rs2 rv_oracle_srf) in
          Some (mk_rv_sym_step_out len None 2%N (Some ce) rel)
      | RV_Jal0 rel =>
          Some (mk_rv_sym_step_out len None 1%N None rel)
      | RV_Ret =>
          Some (mk_rv_sym_step_out len None 3%N None 0%Z)
      | RV_Load _ _ _ _ _ | RV_Store _ _ _ _ => None
      end
  | _ => None
  end.

Definition rv_inst_regs_lt32 (inst : rv_inst) : Prop :=
  match inst with
  | RV_Nop | RV_Jal0 _ | RV_Ret => True
  | RV_Lui rd _ => (rd < 32)%N
  | RV_AluImm _ _ rd rs1 _ => (rd < 32)%N /\ (rs1 < 32)%N
  | RV_AluReg _ _ rd rs1 rs2 => (rd < 32)%N /\ (rs1 < 32)%N /\ (rs2 < 32)%N
  | RV_Load _ _ rd rs1 _ => (rd < 32)%N /\ (rs1 < 32)%N
  | RV_Store _ rs1 rs2 _ => (rs1 < 32)%N /\ (rs2 < 32)%N
  | RV_Branch _ rs1 rs2 _ => (rs1 < 32)%N /\ (rs2 < 32)%N
  end.

Lemma bit_slice_5_lt32 : forall w lo, (bit_slice w lo 5%N < 32)%N.
Proof.
  intros w lo; unfold bit_slice; apply N.mod_lt; discriminate.
Qed.

Lemma c_reg_lt32 : forall bits3, (c_reg bits3 < 32)%N.
Proof.
  intro bits3; unfold c_reg; pose proof (N.mod_lt bits3 8%N ltac:(discriminate)); lia.
Qed.

Lemma decode_rvc_hw_regs_lt32 : forall hw inst,
  decode_rvc_hw hw = Some inst -> rv_inst_regs_lt32 inst.
Proof.
  intros hw inst H; unfold decode_rvc_hw in H.
  destruct (N.eqb hw 0%N); [discriminate |].
  pose proof (bit_slice_5_lt32 hw 7%N); pose proof (bit_slice_5_lt32 hw 2%N).
  pose proof (c_reg_lt32 (bit_slice hw 7%N 3%N)); pose proof (c_reg_lt32 (bit_slice hw 2%N 3%N)).
  cbv zeta in H;
  repeat match type of H with
  | Some _ = Some _ => inversion H; subst; cbn [rv_inst_regs_lt32]; (lia || (repeat split; lia))
  | None = Some _ => discriminate H
  | (if true then _ else _) = _ => cbv iota in H
  | (if false then _ else _) = _ => cbv iota in H
  | (if ?b then _ else _) = _ => destruct b
  end.
Qed.

Lemma decode_rv32_word_regs_lt32 : forall w inst,
  decode_rv32_word w = Some inst -> rv_inst_regs_lt32 inst.
Proof.
  intros w inst H; unfold decode_rv32_word in H.
  pose proof (bit_slice_5_lt32 w 7%N); pose proof (bit_slice_5_lt32 w 15%N); pose proof (bit_slice_5_lt32 w 20%N).
  cbv zeta in H;
  repeat match type of H with
  | Some _ = Some _ => inversion H; subst; cbn [rv_inst_regs_lt32]; (lia || (repeat split; lia))
  | None = Some _ => discriminate H
  | (if true then _ else _) = _ => cbv iota in H
  | (if false then _ else _) = _ => cbv iota in H
  | (if ?b then _ else _) = _ => destruct b
  | Datatypes.option_map _ ?x = _ => destruct x as [op |]; cbn [Datatypes.option_map] in H; [| discriminate H]
  end.
Qed.

Lemma decode_rv64_stream_acc_regs_lt32 : forall fuel rvc cur cur_off acc insts,
  Forall (fun d => rv_inst_regs_lt32 (dri_inst d)) acc ->
  decode_rv64_stream_acc fuel rvc cur cur_off acc = inr insts ->
  Forall (fun d => rv_inst_regs_lt32 (dri_inst d)) insts.
Proof.
  induction fuel as [| fuel' IH]; intros rvc [| b0 r0] cur_off acc insts Hacc H;
    cbn [decode_rv64_stream_acc] in H.
  - inversion H; subst insts; rewrite elf_rev_tr_eq, Forall_forall in *;
      intros x Hx; apply Hacc; rewrite in_rev; exact Hx.
  - discriminate H.
  - inversion H; subst insts; rewrite elf_rev_tr_eq, Forall_forall in *;
      intros x Hx; apply Hacc; rewrite in_rev; exact Hx.
  - destruct (take_u16_le (b0 :: r0)) as [[hw rest2] |]; [| discriminate H].
    destruct (negb (N.eqb (N.modulo hw 4%N) 3%N)).
    + destruct (negb rvc); [discriminate H |].
      destruct (decode_rvc_hw hw) as [inst |] eqn:Ed; [| discriminate H].
      eapply IH; [| exact H]; constructor; [exact (decode_rvc_hw_regs_lt32 hw inst Ed) | exact Hacc].
    + destruct (take_u32_le (b0 :: r0)) as [[w rest4] |]; [| discriminate H].
      destruct (decode_rv32_word w) as [inst |] eqn:Ed; [| discriminate H].
      eapply IH; [| exact H]; constructor; [exact (decode_rv32_word_regs_lt32 w inst Ed) | exact Hacc].
Qed.

Lemma decode_rv64_bytes_single_regs_lt32 : forall rvc code dec,
  decode_rv64_bytes rvc code = inr [dec] ->
  rv_inst_regs_lt32 (dri_inst dec) /\ inst_no_word_mulh dec = true.
Proof.
  intros rvc code dec H.
  pose proof (decode_rv64_bytes_no_word_mulh rvc code [dec] H) as Hnm.
  cbn [forallb andb] in Hnm; rewrite andb_true_r in Hnm; split; [| exact Hnm].
  unfold decode_rv64_bytes in H.
  destruct (Nat.eqb (elf_length_tr code) 0 || negb (Nat.eqb (Nat.modulo (elf_length_tr code) 2) 0));
    [discriminate H |].
  destruct (negb rvc && negb (Nat.eqb (Nat.modulo (elf_length_tr code) 4) 0));
    [discriminate H |].
  pose proof (decode_rv64_stream_acc_regs_lt32 _ rvc code 0 [] [dec] (Forall_nil _) H) as Hfa.
  inversion Hfa; assumption.
Qed.

Definition rv_penv_matches_rf {Pa : Params} (penv : param_env Pa) (rf : rv_regfile) : Prop :=
  forall r, (1 <= r < 32)%N ->
    penv (rv_oracle_reg_name r) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg r rf))).

Lemma rv_oracle_srf_eval :
  forall {Pa : Params} (penv : param_env Pa) foracle rf r,
    rv_penv_matches_rf penv rf ->
    (r < 32)%N ->
    eval_closed_cert_expr penv foracle (rv_sym_read r rv_oracle_srf) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg r rf))).
Proof.
  intros Pa penv foracle rf r Hm Hlt.
  unfold rv_sym_read, rv_oracle_srf.
  destruct (N.eqb r 0%N) eqn:Er0.
  - apply N.eqb_eq in Er0; subst r; unfold rv_read_reg;
      cbn [N.eqb]; rewrite eval_ce_const, repr_zero_N; reflexivity.
  - apply N.eqb_neq in Er0; assert (Hr : (1 <= r < 32)%N) by lia.
    unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite (Hm r Hr);
      cbn [lookup_let_val check_scalar_width Pos.eqb]; reflexivity.
Qed.

Theorem rv_step_sym_oracle_sound :
  forall {Pa : Params} rvc code dec out (penv : param_env Pa) foracle rf,
    decode_rv64_bytes rvc code = inr [dec] ->
    rv_step_sym_oracle rvc code = Some out ->
    rv_penv_matches_rf penv rf ->
    rso_len out = dri_len dec /\
    (forall rd e,
       rso_rd_write out = Some (rd, e) ->
       (rd < 32)%N /\
       match dri_inst dec with
       | RV_Lui rd' imm =>
           rd = rd' /\
           eval_closed_cert_expr penv foracle e =
             raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.repr 64%positive imm)))
       | RV_AluImm op is_word rd' rs1 imm =>
           rd = rd' /\
           eval_closed_cert_expr penv foracle e =
             raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm)))
       | RV_AluReg op is_word rd' rs1 rs2 =>
           rd = rd' /\
           eval_closed_cert_expr penv foracle e =
             raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
               (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf))))
       | _ => False
       end) /\
    (forall cond rs1 rs2 rel,
       dri_inst dec = RV_Branch cond rs1 rs2 rel ->
       rso_pc_kind out = 2%N /\ rso_rel_bytes out = rel /\
       exists ce, rso_br_cond out = Some ce /\
         eval_closed_cert_expr penv foracle ce =
           raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
             (if rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)
              then @Integers.one 1%positive else @Integers.zero 1%positive)))).
Proof.
  intros Pa rvc code dec out penv foracle rf Hdec Hso Hm.
  pose proof (decode_rv64_bytes_single_regs_lt32 rvc code dec Hdec) as [Hreg Hnmul].
  unfold rv_step_sym_oracle in Hso; rewrite Hdec in Hso.
  destruct (dri_inst dec) as
    [| rd imm | op is_word rd rs1 imm | op is_word rd rs1 rs2
     | sz sgn rd rs1 imm | sz rs1 rs2 imm | cond rs1 rs2 rel | rel |] eqn:Ed;
    cbn [rv_inst_regs_lt32] in Hreg; unfold inst_no_word_mulh in Hnmul; rewrite Ed in Hnmul.
  - inversion Hso; subst out;
      repeat split; intros; try discriminate;
      match goal with H : _ = RV_Branch _ _ _ _ |- _ => discriminate H end.
  - inversion Hso; subst out; cbn [rso_len rso_rd_write rso_pc_kind rso_br_cond rso_rel_bytes].
    split; [reflexivity | split].
    + intros rd0 e H; unfold rv_oracle_wr in H; destruct (N.eqb rd 0%N);
        [discriminate H | inversion H; subst; split; [lia | split; [reflexivity | apply eval_ce_bv_z]]].
    + intros ? ? ? ? Hbr; discriminate Hbr.
  - inversion Hso; subst out; cbn [rso_len rso_rd_write rso_pc_kind rso_br_cond rso_rel_bytes].
    split; [reflexivity | split].
    + intros rd0 e H; unfold rv_oracle_wr in H; destruct (N.eqb rd 0%N); [discriminate H | inversion H; subst].
      split; [lia | split; [reflexivity |]].
      apply eval_sym_alu_imm_sound; apply rv_oracle_srf_eval; [exact Hm | lia].
    + intros ? ? ? ? Hbr; discriminate Hbr.
  - inversion Hso; subst out; cbn [rso_len rso_rd_write rso_pc_kind rso_br_cond rso_rel_bytes].
    split; [reflexivity | split].
    + intros rd0 e H; unfold rv_oracle_wr in H; destruct (N.eqb rd 0%N); [discriminate H | inversion H; subst].
      assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
      { destruct is_word; [| left; reflexivity].
        right; destruct op; repeat split; intro C; discriminate C || discriminate Hnmul. }
      split; [lia | split; [reflexivity |]].
      apply eval_sym_alu_reg_sound;
        [exact Hok_m | apply rv_oracle_srf_eval; [exact Hm | lia] | apply rv_oracle_srf_eval; [exact Hm | lia]].
    + intros ? ? ? ? Hbr; discriminate Hbr.
  - discriminate Hso.
  - discriminate Hso.
  - inversion Hso; subst out; cbn [rso_len rso_rd_write rso_pc_kind rso_br_cond rso_rel_bytes].
    split; [reflexivity | split; [intros ? ? Hw; discriminate Hw |]].
    intros cond' rs1' rs2' rel' Hbr; inversion Hbr; subst.
    split; [reflexivity | split; [reflexivity | eexists; split; [reflexivity |]]].
    apply eval_sym_br_cond_sound; apply rv_oracle_srf_eval; [exact Hm | lia | exact Hm | lia].
  - inversion Hso; subst out;
      repeat split; intros; try discriminate;
      match goal with H : _ = RV_Branch _ _ _ _ |- _ => discriminate H end.
  - inversion Hso; subst out;
      repeat split; intros; try discriminate;
      match goal with H : _ = RV_Branch _ _ _ _ |- _ => discriminate H end.
Qed.

Lemma sail_divrem_128_width_reduce :
  forall w (a b : @Integers.bit_int w),
    (w = 32%positive \/ w = 64%positive) ->
    @Integers.unsigned w b <> 0%Z ->
    @Integers.divs 128%positive
      (@Integers.repr 128%positive (@Integers.unsigned w a))
      (@Integers.repr 128%positive (@Integers.unsigned w b)) =
      @Integers.repr 128%positive (@Integers.unsigned w (@Integers.divu w a b)) /\
    @Integers.mods 128%positive
      (@Integers.repr 128%positive (@Integers.unsigned w a))
      (@Integers.repr 128%positive (@Integers.unsigned w b)) =
      @Integers.repr 128%positive (@Integers.unsigned w (@Integers.modu w a b)) /\
    @Integers.divs 128%positive
      (@Integers.repr 128%positive (@Integers.signed w a))
      (@Integers.repr 128%positive (@Integers.signed w b)) =
      (if Z.eqb (@Integers.signed w a) (@Integers.min_signed w) &&
          Z.eqb (@Integers.signed w b) (-1)%Z
       then @Integers.repr 128%positive (@Integers.half_modulus w)
       else @Integers.repr 128%positive (@Integers.signed w (@Integers.divs w a b))) /\
    @Integers.mods 128%positive
      (@Integers.repr 128%positive (@Integers.signed w a))
      (@Integers.repr 128%positive (@Integers.signed w b)) =
      (if Z.eqb (@Integers.signed w a) (@Integers.min_signed w) &&
          Z.eqb (@Integers.signed w b) (-1)%Z
       then @Integers.zero 128%positive
       else @Integers.repr 128%positive (@Integers.signed w (@Integers.mods w a b))).
Proof.
  intros w a b Hw Hbnz.
  assert (Hmodw : (@Integers.modulus w <= @Integers.half_modulus 128%positive)%Z)
    by (destruct Hw as [-> | ->]; vm_compute; discriminate).
  assert (Hhalfw : (2 <= @Integers.half_modulus w)%Z)
    by (destruct Hw as [-> | ->]; vm_compute; discriminate).
  assert (Hra := @Integers.unsigned_range w a).
  assert (Hrb := @Integers.unsigned_range w b).
  assert (Hrsa := @Integers.signed_range w a).
  assert (Hrsb := @Integers.signed_range w b).
  assert (Hmin128 : @Integers.min_signed 128%positive = (- @Integers.half_modulus 128%positive)%Z) by reflexivity.
  assert (Hmax128 : @Integers.max_signed 128%positive = (@Integers.half_modulus 128%positive - 1)%Z) by reflexivity.
  assert (Hmaxuw : @Integers.max_unsigned w = (@Integers.modulus w - 1)%Z) by reflexivity.
  assert (Hminw : @Integers.min_signed w = (- @Integers.half_modulus w)%Z) by reflexivity.
  assert (Hmaxw : @Integers.max_signed w = (@Integers.half_modulus w - 1)%Z) by reflexivity.
  assert (Hmod_half : @Integers.modulus w = (2 * @Integers.half_modulus w)%Z)
    by (rewrite Integers.half_modulus_modulus; reflexivity).
  assert (Hua128 :
    @Integers.signed 128%positive (@Integers.repr 128%positive (@Integers.unsigned w a)) =
    @Integers.unsigned w a)
    by (apply (@Integers.signed_repr 128%positive); lia).
  assert (Hub128 :
    @Integers.signed 128%positive (@Integers.repr 128%positive (@Integers.unsigned w b)) =
    @Integers.unsigned w b)
    by (apply (@Integers.signed_repr 128%positive); lia).
  assert (Hsa128 :
    @Integers.signed 128%positive (@Integers.repr 128%positive (@Integers.signed w a)) =
    @Integers.signed w a)
    by (apply (@Integers.signed_repr 128%positive); lia).
  assert (Hsb128 :
    @Integers.signed 128%positive (@Integers.repr 128%positive (@Integers.signed w b)) =
    @Integers.signed w b)
    by (apply (@Integers.signed_repr 128%positive); lia).
  assert (Hsbnz : (@Integers.signed w b <> 0)%Z).
  { intro Hz; apply Hbnz; unfold Integers.signed in Hz.
    destruct (zlt (@Integers.unsigned w b) (@Integers.half_modulus w)); lia. }
  repeat split.
  - unfold Integers.divs, Integers.divu; rewrite Hua128, Hub128, Z.quot_div_nonneg by lia.
    rewrite (@Integers.unsigned_repr w); [reflexivity |].
    split; [apply Z.div_pos; lia |].
    assert (Hdivle : (@Integers.unsigned w a / @Integers.unsigned w b <= @Integers.unsigned w a)%Z)
      by (apply Z.div_le_upper_bound; [lia | nia]).
    lia.
  - unfold Integers.mods, Integers.modu; rewrite Hua128, Hub128, Z.rem_mod_nonneg by lia.
    rewrite (@Integers.unsigned_repr w); [reflexivity |].
    pose proof (Z.mod_pos_bound (@Integers.unsigned w a) (@Integers.unsigned w b) ltac:(lia)).
    lia.
  - unfold Integers.divs; rewrite Hsa128, Hsb128.
    destruct (Z.eqb (@Integers.signed w a) (@Integers.min_signed w) &&
              Z.eqb (@Integers.signed w b) (-1)%Z) eqn:Hov.
    + apply andb_true_iff in Hov as [Ha1 Hb1]; apply Z.eqb_eq in Ha1; apply Z.eqb_eq in Hb1.
      rewrite Ha1, Hb1, Hminw; destruct Hw as [-> | ->]; reflexivity.
    + rewrite (@Integers.signed_repr w (Z.quot (@Integers.signed w a) (@Integers.signed w b))); [reflexivity |].
      destruct (Z.eq_dec (@Integers.signed w b) 1%Z) as [Hb1 | Hnb1].
      * rewrite Hb1, Z.quot_1_r; exact Hrsa.
      * destruct (Z.eq_dec (@Integers.signed w b) (-1)%Z) as [Hbm1 | Hnbm1].
        -- assert (Hna : @Integers.signed w a <> @Integers.min_signed w).
           { intro Heq; rewrite Heq, Hbm1, !Z.eqb_refl in Hov; discriminate Hov. }
           rewrite Hbm1; change (-1)%Z with (Z.opp 1%Z); rewrite Z.quot_opp_r, Z.quot_1_r by discriminate; lia.
        -- assert (Habsb : (2 <= Z.abs (@Integers.signed w b))%Z) by lia.
           assert (Habsq :
             (Z.abs (Z.quot (@Integers.signed w a) (@Integers.signed w b)) <=
              @Integers.half_modulus w / 2)%Z).
           { rewrite <- Z.quot_abs, Z.quot_div_nonneg by lia.
             assert (Hd1 :
               (Z.abs (@Integers.signed w a) / Z.abs (@Integers.signed w b) <=
                Z.abs (@Integers.signed w a) / 2)%Z)
               by (apply Z.div_le_compat_l; lia).
             assert (Hd2 : (Z.abs (@Integers.signed w a) / 2 <= @Integers.half_modulus w / 2)%Z)
               by (apply Z.div_le_mono; lia).
             lia. }
           assert (Hdiv2 : (@Integers.half_modulus w / 2 <= @Integers.half_modulus w - 1)%Z)
             by (destruct Hw as [-> | ->]; vm_compute; discriminate).
           lia.
  - unfold Integers.mods; rewrite Hsa128, Hsb128.
    destruct (Z.eqb (@Integers.signed w a) (@Integers.min_signed w) &&
              Z.eqb (@Integers.signed w b) (-1)%Z) eqn:Hov.
    + apply andb_true_iff in Hov as [Ha1 Hb1]; apply Z.eqb_eq in Ha1; apply Z.eqb_eq in Hb1.
      rewrite Ha1, Hb1, Hminw; destruct Hw as [-> | ->]; reflexivity.
    + rewrite (@Integers.signed_repr w (Z.rem (@Integers.signed w a) (@Integers.signed w b))); [reflexivity |].
      destruct (Z.eq_dec (@Integers.signed w a) (@Integers.signed w b)) as [Heqab | Hneab].
      * rewrite Heqab, Z.rem_same by exact Hsbnz; lia.
      * pose proof (Z.rem_bound_abs (@Integers.signed w a) (@Integers.signed w b) Hsbnz) as Hrbnd.
        destruct (Z.eq_dec (@Integers.signed w b) (@Integers.min_signed w)) as [Hbm | Hnbm].
        -- pose proof (Z.quot_rem' (@Integers.signed w a) (@Integers.signed w b)) as Hqr.
           assert (Hq0 : (Z.quot (@Integers.signed w a) (@Integers.signed w b) = 0)%Z)
             by (apply Z.quot_small_iff; [exact Hsbnz | lia]).
           rewrite Hq0, Z.mul_0_r, Z.add_0_l in Hqr; rewrite <- Hqr; lia.
        -- lia.
Qed.

