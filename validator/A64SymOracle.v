(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * AArch64 (A64) Concrete Oracle & Step Soundness ([CertValidator.A64SymOracle])

    Purpose:
      Provides Layer-3 differential oracle helpers ([a64_eval_bytes_concrete],
      [a64_decode_word_ok]) and the proven single-step symbolic oracle ([a64_step_sym_oracle],
      [a64_step_sym_oracle_sound]).

    Trust Contract & Fail-Closed Boundary:
      [a64_step_sym_oracle] returns [None] on decode failure or unsupported instructions;
      [Some] outputs are proven sound against [a64_step_concrete] by
      [a64_step_sym_oracle_sound]. Extracted to OCaml via [Extract.v].

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{CertFormat,AigLrat,
      AlgRules,CfgDag,Elf64Spec,McFrameMem,McIsaCommon,A64Decode,A64ExecSym,A64DagProof}];
      zero custom axioms.

    Section Outline:
      6. Concrete differential oracle helpers; 7. Single-step symbolic oracle
      ([a64_step_sym_oracle]) and [a64_step_sym_oracle_sound]. *)

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

(** ** 6. Concrete Extracted ISA Oracle Helpers (Layer-3 Differential Harness) *)

Definition a64_regfile_of_list (regs : list N) : a64_regfile :=
  fun r =>
    match List.nth_error regs (N.to_nat r) with
    | Some v => @Integers.repr 64%positive (Z.of_N v)
    | None => @Integers.zero 64%positive
    end.

Definition a64_regfile_to_list_aux : nat -> nat -> a64_regfile -> list N :=
  fix go idx count rf {struct count} :=
    match count with
    | O => []
    | S count' =>
        Z.to_N (@Integers.unsigned 64%positive (a64_read_reg (N.of_nat idx) rf))
        :: go (S idx) count' rf
    end.

Definition a64_regfile_to_list (rf : a64_regfile) : list N :=
  a64_regfile_to_list_aux 0%nat 31%nat rf.

Definition a64_decode_word_ok (w : N) : bool :=
  match decode_a64_word w with
  | Some _ => true
  | None => false
  end.

Definition a64_eval_bytes_concrete
  (fuel : nat) (code : list N) (init_regs : list N) (n z c v : bool)
  : string + (list N * (bool * bool * bool * bool)) :=
  match decode_a64_bytes code with
  | inl err => inl err
  | inr insts =>
      match a64_exec fuel insts 0%N (a64_regfile_of_list init_regs) (mk_a64_flags n z c v) with
      | None => inl "a64_exec returned None"
      | Some (rf_end, fl_end) =>
          inr (a64_regfile_to_list rf_end, (af_n fl_end, af_z fl_end, af_c fl_end, af_v fl_end))
      end
  end.

(** ** 7. Proven Single-Step Symbolic Oracle Export (Stage-2 Sail/SMT Reference) *)

Definition a64_oracle_reg_name (r : N) : string :=
  if N.eqb r 0%N then "R0" else if N.eqb r 1%N then "R1" else if N.eqb r 2%N then "R2"
  else if N.eqb r 3%N then "R3" else if N.eqb r 4%N then "R4" else if N.eqb r 5%N then "R5"
  else if N.eqb r 6%N then "R6" else if N.eqb r 7%N then "R7" else if N.eqb r 8%N then "R8"
  else if N.eqb r 9%N then "R9" else if N.eqb r 10%N then "R10" else if N.eqb r 11%N then "R11"
  else if N.eqb r 12%N then "R12" else if N.eqb r 13%N then "R13" else if N.eqb r 14%N then "R14"
  else if N.eqb r 15%N then "R15" else if N.eqb r 16%N then "R16" else if N.eqb r 17%N then "R17"
  else if N.eqb r 18%N then "R18" else if N.eqb r 19%N then "R19" else if N.eqb r 20%N then "R20"
  else if N.eqb r 21%N then "R21" else if N.eqb r 22%N then "R22" else if N.eqb r 23%N then "R23"
  else if N.eqb r 24%N then "R24" else if N.eqb r 25%N then "R25" else if N.eqb r 26%N then "R26"
  else if N.eqb r 27%N then "R27" else if N.eqb r 28%N then "R28" else if N.eqb r 29%N then "R29"
  else "R30".

Definition a64_oracle_srf : a64_sym_regs :=
  fun r =>
    if N.leb 31%N r then CE_BvConst 64%positive 0%N
    else CE_Var (a64_oracle_reg_name r) 64%positive.

Definition a64_oracle_sfl : a64_sym_flags :=
  mk_a64_sym_flags
    (CE_Var "NZCV_N" 1%positive)
    (CE_Var "NZCV_Z" 1%positive)
    (CE_Var "NZCV_C" 1%positive)
    (CE_Var "NZCV_V" 1%positive)
    (a64_sym_bool_xor (CE_Var "NZCV_N" 1%positive) (CE_Var "NZCV_V" 1%positive)).

Record a64_sym_step_out : Set := mk_a64_sym_step_out {
  aso_rd_write : option (N * cert_expr);
  aso_flags_write : option (cert_expr * cert_expr * cert_expr * cert_expr);
  aso_pc_kind : N;
  aso_br_cond : option cert_expr;
  aso_rel_bytes : Z;
}.

Definition a64_oracle_wr (sf : bool) (rd : N) (e : cert_expr) : option (N * cert_expr) :=
  if N.leb 31%N rd then None
  else Some (rd, if sf then e else CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags e).

Definition a64_oracle_fl_opt (set_fl : bool) (sfl : a64_sym_flags)
  : option (cert_expr * cert_expr * cert_expr * cert_expr) :=
  if set_fl then Some (asf_n sfl, asf_z sfl, asf_c sfl, asf_v sfl) else None.

Definition a64_step_sym_oracle (w : N) : option a64_sym_step_out :=
  match decode_a64_word w with
  | None => None
  | Some inst =>
      match inst with
      | A64_Nop => Some (mk_a64_sym_step_out None None 0%N None 0%Z)
      | A64_AddSubImm sf is_sub set_fl rd rn imm =>
          if N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N) then None
          else
            let lhs := a64_sym_read_w sf rn a64_oracle_srf in
            let rhs := ce_bv_z (a64_w sf) (Z.of_N imm) in
            let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
            Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) (a64_oracle_fl_opt set_fl sfl') 0%N None 0%Z)
      | A64_AddSubShift sf is_sub set_fl rd rn rm sh amt =>
          let lhs := a64_sym_read_w sf rn a64_oracle_srf in
          let rhs := a64_sym_shift (a64_w sf) (a64_sym_read_w sf rm a64_oracle_srf) sh amt in
          let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) (a64_oracle_fl_opt set_fl sfl') 0%N None 0%Z)
      | A64_AddSubExt sf is_sub set_fl rd rn rm ext amt =>
          let lhs := a64_sym_read_w sf rn a64_oracle_srf in
          let rhs := a64_sym_extend (a64_w sf) (a64_sym_read_reg rm a64_oracle_srf) ext amt in
          let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) (a64_oracle_fl_opt set_fl sfl') 0%N None 0%Z)
      | A64_LogicalImm sf op set_fl rd rn mask =>
          let lhs := a64_sym_read_w sf rn a64_oracle_srf in
          let rhs := ce_bv_z (a64_w sf) (Z.of_N mask) in
          let res := a64_sym_logic_op (a64_w sf) op lhs rhs in
          let sfl' := a64_sym_logic_flags (a64_w sf) res in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) (a64_oracle_fl_opt set_fl sfl') 0%N None 0%Z)
      | A64_LogicalShift sf op inv_rm set_fl rd rn rm sh amt =>
          let lhs := a64_sym_read_w sf rn a64_oracle_srf in
          let shv := a64_sym_shift (a64_w sf) (a64_sym_read_w sf rm a64_oracle_srf) sh amt in
          let rhs := if inv_rm then a64_sym_not (a64_w sf) shv else shv in
          let res := a64_sym_logic_op (a64_w sf) op lhs rhs in
          let sfl' := a64_sym_logic_flags (a64_w sf) res in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) (a64_oracle_fl_opt set_fl sfl') 0%N None 0%Z)
      | A64_MoveWide sf kind rd imm16 shift =>
          let w := a64_w sf in
          let imm_e := ce_bv_z w (Z.of_N (N.shiftl imm16 shift)) in
          let res :=
            match kind with
            | AMW_Movz => imm_e
            | AMW_Movn => a64_sym_not w imm_e
            | AMW_Movk =>
                let cur := a64_sym_read_w sf rd a64_oracle_srf in
                let clr := a64_sym_not w (ce_bv_z w (Z.of_N (N.shiftl 65535%N shift))) in
                CE_BinOp CB_Or w no_binop_flags (CE_BinOp CB_And w no_binop_flags cur clr) imm_e
            end
          in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) None 0%N None 0%Z)
      | A64_Bitfield sf kind rd rn immr imms =>
          let res := a64_sym_bitfield (a64_w sf) kind
                       (a64_sym_read_w sf rn a64_oracle_srf)
                       (a64_sym_read_w sf rd a64_oracle_srf) immr imms in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) None 0%N None 0%Z)
      | A64_Extr sf rd rn rm lsb =>
          let res := a64_sym_extr (a64_w sf) (a64_sym_read_w sf rn a64_oracle_srf)
                       (a64_sym_read_w sf rm a64_oracle_srf) lsb in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) None 0%N None 0%Z)
      | A64_MulAddSub sf is_sub rd rn rm ra =>
          let w := a64_w sf in
          let p := CE_BinOp CB_Mul w no_binop_flags
                     (a64_sym_read_w sf rn a64_oracle_srf)
                     (a64_sym_read_w sf rm a64_oracle_srf) in
          let a := a64_sym_read_w sf ra a64_oracle_srf in
          let res := CE_BinOp (if is_sub then CB_Sub else CB_Add) w no_binop_flags a p in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) None 0%N None 0%Z)
      | A64_MulWidening sgn is_sub rd rn rm ra =>
          let ck := if sgn then CCK_SExt else CCK_ZExt in
          let n64 := CE_Cast ck 32%positive 64%positive no_cast_flags (a64_sym_read_w false rn a64_oracle_srf) in
          let m64 := CE_Cast ck 32%positive 64%positive no_cast_flags (a64_sym_read_w false rm a64_oracle_srf) in
          let p := CE_BinOp CB_Mul 64%positive no_binop_flags n64 m64 in
          let a := a64_sym_read_reg ra a64_oracle_srf in
          let res := CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags a p in
          Some (mk_a64_sym_step_out (a64_oracle_wr true rd res) None 0%N None 0%Z)
      | A64_DataProc2 sf op rd rn rm =>
          let res := a64_sym_dp2 (a64_w sf) op
                       (a64_sym_read_w sf rn a64_oracle_srf)
                       (a64_sym_read_w sf rm a64_oracle_srf) in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) None 0%N None 0%Z)
      | A64_CondSelect sf kind cond rd rn rm =>
          let res := a64_sym_csel (a64_w sf) kind cond a64_oracle_sfl
                       (a64_sym_read_w sf rn a64_oracle_srf)
                       (a64_sym_read_w sf rm a64_oracle_srf) in
          Some (mk_a64_sym_step_out (a64_oracle_wr sf rd res) None 0%N None 0%Z)
      | A64_CondCompareReg sf is_sub cond rn rm nzcv =>
          let '(_, csfl) := a64_sym_add_sub (a64_w sf) is_sub
                              (a64_sym_read_w sf rn a64_oracle_srf)
                              (a64_sym_read_w sf rm a64_oracle_srf) in
          let sfl' := a64_sym_ite_flags (a64_sym_cond cond a64_oracle_sfl) csfl (a64_sym_flags_of_imm4 nzcv) in
          Some (mk_a64_sym_step_out None (a64_oracle_fl_opt true sfl') 0%N None 0%Z)
      | A64_CondCompareImm sf is_sub cond rn imm5 nzcv =>
          let '(_, csfl) := a64_sym_add_sub (a64_w sf) is_sub
                              (a64_sym_read_w sf rn a64_oracle_srf)
                              (ce_bv_z (a64_w sf) (Z.of_N imm5)) in
          let sfl' := a64_sym_ite_flags (a64_sym_cond cond a64_oracle_sfl) csfl (a64_sym_flags_of_imm4 nzcv) in
          Some (mk_a64_sym_step_out None (a64_oracle_fl_opt true sfl') 0%N None 0%Z)
      | A64_B rel =>
          Some (mk_a64_sym_step_out None None 1%N None rel)
      | A64_BCond cond rel =>
          Some (mk_a64_sym_step_out None None 2%N (Some (a64_sym_cond cond a64_oracle_sfl)) rel)
      | A64_Cbz sf is_nz rt rel =>
          let wv := a64_w sf in
          let c_e := CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false wv
                       (a64_sym_read_w sf rt a64_oracle_srf) (CE_BvConst wv 0%N) in
          Some (mk_a64_sym_step_out None None 2%N (Some c_e) rel)
      | A64_Tbz is_nz rt bit rel =>
          let masked := CE_BinOp CB_And 64%positive no_binop_flags
                          (a64_sym_read_reg rt a64_oracle_srf)
                          (CE_BvConst 64%positive (N.shiftl 1%N bit)) in
          let c_e := CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false 64%positive
                       masked (CE_BvConst 64%positive 0%N) in
          Some (mk_a64_sym_step_out None None 2%N (Some c_e) rel)
      | A64_LdStImm _ _ _ _ _ _ _ _ | A64_LdStPair _ _ _ _ _ _ _ => None
      | A64_Ret =>
          Some (mk_a64_sym_step_out None None 3%N None 0%Z)
      end
  end.

Definition a64_penv_matches_state {Pa : Params} (penv : param_env Pa) (rf : a64_regfile) (fl : a64_flags) : Prop :=
  (forall r, (r < 31)%N ->
     penv (a64_oracle_reg_name r) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg r rf)))) /\
  penv "NZCV_N" = Some (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_n fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  penv "NZCV_Z" = Some (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_z fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  penv "NZCV_C" = Some (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_c fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  penv "NZCV_V" = Some (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_v fl then @Integers.one 1%positive else @Integers.zero 1%positive))).

Lemma a64_oracle_srf_agrees :
  forall {Pa : Params} (penv : param_env Pa) foracle rf fl,
    a64_penv_matches_state penv rf fl ->
    a64_env_agrees penv foracle a64_oracle_srf (fun _ => true) rf.
Proof.
  intros Pa penv foracle rf fl [Hreg _] r _.
  unfold a64_sym_read_reg, a64_oracle_srf, a64_read_reg.
  destruct (N.leb 31%N r) eqn:Er31; [rewrite eval_ce_const, repr_zero_N; reflexivity |].
  apply N.leb_gt in Er31.
  unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite (Hreg r Er31).
  cbn [lookup_let_val check_scalar_width Pos.eqb]; unfold a64_read_reg;
    replace (N.leb 31%N r) with false by (symmetry; apply N.leb_gt; exact Er31); reflexivity.
Qed.

Lemma a64_oracle_sfl_agrees :
  forall {Pa : Params} (penv : param_env Pa) foracle rf fl,
    a64_penv_matches_state penv rf fl ->
    sym_flags_agree penv foracle a64_oracle_sfl fl.
Proof.
  intros Pa penv foracle rf fl [_ (Hn & Hz & Hc & Hv)].
  assert (Hlu : forall nm (b : bool),
    penv nm = Some (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (CE_Var nm 1%positive) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))).
  { intros nm b Hp; unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hp;
      cbn [lookup_let_val check_scalar_width Pos.eqb]; reflexivity. }
  unfold sym_flags_agree, a64_oracle_sfl; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v].
  pose proof (Hlu _ _ Hn) as En; pose proof (Hlu _ _ Hz) as Ez;
    pose proof (Hlu _ _ Hc) as Ec; pose proof (Hlu _ _ Hv) as Ev.
  repeat split; try assumption.
  exact (eval_a64_sym_bool_xor_sound _ _ _ _ _ _ En Ev).
Qed.

Definition a64_step_flags_match {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (flw : option (cert_expr * cert_expr * cert_expr * cert_expr)) (fl_out : a64_flags) : Prop :=
  match flw with
  | None => True
  | Some (en, ez, ec, ev) =>
      eval_closed_cert_expr penv foracle en =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_n fl_out then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
      eval_closed_cert_expr penv foracle ez =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_z fl_out then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
      eval_closed_cert_expr penv foracle ec =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_c fl_out then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
      eval_closed_cert_expr penv foracle ev =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_v fl_out then @Integers.one 1%positive else @Integers.zero 1%positive)))
  end.

Definition a64_step_concrete (inst : a64_inst) (rf : a64_regfile) (fl : a64_flags)
  : a64_regfile * a64_flags * option bool :=
  match inst with
  | A64_Nop | A64_B _ | A64_Ret
  | A64_LdStImm _ _ _ _ _ _ _ _ | A64_LdStPair _ _ _ _ _ _ _ => (rf, fl, None)
  | A64_AddSubImm sf is_sub sfl rd rn imm =>
      let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm)) in
      (a64_write_w sf rd res rf, (if sfl then fl' else fl), None)
  | A64_AddSubShift sf is_sub sfl rd rn rm sh amt =>
      let rhs := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt in
      let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) rhs in
      (a64_write_w sf rd res rf, (if sfl then fl' else fl), None)
  | A64_AddSubExt sf is_sub sfl rd rn rm ext amt =>
      let rhs := a64_eval_extend (a64_w sf) (a64_read_reg rm rf) ext amt in
      let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) rhs in
      (a64_write_w sf rd res rf, (if sfl then fl' else fl), None)
  | A64_LogicalImm sf op sfl rd rn mask =>
      let res := a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N mask)) in
      (a64_write_w sf rd res rf, (if sfl then a64_eval_logic_flags (a64_w sf) res else fl), None)
  | A64_LogicalShift sf op inv_rm sfl rd rn rm sh amt =>
      let shv := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt in
      let rhs := if inv_rm then @Integers.not (a64_w sf) shv else shv in
      let res := a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) rhs in
      (a64_write_w sf rd res rf, (if sfl then a64_eval_logic_flags (a64_w sf) res else fl), None)
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
      (a64_write_w sf rd res rf, fl, None)
  | A64_Bitfield sf kind rd rn immr imms =>
      let res := a64_eval_bitfield (a64_w sf) kind (a64_read_w sf rn rf) (a64_read_w sf rd rf) immr imms in
      (a64_write_w sf rd res rf, fl, None)
  | A64_Extr sf rd rn rm lsb =>
      let res := a64_eval_extr (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf) lsb in
      (a64_write_w sf rd res rf, fl, None)
  | A64_MulAddSub sf is_sub rd rn rm ra =>
      let w := a64_w sf in
      let p := @Integers.mul w (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
      let a := a64_read_w sf ra rf in
      let res := if is_sub then @Integers.sub w a p else @Integers.add w a p in
      (a64_write_w sf rd res rf, fl, None)
  | A64_MulWidening sgn is_sub rd rn rm ra =>
      let n32 := a64_read_w false rn rf in
      let m32 := a64_read_w false rm rf in
      let n64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive n32 else @Integers.unsigned 32%positive n32) in
      let m64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive m32 else @Integers.unsigned 32%positive m32) in
      let p := @Integers.mul 64%positive n64 m64 in
      let a := a64_read_reg ra rf in
      let res := if is_sub then @Integers.sub 64%positive a p else @Integers.add 64%positive a p in
      (a64_write_reg rd res rf, fl, None)
  | A64_DataProc2 sf op rd rn rm =>
      let res := a64_eval_dp2 (a64_w sf) op (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
      (a64_write_w sf rd res rf, fl, None)
  | A64_CondSelect sf kind cond rd rn rm =>
      let res := a64_eval_csel (a64_w sf) kind cond fl (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
      (a64_write_w sf rd res rf, fl, None)
  | A64_CondCompareReg sf is_sub cond rn rm nzcv =>
      let '(_, cfl) := a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
      (rf, (if a64_eval_cond cond fl then cfl else a64_flags_of_imm4 nzcv), None)
  | A64_CondCompareImm sf is_sub cond rn imm5 nzcv =>
      let '(_, cfl) := a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm5)) in
      (rf, (if a64_eval_cond cond fl then cfl else a64_flags_of_imm4 nzcv), None)
  | A64_BCond cond _ => (rf, fl, Some (a64_eval_cond cond fl))
  | A64_Cbz sf is_nz rt _ =>
      let v := a64_read_w sf rt rf in
      let eq0 := @Integers.eq (a64_w sf) v (@Integers.zero (a64_w sf)) in
      (rf, fl, Some (if is_nz then negb eq0 else eq0))
  | A64_Tbz is_nz rt bit _ =>
      let v := a64_read_reg rt rf in
      let tb := Z.testbit (@Integers.unsigned 64%positive v) (Z.of_N bit) in
      (rf, fl, Some (if is_nz then tb else negb tb))
  end.

Lemma a64_oracle_wr_eval :
  forall {Pa : Params} (penv : param_env Pa) foracle sf rd res (v : @Integers.bit_int (a64_w sf)) rf,
    eval_closed_cert_expr penv foracle res = raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) v)) ->
    match a64_oracle_wr sf rd res with
    | None => forall r, a64_read_reg r (a64_write_w sf rd v rf) = a64_read_reg r rf
    | Some (rd', e64) =>
        rd' = rd /\ (rd' < 31)%N /\
        eval_closed_cert_expr penv foracle e64 =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg rd' (a64_write_w sf rd v rf))))
    end.
Proof.
  intros Pa penv foracle sf rd res v rf Hres.
  unfold a64_oracle_wr, a64_write_w, a64_write_reg, a64_read_reg.
  destruct (N.leb 31%N rd) eqn:Erd31.
  - intro r; reflexivity.
  - apply N.leb_gt in Erd31; repeat split; [exact Erd31 |].
    replace (N.leb 31%N rd) with false by (symmetry; apply N.leb_gt; exact Erd31).
    rewrite N.eqb_refl; destruct sf; cbn [a64_w] in Hres, v |- *.
    + exact Hres.
    + exact (eval_ce_zext penv foracle 32%positive 64%positive res v eq_refl Hres).
Qed.

Theorem a64_step_sym_oracle_sound :
  forall {Pa : Params} w inst out (penv : param_env Pa) foracle rf fl rf' fl' br_opt,
    decode_a64_word w = Some inst ->
    a64_step_sym_oracle w = Some out ->
    a64_penv_matches_state penv rf fl ->
    a64_step_concrete inst rf fl = (rf', fl', br_opt) ->
    (match aso_rd_write out with
     | None => forall r, a64_read_reg r rf' = a64_read_reg r rf
     | Some (rd, e64) =>
         (rd < 31)%N /\
         (forall r, r <> rd -> a64_read_reg r rf' = a64_read_reg r rf) /\
         eval_closed_cert_expr penv foracle e64 =
           raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg rd rf')))
     end) /\
    (aso_flags_write out = None -> fl' = fl) /\
    a64_step_flags_match penv foracle (aso_flags_write out) fl' /\
    (match br_opt with
     | None => aso_br_cond out = None
     | Some b =>
         exists ce, aso_br_cond out = Some ce /\
         eval_closed_cert_expr penv foracle ce =
           raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))
     end).
Proof.
  intros Pa w inst out penv foracle rf fl rf' fl' br_opt Hdec Hso Hm Hstep.
  pose proof (decode_a64_word_valid w inst Hdec) as Hval.
  pose proof (a64_oracle_srf_agrees penv foracle rf fl Hm) as Hag.
  pose proof (a64_oracle_sfl_agrees penv foracle rf fl Hm) as Hfl.
  unfold a64_step_sym_oracle in Hso; rewrite Hdec in Hso.
  assert (Hdef_all : forall r, a64_def_read r (fun _ : N => true) = true)
    by (intro r; unfold a64_def_read; destruct (N.leb 31%N r); reflexivity).
  assert (Hwr_other : forall sf rd (v : @Integers.bit_int (a64_w sf)) r,
    r <> rd -> a64_read_reg r (a64_write_w sf rd v rf) = a64_read_reg r rf).
  { intros sf0 rd0 v0 r0 Hne; unfold a64_read_reg, a64_write_w, a64_write_reg.
    destruct (N.leb 31%N rd0); [reflexivity |].
    destruct (N.leb 31%N r0); [reflexivity |].
    apply N.eqb_neq in Hne; rewrite Hne; reflexivity. }
  destruct inst; cbn [a64_step_concrete] in Hstep; cbn [a64_inst_valid] in Hval.
  - (* A64_Nop *)
    inversion Hso; inversion Hstep; subst; repeat split; try reflexivity; exact I.
  - (* A64_AddSubImm *)
    destruct (N.eqb rn 31%N || (negb set_flags && N.eqb rd 31%N)); [discriminate Hso |].
    destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se sfl'] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl_n] eqn:Eeas.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)) (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm))) as [Hres Hfl'].
    rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd se vr rf Hres) as Hwr.
    repeat split.
    + destruct (a64_oracle_wr sf rd se) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
    + intro Hfn; unfold a64_oracle_fl_opt in Hfn; destruct set_flags; [discriminate Hfn | reflexivity].
    + unfold a64_oracle_fl_opt, a64_step_flags_match; destruct set_flags; [destruct Hfl' as (H1 & H2 & H3 & H4 & _); repeat split; assumption | exact I].
  - (* A64_AddSubShift *)
    apply andb_true_iff in Hval as [_ Hamt]; apply N.ltb_lt in Hamt.
    pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf) ltac:(destruct sf; exact Hamt) (a64_env_agrees_read_w _ _ _ _ _ sf rm Hag (Hdef_all _))) as Hsh.
    destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se sfl'] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl_n] eqn:Eeas.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)) Hsh) as [Hres Hfl'].
    rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd se vr rf Hres) as Hwr.
    repeat split.
    + destruct (a64_oracle_wr sf rd se) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
    + intro Hfn; unfold a64_oracle_fl_opt in Hfn; destruct set_flags; [discriminate Hfn | reflexivity].
    + unfold a64_oracle_fl_opt, a64_step_flags_match; destruct set_flags; [destruct Hfl' as (H1 & H2 & H3 & H4 & _); repeat split; assumption | exact I].
  - (* A64_AddSubExt *)
    apply N.leb_le in Hval.
    pose proof (eval_a64_sym_extend_sound _ _ (a64_w sf) _ _ ext amt (a64_w_32_64 sf) Hval (Hag rm (Hdef_all rm))) as Hext.
    destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se sfl'] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl_n] eqn:Eeas.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)) Hext) as [Hres Hfl'].
    rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd se vr rf Hres) as Hwr.
    repeat split.
    + destruct (a64_oracle_wr sf rd se) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
    + intro Hfn; unfold a64_oracle_fl_opt in Hfn; destruct set_flags; [discriminate Hfn | reflexivity].
    + unfold a64_oracle_fl_opt, a64_step_flags_match; destruct set_flags; [destruct Hfl' as (H1 & H2 & H3 & H4 & _); repeat split; assumption | exact I].
  - (* A64_LogicalImm *)
    assert (Hres : eval_closed_cert_expr penv foracle
      (a64_sym_logic_op (a64_w sf) op (a64_sym_read_w sf rn a64_oracle_srf) (ce_bv_z (a64_w sf) (Z.of_N mask))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N mask)))))).
    { unfold a64_sym_logic_op, a64_eval_logic_op; rewrite eval_ce_binop, (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)), eval_ce_bv_z; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
    pose proof (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) as Hfl'.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd _ _ rf Hres) as Hwr.
    repeat split.
    + destruct (a64_oracle_wr sf rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
    + intro Hfn; unfold a64_oracle_fl_opt in Hfn; destruct set_flags; [discriminate Hfn | reflexivity].
    + unfold a64_oracle_fl_opt, a64_step_flags_match; destruct set_flags; [destruct Hfl' as (H1 & H2 & H3 & H4 & _); repeat split; assumption | exact I].
  - (* A64_LogicalShift *)
    apply N.ltb_lt in Hval.
    pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf) ltac:(destruct sf; exact Hval) (a64_env_agrees_read_w _ _ _ _ _ sf rm Hag (Hdef_all _))) as Hsh.
    assert (Hrhs : eval_closed_cert_expr penv foracle (if inv_rm then a64_sym_not (a64_w sf) _ else _) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (if inv_rm then @Integers.not (a64_w sf) (a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt)
         else a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt))))
      by (destruct inv_rm; [exact (eval_ce_not _ _ _ _ _ Hsh) | exact Hsh]).
    set (vr_shift := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt) in *.
    set (se_shift := a64_sym_shift (a64_w sf) (a64_sym_read_w sf rm a64_oracle_srf) sh amt) in *.
    set (vr_rhs := if inv_rm then @Integers.not (a64_w sf) vr_shift else vr_shift) in *.
    set (se_rhs := if inv_rm then a64_sym_not (a64_w sf) se_shift else se_shift) in *.
    assert (Hres : eval_closed_cert_expr penv foracle
      (a64_sym_logic_op (a64_w sf) op (a64_sym_read_w sf rn a64_oracle_srf) se_rhs) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) vr_rhs)))).
    { unfold a64_sym_logic_op, a64_eval_logic_op; rewrite eval_ce_binop, (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)), Hrhs; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
    pose proof (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) as Hfl'.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd _ _ rf Hres) as Hwr.
    repeat split.
    + destruct (a64_oracle_wr sf rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
    + intro Hfn; unfold a64_oracle_fl_opt in Hfn; destruct set_flags; [discriminate Hfn | reflexivity].
    + unfold a64_oracle_fl_opt, a64_step_flags_match; destruct set_flags; [destruct Hfl' as (H1 & H2 & H3 & H4 & _); repeat split; assumption | exact I].
  - (* A64_MoveWide *)
    assert (Hres : eval_closed_cert_expr penv foracle
      (match kind with
       | AMW_Movz => ce_bv_z (a64_w sf) (Z.of_N (N.shiftl imm16 shift))
       | AMW_Movn => a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl imm16 shift)))
       | AMW_Movk =>
           CE_BinOp CB_Or (a64_w sf) no_binop_flags
             (CE_BinOp CB_And (a64_w sf) no_binop_flags (a64_sym_read_w sf rd a64_oracle_srf)
               (a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))
             (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl imm16 shift)))
       end) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (match kind with
         | AMW_Movz => @Integers.repr (a64_w sf) (Z.of_N (N.shiftl imm16 shift))
         | AMW_Movn => @Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl imm16 shift)))
         | AMW_Movk =>
             @Integers.or (a64_w sf)
               (@Integers.and (a64_w sf) (a64_read_w sf rd rf)
                 (@Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))
               (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl imm16 shift)))
         end)))).
    { destruct kind.
      - exact (eval_ce_not _ _ _ _ _ (eval_ce_bv_z _ _ _ _)).
      - apply eval_ce_bv_z.
      - assert (Hand : eval_closed_cert_expr penv foracle
          (CE_BinOp CB_And (a64_w sf) no_binop_flags (a64_sym_read_w sf rd a64_oracle_srf)
            (a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl 65535%N shift))))) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
            (@Integers.and (a64_w sf) (a64_read_w sf rd rf)
              (@Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))))).
        { rewrite eval_ce_binop, (a64_env_agrees_read_w _ _ _ _ _ sf rd Hag (Hdef_all _)),
                  (eval_ce_not _ _ _ _ _ (eval_ce_bv_z _ _ _ _)); cbn [eou_bind].
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
        rewrite eval_ce_binop, Hand, eval_ce_bv_z; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd _ _ rf Hres) as Hwr.
    split; [| split; [intro; reflexivity | split; [exact I | reflexivity]]].
    destruct (a64_oracle_wr sf rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
  - (* A64_Bitfield *)
    apply andb_true_iff in Hval as [Hr1 Hs1]; apply N.ltb_lt in Hr1; apply N.ltb_lt in Hs1.
    pose proof (eval_a64_sym_bitfield_sound penv foracle sf kind _ _ _ _ _ _ Hr1 Hs1
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _))
                  (a64_env_agrees_read_w _ _ _ _ _ sf rd Hag (Hdef_all _))) as Hres.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd _ _ rf Hres) as Hwr.
    split; [| split; [intro; reflexivity | split; [exact I | reflexivity]]].
    destruct (a64_oracle_wr sf rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
  - (* A64_Extr *)
    pose proof (eval_a64_sym_extr_sound _ _ (a64_w sf) _ _ _ _ lsb (a64_w_32_64 sf)
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _))
                  (a64_env_agrees_read_w _ _ _ _ _ sf rm Hag (Hdef_all _))) as Hres.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd _ _ rf Hres) as Hwr.
    split; [| split; [intro; reflexivity | split; [exact I | reflexivity]]].
    destruct (a64_oracle_wr sf rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
  - (* A64_MulAddSub *)
    assert (Hmul : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_Mul (a64_w sf) no_binop_flags (a64_sym_read_w sf rn a64_oracle_srf) (a64_sym_read_w sf rm a64_oracle_srf)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (@Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf))))).
    { rewrite eval_ce_binop, (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)),
                (a64_env_agrees_read_w _ _ _ _ _ sf rm Hag (Hdef_all _)); cbn [eou_bind].
      destruct sf; unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.mul a64_read_w]; reflexivity. }
    assert (Hres : eval_closed_cert_expr penv foracle
      (CE_BinOp (if is_sub then CB_Sub else CB_Add) (a64_w sf) no_binop_flags (a64_sym_read_w sf ra a64_oracle_srf)
        (CE_BinOp CB_Mul (a64_w sf) no_binop_flags (a64_sym_read_w sf rn a64_oracle_srf) (a64_sym_read_w sf rm a64_oracle_srf))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (let p := @Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
         let a := a64_read_w sf ra rf in
         if is_sub then @Integers.sub (a64_w sf) a p else @Integers.add (a64_w sf) a p)))).
    { rewrite eval_ce_binop, (a64_env_agrees_read_w _ _ _ _ _ sf ra Hag (Hdef_all _)), Hmul; cbn [eou_bind].
      destruct sf, is_sub; unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.mul Integers.add Integers.sub a64_read_w]; reflexivity. }
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd _ _ rf Hres) as Hwr.
    split; [| split; [intro; reflexivity | split; [exact I | reflexivity]]].
    destruct (a64_oracle_wr sf rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
  - (* A64_MulWidening *)
    set (en64 := CE_Cast (if is_signed then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags (a64_sym_read_w false rn a64_oracle_srf)).
    set (em64 := CE_Cast (if is_signed then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags (a64_sym_read_w false rm a64_oracle_srf)).
    set (vn64 := @Integers.repr 64%positive (if is_signed then @Integers.signed 32%positive (a64_read_w false rn rf) else @Integers.unsigned 32%positive (a64_read_w false rn rf))).
    set (vm64 := @Integers.repr 64%positive (if is_signed then @Integers.signed 32%positive (a64_read_w false rm rf) else @Integers.unsigned 32%positive (a64_read_w false rm rf))).
    assert (Hn64 : eval_closed_cert_expr penv foracle en64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vn64)))
      by (unfold en64, vn64; destruct is_signed; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; exact (a64_env_agrees_read_w _ _ _ _ _ false rn Hag (Hdef_all _))).
    assert (Hm64 : eval_closed_cert_expr penv foracle em64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vm64)))
      by (unfold em64, vm64; destruct is_signed; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; exact (a64_env_agrees_read_w _ _ _ _ _ false rm Hag (Hdef_all _))).
    assert (Hmul : eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul 64%positive no_binop_flags en64 em64) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.mul 64%positive vn64 vm64)))).
    { rewrite eval_ce_binop, Hn64, Hm64; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.mul vn64 vm64]; reflexivity. }
    assert (Hres : eval_closed_cert_expr penv foracle
      (CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags (a64_sym_read_reg ra a64_oracle_srf)
        (CE_BinOp CB_Mul 64%positive no_binop_flags en64 em64)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
        (if is_sub then @Integers.sub 64%positive (a64_read_reg ra rf) (@Integers.mul 64%positive vn64 vm64)
         else @Integers.add 64%positive (a64_read_reg ra rf) (@Integers.mul 64%positive vn64 vm64))))).
    { rewrite eval_ce_binop, (Hag ra (Hdef_all ra)), Hmul; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
        destruct is_sub; cbn - [Integers.mul Integers.add Integers.sub vn64 vm64 a64_read_reg]; reflexivity. }
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle true rd _ _ rf Hres) as Hwr.
    split; [| split; [intro; reflexivity | split; [exact I | reflexivity]]].
    destruct (a64_oracle_wr true rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply (Hwr_other true rd) | exact He] | exact Hwr].
  - (* A64_DataProc2 *)
    pose proof (eval_a64_sym_dp2_sound _ _ (a64_w sf) op _ _ _ _ (a64_w_32_64 sf)
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)) (a64_env_agrees_read_w _ _ _ _ _ sf rm Hag (Hdef_all _))) as Hres.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd _ _ rf Hres) as Hwr.
    split; [| split; [intro; reflexivity | split; [exact I | reflexivity]]].
    destruct (a64_oracle_wr sf rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
  - (* A64_CondSelect *)
    pose proof (eval_a64_sym_csel_sound _ _ (a64_w sf) kind cond a64_oracle_sfl fl _ _ _ _ Hfl
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)) (a64_env_agrees_read_w _ _ _ _ _ sf rm Hag (Hdef_all _))) as Hres.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond].
    pose proof (a64_oracle_wr_eval penv foracle sf rd _ _ rf Hres) as Hwr.
    split; [| split; [intro; reflexivity | split; [exact I | reflexivity]]].
    destruct (a64_oracle_wr sf rd _) as [[rd' e64] |]; [destruct Hwr as [-> [Hlt He]]; repeat split; [exact Hlt | apply Hwr_other | exact He] | exact Hwr].
  - (* A64_CondCompareReg *)
    destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se csfl] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr cfl] eqn:Eeas.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)) (a64_env_agrees_read_w _ _ _ _ _ sf rm Hag (Hdef_all _))) as [_ Hcsfl].
    rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
    pose proof (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _ (eval_a64_sym_cond_sound _ _ cond _ _ Hfl) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv)) as Hite.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond a64_step_flags_match].
    split; [intro; reflexivity | split; [intro C; discriminate C | split; [destruct Hite as (H1 & H2 & H3 & H4 & _); repeat split; assumption | reflexivity]]].
  - (* A64_CondCompareImm *)
    destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se csfl] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr cfl] eqn:Eeas.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                  (a64_env_agrees_read_w _ _ _ _ _ sf rn Hag (Hdef_all _)) (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm5))) as [_ Hcsfl].
    rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
    pose proof (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _ (eval_a64_sym_cond_sound _ _ cond _ _ Hfl) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv)) as Hite.
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond a64_step_flags_match].
    split; [intro; reflexivity | split; [intro C; discriminate C | split; [destruct Hite as (H1 & H2 & H3 & H4 & _); repeat split; assumption | reflexivity]]].
  - (* A64_LdStImm *)
    discriminate Hso.
  - (* A64_LdStPair *)
    discriminate Hso.
  - (* A64_B *)
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond a64_step_flags_match].
    split; [intro; reflexivity | split; [intro; reflexivity | split; [exact I | reflexivity]]].
  - (* A64_BCond *)
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond a64_step_flags_match].
    split; [intro; reflexivity | split; [intro; reflexivity | split; [exact I | eexists; split; [reflexivity | exact (eval_a64_sym_cond_sound _ _ cond _ _ Hfl)]]]].
  - (* A64_Cbz *)
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond a64_step_flags_match].
    split; [intro; reflexivity | split; [intro; reflexivity | split; [exact I | eexists; split; [reflexivity |]]]].
    destruct is_nz;
      [exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ (a64_env_agrees_read_w _ _ _ _ _ sf rt Hag (Hdef_all _)) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))
      | exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ (a64_env_agrees_read_w _ _ _ _ _ sf rt Hag (Hdef_all _)) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))].
  - (* A64_Tbz *)
    apply N.ltb_lt in Hval.
    assert (Hm_tb : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And 64%positive no_binop_flags (a64_sym_read_reg rt a64_oracle_srf) (CE_BvConst 64%positive (N.shiftl 1%N bit))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
        (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))))).
    { rewrite eval_ce_binop, (Hag rt (Hdef_all rt)), eval_ce_const; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
    assert (Heq_tb : negb (@Integers.eq 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))) (@Integers.zero 64%positive)) =
                     Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)).
    { pose proof (integers_eq_zero_iff 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) as Hiz.
      destruct (@Integers.eq 64%positive _ _) eqn:Ez,
               (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)) eqn:Etb; try reflexivity.
      - exfalso; pose proof (proj1 Hiz eq_refl) as Hz.
        assert (Hb : Z.testbit (@Integers.unsigned 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) (Z.of_N bit) = false)
          by (rewrite Hz; apply Z.testbit_0_l).
        change (Z.testbit (@Integers.unsigned 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) (Z.of_N bit))
          with (@Integers.testbit 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))) (Z.of_N bit)) in Hb.
        rewrite Integers.bits_and, (@Integers.testbit_repr 64%positive _ (Z.of_N bit)) in Hb by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
        rewrite N.shiftl_1_l, N2Z.inj_pow, Z.pow2_bits_true in Hb by lia.
        unfold Integers.testbit in Hb; rewrite Etb in Hb; discriminate Hb.
      - exfalso; assert (Hnz : @Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))) = @Integers.zero 64%positive).
        { apply Integers.same_bits_eq; intros i Hi; rewrite Integers.bits_zero, Integers.bits_and by exact Hi.
          rewrite (@Integers.testbit_repr 64%positive _ i Hi); change (@Integers.zwordsize 64%positive) with 64%Z in Hi.
          rewrite N.shiftl_1_l, N2Z.inj_pow; destruct (Z.eq_dec i (Z.of_N bit)) as [-> | Hne].
          - unfold Integers.testbit; rewrite Etb; reflexivity.
          - rewrite Z.pow2_bits_false by (try lia; exact Hne); rewrite andb_false_r; reflexivity. }
        pose proof (proj2 Hiz ltac:(rewrite Hnz, (@Integers.unsigned_zero 64%positive); reflexivity)) as Htru; discriminate Htru. }
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond a64_step_flags_match].
    split; [intro; reflexivity | split; [intro; reflexivity | split; [exact I | eexists; split; [reflexivity |]]]].
    rewrite <- Heq_tb; destruct is_nz.
    + exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ Hm_tb ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)).
    + rewrite negb_involutive; exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hm_tb ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)).
  - (* A64_Ret *)
    inversion Hso; inversion Hstep; subst; clear Hso Hstep.
    cbn [aso_rd_write aso_flags_write aso_br_cond a64_step_flags_match].
    split; [intro; reflexivity | split; [intro; reflexivity | split; [exact I | reflexivity]]].
Qed.

