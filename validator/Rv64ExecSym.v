(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * RV64IM Operational Semantics & Symbolic DAG Lowering ([CertValidator.Rv64ExecSym])

    Purpose:
      Defines concrete Sail-RISC-V-aligned operational semantics ([rv_exec]) over 64/32-bit
      registers and private stack memory, plus total symbolic execution ([summarize_rv64_dag])
      lowering RV64IM+RVC streams to [CfgDag.cfg_dag].

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml directly. [summarize_rv64_dag] fails closed
      ([inl err]) on unsupported instructions, undefined-register reads, invalid stack or
      epilogue state, or fuel exhaustion, emitting UB/poison-free [cfg_dag] terms.

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{CertFormat,AigLrat,
      AlgRules,CfgDag,Elf64Spec,McFrameMem,McIsaCommon,Rv64Decode}]; zero custom axioms.

    Section Outline:
      3. Sail-aligned operational semantics ([rv_exec]); 4. Total symbolic DAG lowering
      ([summarize_rv64_dag_at], [summarize_rv64_dag]). *)

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
  Rv64Decode.

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

(** ** 3. Sail-Aligned Operational Semantics over [@Integers.bit_int 64] *)

Definition rv_regfile : Type := N -> @Integers.bit_int 64.

Definition rv_read_reg (r : N) (rf : rv_regfile) : @Integers.bit_int 64 :=
  if N.eqb r 0%N then @Integers.zero 64 else rf r.

Definition rv_write_reg (r : N) (v : @Integers.bit_int 64) (rf : rv_regfile) : rv_regfile :=
  if N.eqb r 0%N then rf else fun r' => if N.eqb r' r then v else rf r'.

Definition rv_is_callee_saved (r : N) : bool :=
  N.eqb r 2%N || ((N.leb 8%N r) && (N.leb r 9%N)) || ((N.leb 18%N r) && (N.leb r 27%N)).

Definition rv_callee_saved_preserved (rf0 rf1 : rv_regfile) : Prop :=
  forall r, rv_is_callee_saved r = true -> rf1 r = rf0 r.

Definition rv_eval_alu_imm_raw
  (op : rv_alu_imm_op) (w : positive) (a : @Integers.bit_int w) (imm : Z)
  : @Integers.bit_int w :=
  let iw := @Integers.repr w imm in
  let sh := rv_mask_shamt w imm in
  match op with
  | RAI_Addi => @Integers.add w a iw
  | RAI_Slti => if @Integers.lt w a iw then @Integers.one w else @Integers.zero w
  | RAI_Sltiu => if @Integers.ltu w a iw then @Integers.one w else @Integers.zero w
  | RAI_Xori => @Integers.xor w a iw
  | RAI_Ori => @Integers.or w a iw
  | RAI_Andi => @Integers.and w a iw
  | RAI_Slli => @Integers.shl w a sh
  | RAI_Srli => @Integers.shru w a sh
  | RAI_Srai => @Integers.shr w a sh
  end.

Definition rv_eval_alu_imm
  (op : rv_alu_imm_op) (is_word : bool) (a : @Integers.bit_int 64) (imm : Z)
  : @Integers.bit_int 64 :=
  if is_word then
    let r32 := rv_eval_alu_imm_raw op 32%positive (@Integers.repr 32 (@Integers.unsigned 64 a)) imm in
    @Integers.repr 64 (@Integers.signed 32 r32)
  else
    rv_eval_alu_imm_raw op 64%positive a imm.

Definition rv_divu_total (w : positive) (a b : @Integers.bit_int w) : @Integers.bit_int w :=
  if Z.eqb (@Integers.unsigned w b) 0%Z then @Integers.mone w
  else @Integers.divu w a b.

Definition rv_modu_total (w : positive) (a b : @Integers.bit_int w) : @Integers.bit_int w :=
  if Z.eqb (@Integers.unsigned w b) 0%Z then a
  else @Integers.modu w a b.

Definition rv_divs_total (w : positive) (a b : @Integers.bit_int w) : @Integers.bit_int w :=
  if Z.eqb (@Integers.signed w b) 0%Z then @Integers.mone w
  else if Z.eqb (@Integers.signed w a) (@Integers.min_signed w) &&
          Z.eqb (@Integers.signed w b) (-1)%Z then @Integers.repr w (@Integers.min_signed w)
  else @Integers.divs w a b.

Definition rv_mods_total (w : positive) (a b : @Integers.bit_int w) : @Integers.bit_int w :=
  if Z.eqb (@Integers.signed w b) 0%Z then a
  else if Z.eqb (@Integers.signed w a) (@Integers.min_signed w) &&
          Z.eqb (@Integers.signed w b) (-1)%Z then @Integers.zero w
  else @Integers.mods w a b.

Definition rv_eval_alu_reg_raw
  (op : rv_alu_reg_op) (w : positive) (a b : @Integers.bit_int w)
  : @Integers.bit_int w :=
  let sh := rv_mask_shamt w (@Integers.unsigned w b) in
  match op with
  | RAR_Add => @Integers.add w a b
  | RAR_Sub => @Integers.sub w a b
  | RAR_Sll => @Integers.shl w a sh
  | RAR_Slt => if @Integers.lt w a b then @Integers.one w else @Integers.zero w
  | RAR_Sltu => if @Integers.ltu w a b then @Integers.one w else @Integers.zero w
  | RAR_Xor => @Integers.xor w a b
  | RAR_Srl => @Integers.shru w a sh
  | RAR_Sra => @Integers.shr w a sh
  | RAR_Or => @Integers.or w a b
  | RAR_And => @Integers.and w a b
  | RAR_Mul => @Integers.mul w a b
  | RAR_Mulh =>
      let p := (@Integers.signed w a * @Integers.signed w b)%Z in
      @Integers.repr w (Z.shiftr p (Z.pos w))
  | RAR_Mulhsu =>
      let p := (@Integers.signed w a * @Integers.unsigned w b)%Z in
      @Integers.repr w (Z.shiftr p (Z.pos w))
  | RAR_Mulhu =>
      let p := (@Integers.unsigned w a * @Integers.unsigned w b)%Z in
      @Integers.repr w (Z.shiftr p (Z.pos w))
  | RAR_Div => rv_divs_total w a b
  | RAR_Divu => rv_divu_total w a b
  | RAR_Rem => rv_mods_total w a b
  | RAR_Remu => rv_modu_total w a b
  end.

Definition rv_eval_alu_reg
  (op : rv_alu_reg_op) (is_word : bool) (a b : @Integers.bit_int 64)
  : @Integers.bit_int 64 :=
  if is_word then
    let r32 :=
      rv_eval_alu_reg_raw op 32%positive
        (@Integers.repr 32 (@Integers.unsigned 64 a))
        (@Integers.repr 32 (@Integers.unsigned 64 b))
    in
    @Integers.repr 64 (@Integers.signed 32 r32)
  else
    rv_eval_alu_reg_raw op 64%positive a b.

Definition rv_eval_br_cond (c : rv_br_cond) (a b : @Integers.bit_int 64) : bool :=
  match c with
  | RBC_Eq => @Integers.eq 64 a b
  | RBC_Ne => negb (@Integers.eq 64 a b)
  | RBC_Lt => @Integers.lt 64 a b
  | RBC_Ge => negb (@Integers.lt 64 a b)
  | RBC_Ltu => @Integers.ltu 64 a b
  | RBC_Geu => negb (@Integers.ltu 64 a b)
  end.

Fixpoint lookup_rv_inst (insts : list decoded_rv_inst) (pc : N) : option decoded_rv_inst :=
  match insts with
  | [] => None
  | d :: rest => if N.eqb (dri_off d) pc then Some d else lookup_rv_inst rest pc
  end.

Fixpoint rv_exec_mem
  (fuel : nat) (insts : list decoded_rv_inst) (pc : N)
  (sp0 : @Integers.bit_int 64) (rf : rv_regfile) (mstk : mc_stack_mem)
  {struct fuel} : option (rv_regfile * mc_stack_mem) :=
  match fuel with
  | O => None
  | S fuel' =>
      match lookup_rv_inst insts pc with
      | None => None
      | Some dec =>
          let next_pc := (pc + dri_len dec)%N in
          match dri_inst dec with
          | RV_Nop => rv_exec_mem fuel' insts next_pc sp0 rf mstk
          | RV_Lui rd imm =>
              rv_exec_mem fuel' insts next_pc sp0 (rv_write_reg rd (@Integers.repr 64 imm) rf) mstk
          | RV_AluImm op is_word rd rs1 imm =>
              let v := rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm in
              rv_exec_mem fuel' insts next_pc sp0 (rv_write_reg rd v rf) mstk
          | RV_AluReg op is_word rd rs1 rs2 =>
              let v := rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) in
              rv_exec_mem fuel' insts next_pc sp0 (rv_write_reg rd v rf) mstk
          | RV_Load sz is_signed rd rs1 imm =>
              let addr := @Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm) in
              let off := mc_addr_to_off sp0 addr in
              let sp_off := mc_addr_to_off sp0 (rv_read_reg 2%N rf) in
              if mc_slot_in_frame sp_off off sz then
                rv_exec_mem fuel' insts next_pc sp0
                  (rv_write_reg rd (mc_stk_load mstk off sz is_signed) rf) mstk
              else None
          | RV_Store sz rs1 rs2 imm =>
              let addr := @Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm) in
              let off := mc_addr_to_off sp0 addr in
              let sp_off := mc_addr_to_off sp0 (rv_read_reg 2%N rf) in
              if mc_slot_in_frame sp_off off sz then
                rv_exec_mem fuel' insts next_pc sp0 rf
                  (mc_stk_store mstk off sz (rv_read_reg rs2 rf))
              else None
          | RV_Jal0 rel =>
              match add_rel_off pc rel with
              | None => None
              | Some tgt_pc => rv_exec_mem fuel' insts tgt_pc sp0 rf mstk
              end
          | RV_Branch cond rs1 rs2 rel =>
              if rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) then
                match add_rel_off pc rel with
                | None => None
                | Some tgt_pc => rv_exec_mem fuel' insts tgt_pc sp0 rf mstk
                end
              else
                rv_exec_mem fuel' insts next_pc sp0 rf mstk
          | RV_Ret => Some (rf, mstk)
          end
      end
  end.

Definition rv_exec
  (fuel : nat) (insts : list decoded_rv_inst) (pc : N) (rf : rv_regfile)
  : option rv_regfile :=
  option_map fst (rv_exec_mem fuel insts pc (rv_read_reg 2%N rf) rf mc_empty_stack).

(** ** 4. Total Symbolic DAG Lowering to [CfgDag.cfg_dag] *)

Definition rv_init_arg_expr (spec : rv_arg_spec) : cert_expr :=
  let v := CE_Var (ras_name spec) (ras_width spec) in
  if Pos.eqb (ras_width spec) 64%positive then v
  else
    match ras_ext spec with
    | RAE_ZeroExt => CE_Cast CCK_ZExt (ras_width spec) 64%positive no_cast_flags v
    | RAE_SignExt | RAE_None => CE_Cast CCK_SExt (ras_width spec) 64%positive no_cast_flags v
    end.

Definition sym_br_cond (c : rv_br_cond) (a b : cert_expr) : cert_expr :=
  let pr :=
    match c with
    | RBC_Eq => CIP_Eq
    | RBC_Ne => CIP_Ne
    | RBC_Lt => CIP_Slt
    | RBC_Ge => CIP_Sge
    | RBC_Ltu => CIP_Ult
    | RBC_Geu => CIP_Uge
    end
  in
  CE_ICmp pr false 64%positive a b.

Definition sym_alu_imm_raw (op : rv_alu_imm_op) (w : positive) (a : cert_expr) (imm : Z)
  : cert_expr :=
  let iw := ce_bv_z w imm in
  let sh := CE_BvConst w (Z.to_N (imm mod Z.pos w)) in
  let cmp_res pr :=
    CE_Cast CCK_ZExt 1%positive w no_cast_flags (CE_ICmp pr false w a iw)
  in
  match op with
  | RAI_Addi => CE_BinOp CB_Add w no_binop_flags a iw
  | RAI_Slti => cmp_res CIP_Slt
  | RAI_Sltiu => cmp_res CIP_Ult
  | RAI_Xori => CE_BinOp CB_Xor w no_binop_flags a iw
  | RAI_Ori => CE_BinOp CB_Or w no_binop_flags a iw
  | RAI_Andi => CE_BinOp CB_And w no_binop_flags a iw
  | RAI_Slli => CE_BinOp CB_Shl w no_binop_flags a sh
  | RAI_Srli => CE_BinOp CB_LShr w no_binop_flags a sh
  | RAI_Srai => CE_BinOp CB_AShr w no_binop_flags a sh
  end.

Definition sym_alu_imm (op : rv_alu_imm_op) (is_word : bool) (a : cert_expr) (imm : Z)
  : cert_expr :=
  if is_word then
    ce_sext32_64 (sym_alu_imm_raw op 32%positive (ce_trunc64_32 a) imm)
  else
    sym_alu_imm_raw op 64%positive a imm.

Definition sym_div_rem_guarded (op : cert_binop) (w : positive) (a b : cert_expr)
  : cert_expr :=
  let z0 := CE_BvConst w 0%N in
  let ones := ce_all_ones w in
  let is_z := CE_ICmp CIP_Eq false w b z0 in
  match op with
  | CB_UDiv =>
      let sb := CE_Select w is_z (CE_BvConst w 1%N) b in
      CE_Select w is_z ones (CE_BinOp CB_UDiv w no_binop_flags a sb)
  | CB_URem =>
      let sb := CE_Select w is_z (CE_BvConst w 1%N) b in
      CE_Select w is_z a (CE_BinOp CB_URem w no_binop_flags a sb)
  | CB_SDiv =>
      let imin := ce_int_min w in
      let is_ovf :=
        CE_BinOp CB_And 1%positive no_binop_flags
          (CE_ICmp CIP_Eq false w a imin)
          (CE_ICmp CIP_Eq false w b ones)
      in
      let bad := CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf in
      let sa := CE_Select w is_ovf z0 a in
      let sb := CE_Select w bad (CE_BvConst w 1%N) b in
      CE_Select w is_z ones
        (CE_Select w is_ovf imin (CE_BinOp CB_SDiv w no_binop_flags sa sb))
  | _ =>
      let imin := ce_int_min w in
      let is_ovf :=
        CE_BinOp CB_And 1%positive no_binop_flags
          (CE_ICmp CIP_Eq false w a imin)
          (CE_ICmp CIP_Eq false w b ones)
      in
      let bad := CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf in
      let sa := CE_Select w is_ovf z0 a in
      let sb := CE_Select w bad (CE_BvConst w 1%N) b in
      CE_Select w is_z a
        (CE_Select w is_ovf z0 (CE_BinOp CB_SRem w no_binop_flags sa sb))
  end.

Definition sym_mulhi64 (sa_signed sb_signed : bool) (a b : cert_expr) : cert_expr :=
  let a128 := if sa_signed then ce_sext64_128 a else ce_zext64_128 a in
  let b128 := if sb_signed then ce_sext64_128 b else ce_zext64_128 b in
  let prod := CE_BinOp CB_Mul 128%positive no_binop_flags a128 b128 in
  let shifted := CE_BinOp CB_LShr 128%positive no_binop_flags prod (CE_BvConst 128%positive 64%N) in
  ce_trunc128_64 shifted.

Definition sym_alu_reg_raw (op : rv_alu_reg_op) (w : positive) (a b : cert_expr)
  : cert_expr :=
  let sh_mask := CE_BvConst w (Z.to_N (Z.pos w - 1)) in
  let sh := CE_BinOp CB_And w no_binop_flags b sh_mask in
  let cmp_res pr :=
    CE_Cast CCK_ZExt 1%positive w no_cast_flags (CE_ICmp pr false w a b)
  in
  match op with
  | RAR_Add => CE_BinOp CB_Add w no_binop_flags a b
  | RAR_Sub => CE_BinOp CB_Sub w no_binop_flags a b
  | RAR_Sll => CE_BinOp CB_Shl w no_binop_flags a sh
  | RAR_Slt => cmp_res CIP_Slt
  | RAR_Sltu => cmp_res CIP_Ult
  | RAR_Xor => CE_BinOp CB_Xor w no_binop_flags a b
  | RAR_Srl => CE_BinOp CB_LShr w no_binop_flags a sh
  | RAR_Sra => CE_BinOp CB_AShr w no_binop_flags a sh
  | RAR_Or => CE_BinOp CB_Or w no_binop_flags a b
  | RAR_And => CE_BinOp CB_And w no_binop_flags a b
  | RAR_Mul => CE_BinOp CB_Mul w no_binop_flags a b
  | RAR_Mulh => sym_mulhi64 true true a b
  | RAR_Mulhsu => sym_mulhi64 true false a b
  | RAR_Mulhu => sym_mulhi64 false false a b
  | RAR_Div => sym_div_rem_guarded CB_SDiv w a b
  | RAR_Divu => sym_div_rem_guarded CB_UDiv w a b
  | RAR_Rem => sym_div_rem_guarded CB_SRem w a b
  | RAR_Remu => sym_div_rem_guarded CB_URem w a b
  end.

Definition sym_alu_reg (op : rv_alu_reg_op) (is_word : bool) (a b : cert_expr)
  : cert_expr :=
  if is_word then
    ce_sext32_64 (sym_alu_reg_raw op 32%positive (ce_trunc64_32 a) (ce_trunc64_32 b))
  else
    sym_alu_reg_raw op 64%positive a b.

Definition rv_sym_regs : Type := N -> cert_expr.
Definition rv_def_mask : Type := N -> bool.

Definition rv_sym_read (r : N) (srf : rv_sym_regs) : cert_expr :=
  if N.eqb r 0%N then CE_BvConst 64%positive 0%N else srf r.

Definition rv_sym_write (r : N) (e : cert_expr) (srf : rv_sym_regs) : rv_sym_regs :=
  if N.eqb r 0%N then srf else fun r' => if N.eqb r' r then e else srf r'.

Definition rv_def_read (r : N) (def : rv_def_mask) : bool :=
  if N.eqb r 0%N then true else def r.

Definition rv_def_write (r : N) (def : rv_def_mask) : rv_def_mask :=
  if N.eqb r 0%N then def else fun r' => if N.eqb r' r then true else def r'.

Fixpoint n_in_list (x : N) (xs : list N) : bool :=
  match xs with
  | [] => false
  | y :: rest => N.eqb x y || n_in_list x rest
  end.

Fixpoint rv_build_init_state
  (idx : N) (specs : list rv_arg_spec)
  : rv_sym_regs * rv_def_mask :=
  match specs with
  | [] => ((fun _ => CE_BvConst 64%positive 0%N), (fun r => N.eqb r 0%N))
  | sp :: rest =>
      let '(srf', def') := rv_build_init_state (N.succ idx) rest in
      let e := rv_init_arg_expr sp in
      ((fun r => if N.eqb r idx then e else srf' r),
       (fun r => N.eqb r idx || def' r))
  end.

Definition rv_val_regs : Type := N -> mc_sym_val.

Definition rv_val_read (r : N) (vrf : rv_val_regs) : mc_sym_val :=
  if N.eqb r 0%N then MSV_Expr (CE_BvConst 64%positive 0%N) else vrf r.

Definition rv_val_write (r : N) (sv : mc_sym_val) (vrf : rv_val_regs) : rv_val_regs :=
  if N.eqb r 0%N then vrf else fun r' => if N.eqb r' r then sv else vrf r'.

Definition rv_preserved_non_sp_regs : list N :=
  [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%N.

Definition rv_sym_epilogue_ok (sp_off : Z) (vrf : rv_val_regs) : bool :=
  Z.eqb sp_off 0%Z &&
  (match rv_val_read 2%N vrf with MSV_StackPtr 0%Z => true | _ => false end) &&
  forallb
    (fun r =>
       match rv_val_read r vrf with
       | MSV_SavedReg r0 => N.eqb r0 r
       | _ => false
       end)
    rv_preserved_non_sp_regs.

Definition rv_empty_val_regs : rv_val_regs :=
  fun r =>
    if N.eqb r 0%N then MSV_Expr (CE_BvConst 64%positive 0%N)
    else if N.eqb r 2%N then MSV_StackPtr 0%Z
    else if n_in_list r rv_preserved_non_sp_regs then MSV_SavedReg r
    else MSV_Undef.

Fixpoint rv_build_init_val_regs
  (idx : N) (specs : list rv_arg_spec) : rv_val_regs :=
  match specs with
  | [] => rv_empty_val_regs
  | sp :: rest =>
      let vrf' := rv_build_init_val_regs (N.succ idx) rest in
      let e := rv_init_arg_expr sp in
      fun r => if N.eqb r idx then MSV_Expr e else vrf' r
  end.

Lemma lookup_rv_inst_eq_key : forall insts pc,
  lookup_rv_inst insts pc = lookup_by_key dri_off insts pc.
Proof.
  induction insts as [| d rest IH]; intro pc; cbn; [reflexivity |].
  destruct (N.eqb (dri_off d) pc); [reflexivity | exact (IH pc)].
Qed.

Lemma pt_of_list_first_lookup_rv : forall insts pc,
  pt_get (N.succ_pos pc) (pt_of_list_first dri_off insts) = lookup_rv_inst insts pc.
Proof.
  intros insts pc; rewrite pt_of_list_first_get, lookup_rv_inst_eq_key; reflexivity.
Qed.

Definition rv_sym_step_write
  (rd : N) (sv : mc_sym_val) (sp_off : Z) (vrf : rv_val_regs) (astk : mc_sym_stack)
  : option (Z * rv_val_regs * mc_sym_stack) :=
  if N.eqb rd 2%N then
    match sv with
    | MSV_StackPtr off' =>
        if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then
          Some (off', rv_val_write 2%N (MSV_StackPtr off') vrf, mc_sym_stk_prune off' astk)
        else None
    | _ => None
    end
  else Some (sp_off, rv_val_write rd sv vrf, astk).

Fixpoint summarize_rv64_dag_at
  (fuel : nat) (im : pos_trie decoded_rv_inst) (visited : pos_trie unit)
  (pc : N) (sp_off : Z) (vrf : rv_val_regs) (astk : mc_sym_stack) (ret_w : positive)
  {struct fuel} : string + cfg_dag :=
  let loc (_ : unit) : string :=
    ("rv64 at pc=" ++ diag_N_hex pc ++ " sp-off=" ++ diag_Z_dec sp_off)%string
  in
  if pt_has_n pc visited then
    inl (diag "mc-exec" ("cycle/loop detected in rv64 acyclic DAG mode (" ++ loc tt ++ "); provide a (loop ...) certificate"))
  else
    match fuel with
    | O => inl (diag "mc-exec" ("rv64 symbolic execution fuel exhausted (" ++ loc tt ++ ")"))
    | S fuel' =>
        match pt_get (N.succ_pos pc) im with
        | None => inl (diag "mc-exec" ("rv64 execution escaped function slice (" ++ loc tt ++ ")"))
        | Some dec =>
            let next_pc := (pc + dri_len dec)%N in
            let visited' := pt_add_n pc visited in
            match dri_inst dec with
            | RV_Nop =>
                summarize_rv64_dag_at fuel' im visited' next_pc sp_off vrf astk ret_w
            | RV_Lui rd imm =>
                match rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk with
                | None => inl (diag "mc-frame" ("invalid sp/register write in rv64 lui (" ++ loc tt ++ ")"))
                | Some (sp_off', vrf', astk') =>
                    summarize_rv64_dag_at fuel' im visited' next_pc sp_off' vrf' astk' ret_w
                end
            | RV_AluImm op is_word rd rs1 imm =>
                let sv_opt :=
                  match op, is_word, rv_val_read rs1 vrf with
                  | RAI_Addi, false, MSV_StackPtr base_off =>
                      let off' := (base_off + imm)%Z in
                      if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z
                      then Some (MSV_StackPtr off')
                      else None
                  | RAI_Addi, false, MSV_SavedReg r0 =>
                      if Z.eqb imm 0%Z then Some (MSV_SavedReg r0) else None
                  | _, _, MSV_Expr e =>
                      Some (MSV_Expr (sym_alu_imm op is_word e imm))
                  | _, _, _ => None
                  end
                in
                match sv_opt with
                | None =>
                    inl (diag (if N.eqb rd 2%N || N.eqb rs1 2%N then "mc-frame" else "mc-exec")
                          ("unsupported alu-imm operand or out-of-frame sp update in rv64 (" ++ loc tt ++ ")"))
                | Some sv =>
                    match rv_sym_step_write rd sv sp_off vrf astk with
                    | None =>
                        inl (diag "mc-frame" ("invalid sp update or frame bound violation in rv64 alu-imm (" ++ loc tt ++ ")"))
                    | Some (sp_off', vrf', astk') =>
                        summarize_rv64_dag_at fuel' im visited' next_pc sp_off' vrf' astk' ret_w
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
                    | MSV_Expr e1, MSV_Expr e2 =>
                        Some (MSV_Expr (sym_alu_reg op is_word e1 e2))
                    | _, _ => None
                    end
                in
                match sv_opt with
                | None =>
                    inl (diag "mc-exec" ("undefined or non-expression operand in rv64 alu-reg (" ++ loc tt ++ ")"))
                | Some sv =>
                    match rv_sym_step_write rd sv sp_off vrf astk with
                    | None =>
                        inl (diag "mc-frame" ("invalid sp update in rv64 alu-reg (" ++ loc tt ++ ")"))
                    | Some (sp_off', vrf', astk') =>
                        summarize_rv64_dag_at fuel' im visited' next_pc sp_off' vrf' astk' ret_w
                    end
                end
            | RV_Load sz is_signed rd rs1 imm =>
                match rv_val_read rs1 vrf with
                | MSV_StackPtr base_off =>
                    let off := (base_off + imm)%Z in
                    if mc_slot_in_frame sp_off off sz then
                      match mc_sym_stk_load off sz is_signed astk with
                      | None =>
                          inl (diag "mc-frame" ("rv64 load from uninitialized stack slot sp+" ++ diag_Z_dec off ++ " (" ++ loc tt ++ ")"))
                      | Some sv =>
                          match rv_sym_step_write rd sv sp_off vrf astk with
                          | None =>
                              inl (diag "mc-frame" ("invalid sp/register write from rv64 load (" ++ loc tt ++ ")"))
                          | Some (sp_off', vrf', astk') =>
                              summarize_rv64_dag_at fuel' im visited' next_pc sp_off' vrf' astk' ret_w
                          end
                      end
                    else
                      inl (diag "mc-frame"
                        ("rv64 load at sp+" ++ diag_Z_dec off ++ " (size " ++ diag_Z_dec (mc_mem_bytes_Z sz) ++
                         ") out of frame bounds (" ++ loc tt ++ ")"))
                | _ =>
                    inl (diag "mc-frame" ("rv64 load base register x" ++ diag_N_dec rs1 ++ " is not a stack pointer (" ++ loc tt ++ ")"))
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
                        let astk' := mc_sym_stk_store off sz sv astk in
                        summarize_rv64_dag_at fuel' im visited' next_pc sp_off vrf astk' ret_w
                      else
                        inl (diag "mc-frame"
                          ("invalid or narrow stack store of register x" ++ diag_N_dec rs2 ++
                           " at sp+" ++ diag_Z_dec off ++ " (" ++ loc tt ++ ")"))
                    else
                      inl (diag "mc-frame"
                        ("rv64 store at sp+" ++ diag_Z_dec off ++ " (size " ++ diag_Z_dec (mc_mem_bytes_Z sz) ++
                         ") out of frame bounds (" ++ loc tt ++ ")"))
                | _ =>
                    inl (diag "mc-frame" ("rv64 store base register x" ++ diag_N_dec rs1 ++ " is not a stack pointer (" ++ loc tt ++ ")"))
                end
            | RV_Jal0 rel =>
                match add_rel_off pc rel with
                | None => inl (diag "mc-exec" ("negative rv64 jump target (" ++ loc tt ++ ")"))
                | Some tgt_pc =>
                    summarize_rv64_dag_at fuel' im visited' tgt_pc sp_off vrf astk ret_w
                end
            | RV_Branch cond rs1 rs2 rel =>
                match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
                | MSV_Expr e1, MSV_Expr e2 =>
                    match add_rel_off pc rel with
                    | None => inl (diag "mc-exec" ("negative rv64 branch target (" ++ loc tt ++ ")"))
                    | Some tgt_pc =>
                        let c_e := sym_br_cond cond e1 e2 in
                        match summarize_rv64_dag_at fuel' im visited' tgt_pc sp_off vrf astk ret_w with
                        | inl err => inl err
                        | inr d_t =>
                            match summarize_rv64_dag_at fuel' im visited' next_pc sp_off vrf astk ret_w with
                            | inl err => inl err
                            | inr d_f => inr (CD_Branch c_e d_t d_f)
                            end
                        end
                    end
                | _, _ => inl (diag "mc-exec" ("non-expression branch operand in rv64 (" ++ loc tt ++ ")"))
                end
            | RV_Ret =>
                if rv_sym_epilogue_ok sp_off vrf then
                  match rv_val_read 10%N vrf with
                  | MSV_Expr e_ret =>
                      inr (CD_RetScalar ret_w (rv_trunc_ret_expr ret_w e_ret))
                  | _ =>
                      inl (diag "mc-exec" ("return register a0/x10 does not hold a value expression at rv64 ret (" ++ loc tt ++ ")"))
                  end
                else
                  inl (diag "mc-frame"
                    ((if negb (Z.eqb sp_off 0%Z)
                      then "unrestored stack pointer"
                      else "clobbered callee-saved register or ra") ++ " at rv64 ret (" ++ loc tt ++ ")"))
            end
        end
    end.

Definition summarize_rv64_dag
  (fuel : nat) (insts : list decoded_rv_inst)
  (arg_specs : list rv_arg_spec) (ret_w : positive) : string + cfg_dag :=
  if negb (Nat.leb (List.length arg_specs) 8) then
    inl (diag "mc-exec" ("too many argument specs (" ++ diag_nat_dec (List.length arg_specs) ++ " > 8)"))
  else if negb (forallb rv_valid_arg_spec arg_specs) then
    inl (diag "mc-exec" "invalid argument spec for rv64 symbolic execution")
  else if negb (rv_supported_arg_width ret_w) then
    inl (diag "mc-exec" ("unsupported return width " ++ diag_pos_dec ret_w ++ " for rv64 symbolic execution"))
  else
    let vrf0 := rv_build_init_val_regs 10%N arg_specs in
    let im := pt_of_list_first dri_off insts in
    summarize_rv64_dag_at fuel im (@PT_Empty unit) 0%N 0%Z vrf0 [] ret_w.

