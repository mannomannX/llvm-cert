(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified [RV64IM] + [RVC] Instruction Decoder, Operational Semantics & Symbolic DAG Lowering

    Implements for Milestone M1 of Phase [8.3a] ([CertValidator.Rv64Sem]):
    1. Canonical [RV64IM] + [RVC] AST and total little-endian mixed 16/32-bit
       decoder ([decode_rv64_bytes]).
    2. Concrete Sail-RISC-V-aligned operational semantics ([rv_eval_alu_imm],
       [rv_eval_alu_reg], [rv_eval_br_cond], [rv_exec]) over [@Integers.bit_int 64]
       and [@Integers.bit_int 32] with exact LP64 callee-saved preservation.
    3. Verified symbolic execution ([summarize_rv64_dag]) emitting well-typed,
       total, UB-free and poison-free [CertValidator.CertValidator.cfg_dag] terms
       using an explicit undefined-register mask so arbitrary initial scratch
       registers cannot unsoundly verify.
    4. Machine-checked semantic equivalence ([summarize_rv64_dag_sound], [Qed.])
       between the concrete machine execution [rv_exec] and [eval_cfg_dag],
       checked with zero custom axioms. *)

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
  CertValidator
  Elf64Spec
  McFrameMem.

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

(** ** 1. Canonical [RV64IM + RVC] Instruction AST *)

Variant rv_alu_imm_op : Set :=
| RAI_Addi
| RAI_Slti
| RAI_Sltiu
| RAI_Xori
| RAI_Ori
| RAI_Andi
| RAI_Slli
| RAI_Srli
| RAI_Srai.

Variant rv_alu_reg_op : Set :=
| RAR_Add
| RAR_Sub
| RAR_Sll
| RAR_Slt
| RAR_Sltu
| RAR_Xor
| RAR_Srl
| RAR_Sra
| RAR_Or
| RAR_And
| RAR_Mul
| RAR_Mulh
| RAR_Mulhsu
| RAR_Mulhu
| RAR_Div
| RAR_Divu
| RAR_Rem
| RAR_Remu.

Variant rv_br_cond : Set :=
| RBC_Eq
| RBC_Ne
| RBC_Lt
| RBC_Ge
| RBC_Ltu
| RBC_Geu.

Variant rv_inst : Set :=
| RV_Nop
| RV_Lui (rd : N) (imm_shifted : Z)
| RV_AluImm (op : rv_alu_imm_op) (is_word : bool) (rd rs1 : N) (imm : Z)
| RV_AluReg (op : rv_alu_reg_op) (is_word : bool) (rd rs1 rs2 : N)
| RV_Load (sz : mc_mem_size) (is_signed : bool) (rd rs1 : N) (imm : Z)
| RV_Store (sz : mc_mem_size) (rs1 rs2 : N) (imm : Z)
| RV_Branch (cond : rv_br_cond) (rs1 rs2 : N) (rel_off : Z)
| RV_Jal0 (rel_off : Z)
| RV_Ret.

Record decoded_rv_inst : Set := mk_decoded_rv {
  dri_off : N;
  dri_len : N;
  dri_inst : rv_inst;
}.

(** ** 2. Total Mixed 16/32-Bit [RV64IM + RVC] Decoder *)

Definition bit_slice (v lo len : N) : N :=
  N.modulo (N.div v (N.pow 2%N lo)) (N.pow 2%N len).

Definition sext_z (v bits : N) : Z :=
  let m := Z.pow 2 (Z.of_N bits) in
  let h := Z.pow 2 (Z.of_N bits - 1) in
  let zv := ((Z.of_N v) mod m)%Z in
  if Z.geb zv h then (zv - m)%Z else zv.

Definition c_reg (bits3 : N) : N :=
  (8%N + N.modulo bits3 8%N)%N.

Definition decode_rvc_hw (hw : N) : option rv_inst :=
  if N.eqb hw 0%N then None
  else
    let op := bit_slice hw 0%N 2%N in
    let funct3 := bit_slice hw 13%N 3%N in
    if N.eqb op 0%N then
      let rd_p := c_reg (bit_slice hw 2%N 3%N) in
      let rs1_p := c_reg (bit_slice hw 7%N 3%N) in
      if N.eqb funct3 0%N then
        let nzuimm :=
          (bit_slice hw 6%N 1%N * 4%N +
           bit_slice hw 5%N 1%N * 8%N +
           bit_slice hw 11%N 2%N * 16%N +
           bit_slice hw 7%N 4%N * 64%N)%N
        in
        if N.eqb nzuimm 0%N then None
        else Some (RV_AluImm RAI_Addi false rd_p 2%N (Z.of_N nzuimm))
      else if N.eqb funct3 2%N || N.eqb funct3 6%N then
        let uimm_w :=
          (bit_slice hw 6%N 1%N * 4%N +
           bit_slice hw 10%N 3%N * 8%N +
           bit_slice hw 5%N 1%N * 64%N)%N
        in
        if N.eqb funct3 2%N then Some (RV_Load MS_4 true rd_p rs1_p (Z.of_N uimm_w))
        else Some (RV_Store MS_4 rs1_p rd_p (Z.of_N uimm_w))
      else if N.eqb funct3 3%N || N.eqb funct3 7%N then
        let uimm_d :=
          (bit_slice hw 10%N 3%N * 8%N +
           bit_slice hw 5%N 2%N * 64%N)%N
        in
        if N.eqb funct3 3%N then Some (RV_Load MS_8 true rd_p rs1_p (Z.of_N uimm_d))
        else Some (RV_Store MS_8 rs1_p rd_p (Z.of_N uimm_d))
      else None
    else if N.eqb op 1%N then
      let rd := bit_slice hw 7%N 5%N in
      let rd_p := c_reg (bit_slice hw 7%N 3%N) in
      let rs2_p := c_reg (bit_slice hw 2%N 3%N) in
      let imm6_raw := (bit_slice hw 12%N 1%N * 32%N + bit_slice hw 2%N 5%N)%N in
      let imm6 := sext_z imm6_raw 6%N in
      if N.eqb funct3 0%N then
        if N.eqb rd 0%N then Some RV_Nop
        else Some (RV_AluImm RAI_Addi false rd rd imm6)
      else if N.eqb funct3 1%N then
        if N.eqb rd 0%N then None
        else Some (RV_AluImm RAI_Addi true rd rd imm6)
      else if N.eqb funct3 2%N then
        if N.eqb rd 0%N then Some RV_Nop
        else Some (RV_AluImm RAI_Addi false rd 0%N imm6)
      else if N.eqb funct3 3%N then
        if N.eqb imm6_raw 0%N then None
        else if N.eqb rd 2%N then
          let nzimm10 :=
            (bit_slice hw 6%N 1%N * 16%N +
             bit_slice hw 2%N 1%N * 32%N +
             bit_slice hw 5%N 1%N * 64%N +
             bit_slice hw 3%N 2%N * 128%N +
             bit_slice hw 12%N 1%N * 512%N)%N
          in
          Some (RV_AluImm RAI_Addi false 2%N 2%N (sext_z nzimm10 10%N))
        else
          let imm_hi := sext_z (imm6_raw * 4096%N) 18%N in
          Some (RV_Lui rd imm_hi)
      else if N.eqb funct3 4%N then
        let f2 := bit_slice hw 10%N 2%N in
        if N.eqb f2 0%N then Some (RV_AluImm RAI_Srli false rd_p rd_p (Z.of_N imm6_raw))
        else if N.eqb f2 1%N then Some (RV_AluImm RAI_Srai false rd_p rd_p (Z.of_N imm6_raw))
        else if N.eqb f2 2%N then Some (RV_AluImm RAI_Andi false rd_p rd_p imm6)
        else
          let bit12 := bit_slice hw 12%N 1%N in
          let sub_op := bit_slice hw 5%N 2%N in
          if N.eqb bit12 0%N then
            if N.eqb sub_op 0%N then Some (RV_AluReg RAR_Sub false rd_p rd_p rs2_p)
            else if N.eqb sub_op 1%N then Some (RV_AluReg RAR_Xor false rd_p rd_p rs2_p)
            else if N.eqb sub_op 2%N then Some (RV_AluReg RAR_Or false rd_p rd_p rs2_p)
            else Some (RV_AluReg RAR_And false rd_p rd_p rs2_p)
          else
            if N.eqb sub_op 0%N then Some (RV_AluReg RAR_Sub true rd_p rd_p rs2_p)
            else if N.eqb sub_op 1%N then Some (RV_AluReg RAR_Add true rd_p rd_p rs2_p)
            else None
      else if N.eqb funct3 5%N then
        let j12 :=
          (bit_slice hw 12%N 1%N * 2048%N +
           bit_slice hw 8%N 1%N * 1024%N +
           bit_slice hw 9%N 2%N * 256%N +
           bit_slice hw 6%N 1%N * 128%N +
           bit_slice hw 7%N 1%N * 64%N +
           bit_slice hw 2%N 1%N * 32%N +
           bit_slice hw 11%N 1%N * 16%N +
           bit_slice hw 3%N 3%N * 2%N)%N
        in
        Some (RV_Jal0 (sext_z j12 12%N))
      else if N.eqb funct3 6%N || N.eqb funct3 7%N then
        let b9 :=
          (bit_slice hw 12%N 1%N * 256%N +
           bit_slice hw 5%N 2%N * 64%N +
           bit_slice hw 2%N 1%N * 32%N +
           bit_slice hw 10%N 2%N * 8%N +
           bit_slice hw 3%N 2%N * 2%N)%N
        in
        let cond := if N.eqb funct3 6%N then RBC_Eq else RBC_Ne in
        Some (RV_Branch cond rd_p 0%N (sext_z b9 9%N))
      else None
    else if N.eqb op 2%N then
      let rd := bit_slice hw 7%N 5%N in
      let rs2 := bit_slice hw 2%N 5%N in
      let b12 := bit_slice hw 12%N 1%N in
      let imm6_u := (b12 * 32%N + rs2)%N in
      if N.eqb funct3 0%N then
        if N.eqb rd 0%N then None
        else Some (RV_AluImm RAI_Slli false rd rd (Z.of_N imm6_u))
      else if N.eqb funct3 2%N then
        if N.eqb rd 0%N then None
        else
          let uimm := (bit_slice hw 4%N 3%N * 4%N + b12 * 32%N + bit_slice hw 2%N 2%N * 64%N)%N in
          Some (RV_Load MS_4 true rd 2%N (Z.of_N uimm))
      else if N.eqb funct3 3%N then
        if N.eqb rd 0%N then None
        else
          let uimm := (bit_slice hw 5%N 2%N * 8%N + b12 * 32%N + bit_slice hw 2%N 3%N * 64%N)%N in
          Some (RV_Load MS_8 true rd 2%N (Z.of_N uimm))
      else if N.eqb funct3 4%N then
        if N.eqb b12 0%N && N.eqb rs2 0%N then
          if N.eqb rd 1%N then Some RV_Ret else None
        else if N.eqb b12 0%N then
          if N.eqb rd 0%N then None
          else Some (RV_AluReg RAR_Add false rd 0%N rs2)
        else if N.eqb rd 0%N || N.eqb rs2 0%N then None
        else Some (RV_AluReg RAR_Add false rd rd rs2)
      else if N.eqb funct3 6%N then
        let uimm := (bit_slice hw 9%N 4%N * 4%N + bit_slice hw 7%N 2%N * 64%N)%N in
        Some (RV_Store MS_4 2%N rs2 (Z.of_N uimm))
      else if N.eqb funct3 7%N then
        let uimm := (bit_slice hw 10%N 3%N * 8%N + bit_slice hw 7%N 3%N * 64%N)%N in
        Some (RV_Store MS_8 2%N rs2 (Z.of_N uimm))
      else None
    else None.

Definition decode_rv32_word (w : N) : option rv_inst :=
  let opcode := bit_slice w 0%N 7%N in
  let rd := bit_slice w 7%N 5%N in
  let funct3 := bit_slice w 12%N 3%N in
  let rs1 := bit_slice w 15%N 5%N in
  let rs2 := bit_slice w 20%N 5%N in
  let funct7 := bit_slice w 25%N 7%N in
  let imm12 := sext_z (bit_slice w 20%N 12%N) 12%N in
  if N.eqb opcode 55%N then
    (* 0x37 LUI *)
    Some (RV_Lui rd (sext_z (bit_slice w 12%N 20%N * 4096%N) 32%N))
  else if N.eqb opcode 19%N then
    (* 0x13 OP-IMM *)
    let top6 := bit_slice w 26%N 6%N in
    let sh6 := Z.of_N (bit_slice w 20%N 6%N) in
    if N.eqb funct3 0%N then Some (RV_AluImm RAI_Addi false rd rs1 imm12)
    else if N.eqb funct3 2%N then Some (RV_AluImm RAI_Slti false rd rs1 imm12)
    else if N.eqb funct3 3%N then Some (RV_AluImm RAI_Sltiu false rd rs1 imm12)
    else if N.eqb funct3 4%N then Some (RV_AluImm RAI_Xori false rd rs1 imm12)
    else if N.eqb funct3 6%N then Some (RV_AluImm RAI_Ori false rd rs1 imm12)
    else if N.eqb funct3 7%N then Some (RV_AluImm RAI_Andi false rd rs1 imm12)
    else if N.eqb funct3 1%N then
      if N.eqb top6 0%N then Some (RV_AluImm RAI_Slli false rd rs1 sh6) else None
    else if N.eqb funct3 5%N then
      if N.eqb top6 0%N then Some (RV_AluImm RAI_Srli false rd rs1 sh6)
      else if N.eqb top6 16%N then Some (RV_AluImm RAI_Srai false rd rs1 sh6)
      else None
    else None
  else if N.eqb opcode 27%N then
    (* 0x1b OP-IMM-32 *)
    let sh5 := Z.of_N rs2 in
    if N.eqb funct3 0%N then Some (RV_AluImm RAI_Addi true rd rs1 imm12)
    else if N.eqb funct3 1%N then
      if N.eqb funct7 0%N then Some (RV_AluImm RAI_Slli true rd rs1 sh5) else None
    else if N.eqb funct3 5%N then
      if N.eqb funct7 0%N then Some (RV_AluImm RAI_Srli true rd rs1 sh5)
      else if N.eqb funct7 32%N then Some (RV_AluImm RAI_Srai true rd rs1 sh5)
      else None
    else None
  else if N.eqb opcode 51%N then
    (* 0x33 RV64IM OP *)
    let op_opt :=
      if N.eqb funct7 0%N then
        if N.eqb funct3 0%N then Some RAR_Add
        else if N.eqb funct3 1%N then Some RAR_Sll
        else if N.eqb funct3 2%N then Some RAR_Slt
        else if N.eqb funct3 3%N then Some RAR_Sltu
        else if N.eqb funct3 4%N then Some RAR_Xor
        else if N.eqb funct3 5%N then Some RAR_Srl
        else if N.eqb funct3 6%N then Some RAR_Or
        else Some RAR_And
      else if N.eqb funct7 32%N then
        if N.eqb funct3 0%N then Some RAR_Sub
        else if N.eqb funct3 5%N then Some RAR_Sra
        else None
      else if N.eqb funct7 1%N then
        if N.eqb funct3 0%N then Some RAR_Mul
        else if N.eqb funct3 1%N then Some RAR_Mulh
        else if N.eqb funct3 2%N then Some RAR_Mulhsu
        else if N.eqb funct3 3%N then Some RAR_Mulhu
        else if N.eqb funct3 4%N then Some RAR_Div
        else if N.eqb funct3 5%N then Some RAR_Divu
        else if N.eqb funct3 6%N then Some RAR_Rem
        else Some RAR_Remu
      else None
    in
    option_map (fun op => RV_AluReg op false rd rs1 rs2) op_opt
  else if N.eqb opcode 59%N then
    (* 0x3b RV64IM OP-32 *)
    let op_opt :=
      if N.eqb funct7 0%N then
        if N.eqb funct3 0%N then Some RAR_Add
        else if N.eqb funct3 1%N then Some RAR_Sll
        else if N.eqb funct3 5%N then Some RAR_Srl
        else None
      else if N.eqb funct7 32%N then
        if N.eqb funct3 0%N then Some RAR_Sub
        else if N.eqb funct3 5%N then Some RAR_Sra
        else None
      else if N.eqb funct7 1%N then
        if N.eqb funct3 0%N then Some RAR_Mul
        else if N.eqb funct3 4%N then Some RAR_Div
        else if N.eqb funct3 5%N then Some RAR_Divu
        else if N.eqb funct3 6%N then Some RAR_Rem
        else if N.eqb funct3 7%N then Some RAR_Remu
        else None
      else None
    in
    option_map (fun op => RV_AluReg op true rd rs1 rs2) op_opt
  else if N.eqb opcode 99%N then
    (* 0x63 BRANCH *)
    let b13 :=
      (bit_slice w 31%N 1%N * 4096%N +
       bit_slice w 7%N 1%N * 2048%N +
       bit_slice w 25%N 6%N * 32%N +
       bit_slice w 8%N 4%N * 2%N)%N
    in
    let rel := sext_z b13 13%N in
    let c_opt :=
      if N.eqb funct3 0%N then Some RBC_Eq
      else if N.eqb funct3 1%N then Some RBC_Ne
      else if N.eqb funct3 4%N then Some RBC_Lt
      else if N.eqb funct3 5%N then Some RBC_Ge
      else if N.eqb funct3 6%N then Some RBC_Ltu
      else if N.eqb funct3 7%N then Some RBC_Geu
      else None
    in
    option_map (fun c => RV_Branch c rs1 rs2 rel) c_opt
  else if N.eqb opcode 111%N then
    (* 0x6f JAL (only direct jump rd=0 supported in M1) *)
    if N.eqb rd 0%N then
      let j21 :=
        (bit_slice w 31%N 1%N * 1048576%N +
         bit_slice w 12%N 8%N * 4096%N +
         bit_slice w 20%N 1%N * 2048%N +
         bit_slice w 21%N 10%N * 2%N)%N
      in
      Some (RV_Jal0 (sext_z j21 21%N))
    else None
  else if N.eqb opcode 103%N then
    (* 0x67 JALR: only RET (jalr x0, ra, 0) supported *)
    if N.eqb rd 0%N && N.eqb rs1 1%N && N.eqb funct3 0%N && Z.eqb imm12 0%Z
    then Some RV_Ret
    else None
  else if N.eqb opcode 3%N then
    (* 0x03 LOAD *)
    if N.eqb funct3 0%N then Some (RV_Load MS_1 true rd rs1 imm12)
    else if N.eqb funct3 1%N then Some (RV_Load MS_2 true rd rs1 imm12)
    else if N.eqb funct3 2%N then Some (RV_Load MS_4 true rd rs1 imm12)
    else if N.eqb funct3 3%N then Some (RV_Load MS_8 true rd rs1 imm12)
    else if N.eqb funct3 4%N then Some (RV_Load MS_1 false rd rs1 imm12)
    else if N.eqb funct3 5%N then Some (RV_Load MS_2 false rd rs1 imm12)
    else if N.eqb funct3 6%N then Some (RV_Load MS_4 false rd rs1 imm12)
    else None
  else if N.eqb opcode 35%N then
    (* 0x23 STORE *)
    let simm12 := sext_z (funct7 * 32%N + rd) 12%N in
    if N.eqb funct3 0%N then Some (RV_Store MS_1 rs1 rs2 simm12)
    else if N.eqb funct3 1%N then Some (RV_Store MS_2 rs1 rs2 simm12)
    else if N.eqb funct3 2%N then Some (RV_Store MS_4 rs1 rs2 simm12)
    else if N.eqb funct3 3%N then Some (RV_Store MS_8 rs1 rs2 simm12)
    else None
  else None.

Fixpoint decode_rv64_stream_acc
  (fuel : nat) (rvc_enabled : bool) (cur : list N) (cur_off : nat)
  (acc : list decoded_rv_inst) {struct fuel} : string + list decoded_rv_inst :=
  match cur with
  | [] => inr (elf_rev_tr acc)
  | _ :: _ =>
      match fuel with
      | O => inl "RV64 decoder fuel exhausted"
      | S fuel' =>
          match take_u16_le cur with
          | None => inl "truncated RV64 instruction stream"
          | Some (hw, rest2) =>
              if negb (N.eqb (N.modulo hw 4%N) 3%N) then
                if negb rvc_enabled then
                  inl "16-bit RVC instruction encountered with RVC disabled"
                else
                  match decode_rvc_hw hw with
                  | None => inl "unsupported 16-bit RVC instruction"
                  | Some inst =>
                      let acc' := mk_decoded_rv (N.of_nat cur_off) 2%N inst :: acc in
                      decode_rv64_stream_acc fuel' rvc_enabled rest2 (cur_off + 2) acc'
                  end
              else
                match take_u32_le cur with
                | None => inl "truncated 32-bit RV64 instruction"
                | Some (w, rest4) =>
                    match decode_rv32_word w with
                    | None => inl "unsupported 32-bit RV64 instruction"
                    | Some inst =>
                        let acc' := mk_decoded_rv (N.of_nat cur_off) 4%N inst :: acc in
                        decode_rv64_stream_acc fuel' rvc_enabled rest4 (cur_off + 4) acc'
                    end
                end
          end
      end
  end.

Definition decode_rv64_bytes (rvc_enabled : bool) (code : list N)
  : string + list decoded_rv_inst :=
  let len := elf_length_tr code in
  if Nat.eqb len 0 || negb (Nat.eqb (Nat.modulo len 2) 0) then
    inl "RV64 function byte length must be positive and even"
  else if negb rvc_enabled && negb (Nat.eqb (Nat.modulo len 4) 0) then
    inl "non-RVC RV64 function length must be a multiple of 4"
  else
    decode_rv64_stream_acc (Nat.div len 2 + 1) rvc_enabled code 0 [].

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

Definition rv_mask_shamt (w : positive) (z : Z) : @Integers.bit_int w :=
  @Integers.repr w (z mod Z.pos w).

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

Definition add_rel_off (pc : N) (rel : Z) : option N :=
  let sum := (Z.of_N pc + rel)%Z in
  if Z.geb sum 0%Z then Some (Z.to_N sum) else None.

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

(** ** 4. Total Symbolic DAG Lowering to [CertValidator.cfg_dag] *)

Variant rv_arg_ext : Set :=
| RAE_None
| RAE_SignExt
| RAE_ZeroExt.

Record rv_arg_spec : Set := mk_rv_arg_spec {
  ras_name : string;
  ras_width : positive;
  ras_ext : rv_arg_ext;
}.

Definition rv_supported_arg_width (w : positive) : bool :=
  match w with
  | 1%positive | 8%positive | 16%positive | 32%positive | 64%positive => true
  | _ => false
  end.

Lemma rv_supported_arg_width_lt64 : forall w,
  rv_supported_arg_width w = true ->
  (w =? 64)%positive = false ->
  (w <? 64)%positive = true.
Proof.
  intros w Hw Hne.
  do 7 (destruct w as [w|w|]; cbn in Hw; try discriminate Hw; try reflexivity).
  all: try (rewrite Pos.eqb_refl in Hne; discriminate Hne).
Qed.

Definition rv_init_arg_expr (spec : rv_arg_spec) : cert_expr :=
  let v := CE_Var (ras_name spec) (ras_width spec) in
  if Pos.eqb (ras_width spec) 64%positive then v
  else
    match ras_ext spec with
    | RAE_ZeroExt => CE_Cast CCK_ZExt (ras_width spec) 64%positive no_cast_flags v
    | RAE_SignExt | RAE_None => CE_Cast CCK_SExt (ras_width spec) 64%positive no_cast_flags v
    end.

Definition z_to_bv_N (w : positive) (z : Z) : N :=
  Z.to_N (z mod @Integers.modulus w).

Definition ce_bv_z (w : positive) (z : Z) : cert_expr :=
  CE_BvConst w (z_to_bv_N w z).

Definition ce_all_ones (w : positive) : cert_expr :=
  CE_BvConst w (all_ones_N w).

Definition ce_int_min (w : positive) : cert_expr :=
  CE_BvConst w (Z.to_N (@Integers.half_modulus w)).

Definition ce_trunc64_32 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_Trunc 64%positive 32%positive no_cast_flags e.

Definition ce_sext32_64 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_SExt 32%positive 64%positive no_cast_flags e.

Definition ce_zext64_128 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_ZExt 64%positive 128%positive no_cast_flags e.

Definition ce_sext64_128 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_SExt 64%positive 128%positive no_cast_flags e.

Definition ce_trunc128_64 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_Trunc 128%positive 64%positive no_cast_flags e.

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

Definition rv_trunc_ret_expr (ret_w : positive) (a0_e : cert_expr) : cert_expr :=
  if Pos.eqb ret_w 64%positive then a0_e
  else CE_Cast CCK_Trunc 64%positive ret_w no_cast_flags a0_e.

Definition rv_trunc_ret_val (ret_w : positive) (a0 : @Integers.bit_int 64)
  : @Integers.bit_int ret_w :=
  if Pos.eqb ret_w 64%positive then
    @Integers.repr ret_w (@Integers.unsigned 64 a0)
  else
    @Integers.repr ret_w (@Integers.unsigned 64 a0).

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

(** *** 4.1 First-Wins [pos_trie] Instruction Index & Visited Set *)

Fixpoint lookup_by_key {A : Type} (key_of : A -> N) (xs : list A) (k : N)
  {struct xs} : option A :=
  match xs with
  | [] => None
  | x :: rest => if N.eqb (key_of x) k then Some x else lookup_by_key key_of rest k
  end.

Fixpoint pt_of_list_first_acc {A : Type} (key_of : A -> N)
  (im : pos_trie A) (xs : list A) {struct xs} : pos_trie A :=
  match xs with
  | [] => im
  | x :: rest =>
      let k := N.succ_pos (key_of x) in
      match pt_get k im with
      | Some _ => pt_of_list_first_acc key_of im rest
      | None => pt_of_list_first_acc key_of (pt_set k x im) rest
      end
  end.

Definition pt_of_list_first {A : Type} (key_of : A -> N) (xs : list A)
  : pos_trie A :=
  pt_of_list_first_acc key_of (@PT_Empty A) xs.

Lemma pt_of_list_first_acc_get :
  forall {A : Type} (key_of : A -> N) (xs : list A) (im : pos_trie A) (k : N),
    pt_get (N.succ_pos k) (pt_of_list_first_acc key_of im xs) =
    match pt_get (N.succ_pos k) im with
    | Some d => Some d
    | None => lookup_by_key key_of xs k
    end.
Proof.
  intros A key_of xs; induction xs as [| x rest IH];
    intros im k; cbn [pt_of_list_first_acc lookup_by_key].
  - destruct (pt_get (N.succ_pos k) im); reflexivity.
  - destruct (pt_get (N.succ_pos (key_of x)) im) eqn:Ex.
    + rewrite IH; destruct (pt_get (N.succ_pos k) im) eqn:Ek; try reflexivity.
      destruct (N.eqb (key_of x) k) eqn:Heq; [| reflexivity].
      apply N.eqb_eq in Heq; rewrite Heq, Ek in Ex; discriminate Ex.
    + rewrite IH.
      destruct (N.eqb (key_of x) k) eqn:Heq.
      * apply N.eqb_eq in Heq; subst k.
        rewrite Ex, pt_get_set_same; reflexivity.
      * apply N.eqb_neq in Heq.
        assert (Hneq : N.succ_pos k <> N.succ_pos (key_of x)).
        { intro Hinj; apply Heq; symmetry.
          destruct k as [| pk], (key_of x) as [| pm]; cbn in Hinj.
          - reflexivity.
          - destruct pm; discriminate Hinj.
          - destruct pk; discriminate Hinj.
          - f_equal; exact (Pos.succ_inj _ _ Hinj). }
        rewrite (pt_get_set_other _ _ _ _ Hneq); reflexivity.
Qed.

Lemma pt_of_list_first_get :
  forall {A : Type} (key_of : A -> N) (xs : list A) (k : N),
    pt_get (N.succ_pos k) (pt_of_list_first key_of xs) = lookup_by_key key_of xs k.
Proof.
  intros A key_of xs k; unfold pt_of_list_first.
  rewrite pt_of_list_first_acc_get, pt_get_empty; reflexivity.
Qed.

Definition pt_has_n (pc : N) (vis : pos_trie unit) : bool :=
  match pt_get (N.succ_pos pc) vis with
  | Some _ => true
  | None => false
  end.

Definition pt_add_n (pc : N) (vis : pos_trie unit) : pos_trie unit :=
  pt_set (N.succ_pos pc) tt vis.

Fixpoint pt_of_visited_acc (acc : pos_trie unit) (xs : list N) {struct xs} : pos_trie unit :=
  match xs with
  | [] => acc
  | pc :: rest => pt_of_visited_acc (pt_add_n pc acc) rest
  end.

Definition pt_of_visited (xs : list N) : pos_trie unit :=
  pt_of_visited_acc (@PT_Empty unit) xs.

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
  {struct fuel} : option cfg_dag :=
  if pt_has_n pc visited then None
  else
    match fuel with
    | O => None
    | S fuel' =>
        match pt_get (N.succ_pos pc) im with
        | None => None
        | Some dec =>
            let next_pc := (pc + dri_len dec)%N in
            let visited' := pt_add_n pc visited in
            match dri_inst dec with
            | RV_Nop =>
                summarize_rv64_dag_at fuel' im visited' next_pc sp_off vrf astk ret_w
            | RV_Lui rd imm =>
                match rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk with
                | None => None
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
                | None => None
                | Some sv =>
                    match rv_sym_step_write rd sv sp_off vrf astk with
                    | None => None
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
                | None => None
                | Some sv =>
                    match rv_sym_step_write rd sv sp_off vrf astk with
                    | None => None
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
                      | None => None
                      | Some sv =>
                          match rv_sym_step_write rd sv sp_off vrf astk with
                          | None => None
                          | Some (sp_off', vrf', astk') =>
                              summarize_rv64_dag_at fuel' im visited' next_pc sp_off' vrf' astk' ret_w
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
                        let astk' := mc_sym_stk_store off sz sv astk in
                        summarize_rv64_dag_at fuel' im visited' next_pc sp_off vrf astk' ret_w
                      else None
                    else None
                | _ => None
                end
            | RV_Jal0 rel =>
                match add_rel_off pc rel with
                | None => None
                | Some tgt_pc =>
                    summarize_rv64_dag_at fuel' im visited' tgt_pc sp_off vrf astk ret_w
                end
            | RV_Branch cond rs1 rs2 rel =>
                match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
                | MSV_Expr e1, MSV_Expr e2 =>
                    match add_rel_off pc rel with
                    | None => None
                    | Some tgt_pc =>
                        let c_e := sym_br_cond cond e1 e2 in
                        match summarize_rv64_dag_at fuel' im visited' tgt_pc sp_off vrf astk ret_w,
                              summarize_rv64_dag_at fuel' im visited' next_pc sp_off vrf astk ret_w
                        with
                        | Some d_t, Some d_f => Some (CD_Branch c_e d_t d_f)
                        | _, _ => None
                        end
                    end
                | _, _ => None
                end
            | RV_Ret =>
                if rv_sym_epilogue_ok sp_off vrf then
                  match rv_val_read 10%N vrf with
                  | MSV_Expr e_ret =>
                      Some (CD_RetScalar ret_w (rv_trunc_ret_expr ret_w e_ret))
                  | _ => None
                  end
                else None
            end
        end
    end.

Definition rv_valid_arg_spec (sp : rv_arg_spec) : bool :=
  rv_supported_arg_width (ras_width sp) && negb (starts_with_dollar (ras_name sp)).

Definition summarize_rv64_dag
  (fuel : nat) (insts : list decoded_rv_inst)
  (arg_specs : list rv_arg_spec) (ret_w : positive) : option cfg_dag :=
  if negb (Nat.leb (List.length arg_specs) 8) then None
  else if negb (forallb rv_valid_arg_spec arg_specs) then None
  else if negb (rv_supported_arg_width ret_w) then None
  else
    let vrf0 := rv_build_init_val_regs 10%N arg_specs in
    let im := pt_of_list_first dri_off insts in
    summarize_rv64_dag_at fuel im (@PT_Empty unit) 0%N 0%Z vrf0 [] ret_w.

(** ** 5. Bitvector Arithmetic & Semantic Equivalence Proofs ([0 Admitted], [0] Custom Axioms) *)

Lemma eval_ce_bv_z :
  forall {Pa : Params} (penv : param_env Pa) foracle w z,
    eval_closed_cert_expr penv foracle (ce_bv_z w z) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w z))).
Proof.
  intros Pa penv foracle w z.
  unfold eval_closed_cert_expr, ce_bv_z, z_to_bv_N; cbn [eval_cert_expr].
  pose proof (@Integers.modulus_pos w) as Hm.
  assert (Hmod : (0 <= z mod @Integers.modulus w)%Z) by (apply Z.mod_pos_bound; lia).
  rewrite (Z2N.id _ Hmod).
  f_equal; f_equal; f_equal.
  apply Integers.eqm_samerepr, Integers.eqm_sym.
  apply Integers.eqmod_mod.
Qed.

Lemma eval_ce_all_ones :
  forall {Pa : Params} (penv : param_env Pa) foracle w,
    eval_closed_cert_expr penv foracle (ce_all_ones w) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.mone w))).
Proof.
  intros Pa penv foracle w.
  unfold eval_closed_cert_expr, ce_all_ones; cbn [eval_cert_expr].
  rewrite repr_all_ones_N; reflexivity.
Qed.

Lemma eval_ce_int_min :
  forall {Pa : Params} (penv : param_env Pa) foracle w,
    eval_closed_cert_expr penv foracle (ce_int_min w) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.min_signed w)))).
Proof.
  intros Pa penv foracle w.
  unfold eval_closed_cert_expr, ce_int_min; cbn [eval_cert_expr].
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  rewrite (Z2N.id (@Integers.half_modulus w) ltac:(lia)).
  do 3 f_equal.
  apply Integers.eqm_samerepr.
  unfold Integers.eqm, Integers.min_signed.
  exists 1%Z.
  rewrite Integers.half_modulus_modulus; lia.
Qed.

Lemma eval_ce_const :
  forall {Pa : Params} (penv : param_env Pa) foracle w v,
    eval_closed_cert_expr penv foracle (CE_BvConst w v) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N v)))).
Proof.
  intros; reflexivity.
Qed.

Lemma eval_ce_trunc :
  forall {Pa : Params} (penv : param_env Pa) foracle fw tw o vo,
    (tw <? fw)%positive = true ->
    eval_closed_cert_expr penv foracle o = raise_ret (DVALUE_Base (@DVALUE_I Pa fw vo)) ->
    eval_closed_cert_expr penv foracle (CE_Cast CCK_Trunc fw tw no_cast_flags o) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.unsigned fw vo)))).
Proof.
  intros Pa penv foracle fw tw o vo Hlt Ho.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite Ho; cbn - [andb Pos.ltb Pos.eqb Integers.repr Integers.unsigned Integers.signed].
  rewrite Pos.eqb_refl, Hlt; reflexivity.
Qed.

Lemma eval_ce_sext :
  forall {Pa : Params} (penv : param_env Pa) foracle fw tw o vo,
    (fw <? tw)%positive = true ->
    eval_closed_cert_expr penv foracle o = raise_ret (DVALUE_Base (@DVALUE_I Pa fw vo)) ->
    eval_closed_cert_expr penv foracle (CE_Cast CCK_SExt fw tw no_cast_flags o) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.signed fw vo)))).
Proof.
  intros Pa penv foracle fw tw o vo Hlt Ho.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite Ho; cbn - [andb Pos.ltb Pos.eqb Integers.repr Integers.unsigned Integers.signed].
  rewrite Pos.eqb_refl, Hlt; reflexivity.
Qed.

Lemma eval_ce_zext :
  forall {Pa : Params} (penv : param_env Pa) foracle fw tw o vo,
    (fw <? tw)%positive = true ->
    eval_closed_cert_expr penv foracle o = raise_ret (DVALUE_Base (@DVALUE_I Pa fw vo)) ->
    eval_closed_cert_expr penv foracle (CE_Cast CCK_ZExt fw tw no_cast_flags o) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.unsigned fw vo)))).
Proof.
  intros Pa penv foracle fw tw o vo Hlt Ho.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite Ho; cbn - [andb Pos.ltb Pos.eqb Integers.repr Integers.unsigned Integers.signed].
  rewrite Pos.eqb_refl, Hlt; reflexivity.
Qed.

Lemma eval_ce_icmp_eq_bool :
  forall {Pa : Params} (penv : param_env Pa) foracle pr w l r vl vr,
    eval_closed_cert_expr penv foracle l = raise_ret (DVALUE_Base (@DVALUE_I Pa w vl)) ->
    eval_closed_cert_expr penv foracle r = raise_ret (DVALUE_Base (@DVALUE_I Pa w vr)) ->
    eval_closed_cert_expr penv foracle (CE_ICmp pr false w l r) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
      (if match pr with
          | CIP_Eq => @Integers.eq w vl vr
          | CIP_Ne => negb (@Integers.eq w vl vr)
          | CIP_Ult => @Integers.ltu w vl vr
          | CIP_Ule => negb (@Integers.ltu w vr vl)
          | CIP_Ugt => @Integers.ltu w vr vl
          | CIP_Uge => negb (@Integers.ltu w vl vr)
          | CIP_Slt => @Integers.lt w vl vr
          | CIP_Sle => negb (@Integers.lt w vr vl)
          | CIP_Sgt => @Integers.lt w vr vl
          | CIP_Sge => negb (@Integers.lt w vl vr)
          end
       then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle pr w l r vl vr Hl Hr.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite Hl, Hr; cbn [eou_bind].
  unfold eval_icmp; rewrite eval_icmp_base_same_width.
  destruct pr; cbn - [Integers.eq Integers.lt Integers.ltu Integers.one Integers.zero].
  - destruct (@Integers.eq w vl vr); reflexivity.
  - destruct (@Integers.eq w vl vr); reflexivity.
  - destruct (@Integers.ltu w vl vr); reflexivity.
  - destruct (@Integers.ltu w vr vl); reflexivity.
  - destruct (@Integers.ltu w vr vl); reflexivity.
  - destruct (@Integers.ltu w vl vr); reflexivity.
  - destruct (@Integers.lt w vl vr); reflexivity.
  - destruct (@Integers.lt w vr vl); reflexivity.
  - destruct (@Integers.lt w vr vl); reflexivity.
  - destruct (@Integers.lt w vl vr); reflexivity.
Qed.

Lemma eval_ce_select_int :
  forall {Pa : Params} (penv : param_env Pa) foracle w c t f (b : bool) vt vf,
    eval_closed_cert_expr penv foracle c =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle t = raise_ret (DVALUE_Base (@DVALUE_I Pa w vt)) ->
    eval_closed_cert_expr penv foracle f = raise_ret (DVALUE_Base (@DVALUE_I Pa w vf)) ->
    eval_closed_cert_expr penv foracle (CE_Select w c t f) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (if b then vt else vf))).
Proof.
  intros Pa penv foracle w c t f [|] vt vf Hc Ht Hf;
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
    rewrite Hc, Ht, Hf; cbn [eou_bind eval_select eval_select_base_dvalue].
  - rewrite (@Integers.unsigned_one 1%positive); reflexivity.
  - rewrite (@Integers.unsigned_zero 1%positive); reflexivity.
Qed.

Lemma eval_ce_binop :
  forall {Pa : Params} (penv : param_env Pa) foracle op w fl l r,
    eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r) =
    eou_bind (eval_closed_cert_expr penv foracle l) (fun vl =>
    eou_bind (eval_closed_cert_expr penv foracle r) (fun vr =>
    @eval_iop Pa (cert_to_ibinop op fl) vl vr)).
Proof.
  intros; reflexivity.
Qed.

Lemma z_mod_pos_lt_modulus :
  forall (w : positive) (z : Z),
    (Z.pos w < @Integers.modulus w)%Z ->
    (@Integers.unsigned w (@Integers.repr w (z mod Z.pos w)) >=? Z.pos w)%Z = false /\
    @Integers.repr w (z mod Z.pos w) = rv_mask_shamt w z.
Proof.
  intros w z Hlt.
  pose proof (Z.mod_pos_bound z (Z.pos w) ltac:(lia)) as Hb.
  rewrite (@Integers.unsigned_repr w (z mod Z.pos w)).
  - split; [rewrite Z.geb_leb; apply Z.leb_gt; lia | reflexivity].
  - pose proof (@Integers.modulus_pos w); unfold Integers.max_unsigned; lia.
Qed.

Lemma mod_lt_32_64 :
  forall w, (w = 32%positive \/ w = 64%positive) -> (Z.pos w < @Integers.modulus w)%Z.
Proof.
  intros w [-> | ->]; compute; reflexivity.
Qed.

Lemma integers_eq_zero_iff :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.eq w v (@Integers.zero w) = true <-> @Integers.unsigned w v = 0%Z.
Proof.
  intros w v; pose proof (@Integers.eq_spec w v (@Integers.zero w)) as Hsp.
  destruct (@Integers.eq w v (@Integers.zero w)); split; intro H.
  - subst v; apply (@Integers.unsigned_zero w).
  - reflexivity.
  - discriminate H.
  - exfalso; apply Hsp; rewrite <- (@Integers.repr_unsigned w v), H; reflexivity.
Qed.

Lemma integers_signed_zero_iff :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.signed w v = 0%Z <-> @Integers.unsigned w v = 0%Z.
Proof.
  intros w v.
  pose proof (@Integers.unsigned_range w v) as Hrng.
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  pose proof (@Integers.half_modulus_modulus w) as Hhmm.
  unfold Integers.signed.
  match goal with |- context [if ?c then _ else _] => destruct c end; split; intro H; lia.
Qed.

Lemma unsigned_half_modulus_signed_min :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.unsigned w v = @Integers.unsigned w (@Integers.repr w (@Integers.min_signed w)) <->
    @Integers.signed w v = @Integers.min_signed w.
Proof.
  intros w v.
  pose proof (@Integers.unsigned_range w v) as Hrng.
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  unfold Integers.min_signed.
  rewrite Integers.unsigned_repr_eq.
  pose proof (@Integers.half_modulus_modulus w) as Hhmm.
  assert (Hrep : ((- @Integers.half_modulus w) mod @Integers.modulus w)%Z = @Integers.half_modulus w).
  { rewrite <- (Z.mod_add (- @Integers.half_modulus w) 1 (@Integers.modulus w)) by lia.
    replace (- @Integers.half_modulus w + 1 * @Integers.modulus w)%Z with (@Integers.half_modulus w) by lia.
    apply Z.mod_small; lia. }
  rewrite Hrep.
  unfold Integers.signed.
  match goal with |- context [if ?c then _ else _] => destruct c end; split; intro H; lia.
Qed.

Lemma unsigned_mone_signed_neg1 :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.unsigned w v = @Integers.unsigned w (@Integers.mone w) <->
    @Integers.signed w v = (-1)%Z.
Proof.
  intros w v.
  pose proof (@Integers.unsigned_range w v) as Hrng.
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  pose proof (@Integers.half_modulus_modulus w) as Hhmm.
  rewrite (@Integers.unsigned_mone w).
  unfold Integers.max_unsigned, Integers.signed.
  match goal with |- context [if ?c then _ else _] => destruct c end; split; intro H; lia.
Qed.

Lemma integers_eq_min_signed_iff :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.eq w v (@Integers.repr w (@Integers.min_signed w)) = true <->
    @Integers.signed w v = @Integers.min_signed w.
Proof.
  intros w v.
  pose proof (@Integers.eq_spec w v (@Integers.repr w (@Integers.min_signed w))) as Hsp.
  destruct (@Integers.eq w v (@Integers.repr w (@Integers.min_signed w))); split; intro H.
  - subst v; apply (unsigned_half_modulus_signed_min w _); reflexivity.
  - reflexivity.
  - discriminate H.
  - exfalso; apply Hsp; rewrite <- (@Integers.repr_unsigned w v), <- (@Integers.repr_unsigned w (@Integers.repr w (@Integers.min_signed w))); f_equal.
    apply (unsigned_half_modulus_signed_min w v); exact H.
Qed.

Lemma integers_eq_mone_iff :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.eq w v (@Integers.mone w) = true <-> @Integers.signed w v = (-1)%Z.
Proof.
  intros w v.
  pose proof (@Integers.eq_spec w v (@Integers.mone w)) as Hsp.
  destruct (@Integers.eq w v (@Integers.mone w)); split; intro H.
  - subst v; apply (unsigned_mone_signed_neg1 w _); reflexivity.
  - reflexivity.
  - discriminate H.
  - exfalso; apply Hsp; rewrite <- (@Integers.repr_unsigned w v).
    apply (unsigned_mone_signed_neg1 w v) in H; rewrite H.
    apply (@Integers.repr_unsigned w).
Qed.

Lemma mul_hi64_eq :
  forall p : Z,
    @Integers.repr 64%positive
      (@Integers.unsigned 128%positive
         (@Integers.shru 128%positive (@Integers.repr 128%positive p) (@Integers.repr 128%positive 64%Z))) =
    @Integers.repr 64%positive (Z.shiftr p 64%Z).
Proof.
  intro p.
  unfold Integers.shru.
  rewrite (@Integers.unsigned_repr 128%positive 64%Z) by (compute; split; discriminate).
  apply Integers.same_bits_eq; intros i Hi.
  rewrite !(@Integers.testbit_repr _ _ i Hi).
  assert (Hi64 : (0 <= i < 64)%Z) by (replace 64%Z with (@Integers.zwordsize 64%positive) by reflexivity; exact Hi).
  rewrite (@Integers.unsigned_repr 128%positive (Z.shiftr (@Integers.unsigned 128%positive (@Integers.repr 128%positive p)) 64%Z)).
  - rewrite !Z.shiftr_spec by lia.
    rewrite (@Integers.unsigned_repr_eq 128%positive p).
    change (@Integers.modulus 128%positive) with (2 ^ 128)%Z.
    rewrite Z.mod_pow2_bits_low by lia.
    reflexivity.
  - pose proof (@Integers.unsigned_range 128%positive (@Integers.repr 128%positive p)) as Hr.
    rewrite Z.shiftr_div_pow2 by lia.
    change (@Integers.modulus 128%positive) with (2 ^ 128)%Z in Hr.
    change (@Integers.max_unsigned 128%positive) with (2 ^ 128 - 1)%Z.
    split; [apply Z.div_pos; lia |].
    apply Z.lt_le_pred, Z.div_lt_upper_bound; lia.
Qed.

Lemma land_mask_w_mod :
  forall w (x : @Integers.bit_int w),
    (w = 32%positive \/ w = 64%positive) ->
    @Integers.repr w (Z.land (@Integers.unsigned w x) (Z.pos w - 1)) = rv_mask_shamt w (@Integers.unsigned w x) /\
    (@Integers.unsigned w (@Integers.repr w (Z.land (@Integers.unsigned w x) (Z.pos w - 1))) >=? Z.pos w)%Z = false.
Proof.
  intros w x Hw.
  assert (Hland : Z.land (@Integers.unsigned w x) (Z.pos w - 1) = ((@Integers.unsigned w x) mod Z.pos w)%Z).
  { destruct Hw as [-> | ->].
    - replace (Z.pos 32 - 1)%Z with (Z.ones 5) by reflexivity.
      rewrite Z.land_ones by lia; reflexivity.
    - replace (Z.pos 64 - 1)%Z with (Z.ones 6) by reflexivity.
      rewrite Z.land_ones by lia; reflexivity. }
  rewrite Hland.
  pose proof (z_mod_pos_lt_modulus w (@Integers.unsigned w x) (mod_lt_32_64 w Hw)) as [Hlt Heq].
  split; [exact Heq | exact Hlt].
Qed.

Lemma eval_sym_alu_imm_raw_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op w a va imm,
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w va)) ->
    eval_closed_cert_expr penv foracle (sym_alu_imm_raw op w a imm) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (rv_eval_alu_imm_raw op w va imm))).
Proof.
  intros Pa penv foracle op w a va imm Hw Ha.
  destruct op; cbn [sym_alu_imm_raw rv_eval_alu_imm_raw].
  - (* RAI_Addi *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Ha. pose proof (eval_ce_bv_z penv foracle w imm) as Hz.
    unfold eval_closed_cert_expr in Hz; rewrite Hz; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAI_Slti *)
    assert (H1w : (1 <? w)%positive = true) by (destruct Hw as [-> | ->]; reflexivity).
    rewrite (eval_ce_zext _ _ _ _ _ _ H1w
               (eval_ce_icmp_eq_bool penv foracle CIP_Slt w a (ce_bv_z w imm) va (@Integers.repr w imm) Ha (eval_ce_bv_z _ _ _ _))).
    destruct (@Integers.lt w va (@Integers.repr w imm));
      [rewrite (@Integers.unsigned_one 1%positive) | rewrite (@Integers.unsigned_zero 1%positive)]; reflexivity.
  - (* RAI_Sltiu *)
    assert (H1w : (1 <? w)%positive = true) by (destruct Hw as [-> | ->]; reflexivity).
    rewrite (eval_ce_zext _ _ _ _ _ _ H1w
               (eval_ce_icmp_eq_bool penv foracle CIP_Ult w a (ce_bv_z w imm) va (@Integers.repr w imm) Ha (eval_ce_bv_z _ _ _ _))).
    destruct (@Integers.ltu w va (@Integers.repr w imm));
      [rewrite (@Integers.unsigned_one 1%positive) | rewrite (@Integers.unsigned_zero 1%positive)]; reflexivity.
  - (* RAI_Xori *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Ha. pose proof (eval_ce_bv_z penv foracle w imm) as Hz.
    unfold eval_closed_cert_expr in Hz; rewrite Hz; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAI_Ori *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Ha. pose proof (eval_ce_bv_z penv foracle w imm) as Hz.
    unfold eval_closed_cert_expr in Hz; rewrite Hz; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAI_Andi *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Ha. pose proof (eval_ce_bv_z penv foracle w imm) as Hz.
    unfold eval_closed_cert_expr in Hz; rewrite Hz; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAI_Slli *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha; cbn [eou_bind].
    pose proof (Z.mod_pos_bound imm (Z.pos w) ltac:(lia)) as Hbd.
    rewrite (Z2N.id _ (proj1 Hbd)).
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct (z_mod_pos_lt_modulus w imm (mod_lt_32_64 w Hw)) as [Hlt Heq].
    cbn - [Integers.unsigned Integers.repr Integers.shl Z.geb Z.of_N Z.modulo].
    rewrite Hlt, Heq; reflexivity.
  - (* RAI_Srli *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha; cbn [eou_bind].
    pose proof (Z.mod_pos_bound imm (Z.pos w) ltac:(lia)) as Hbd.
    rewrite (Z2N.id _ (proj1 Hbd)).
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct (z_mod_pos_lt_modulus w imm (mod_lt_32_64 w Hw)) as [Hlt Heq].
    cbn - [Integers.unsigned Integers.repr Integers.shru Z.geb Z.of_N Z.modulo].
    rewrite Hlt, Heq; reflexivity.
  - (* RAI_Srai *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha; cbn [eou_bind].
    pose proof (Z.mod_pos_bound imm (Z.pos w) ltac:(lia)) as Hbd.
    rewrite (Z2N.id _ (proj1 Hbd)).
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct (z_mod_pos_lt_modulus w imm (mod_lt_32_64 w Hw)) as [Hlt Heq].
    cbn - [Integers.unsigned Integers.repr Integers.shr Z.geb Z.of_N Z.modulo].
    rewrite Hlt, Heq; reflexivity.
Qed.

Lemma eval_sym_alu_imm_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op is_word a va imm,
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive va)) ->
    eval_closed_cert_expr penv foracle (sym_alu_imm op is_word a imm) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_eval_alu_imm op is_word va imm))).
Proof.
  intros Pa penv foracle op [|] a va imm Ha; cbn [sym_alu_imm rv_eval_alu_imm].
  - eapply eval_ce_sext; [reflexivity |].
    apply eval_sym_alu_imm_raw_sound; [left; reflexivity |].
    apply eval_ce_trunc; [reflexivity | exact Ha].
  - apply eval_sym_alu_imm_raw_sound; [right; reflexivity | exact Ha].
Qed.

Lemma eval_sym_div_rem_guarded_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op w a b va vb,
    (w = 32%positive \/ w = 64%positive) ->
    (op = CB_UDiv \/ op = CB_URem \/ op = CB_SDiv \/ op = CB_SRem) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa w vb)) ->
    eval_closed_cert_expr penv foracle (sym_div_rem_guarded op w a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w
      (match op with
       | CB_UDiv => rv_divu_total w va vb
       | CB_URem => rv_modu_total w va vb
       | CB_SDiv => rv_divs_total w va vb
       | _ => rv_mods_total w va vb
       end))).
Proof.
  intros Pa penv foracle op w a b va vb Hw Hop Ha Hb.
  assert (Hzw : (@Integers.zwordsize w > 1)%Z)
    by (destruct Hw as [-> | ->];
        [replace (@Integers.zwordsize 32%positive) with 32%Z by reflexivity
        | replace (@Integers.zwordsize 64%positive) with 64%Z by reflexivity]; lia).
  destruct Hop as [-> | [-> | [-> | ->]]]; cbn [sym_div_rem_guarded].
  - (* CB_UDiv *)
    set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if @Integers.eq w vb (@Integers.zero w) then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { unfold is_z; apply (eval_ce_icmp_eq_bool _ _ CIP_Eq); [exact Hb | rewrite eval_ce_const, repr_zero_N; reflexivity]. }
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w is_z (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if @Integers.eq w vb (@Integers.zero w) then @Integers.one w else vb)))).
    { eapply eval_ce_select_int; [exact Hisz | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]. }
    unfold rv_divu_total.
    destruct (@Integers.eq w vb (@Integers.zero w)) eqn:Ez.
    + pose proof Ez as Ez'; apply integers_eq_zero_iff in Ez'; rewrite Ez'; cbn [Z.eqb].
      eapply (eval_ce_select_int _ _ _ _ _ _ true); [rewrite Hisz; reflexivity | exact (eval_ce_all_ones _ _ _) |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.divu Integers.unsigned].
      rewrite (@Integers.unsigned_one w); reflexivity.
    + assert (Hnz : (@Integers.unsigned w vb =? 0)%Z = false).
      { destruct (Z.eqb (@Integers.unsigned w vb) 0%Z) eqn:Ezb; [| reflexivity].
        apply Z.eqb_eq in Ezb; apply integers_eq_zero_iff in Ezb; congruence. }
      rewrite Hnz.
      eapply (eval_ce_select_int _ _ _ _ _ _ false); [rewrite Hisz; reflexivity | exact (eval_ce_all_ones _ _ _) |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.divu Integers.unsigned].
      rewrite Hnz; reflexivity.
  - (* CB_URem *)
    set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if @Integers.eq w vb (@Integers.zero w) then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { unfold is_z; apply (eval_ce_icmp_eq_bool _ _ CIP_Eq); [exact Hb | rewrite eval_ce_const, repr_zero_N; reflexivity]. }
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w is_z (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if @Integers.eq w vb (@Integers.zero w) then @Integers.one w else vb)))).
    { eapply eval_ce_select_int; [exact Hisz | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]. }
    unfold rv_modu_total.
    destruct (@Integers.eq w vb (@Integers.zero w)) eqn:Ez.
    + pose proof Ez as Ez'; apply integers_eq_zero_iff in Ez'; rewrite Ez'; cbn [Z.eqb].
      eapply (eval_ce_select_int _ _ _ _ _ _ true); [rewrite Hisz; reflexivity | exact Ha |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.modu Integers.unsigned].
      rewrite (@Integers.unsigned_one w); reflexivity.
    + assert (Hnz : (@Integers.unsigned w vb =? 0)%Z = false).
      { destruct (Z.eqb (@Integers.unsigned w vb) 0%Z) eqn:Ezb; [| reflexivity].
        apply Z.eqb_eq in Ezb; apply integers_eq_zero_iff in Ezb; congruence. }
      rewrite Hnz.
      eapply (eval_ce_select_int _ _ _ _ _ _ false); [rewrite Hisz; reflexivity | exact Ha |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.modu Integers.unsigned].
      rewrite Hnz; reflexivity.
  - (* CB_SDiv *)
    set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
    set (imin := ce_int_min w).
    set (is_ovf := CE_BinOp CB_And 1%positive no_binop_flags (CE_ICmp CIP_Eq false w a imin) (CE_ICmp CIP_Eq false w b (ce_all_ones w))).
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if Z.eqb (@Integers.signed w vb) 0%Z then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { assert (Hz0 : eval_closed_cert_expr penv foracle (CE_BvConst w 0%N) = raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
        by (rewrite eval_ce_const, repr_zero_N; reflexivity).
      unfold is_z; rewrite (eval_ce_icmp_eq_bool _ _ CIP_Eq w b (CE_BvConst w 0%N) vb (@Integers.zero w) Hb Hz0).
      destruct (Z.eqb (@Integers.signed w vb) 0%Z) eqn:Esz, (@Integers.eq w vb (@Integers.zero w)) eqn:Euz;
        try reflexivity; [exfalso; apply Z.eqb_eq, integers_signed_zero_iff, integers_eq_zero_iff in Esz; congruence
                       | exfalso; apply integers_eq_zero_iff, integers_signed_zero_iff, Z.eqb_eq in Euz; congruence]. }
    assert (Hovf : eval_closed_cert_expr penv foracle is_ovf =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
        (if Z.eqb (@Integers.signed w va) (@Integers.min_signed w) && Z.eqb (@Integers.signed w vb) (-1)%Z
         then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { unfold is_ovf; rewrite eval_ce_binop.
      rewrite (eval_ce_icmp_eq_bool penv foracle CIP_Eq w a imin va (@Integers.repr w (@Integers.min_signed w)) Ha (eval_ce_int_min _ _ _)).
      rewrite (eval_ce_icmp_eq_bool penv foracle CIP_Eq w b (ce_all_ones w) vb (@Integers.mone w) Hb (eval_ce_all_ones _ _ _)).
      cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct (@Integers.eq w va (@Integers.repr w (@Integers.min_signed w))) eqn:Ea,
               (@Integers.eq w vb (@Integers.mone w)) eqn:Eb;
        destruct (Z.eqb (@Integers.signed w va) (@Integers.min_signed w)) eqn:Esa,
                 (Z.eqb (@Integers.signed w vb) (-1)%Z) eqn:Esb;
        cbn [andb];
        try (exfalso; apply integers_eq_min_signed_iff in Ea; apply Z.eqb_neq in Esa; congruence);
        try (exfalso; apply Z.eqb_eq in Esa; apply integers_eq_min_signed_iff in Esa; congruence);
        try (exfalso; apply integers_eq_mone_iff in Eb; apply Z.eqb_neq in Esb; congruence);
        try (exfalso; apply Z.eqb_eq in Esb; apply integers_eq_mone_iff in Esb; congruence);
        reflexivity. }
    set (cz := Z.eqb (@Integers.signed w vb) 0%Z) in *.
    set (co := (Z.eqb (@Integers.signed w va) (@Integers.min_signed w) && Z.eqb (@Integers.signed w vb) (-1)%Z)%bool) in *.
    assert (Hbad : eval_closed_cert_expr penv foracle (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if (cz || co)%bool then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { rewrite eval_ce_binop, Hisz, Hovf; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct cz, co; reflexivity. }
    assert (Hsa : eval_closed_cert_expr penv foracle (CE_Select w is_ovf (CE_BvConst w 0%N) a) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if co then @Integers.zero w else va)))).
    { eapply eval_ce_select_int; [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Ha]. }
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if (cz || co)%bool then @Integers.one w else vb)))).
    { eapply eval_ce_select_int; [exact Hbad | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]. }
    assert (Hsdiv : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_SDiv w no_binop_flags (CE_Select w is_ovf (CE_BvConst w 0%N) a)
        (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.divs w (if co then @Integers.zero w else va) (if (cz || co)%bool then @Integers.one w else vb))))).
    { rewrite eval_ce_binop, Hsa, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.signed Integers.min_signed Integers.divs Z.eqb].
      destruct (cz || co)%bool eqn:Ebc.
      - rewrite (@Integers.signed_one w) by exact Hzw; cbn [Z.eqb].
        rewrite andb_false_r; reflexivity.
      - apply orb_false_iff in Ebc as [Hcz Hco].
        unfold cz in Hcz; rewrite Hcz, Hco.
        rewrite (Z.eqb_sym (@Integers.min_signed w) (@Integers.signed w va)).
        unfold co in Hco; rewrite Hco; reflexivity. }
    unfold rv_divs_total; fold cz co.
    destruct cz eqn:Ecz.
    { eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hisz | exact (eval_ce_all_ones _ _ _) |].
      eapply eval_ce_select_int; [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]. }
    { destruct co eqn:Eco.
      - eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact (eval_ce_all_ones _ _ _) |].
        eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv].
      - eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact (eval_ce_all_ones _ _ _) |].
        eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]. }
  - (* CB_SRem *)
    set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
    set (imin := ce_int_min w).
    set (is_ovf := CE_BinOp CB_And 1%positive no_binop_flags (CE_ICmp CIP_Eq false w a imin) (CE_ICmp CIP_Eq false w b (ce_all_ones w))).
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if Z.eqb (@Integers.signed w vb) 0%Z then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { assert (Hz0 : eval_closed_cert_expr penv foracle (CE_BvConst w 0%N) = raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
        by (rewrite eval_ce_const, repr_zero_N; reflexivity).
      unfold is_z; rewrite (eval_ce_icmp_eq_bool _ _ CIP_Eq w b (CE_BvConst w 0%N) vb (@Integers.zero w) Hb Hz0).
      destruct (Z.eqb (@Integers.signed w vb) 0%Z) eqn:Esz, (@Integers.eq w vb (@Integers.zero w)) eqn:Euz;
        try reflexivity; [exfalso; apply Z.eqb_eq, integers_signed_zero_iff, integers_eq_zero_iff in Esz; congruence
                       | exfalso; apply integers_eq_zero_iff, integers_signed_zero_iff, Z.eqb_eq in Euz; congruence]. }
    assert (Hovf : eval_closed_cert_expr penv foracle is_ovf =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
        (if Z.eqb (@Integers.signed w va) (@Integers.min_signed w) && Z.eqb (@Integers.signed w vb) (-1)%Z
         then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { unfold is_ovf; rewrite eval_ce_binop.
      rewrite (eval_ce_icmp_eq_bool penv foracle CIP_Eq w a imin va (@Integers.repr w (@Integers.min_signed w)) Ha (eval_ce_int_min _ _ _)).
      rewrite (eval_ce_icmp_eq_bool penv foracle CIP_Eq w b (ce_all_ones w) vb (@Integers.mone w) Hb (eval_ce_all_ones _ _ _)).
      cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct (@Integers.eq w va (@Integers.repr w (@Integers.min_signed w))) eqn:Ea,
               (@Integers.eq w vb (@Integers.mone w)) eqn:Eb;
        destruct (Z.eqb (@Integers.signed w va) (@Integers.min_signed w)) eqn:Esa,
                 (Z.eqb (@Integers.signed w vb) (-1)%Z) eqn:Esb;
        cbn [andb];
        try (exfalso; apply integers_eq_min_signed_iff in Ea; apply Z.eqb_neq in Esa; congruence);
        try (exfalso; apply Z.eqb_eq in Esa; apply integers_eq_min_signed_iff in Esa; congruence);
        try (exfalso; apply integers_eq_mone_iff in Eb; apply Z.eqb_neq in Esb; congruence);
        try (exfalso; apply Z.eqb_eq in Esb; apply integers_eq_mone_iff in Esb; congruence);
        reflexivity. }
    set (cz := Z.eqb (@Integers.signed w vb) 0%Z) in *.
    set (co := (Z.eqb (@Integers.signed w va) (@Integers.min_signed w) && Z.eqb (@Integers.signed w vb) (-1)%Z)%bool) in *.
    assert (Hbad : eval_closed_cert_expr penv foracle (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if (cz || co)%bool then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { rewrite eval_ce_binop, Hisz, Hovf; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct cz, co; reflexivity. }
    assert (Hsa : eval_closed_cert_expr penv foracle (CE_Select w is_ovf (CE_BvConst w 0%N) a) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if co then @Integers.zero w else va)))).
    { eapply eval_ce_select_int; [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Ha]. }
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if (cz || co)%bool then @Integers.one w else vb)))).
    { eapply eval_ce_select_int; [exact Hbad | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]. }
    assert (Hsrem : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_SRem w no_binop_flags (CE_Select w is_ovf (CE_BvConst w 0%N) a)
        (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.mods w (if co then @Integers.zero w else va) (if (cz || co)%bool then @Integers.one w else vb))))).
    { rewrite eval_ce_binop, Hsa, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.signed Integers.min_signed Integers.mods Z.eqb].
      destruct (cz || co)%bool eqn:Ebc.
      - rewrite (@Integers.signed_one w) by exact Hzw; cbn [Z.eqb].
        rewrite andb_false_r; reflexivity.
      - apply orb_false_iff in Ebc as [Hcz Hco].
        unfold cz in Hcz; rewrite Hcz, Hco.
        rewrite (Z.eqb_sym (@Integers.min_signed w) (@Integers.signed w va)).
        unfold co in Hco; rewrite Hco; reflexivity. }
    unfold rv_mods_total; fold cz co.
    destruct cz eqn:Ecz.
    { eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hisz | exact Ha |].
      eapply eval_ce_select_int; [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Hsrem]. }
    { destruct co eqn:Eco.
      - eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact Ha |].
        eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Hsrem].
      - eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact Ha |].
        eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Hsrem]. }
Qed.

Lemma eval_sym_mulhi64_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle sa sb a b va vb,
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vb)) ->
    eval_closed_cert_expr penv foracle (sym_mulhi64 sa sb a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
      (@Integers.repr 64%positive
         (Z.shiftr ((if sa then @Integers.signed 64%positive va else @Integers.unsigned 64%positive va) *
                    (if sb then @Integers.signed 64%positive vb else @Integers.unsigned 64%positive vb)) 64%Z)))).
Proof.
  intros Pa penv foracle sa sb a b va vb Ha Hb.
  unfold sym_mulhi64.
  assert (Ha128 : eval_closed_cert_expr penv foracle (if sa then ce_sext64_128 a else ce_zext64_128 a) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 128%positive
      (@Integers.repr 128%positive (if sa then @Integers.signed 64%positive va else @Integers.unsigned 64%positive va))))).
  { destruct sa; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; assumption. }
  assert (Hb128 : eval_closed_cert_expr penv foracle (if sb then ce_sext64_128 b else ce_zext64_128 b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 128%positive
      (@Integers.repr 128%positive (if sb then @Integers.signed 64%positive vb else @Integers.unsigned 64%positive vb))))).
  { destruct sb; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; assumption. }
  assert (Hprod : eval_closed_cert_expr penv foracle
    (CE_BinOp CB_Mul 128%positive no_binop_flags
      (if sa then ce_sext64_128 a else ce_zext64_128 a)
      (if sb then ce_sext64_128 b else ce_zext64_128 b)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 128%positive
      (@Integers.repr 128%positive
        ((if sa then @Integers.signed 64%positive va else @Integers.unsigned 64%positive va) *
         (if sb then @Integers.signed 64%positive vb else @Integers.unsigned 64%positive vb)))))).
  { rewrite eval_ce_binop, Ha128, Hb128; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.mul Integers.repr Integers.signed Integers.unsigned Z.mul].
    unfold Integers.mul; do 3 f_equal.
    apply Integers.eqm_samerepr, Integers.eqm_mult;
      apply Integers.eqm_sym, Integers.eqm_unsigned_repr. }
  rewrite <- (mul_hi64_eq _).
  eapply eval_ce_trunc; [reflexivity |].
  rewrite eval_ce_binop, Hprod, eval_ce_const; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  cbn - [Integers.shru Integers.repr Integers.unsigned Z.geb].
  rewrite (@Integers.unsigned_repr 128%positive 64%Z) by (compute; split; discriminate).
  replace (64 >=? Z.pos 128)%Z with false by reflexivity.
  reflexivity.
Qed.

Lemma eval_sym_alu_reg_raw_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op w a b va vb,
    (w = 32%positive \/ w = 64%positive) ->
    (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa w vb)) ->
    eval_closed_cert_expr penv foracle (sym_alu_reg_raw op w a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (rv_eval_alu_reg_raw op w va vb))).
Proof.
  intros Pa penv foracle op w a b va vb Hw Hmul Ha Hb.
  destruct op; cbn [sym_alu_reg_raw rv_eval_alu_reg_raw];
    try (exfalso; destruct Hmul as [[H0 [H1 H2]] | ->]; [contradiction | discriminate H0 || discriminate H1 || discriminate H2]).
  - (* RAR_Add *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_Sub *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_Sll *)
    assert (Hmask : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And w no_binop_flags b (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.land (@Integers.unsigned w vb) (Z.pos w - 1)))))).
    { rewrite eval_ce_binop, Hb, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      destruct Hw as [-> | ->];
        cbn - [Integers.and Integers.unsigned Integers.repr Z.land];
        unfold Integers.and;
        [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
        | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)];
        reflexivity. }
    rewrite eval_ce_binop, Ha, Hmask; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.shiftl Z.land Z.sub].
    destruct (land_mask_w_mod w vb Hw) as [Heq Hlt].
    rewrite Hlt, Heq; reflexivity.
  - (* RAR_Slt *)
    assert (H1w : (1 <? w)%positive = true) by (destruct Hw as [-> | ->]; reflexivity).
    rewrite (eval_ce_zext _ _ _ _ _ _ H1w (eval_ce_icmp_eq_bool penv foracle CIP_Slt w a b va vb Ha Hb)).
    destruct (@Integers.lt w va vb);
      [rewrite (@Integers.unsigned_one 1%positive) | rewrite (@Integers.unsigned_zero 1%positive)]; reflexivity.
  - (* RAR_Sltu *)
    assert (H1w : (1 <? w)%positive = true) by (destruct Hw as [-> | ->]; reflexivity).
    rewrite (eval_ce_zext _ _ _ _ _ _ H1w (eval_ce_icmp_eq_bool penv foracle CIP_Ult w a b va vb Ha Hb)).
    destruct (@Integers.ltu w va vb);
      [rewrite (@Integers.unsigned_one 1%positive) | rewrite (@Integers.unsigned_zero 1%positive)]; reflexivity.
  - (* RAR_Xor *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_Srl *)
    assert (Hmask : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And w no_binop_flags b (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.land (@Integers.unsigned w vb) (Z.pos w - 1)))))).
    { rewrite eval_ce_binop, Hb, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      destruct Hw as [-> | ->];
        cbn - [Integers.and Integers.unsigned Integers.repr Z.land];
        unfold Integers.and;
        [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
        | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)];
        reflexivity. }
    rewrite eval_ce_binop, Ha, Hmask; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.land Z.sub].
    destruct (land_mask_w_mod w vb Hw) as [Heq Hlt].
    rewrite Hlt, Heq; reflexivity.
  - (* RAR_Sra *)
    assert (Hmask : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And w no_binop_flags b (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.land (@Integers.unsigned w vb) (Z.pos w - 1)))))).
    { rewrite eval_ce_binop, Hb, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      destruct Hw as [-> | ->];
        cbn - [Integers.and Integers.unsigned Integers.repr Z.land];
        unfold Integers.and;
        [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
        | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)];
        reflexivity. }
    rewrite eval_ce_binop, Ha, Hmask; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shr Integers.unsigned Integers.repr Z.geb Z.land Z.sub].
    destruct (land_mask_w_mod w vb Hw) as [Heq Hlt].
    rewrite Hlt, Heq; reflexivity.
  - (* RAR_Or *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_And *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_Mul *)
    rewrite eval_ce_binop, Ha, Hb; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct Hw as [-> | ->];
      cbn - [Integers.mul Integers.unsigned Integers.signed Integers.min_signed Integers.max_signed Z.mul Z.gtb];
      reflexivity.
  - (* RAR_Mulh *)
    destruct Hmul as [[H0 _] | ->]; [exfalso; apply H0; reflexivity |].
    exact (eval_sym_mulhi64_sound penv foracle true true a b va vb Ha Hb).
  - (* RAR_Mulhsu *)
    destruct Hmul as [[_ [H1 _]] | ->]; [exfalso; apply H1; reflexivity |].
    exact (eval_sym_mulhi64_sound penv foracle true false a b va vb Ha Hb).
  - (* RAR_Mulhu *)
    destruct Hmul as [[_ [_ H2]] | ->]; [exfalso; apply H2; reflexivity |].
    exact (eval_sym_mulhi64_sound penv foracle false false a b va vb Ha Hb).
  - (* RAR_Div *)
    exact (eval_sym_div_rem_guarded_sound penv foracle CB_SDiv w a b va vb Hw
             (or_intror (or_intror (or_introl eq_refl))) Ha Hb).
  - (* RAR_Divu *)
    exact (eval_sym_div_rem_guarded_sound penv foracle CB_UDiv w a b va vb Hw
             (or_introl eq_refl) Ha Hb).
  - (* RAR_Rem *)
    exact (eval_sym_div_rem_guarded_sound penv foracle CB_SRem w a b va vb Hw
             (or_intror (or_intror (or_intror eq_refl))) Ha Hb).
  - (* RAR_Remu *)
    exact (eval_sym_div_rem_guarded_sound penv foracle CB_URem w a b va vb Hw
             (or_intror (or_introl eq_refl)) Ha Hb).
Qed.

Lemma eval_sym_alu_reg_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op is_word a b va vb,
    (is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vb)) ->
    eval_closed_cert_expr penv foracle (sym_alu_reg op is_word a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_eval_alu_reg op is_word va vb))).
Proof.
  intros Pa penv foracle op [|] a b va vb Hmul Ha Hb; cbn [sym_alu_reg rv_eval_alu_reg].
  - destruct Hmul as [Hdis | Hno]; [discriminate Hdis |].
    eapply eval_ce_sext; [reflexivity |].
    apply eval_sym_alu_reg_raw_sound; [left; reflexivity | left; exact Hno | |].
    + apply eval_ce_trunc; [reflexivity | exact Ha].
    + apply eval_ce_trunc; [reflexivity | exact Hb].
  - apply eval_sym_alu_reg_raw_sound; [right; reflexivity | right; reflexivity | exact Ha | exact Hb].
Qed.

Lemma eval_sym_br_cond_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle c a b va vb,
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vb)) ->
    eval_closed_cert_expr penv foracle (sym_br_cond c a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
      (if rv_eval_br_cond c va vb then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle c a b va vb Ha Hb.
  destruct c; unfold sym_br_cond, rv_eval_br_cond;
    [rewrite (eval_ce_icmp_eq_bool _ _ CIP_Eq 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Ne 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Slt 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Sge 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Ult 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Uge 64%positive a b va vb Ha Hb)]; reflexivity.
Qed.

Definition rv_val_regs_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (rf0 : rv_regfile) (sp0 : @Integers.bit_int 64%positive)
  (vrf : rv_val_regs) (rf : rv_regfile) : Prop :=
  forall r,
    mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0
      (rv_val_read r vrf) (rv_read_reg r rf).

Lemma rv_val_regs_agrees_write {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 vrf rf rd sv v,
    rv_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0 sv v ->
    rv_val_regs_agrees penv foracle rf0 sp0 (rv_val_write rd sv vrf) (rv_write_reg rd v rf).
Proof.
  intros penv foracle rf0 sp0 vrf rf rd sv v Hag Hv r.
  unfold rv_val_read, rv_val_write, rv_read_reg, rv_write_reg.
  destruct (N.eqb r 0%N) eqn:Er0.
  - cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity.
  - destruct (N.eqb rd 0%N) eqn:Erd0.
    + pose proof (Hag r) as Hr; unfold rv_val_read, rv_read_reg in Hr; rewrite Er0 in Hr; exact Hr.
    + destruct (N.eqb r rd) eqn:Erd.
      * exact Hv.
      * pose proof (Hag r) as Hr; unfold rv_val_read, rv_read_reg in Hr; rewrite Er0 in Hr; exact Hr.
Qed.

Lemma rv_sym_step_write_sp : forall rd sv sp_off vrf astk sp_off' vrf' astk',
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
  rv_sym_step_write rd sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
  (- mc_frame_cap <= sp_off' <= 0)%Z /\
  rv_val_read 2%N vrf' = MSV_StackPtr sp_off'.
Proof.
  intros rd sv sp_off vrf astk sp_off' vrf' astk' Hrng Hsp Hst.
  unfold rv_sym_step_write in Hst.
  destruct (N.eqb rd 2%N) eqn:Erd2.
  - apply N.eqb_eq in Erd2; subst rd.
    destruct sv as [| | | off']; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z) eqn:Eb; [| discriminate Hst].
    apply andb_true_iff in Eb as [Eb1 Eb2]; apply Z.leb_le in Eb1; apply Z.leb_le in Eb2.
    inversion Hst; subst; split; [lia | reflexivity].
  - inversion Hst; subst; split; [exact Hrng |].
    unfold rv_val_read, rv_val_write in Hsp |- *; cbn [N.eqb] in Hsp |- *.
    destruct (N.eqb rd 0%N); [exact Hsp | rewrite N.eqb_sym, Erd2; exact Hsp].
Qed.

Lemma rv_sym_step_write_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 rd sv v sp_off vrf astk rf mstk sp_off' vrf' astk',
    rv_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0 astk mstk ->
    mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0 sv v ->
    rv_sym_step_write rd sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
    rv_val_regs_agrees penv foracle rf0 sp0 vrf' (rv_write_reg rd v rf) /\
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0 astk' mstk.
Proof.
  intros penv foracle rf0 sp0 rd sv v sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hv Hst.
  unfold rv_sym_step_write in Hst.
  destruct (N.eqb rd 2%N) eqn:Erd2.
  - apply N.eqb_eq in Erd2; subst rd.
    destruct sv as [| | | off']; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z); [| discriminate Hst].
    inversion Hst; subst; split.
    + apply rv_val_regs_agrees_write; assumption.
    + apply mc_sym_stk_prune_agrees; exact Hastk.
  - inversion Hst; subst; split; [apply rv_val_regs_agrees_write; assumption | exact Hastk].
Qed.

Definition inst_no_word_mulh (d : decoded_rv_inst) : bool :=
  match dri_inst d with
  | RV_AluReg RAR_Mulh true _ _ _
  | RV_AluReg RAR_Mulhsu true _ _ _
  | RV_AluReg RAR_Mulhu true _ _ _ => false
  | _ => true
  end.

Lemma rv_sym_epilogue_ok_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp_off vrf rf,
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    rv_sym_epilogue_ok sp_off vrf = true ->
    rv_callee_saved_preserved rf0 rf /\ rf 1%N = rf0 1%N.
Proof.
  intros penv foracle rf0 sp_off vrf rf Hag Hep.
  unfold rv_sym_epilogue_ok in Hep; rewrite !andb_true_iff in Hep.
  destruct Hep as [[_ Hsp2] Hforall].
  destruct (rv_val_read 2%N vrf) as [| | | zsp] eqn:Ev2; try discriminate Hsp2.
  destruct zsp; try discriminate Hsp2.
  assert (Hreg_saved : forall r, In r rv_preserved_non_sp_regs -> rf r = rf0 r).
  { intros r Hin; rewrite forallb_forall in Hforall; pose proof (Hforall r Hin) as Hmatch.
    destruct (rv_val_read r vrf) as [| | r0 |] eqn:Erv; try discriminate Hmatch.
    apply N.eqb_eq in Hmatch; subst r0.
    pose proof (Hag r) as Hagr; rewrite Erv in Hagr; cbn [mc_sym_val_agrees] in Hagr.
    assert (Hrnz : r <> 0%N).
    { cbn [rv_preserved_non_sp_regs In] in Hin.
      repeat destruct Hin as [<- | Hin]; try discriminate; contradiction. }
    unfold rv_read_reg in Hagr; apply N.eqb_neq in Hrnz; rewrite Hrnz in Hagr; exact Hagr. }
  split.
  - intros r Hcs; unfold rv_is_callee_saved in Hcs; rewrite !orb_true_iff in Hcs.
    destruct Hcs as [[Hr2 | Hr89] | Hr18].
    + apply N.eqb_eq in Hr2; subst r.
      pose proof (Hag 2%N) as Hag2; rewrite Ev2 in Hag2; cbn [mc_sym_val_agrees] in Hag2.
      destruct Hag2 as [_ Heq2]; rewrite mc_add_ptr_zero in Heq2; exact Heq2.
    + apply andb_true_iff in Hr89 as [Hge Hle]; apply N.leb_le in Hge; apply N.leb_le in Hle.
      apply Hreg_saved; cbn [rv_preserved_non_sp_regs In].
      assert (r = 8%N \/ r = 9%N) by lia; destruct H as [-> | ->]; auto.
    + apply andb_true_iff in Hr18 as [Hge Hle]; apply N.leb_le in Hge; apply N.leb_le in Hle.
      apply Hreg_saved; cbn [rv_preserved_non_sp_regs In].
      assert (r = 18%N \/ r = 19%N \/ r = 20%N \/ r = 21%N \/ r = 22%N \/
              r = 23%N \/ r = 24%N \/ r = 25%N \/ r = 26%N \/ r = 27%N) by lia.
      repeat destruct H as [-> | H]; auto 20.
  - apply Hreg_saved; left; reflexivity.
Qed.

Theorem summarize_rv64_dag_at_sound :
  forall {Pa : Params} fuel insts im visited pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk,
    (forall q, pt_get (N.succ_pos q) im = lookup_rv_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk mstk ->
    summarize_rv64_dag_at fuel im visited pc sp_off vrf astk ret_w = Some d_mc ->
    exists rf_end mstk_end,
      rv_exec_mem fuel insts pc (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
      rv_callee_saved_preserved rf0 rf_end /\
      rf_end 1%N = rf0 1%N /\
      eval_cfg_dag penv foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))).
Proof.
  intros Pa fuel insts im visited pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk Him.
  revert visited pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk.
  induction fuel as [| fuel' IH];
    intros visited pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk
           Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hsum;
    cbn [summarize_rv64_dag_at rv_exec_mem] in *.
  - destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook; rewrite Elook.
    assert (Hdec_mulh : inst_no_word_mulh dec = true).
    { clear -Elook Hnmul. induction insts as [| d rest IHl]; cbn in *; [discriminate |].
      apply andb_true_iff in Hnmul as [Hd Hr].
      destruct (N.eqb (dri_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
    destruct (dri_inst dec) as
      [| rd imm
       | op is_word rd rs1 imm
       | op is_word rd rs1 rs2
       | sz is_signed rd rs1 imm
       | sz rs1 rs2 imm
       | cond rs1 rs2 rel
       | rel
       | ] eqn:Ed.
    + (* RV_Nop *)
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk
                Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hsum).
    + (* RV_Lui *)
      destruct (rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk)
        as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hsum].
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                  rd (MSV_Expr (ce_bv_z 64%positive imm)) (@Integers.repr 64%positive imm)
                  sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk (eval_ce_bv_z penv foracle 64%positive imm) Est)
        as [Hag' Hastk'].
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off' vrf' astk' ret_w d_mc
                penv foracle rf0 (rv_write_reg rd (@Integers.repr 64%positive imm) rf) mstk
                Hrw Hnmul Hsp0 Hrng' Hsp2' Hag' Hastk' Hsum).
    + (* RV_AluImm *)
      set (sv_opt :=
        match op, is_word, rv_val_read rs1 vrf with
        | RAI_Addi, false, MSV_StackPtr base_off =>
            let off' := (base_off + imm)%Z in
            if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
        | RAI_Addi, false, MSV_SavedReg r0 =>
            if Z.eqb imm 0%Z then Some (MSV_SavedReg r0) else None
        | _, _, MSV_Expr e => Some (MSV_Expr (sym_alu_imm op is_word e imm))
        | _, _, _ => None
        end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      assert (Hval_sv : mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                          sv (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm)).
      { subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | r0 | base_off] eqn:Er1.
        - destruct op, is_word; discriminate Esv.
        - assert (He_eq : sv = MSV_Expr (sym_alu_imm op is_word e1 imm))
            by (destruct op, is_word; inversion Esv; reflexivity).
          rewrite He_eq; cbn [mc_sym_val_agrees]; apply eval_sym_alu_imm_sound.
          pose proof (Hag rs1) as H1; rewrite Er1 in H1; exact H1.
        - destruct op; destruct is_word; try discriminate Esv.
          destruct (Z.eqb imm 0%Z) eqn:Ez0; [| discriminate Esv].
          apply Z.eqb_eq in Ez0; subst imm; inversion Esv; subst sv; clear Esv.
          pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1 |- *.
          cbn [rv_eval_alu_imm rv_eval_alu_imm_raw]; rewrite H1, mc_add_ptr_zero; reflexivity.
        - destruct op; destruct is_word; try discriminate Esv.
          cbv zeta in Esv.
          destruct (Z.leb (- mc_frame_cap) (base_off + imm) && Z.leb (base_off + imm) 0%Z) eqn:Erng;
            [| discriminate Esv].
          apply andb_true_iff in Erng as [Erng1 Erng2]; apply Z.leb_le in Erng1; apply Z.leb_le in Erng2.
          inversion Esv; subst sv; clear Esv.
          pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1 |- *.
          destruct H1 as [_ Hptr]; split; [lia |].
          cbn [rv_eval_alu_imm rv_eval_alu_imm_raw]; rewrite Hptr, mc_add_ptr_off; reflexivity. }
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                  rd sv (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm)
                  sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est)
        as [Hag' Hastk'].
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off' vrf' astk' ret_w d_mc
                penv foracle rf0 (rv_write_reg rd (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm) rf) mstk
                Hrw Hnmul Hsp0 Hrng' Hsp2' Hag' Hastk' Hsum).
    + (* RV_AluReg *)
      set (is_mv := ((match op with RAR_Add => negb is_word | _ => false end) &&
                     (N.eqb rs1 0%N || N.eqb rs2 0%N))%bool) in *.
      set (sv_opt :=
        if is_mv then
          let sv := if N.eqb rs1 0%N then rv_val_read rs2 vrf else rv_val_read rs1 vrf in
          match sv with MSV_Undef => None | _ => Some sv end
        else
          match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
          | MSV_Expr e1, MSV_Expr e2 => Some (MSV_Expr (sym_alu_reg op is_word e1 e2))
          | _, _ => None
          end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      assert (Hval_sv : mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                          sv (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf))).
      { destruct is_mv eqn:Emv.
        - subst is_mv; apply andb_true_iff in Emv as [Hopm Hz].
          destruct op; try discriminate Hopm; destruct is_word; try discriminate Hopm.
          cbn [rv_eval_alu_reg rv_eval_alu_reg_raw].
          destruct (N.eqb rs1 0%N) eqn:Ez1.
          + apply N.eqb_eq in Ez1; subst rs1.
            replace (rv_read_reg 0%N rf) with (@Integers.zero 64%positive) by reflexivity.
            rewrite (@Integers.add_zero_l 64%positive).
            destruct (rv_val_read rs2 vrf) eqn:Er2; try discriminate Esv;
              inversion Esv; subst sv; pose proof (Hag rs2) as H2; rewrite Er2 in H2; exact H2.
          + cbn [orb] in Hz; apply N.eqb_eq in Hz; subst rs2.
            replace (rv_read_reg 0%N rf) with (@Integers.zero 64%positive) by reflexivity.
            rewrite (@Integers.add_zero 64%positive).
            destruct (rv_val_read rs1 vrf) eqn:Er1; try discriminate Esv;
              inversion Esv; subst sv; pose proof (Hag rs1) as H1; rewrite Er1 in H1; exact H1.
        - subst sv_opt; cbn [fst snd] in Esv.
          destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Esv.
          destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Esv.
          inversion Esv; subst sv; clear Esv.
          pose proof (Hag rs1) as H1; rewrite Er1 in H1;
            pose proof (Hag rs2) as H2; rewrite Er2 in H2; cbn [mc_sym_val_agrees] in H1, H2 |- *.
          assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
          { destruct is_word; [| left; reflexivity].
            right; unfold inst_no_word_mulh in Hdec_mulh; rewrite Ed in Hdec_mulh.
            destruct op; repeat split; intro C; discriminate C || discriminate Hdec_mulh. }
          apply eval_sym_alu_reg_sound; assumption. }
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                  rd sv (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf))
                  sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est)
        as [Hag' Hastk'].
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off' vrf' astk' ret_w d_mc
                penv foracle rf0 (rv_write_reg rd (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)) rf) mstk
                Hrw Hnmul Hsp0 Hrng' Hsp2' Hag' Hastk' Hsum).
    + (* RV_Load *)
      destruct (rv_val_read rs1 vrf) as [| | | base_off] eqn:Er1; try discriminate Hsum.
      destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hsum].
      destruct (mc_sym_stk_load (base_off + imm) sz is_signed astk) as [sv |] eqn:Eload;
        [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
      assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
      pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1; destruct H1 as [_ Hptr1].
      pose proof (Hag 2%N) as H2; rewrite Hsp2 in H2; cbn [mc_sym_val_agrees] in H2; destruct H2 as [_ Hptr2].
      destruct Hsp0 as [Hsp0_cap Hsp0_al].
      assert (Hoff_eq : mc_addr_to_off (rv_read_reg 2%N rf0)
                          (@Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm)) =
                        (base_off + imm)%Z).
      { rewrite Hptr1, mc_add_ptr_off; apply mc_addr_to_off_add; [exact Hsp0_cap | lia]. }
      assert (Hsp_eq : mc_addr_to_off (rv_read_reg 2%N rf0) (rv_read_reg 2%N rf) = sp_off).
      { rewrite Hptr2; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]. }
      rewrite Hoff_eq, Hsp_eq, Eslot.
      pose proof (mc_sym_stk_load_sound penv foracle (fun r0 => rv_read_reg r0 rf0)
                    (rv_read_reg 2%N rf0) (base_off + imm) sz is_signed astk mstk sv Hastk Eload) as Hval_sv.
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                  rd sv (mc_stk_load mstk (base_off + imm) sz is_signed)
                  sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est)
        as [Hag' Hastk'].
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off' vrf' astk' ret_w d_mc
                penv foracle rf0 (rv_write_reg rd (mc_stk_load mstk (base_off + imm) sz is_signed) rf) mstk
                Hrw Hnmul (conj Hsp0_cap Hsp0_al) Hrng' Hsp2' Hag' Hastk' Hsum).
    + (* RV_Store *)
      destruct (rv_val_read rs1 vrf) as [| | | base_off] eqn:Er1; try discriminate Hsum.
      destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hsum].
      destruct (match rv_val_read rs2 vrf with
                | MSV_Undef => false
                | MSV_Expr _ => true
                | MSV_SavedReg _ | MSV_StackPtr _ => mc_mem_size_eqb sz MS_8
                end) eqn:Esvok; [| discriminate Hsum].
      pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
      assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
      pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1; destruct H1 as [_ Hptr1].
      pose proof (Hag 2%N) as H2; rewrite Hsp2 in H2; cbn [mc_sym_val_agrees] in H2; destruct H2 as [_ Hptr2].
      destruct Hsp0 as [Hsp0_cap Hsp0_al].
      assert (Hoff_eq : mc_addr_to_off (rv_read_reg 2%N rf0)
                          (@Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm)) =
                        (base_off + imm)%Z).
      { rewrite Hptr1, mc_add_ptr_off; apply mc_addr_to_off_add; [exact Hsp0_cap | lia]. }
      assert (Hsp_eq : mc_addr_to_off (rv_read_reg 2%N rf0) (rv_read_reg 2%N rf) = sp_off).
      { rewrite Hptr2; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]. }
      rewrite Hoff_eq, Hsp_eq, Eslot.
      assert (Hsz_match : match rv_val_read rs2 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end).
      { destruct (rv_val_read rs2 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Esvok. }
      pose proof (mc_sym_stk_store_agrees penv foracle (fun r0 => rv_read_reg r0 rf0)
                    (rv_read_reg 2%N rf0) (base_off + imm) sz (rv_val_read rs2 vrf) (rv_read_reg rs2 rf)
                    astk mstk Hsz_match (Hag rs2) Hastk) as Hastk'.
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf
                (mc_sym_stk_store (base_off + imm) sz (rv_val_read rs2 vrf) astk)
                ret_w d_mc penv foracle rf0 rf (mc_stk_store mstk (base_off + imm) sz (rv_read_reg rs2 rf))
                Hrw Hnmul (conj Hsp0_cap Hsp0_al) Hrng Hsp2 Hag Hastk' Hsum).
    + (* RV_Branch *)
      destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Hsum.
      destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Hsum.
      destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w) as [dt |] eqn:Edt;
        [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' im (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf astk ret_w) as [df |] eqn:Edf;
        [| discriminate Hsum].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1.
      pose proof (Hag rs2) as H2; rewrite Er2 in H2; cbn [mc_sym_val_agrees] in H2.
      pose proof (eval_sym_br_cond_sound penv foracle cond e1 e2 (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) H1 H2) as Hbr.
      cbn [eval_cfg_dag]; rewrite Hbr.
      destruct (rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w dt penv foracle rf0 rf mstk
                  Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf astk ret_w df penv foracle rf0 rf mstk
                  Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Edf).
    + (* RV_Jal0 *)
      destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hsum].
      exact (IH (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk
                Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hsum).
    + (* RV_Ret *)
      destruct (rv_sym_epilogue_ok sp_off vrf) eqn:Eep; [| discriminate Hsum].
      destruct (rv_val_read 10%N vrf) as [| e_ret | |] eqn:Er10; try discriminate Hsum.
      inversion Hsum; subst d_mc; clear Hsum.
      destruct (rv_sym_epilogue_ok_sound penv foracle rf0 sp_off vrf rf Hag Eep) as [Hcs Hra].
      exists rf, mstk; split; [reflexivity | split; [exact Hcs | split; [exact Hra |]]].
      cbn [eval_cfg_dag]; unfold rv_trunc_ret_expr, rv_trunc_ret_val.
      pose proof (Hag 10%N) as Ha10; rewrite Er10 in Ha10; cbn [mc_sym_val_agrees] in Ha10.
      destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
      * apply Pos.eqb_eq in Ew64; subst ret_w.
        rewrite Ha10, (@Integers.repr_unsigned 64%positive); reflexivity.
      * assert (Hlt64 : (ret_w <? 64)%positive = true) by (exact (rv_supported_arg_width_lt64 _ Hrw Ew64)).
        rewrite (eval_ce_trunc penv foracle 64%positive ret_w e_ret _ Hlt64 Ha10); reflexivity.
Qed.

Definition wf_sym_expr (allowed : list (string * positive)) (w : positive) (e : cert_expr) : Prop :=
  wt_cert_expr [] e = true /\
  cert_expr_bit_width e = w /\
  is_let_free_expr e = true /\
  vars_subset_b (collect_free_vars [] e) allowed = true.

Definition wf_sym_regs (allowed : list (string * positive)) (srf : rv_sym_regs) (def : rv_def_mask) : Prop :=
  forall r, rv_def_read r def = true -> wf_sym_expr allowed 64%positive (rv_sym_read r srf).

Lemma wf_sym_bv_const : forall allowed w v,
  wf_sym_expr allowed w (CE_BvConst w v).
Proof.
  intros; repeat split; try reflexivity; cbn; rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma wf_sym_bv_z : forall allowed w z,
  wf_sym_expr allowed w (ce_bv_z w z).
Proof.
  intros; apply wf_sym_bv_const.
Qed.

Lemma vars_subset_app : forall vs1 vs2 allowed,
  vars_subset_b vs1 allowed = true ->
  vars_subset_b vs2 allowed = true ->
  vars_subset_b (vs1 ++ vs2) allowed = true.
Proof.
  intros vs1 vs2 allowed H1 H2.
  unfold vars_subset_b in *; rewrite forallb_app, H1, H2; reflexivity.
Qed.

Lemma wf_sym_binop : forall allowed op w a b,
  w <> 1%positive \/ (op = CB_And \/ op = CB_Or) ->
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (CE_BinOp op w no_binop_flags a b).
Proof.
  intros allowed op w a b Hw1 (Hta & Hwa & Hlfa & Hva) (Htb & Hwb & Hlfb & Hvb).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - destruct op; rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl; reflexivity.
  - reflexivity.
  - rewrite Hlfa, Hlfb; reflexivity.
  - apply vars_subset_app; assumption.
Qed.

Lemma wf_sym_icmp : forall allowed pr w a b,
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed 1%positive (CE_ICmp pr false w a b).
Proof.
  intros allowed pr w a b (Hta & Hwa & Hlfa & Hva) (Htb & Hwb & Hlfb & Hvb).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl; reflexivity.
  - reflexivity.
  - rewrite Hlfa, Hlfb; reflexivity.
  - apply vars_subset_app; assumption.
Qed.

Lemma wf_sym_select : forall allowed w c t f,
  wf_sym_expr allowed 1%positive c ->
  wf_sym_expr allowed w t ->
  wf_sym_expr allowed w f ->
  wf_sym_expr allowed w (CE_Select w c t f).
Proof.
  intros allowed w c t f (Htc & Hwc & Hlfc & Hvc) (Htt & Hwt & Hlft & Hvt) (Htf & Hwf & Hlff & Hvf).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - rewrite Htc, Htt, Htf, Hwc, Hwt, Hwf, !Pos.eqb_refl; reflexivity.
  - reflexivity.
  - rewrite Hlfc, Hlft, Hlff; reflexivity.
  - apply vars_subset_app; [exact Hvc | apply vars_subset_app; assumption].
Qed.

Lemma wf_sym_cast : forall allowed k fw tw o,
  ((match k with
    | CCK_ZExt | CCK_SExt => (fw <? tw)%positive
    | CCK_Trunc => (tw <? fw)%positive
    end) = true) ->
  wf_sym_expr allowed fw o ->
  wf_sym_expr allowed tw (CE_Cast k fw tw no_cast_flags o).
Proof.
  intros allowed k fw tw o Hlt (Hto & Hwo & Hlfo & Hvo).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - rewrite Hto, Hwo, Pos.eqb_refl; destruct k; rewrite Hlt; reflexivity.
  - reflexivity.
  - exact Hlfo.
  - exact Hvo.
Qed.

Lemma wf_sym_alu_imm_raw : forall allowed op w a imm,
  (w = 32%positive \/ w = 64%positive) ->
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w (sym_alu_imm_raw op w a imm).
Proof.
  intros allowed op w a imm Hw Ha.
  destruct op; cbn [sym_alu_imm_raw].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_cast; [destruct Hw as [-> | ->]; reflexivity |].
    apply wf_sym_icmp; [exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_cast; [destruct Hw as [-> | ->]; reflexivity |].
    apply wf_sym_icmp; [exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_const].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_const].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_const].
Qed.

Lemma wf_sym_alu_imm : forall allowed op is_word a imm,
  wf_sym_expr allowed 64%positive a ->
  wf_sym_expr allowed 64%positive (sym_alu_imm op is_word a imm).
Proof.
  intros allowed op [|] a imm Ha; cbn [sym_alu_imm].
  - apply wf_sym_cast; [reflexivity |].
    apply wf_sym_alu_imm_raw; [left; reflexivity |].
    apply wf_sym_cast; [reflexivity | exact Ha].
  - apply wf_sym_alu_imm_raw; [right; reflexivity | exact Ha].
Qed.

Lemma wf_sym_div_rem_guarded : forall allowed op w a b,
  (w = 32%positive \/ w = 64%positive) ->
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (sym_div_rem_guarded op w a b).
Proof.
  intros allowed op w a b Hw Ha Hb.
  assert (Hnz : w <> 1%positive) by (destruct Hw as [-> | ->]; discriminate).
  assert (Hiz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)))
    by (apply wf_sym_icmp; [exact Hb | apply wf_sym_bv_const]).
  destruct op; cbn [sym_div_rem_guarded];
    try (
      assert (Hovf : wf_sym_expr allowed 1%positive
        (CE_BinOp CB_And 1%positive no_binop_flags
          (CE_ICmp CIP_Eq false w a (ce_int_min w))
          (CE_ICmp CIP_Eq false w b (ce_all_ones w))))
      by (apply wf_sym_binop; [right; left; reflexivity | apply wf_sym_icmp; [exact Ha | apply wf_sym_bv_const] | apply wf_sym_icmp; [exact Hb | apply wf_sym_bv_const]]);
      assert (Hbad : wf_sym_expr allowed 1%positive
        (CE_BinOp CB_Or 1%positive no_binop_flags
          (CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N))
          (CE_BinOp CB_And 1%positive no_binop_flags
            (CE_ICmp CIP_Eq false w a (ce_int_min w))
            (CE_ICmp CIP_Eq false w b (ce_all_ones w)))))
      by (apply wf_sym_binop; [right; right; reflexivity | exact Hiz | exact Hovf]);
      apply wf_sym_select; [exact Hiz | try apply wf_sym_bv_const; try exact Ha |
        apply wf_sym_select; [exact Hovf | apply wf_sym_bv_const |
          apply wf_sym_binop; [left; exact Hnz | apply wf_sym_select; [exact Hovf | apply wf_sym_bv_const | exact Ha] | apply wf_sym_select; [exact Hbad | apply wf_sym_bv_const | exact Hb]]]]).
  - (* CB_UDiv *)
    apply wf_sym_select; [exact Hiz | apply wf_sym_bv_const |].
    apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_select; [exact Hiz | apply wf_sym_bv_const | exact Hb]].
  - (* CB_URem *)
    apply wf_sym_select; [exact Hiz | exact Ha |].
    apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_select; [exact Hiz | apply wf_sym_bv_const | exact Hb]].
Qed.

Lemma wf_sym_mulhi64 : forall allowed sa sb a b,
  wf_sym_expr allowed 64%positive a ->
  wf_sym_expr allowed 64%positive b ->
  wf_sym_expr allowed 64%positive (sym_mulhi64 sa sb a b).
Proof.
  intros allowed sa sb a b Ha Hb; unfold sym_mulhi64.
  apply wf_sym_cast; [reflexivity |].
  apply wf_sym_binop; [left; discriminate | | apply wf_sym_bv_const].
  apply wf_sym_binop; [left; discriminate | |].
  - destruct sa; apply wf_sym_cast; [reflexivity | exact Ha | reflexivity | exact Ha].
  - destruct sb; apply wf_sym_cast; [reflexivity | exact Hb | reflexivity | exact Hb].
Qed.

Lemma wf_sym_alu_reg_raw : forall allowed op w a b,
  (w = 32%positive \/ w = 64%positive) ->
  (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu \/ w = 64%positive) ->
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (sym_alu_reg_raw op w a b).
Proof.
  intros allowed op w a b Hw Hmul Ha Hb.
  assert (Hnz : w <> 1%positive) by (destruct Hw as [-> | ->]; discriminate).
  destruct op; cbn [sym_alu_reg_raw];
    try (exfalso; destruct Hmul as [[H0 [H1 H2]] | ->]; [contradiction | discriminate H0 || discriminate H1 || discriminate H2]).
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_binop; [left; exact Hnz | exact Hb | apply wf_sym_bv_const]].
  - apply wf_sym_cast; [destruct Hw as [-> | ->]; reflexivity | apply wf_sym_icmp; assumption].
  - apply wf_sym_cast; [destruct Hw as [-> | ->]; reflexivity | apply wf_sym_icmp; assumption].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_binop; [left; exact Hnz | exact Hb | apply wf_sym_bv_const]].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_binop; [left; exact Hnz | exact Hb | apply wf_sym_bv_const]].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - destruct Hmul as [[H0 _] | ->]; [exfalso; apply H0; reflexivity | apply wf_sym_mulhi64; assumption].
  - destruct Hmul as [[_ [H1 _]] | ->]; [exfalso; apply H1; reflexivity | apply wf_sym_mulhi64; assumption].
  - destruct Hmul as [[_ [_ H2]] | ->]; [exfalso; apply H2; reflexivity | apply wf_sym_mulhi64; assumption].
  - apply wf_sym_div_rem_guarded; assumption.
  - apply wf_sym_div_rem_guarded; assumption.
  - apply wf_sym_div_rem_guarded; assumption.
  - apply wf_sym_div_rem_guarded; assumption.
Qed.

Lemma wf_sym_alu_reg : forall allowed op is_word a b,
  (is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)) ->
  wf_sym_expr allowed 64%positive a ->
  wf_sym_expr allowed 64%positive b ->
  wf_sym_expr allowed 64%positive (sym_alu_reg op is_word a b).
Proof.
  intros allowed op [|] a b Hmul Ha Hb; cbn [sym_alu_reg].
  - destruct Hmul as [Hdis | Hno]; [discriminate Hdis |].
    apply wf_sym_cast; [reflexivity |].
    apply wf_sym_alu_reg_raw;
      [left; reflexivity | left; exact Hno
      | apply wf_sym_cast; [reflexivity | exact Ha]
      | apply wf_sym_cast; [reflexivity | exact Hb]].
  - apply wf_sym_alu_reg_raw; [right; reflexivity | right; reflexivity | exact Ha | exact Hb].
Qed.

Definition rv_val_regs_wf (allowed : list (string * positive)) (vrf : rv_val_regs) : Prop :=
  forall r, mc_sym_val_wf allowed (rv_val_read r vrf).

Lemma rv_val_regs_wf_write : forall allowed vrf rd sv,
  rv_val_regs_wf allowed vrf ->
  mc_sym_val_wf allowed sv ->
  rv_val_regs_wf allowed (rv_val_write rd sv vrf).
Proof.
  intros allowed vrf rd sv Hw Hsv r.
  unfold rv_val_read, rv_val_write.
  destruct (N.eqb r 0%N) eqn:Er0; [apply wf_sym_bv_const |].
  destruct (N.eqb rd 0%N) eqn:Erd0.
  { pose proof (Hw r) as Hr'; unfold rv_val_read in Hr'; rewrite Er0 in Hr'; exact Hr'. }
  destruct (N.eqb r rd); [exact Hsv |].
  pose proof (Hw r) as Hr'; unfold rv_val_read in Hr'; rewrite Er0 in Hr'; exact Hr'.
Qed.

Theorem summarize_rv64_dag_at_wf :
  forall fuel insts im visited pc allowed sp_off vrf astk ret_w d_mc,
    (forall q, pt_get (N.succ_pos q) im = lookup_rv_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_wf allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    summarize_rv64_dag_at fuel im visited pc sp_off vrf astk ret_w = Some d_mc ->
    wf_cfg_dag allowed d_mc = true.
Proof.
  intros fuel insts im visited pc allowed sp_off vrf astk ret_w d_mc Him.
  revert visited pc allowed sp_off vrf astk ret_w d_mc.
  induction fuel as [| fuel' IH];
    intros visited pc allowed sp_off vrf astk ret_w d_mc
           Hrw Hnmul Hrng Hsp2 Hwf Hstk Hsum;
    cbn [summarize_rv64_dag_at] in Hsum.
  - destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook.
    assert (Hdec_mulh : inst_no_word_mulh dec = true).
    { clear -Elook Hnmul. induction insts as [| d rest IHl]; cbn in *; [discriminate |].
      apply andb_true_iff in Hnmul as [Hd Hr].
      destruct (N.eqb (dri_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
    destruct (dri_inst dec) as
      [| rd imm
       | op is_word rd rs1 imm
       | op is_word rd rs1 rs2
       | sz is_signed rd rs1 imm
       | sz rs1 rs2 imm
       | cond rs1 rs2 rel
       | rel
       | ] eqn:Ed.
    + exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N allowed sp_off vrf astk ret_w d_mc
                Hrw Hnmul Hrng Hsp2 Hwf Hstk Hsum).
    + destruct (rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk)
        as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hsum].
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      assert (Hwf' : rv_val_regs_wf allowed vrf').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N); [discriminate Est |].
        inversion Est; subst; apply rv_val_regs_wf_write; [exact Hwf | apply wf_sym_bv_z]. }
      assert (Hstk' : mc_sym_stack_wf allowed sp_off' astk').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N); [discriminate Est | inversion Est; subst; exact Hstk]. }
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' Hwf' Hstk' Hsum).
    + set (sv_opt :=
        match op, is_word, rv_val_read rs1 vrf with
        | RAI_Addi, false, MSV_StackPtr base_off =>
            let off' := (base_off + imm)%Z in
            if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
        | RAI_Addi, false, MSV_SavedReg r0 =>
            if Z.eqb imm 0%Z then Some (MSV_SavedReg r0) else None
        | _, _, MSV_Expr e => Some (MSV_Expr (sym_alu_imm op is_word e imm))
        | _, _, _ => None
        end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      assert (Hsv_wf : mc_sym_val_wf allowed sv).
      { subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | r0 | base_off] eqn:Er1.
        - destruct op, is_word; discriminate Esv.
        - assert (He_eq : sv = MSV_Expr (sym_alu_imm op is_word e1 imm))
            by (destruct op, is_word; inversion Esv; reflexivity).
          rewrite He_eq; apply wf_sym_alu_imm; pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1.
        - destruct op, is_word; try discriminate Esv; destruct (Z.eqb imm 0%Z); try discriminate Esv;
            inversion Esv; exact I.
        - destruct op, is_word; try discriminate Esv.
          cbv zeta in Esv.
          destruct (Z.leb (- mc_frame_cap) (base_off + imm) && Z.leb (base_off + imm) 0%Z) eqn:Eb; try discriminate Esv.
          apply andb_true_iff in Eb as [Eb1 Eb2]; apply Z.leb_le in Eb1; apply Z.leb_le in Eb2.
          inversion Esv; cbn [mc_sym_val_wf]; lia. }
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      assert (Hwf' : rv_val_regs_wf allowed vrf' /\ mc_sym_stack_wf allowed sp_off' astk').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
        - destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z) eqn:Eb; try discriminate Est.
          apply andb_true_iff in Eb as [Eb1 Eb2]; apply Z.leb_le in Eb1; apply Z.leb_le in Eb2.
          inversion Est; subst; split;
            [apply rv_val_regs_wf_write; assumption | eapply mc_sym_stk_prune_wf; [lia | exact Hstk]].
        - inversion Est; subst; split; [apply rv_val_regs_wf_write; assumption | exact Hstk]. }
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' (proj1 Hwf') (proj2 Hwf') Hsum).
    + set (is_mv := ((match op with RAR_Add => negb is_word | _ => false end) &&
                     (N.eqb rs1 0%N || N.eqb rs2 0%N))%bool) in *.
      set (sv_opt :=
        if is_mv then
          let sv := if N.eqb rs1 0%N then rv_val_read rs2 vrf else rv_val_read rs1 vrf in
          match sv with MSV_Undef => None | _ => Some sv end
        else
          match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
          | MSV_Expr e1, MSV_Expr e2 => Some (MSV_Expr (sym_alu_reg op is_word e1 e2))
          | _, _ => None
          end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      assert (Hsv_wf : mc_sym_val_wf allowed sv).
      { destruct is_mv eqn:Emv.
        - subst sv_opt; cbn [fst snd] in Esv.
          destruct (N.eqb rs1 0%N).
          + destruct (rv_val_read rs2 vrf) eqn:Er2; try discriminate Esv; inversion Esv; subst sv;
              pose proof (Hwf rs2) as H2; rewrite Er2 in H2; exact H2.
          + destruct (rv_val_read rs1 vrf) eqn:Er1; try discriminate Esv; inversion Esv; subst sv;
              pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1.
        - subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Esv.
          destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Esv.
          inversion Esv; subst sv; clear Esv.
          assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
          { destruct is_word; [| left; reflexivity].
            right; unfold inst_no_word_mulh in Hdec_mulh; rewrite Ed in Hdec_mulh.
            destruct op; repeat split; intro C; discriminate C || discriminate Hdec_mulh. }
          apply wf_sym_alu_reg;
            [exact Hok_m
            | pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1
            | pose proof (Hwf rs2) as H2; rewrite Er2 in H2; exact H2]. }
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      assert (Hwf' : rv_val_regs_wf allowed vrf' /\ mc_sym_stack_wf allowed sp_off' astk').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
        - destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z); try discriminate Est.
          inversion Est; subst; split;
            [apply rv_val_regs_wf_write; assumption | eapply mc_sym_stk_prune_wf; [lia | exact Hstk]].
        - inversion Est; subst; split; [apply rv_val_regs_wf_write; assumption | exact Hstk]. }
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' (proj1 Hwf') (proj2 Hwf') Hsum).
    + destruct (rv_val_read rs1 vrf) as [| | | base_off]; try discriminate Hsum.
      destruct (mc_slot_in_frame sp_off (base_off + imm) sz); [| discriminate Hsum].
      destruct (mc_sym_stk_load (base_off + imm) sz is_signed astk) as [sv |] eqn:Eload;
        [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Eload) as Hsv_wf.
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      assert (Hwf' : rv_val_regs_wf allowed vrf' /\ mc_sym_stack_wf allowed sp_off' astk').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
        - destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z); try discriminate Est.
          inversion Est; subst; split;
            [apply rv_val_regs_wf_write; assumption | eapply mc_sym_stk_prune_wf; [lia | exact Hstk]].
        - inversion Est; subst; split; [apply rv_val_regs_wf_write; assumption | exact Hstk]. }
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' (proj1 Hwf') (proj2 Hwf') Hsum).
    + destruct (rv_val_read rs1 vrf) as [| | | base_off]; try discriminate Hsum.
      destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hsum].
      destruct (match rv_val_read rs2 vrf with
                | MSV_Undef => false
                | MSV_Expr _ => true
                | MSV_SavedReg _ | MSV_StackPtr _ => mc_mem_size_eqb sz MS_8
                end); [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng Hsp2 Hwf
                (mc_sym_stk_store_wf _ _ _ _ _ _ Eslot (Hwf rs2) Hstk) Hsum).
    + destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Hsum.
      destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Hsum.
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w) as [dt |] eqn:Edt;
        [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' im (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf astk ret_w) as [df |] eqn:Edf;
        [| discriminate Hsum].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf rs1) as H1; rewrite Er1 in H1; pose proof (Hwf rs2) as H2; rewrite Er2 in H2.
      assert (Hbc : wf_sym_expr allowed 1%positive (sym_br_cond cond e1 e2))
        by (destruct cond; apply wf_sym_icmp; assumption).
      destruct Hbc as (Htc & Hwc & Hlfc & Hvc).
      cbn [wf_cfg_dag]; rewrite Htc, Hwc, Hlfc, Hvc; cbn [Pos.eqb andb].
      rewrite (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng Hsp2 Hwf Hstk Edt),
              (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng Hsp2 Hwf Hstk Edf); reflexivity.
    + destruct (add_rel_off pc rel); [| discriminate Hsum].
      exact (IH (pt_add_n pc visited) _ allowed sp_off vrf astk ret_w d_mc Hrw Hnmul Hrng Hsp2 Hwf Hstk Hsum).
    + destruct (rv_sym_epilogue_ok sp_off vrf); [| discriminate Hsum].
      destruct (rv_val_read 10%N vrf) as [| e_ret | |] eqn:Er10; try discriminate Hsum.
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf 10%N) as Ha10; rewrite Er10 in Ha10.
      assert (Hrte : wf_sym_expr allowed ret_w (rv_trunc_ret_expr ret_w e_ret)).
      { unfold rv_trunc_ret_expr; destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
        - apply Pos.eqb_eq in Ew64; subst ret_w; exact Ha10.
        - assert (Hlt64 : (ret_w <? 64)%positive = true) by (exact (rv_supported_arg_width_lt64 _ Hrw Ew64)).
          apply wf_sym_cast; [exact Hlt64 | exact Ha10]. }
      destruct Hrte as (Hte & Hwe & Hlfe & Hve).
      cbn [wf_cfg_dag]; rewrite Hte, Hwe, Hlfe, Hve, Pos.eqb_refl; reflexivity.
Qed.

Lemma decode_rvc_hw_no_word_mulh : forall hw inst,
  decode_rvc_hw hw = Some inst ->
  (match inst with
   | RV_AluReg RAR_Mulh true _ _ _
   | RV_AluReg RAR_Mulhsu true _ _ _
   | RV_AluReg RAR_Mulhu true _ _ _ => False
   | _ => True
   end).
Proof.
  intros hw inst H.
  unfold decode_rvc_hw in H.
  destruct (N.eqb hw 0%N); [discriminate |].
  cbv zeta in H;
  repeat match type of H with
  | Some _ = Some _ => inversion H; subst; exact I
  | None = Some _ => discriminate H
  | (if true then _ else _) = _ => cbv iota in H
  | (if false then _ else _) = _ => cbv iota in H
  | (if ?b then _ else _) = _ => destruct b
  end.
Qed.

Lemma decode_rv32_word_no_word_mulh : forall w inst,
  decode_rv32_word w = Some inst ->
  (match inst with
   | RV_AluReg RAR_Mulh true _ _ _
   | RV_AluReg RAR_Mulhsu true _ _ _
   | RV_AluReg RAR_Mulhu true _ _ _ => False
   | _ => True
   end).
Proof.
  intros w inst H.
  unfold decode_rv32_word in H.
  destruct (N.eqb (bit_slice w 0%N 7%N) 55%N); [inversion H; subst; exact I |].
  destruct (N.eqb (bit_slice w 0%N 7%N) 19%N).
  { cbv zeta in H;
    repeat match type of H with
    | Some _ = Some _ => inversion H; subst; exact I
    | None = Some _ => discriminate H
    | (if true then _ else _) = _ => cbv iota in H
    | (if false then _ else _) = _ => cbv iota in H
    | (if ?b then _ else _) = _ => destruct b
    end. }
  destruct (N.eqb (bit_slice w 0%N 7%N) 27%N).
  { cbv zeta in H;
    repeat match type of H with
    | Some _ = Some _ => inversion H; subst; exact I
    | None = Some _ => discriminate H
    | (if true then _ else _) = _ => cbv iota in H
    | (if false then _ else _) = _ => cbv iota in H
    | (if ?b then _ else _) = _ => destruct b
    end. }
  destruct (N.eqb (bit_slice w 0%N 7%N) 51%N).
  { cbn [option_map] in H.
    destruct (if N.eqb _ 0%N then _ else _) as [r |]; [inversion H; subst; destruct r; exact I | discriminate H]. }
  destruct (N.eqb (bit_slice w 0%N 7%N) 59%N).
  { destruct (N.eqb (bit_slice w 25%N 7%N) 0%N);
      [destruct (N.eqb (bit_slice w 12%N 3%N) 0%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 1%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 5%N)]];
       try (inversion H; subst; exact I); discriminate H |].
    destruct (N.eqb (bit_slice w 25%N 7%N) 32%N);
      [destruct (N.eqb (bit_slice w 12%N 3%N) 0%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 5%N)];
       try (inversion H; subst; exact I); discriminate H |].
    destruct (N.eqb (bit_slice w 25%N 7%N) 1%N);
      [destruct (N.eqb (bit_slice w 12%N 3%N) 0%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 4%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 5%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 6%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 7%N)]]]];
       try (inversion H; subst; exact I); discriminate H | discriminate H]. }
  cbv zeta in H;
  repeat match type of H with
  | Some _ = Some _ => inversion H; subst; exact I
  | None = Some _ => discriminate H
  | (if true then _ else _) = _ => cbv iota in H
  | (if false then _ else _) = _ => cbv iota in H
  | (if ?b then _ else _) = _ => destruct b
  | option_map _ ?x = _ => destruct x; cbn [option_map] in H
  end.
Qed.

Lemma decode_rv64_stream_acc_no_word_mulh : forall fuel rvc cur cur_off acc insts,
  forallb inst_no_word_mulh acc = true ->
  decode_rv64_stream_acc fuel rvc cur cur_off acc = inr insts ->
  forallb inst_no_word_mulh insts = true.
Proof.
  induction fuel as [| fuel' IH]; intros rvc [| b0 r0] cur_off acc insts Hacc H;
    cbn [decode_rv64_stream_acc] in H.
  - inversion H; subst insts; rewrite elf_rev_tr_eq, forallb_forall in *;
      intros x Hx; apply Hacc; rewrite in_rev; exact Hx.
  - discriminate H.
  - inversion H; subst insts; rewrite elf_rev_tr_eq, forallb_forall in *;
      intros x Hx; apply Hacc; rewrite in_rev; exact Hx.
  - destruct (take_u16_le (b0 :: r0)) as [[hw rest2] |] eqn:Ehw; [| discriminate H].
    destruct (negb (N.eqb (N.modulo hw 4%N) 3%N)).
    + destruct (negb rvc); [discriminate H |].
      destruct (decode_rvc_hw hw) as [inst |] eqn:Edec; [| discriminate H].
      eapply IH; [| exact H].
      cbn [forallb]; rewrite Hacc, andb_true_r.
      pose proof (decode_rvc_hw_no_word_mulh hw inst Edec) as Hnm.
      unfold inst_no_word_mulh; cbn [dri_inst].
      destruct inst as [| | | op [|] | | | | |]; try reflexivity; destruct op; try reflexivity; contradiction.
    + destruct (take_u32_le (b0 :: r0)) as [[w rest4] |] eqn:Ew; [| discriminate H].
      destruct (decode_rv32_word w) as [inst |] eqn:Edec; [| discriminate H].
      eapply IH; [| exact H].
      cbn [forallb]; rewrite Hacc, andb_true_r.
      pose proof (decode_rv32_word_no_word_mulh w inst Edec) as Hnm.
      unfold inst_no_word_mulh; cbn [dri_inst].
      destruct inst as [| | | op [|] | | | | |]; try reflexivity; destruct op; try reflexivity; contradiction.
Qed.

Lemma decode_rv64_bytes_no_word_mulh : forall rvc code insts,
  decode_rv64_bytes rvc code = inr insts ->
  forallb inst_no_word_mulh insts = true.
Proof.
  intros rvc code insts H; unfold decode_rv64_bytes in H.
  destruct (Nat.eqb (elf_length_tr code) 0 || negb (Nat.eqb (Nat.modulo (elf_length_tr code) 2) 0));
    [discriminate H |].
  destruct (negb rvc && negb (Nat.eqb (Nat.modulo (elf_length_tr code) 4) 0));
    [discriminate H |].
  eapply decode_rv64_stream_acc_no_word_mulh; [| exact H]; reflexivity.
Qed.

Definition rv_rf_matches_args {Pa : Params}
  (penv : param_env Pa) (arg_specs : list rv_arg_spec) (rf : rv_regfile) : Prop :=
  forall (k : nat) sp,
    (k < List.length arg_specs)%nat ->
    nth_error arg_specs k = Some sp ->
    exists v : @Integers.bit_int (ras_width sp),
      penv (ras_name sp) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      rv_read_reg (10%N + N.of_nat k) rf =
        (if Pos.eqb (ras_width sp) 64%positive then
           @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
         else
           match ras_ext sp with
           | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
           | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
           end).

Lemma rv_build_init_val_regs_other : forall specs base r,
  (r < base \/ base + N.of_nat (List.length specs) <= r)%N ->
  rv_build_init_val_regs base specs r = rv_empty_val_regs r.
Proof.
  induction specs as [| sp rest IH]; intros base r Hrng; cbn [rv_build_init_val_regs List.length] in *.
  - reflexivity.
  - destruct (N.eqb r base) eqn:Erb.
    + apply N.eqb_eq in Erb; lia.
    + apply IH; lia.
Qed.

Lemma rv_init_val_regs_agrees :
  forall {Pa : Params} (penv : param_env Pa) foracle arg_specs rf,
    forallb rv_valid_arg_spec arg_specs = true ->
    rv_rf_matches_args penv arg_specs rf ->
    rv_val_regs_agrees penv foracle rf (rv_read_reg 2%N rf)
      (rv_build_init_val_regs 10%N arg_specs) rf.
Proof.
  intros Pa penv foracle arg_specs rf Hws Hm r.
  assert (Hgen : forall base specs,
    (1 <= base)%N ->
    forallb rv_valid_arg_spec specs = true ->
    (forall (k : nat) sp, (k < List.length specs)%nat -> nth_error specs k = Some sp ->
      exists v : @Integers.bit_int (ras_width sp),
        penv (ras_name sp) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
        rv_read_reg (base + N.of_nat k) rf =
          (if Pos.eqb (ras_width sp) 64%positive then
             @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
           else
             match ras_ext sp with
             | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
             | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
             end)) ->
    forall r0,
      mc_sym_val_agrees penv foracle (fun r1 => rv_read_reg r1 rf) (rv_read_reg 2%N rf)
        (rv_val_read r0 (rv_build_init_val_regs base specs)) (rv_read_reg r0 rf)).
  { clear Hws Hm r.
    intros base specs; revert base; induction specs as [| sp rest IH]; intros base Hge1 Hws' Hm' r0;
      cbn [rv_build_init_val_regs] in *.
    - unfold rv_val_read, rv_empty_val_regs.
      destruct (N.eqb r0 0%N) eqn:Er0.
      + apply N.eqb_eq in Er0; subst r0; unfold rv_read_reg; cbn [N.eqb mc_sym_val_agrees];
          rewrite eval_ce_const, repr_zero_N; reflexivity.
      + destruct (N.eqb r0 2%N) eqn:Er2.
        * apply N.eqb_eq in Er2; subst r0; cbn [mc_sym_val_agrees]; split;
            [unfold mc_frame_cap; lia | rewrite mc_add_ptr_zero; reflexivity].
        * destruct (n_in_list r0 rv_preserved_non_sp_regs); [reflexivity | exact I].
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold rv_valid_arg_spec in Hwsp; apply andb_true_iff in Hwsp as [Hwsp Hnd].
      unfold rv_val_read in *.
      destruct (N.eqb r0 0%N) eqn:Er0.
      { unfold rv_read_reg; rewrite Er0; cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity. }
      destruct (N.eqb r0 base) eqn:Erb.
      + apply N.eqb_eq in Erb; subst base.
        destruct (Hm' 0%nat sp ltac:(cbn; lia) eq_refl) as [v [Hp Hrv]].
        rewrite N.add_0_r in Hrv; rewrite Hrv.
        cbn [mc_sym_val_agrees]; unfold rv_init_arg_expr.
        destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; destruct sp as [nm w ext]; cbn in *; subst w.
          unfold eval_closed_cert_expr; cbn [eval_cert_expr].
          rewrite Hp; cbn [eou_bind lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl.
          rewrite (@Integers.repr_unsigned 64%positive); reflexivity.
        * destruct (ras_ext sp) eqn:Eext.
          -- rewrite (eval_ce_sext penv foracle (ras_width sp) 64%positive (CE_Var (ras_name sp) (ras_width sp)) v).
             ++ reflexivity.
             ++ exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             ++ unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hp; cbn [lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
          -- rewrite (eval_ce_sext penv foracle (ras_width sp) 64%positive (CE_Var (ras_name sp) (ras_width sp)) v).
             ++ reflexivity.
             ++ exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             ++ unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hp; cbn [lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
          -- rewrite (eval_ce_zext penv foracle (ras_width sp) 64%positive (CE_Var (ras_name sp) (ras_width sp)) v).
             ++ reflexivity.
             ++ exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             ++ unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hp; cbn [lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
      + assert (Hargs : forall (k : nat) sp0, (k < List.length rest)%nat -> nth_error rest k = Some sp0 ->
          exists v : @Integers.bit_int (ras_width sp0),
            penv (ras_name sp0) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp0) v)) /\
            rv_read_reg (N.succ base + N.of_nat k) rf =
              (if Pos.eqb (ras_width sp0) 64%positive then
                 @Integers.repr 64%positive (@Integers.unsigned (ras_width sp0) v)
               else
                 match ras_ext sp0 with
                 | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp0) v)
                 | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp0) v)
                 end)).
        { intros k sp0 Hk Hnth.
          destruct (Hm' (S k) sp0 ltac:(cbn; lia) Hnth) as [v [Hp0 Hrv0]].
          exists v; split; [exact Hp0 |].
          replace (N.succ base + N.of_nat k)%N with (base + N.of_nat (S k))%N by lia; exact Hrv0. }
        pose proof (IH (N.succ base) ltac:(lia) Hwrest Hargs r0) as Hrec.
        unfold rv_val_read in Hrec; rewrite Er0 in Hrec; exact Hrec. }
  exact (Hgen 10%N arg_specs ltac:(lia) Hws Hm r).
Qed.

Lemma rv_init_val_regs_wf :
  forall allowed_all arg_specs,
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed_all) ->
    forallb rv_valid_arg_spec arg_specs = true ->
    rv_val_regs_wf allowed_all (rv_build_init_val_regs 10%N arg_specs).
Proof.
  intros allowed_all arg_specs Hall Hws.
  assert (Hgen : forall base specs,
    (forall sp, In sp specs -> In (ras_name sp, ras_width sp) allowed_all) ->
    forallb rv_valid_arg_spec specs = true ->
    rv_val_regs_wf allowed_all (rv_build_init_val_regs base specs)).
  { intros base specs; revert base; induction specs as [| sp rest IH]; intros base Hin Hws' r;
      cbn [rv_build_init_val_regs] in *.
    - unfold rv_val_read, rv_empty_val_regs.
      destruct (N.eqb r 0%N); [apply wf_sym_bv_const |].
      destruct (N.eqb r 2%N); [cbn [mc_sym_val_wf]; unfold mc_frame_cap; lia |].
      destruct (n_in_list r rv_preserved_non_sp_regs); exact I.
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold rv_valid_arg_spec in Hwsp; apply andb_true_iff in Hwsp as [Hwsp Hnd].
      unfold rv_val_read in *.
      destruct (N.eqb r 0%N) eqn:Er0; [apply wf_sym_bv_const |].
      destruct (N.eqb r base) eqn:Erb.
      + unfold rv_init_arg_expr.
        assert (Hvar : wf_sym_expr allowed_all (ras_width sp) (CE_Var (ras_name sp) (ras_width sp))).
        { split; [| split; [| split]].
          - cbn [wt_cert_expr lookup_let_width]; exact Hnd.
          - reflexivity.
          - reflexivity.
          - apply incl_vars_subset_b; intros [nm0 w0] H0; cbn in H0; destruct H0 as [H0 | []].
            inversion H0; subst; apply Hin; left; reflexivity. }
        destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; rewrite Ew64 in Hvar |- *; exact Hvar.
        * assert (Hlt : (ras_width sp <? 64)%positive = true) by (exact (rv_supported_arg_width_lt64 _ Hwsp Ew64)).
          destruct (ras_ext sp); apply wf_sym_cast; assumption.
      + pose proof (IH (N.succ base) (fun s Hs => Hin s (or_intror Hs)) Hwrest r) as Hrec.
        unfold rv_val_read in Hrec; rewrite Er0 in Hrec; exact Hrec. }
  exact (Hgen 10%N arg_specs Hall Hws).
Qed.

Theorem summarize_rv64_dag_wf :
  forall fuel insts arg_specs ret_w d_mc,
    forallb inst_no_word_mulh insts = true ->
    summarize_rv64_dag fuel insts arg_specs ret_w = Some d_mc ->
    wf_cfg_dag (List.map (fun sp => (ras_name sp, ras_width sp)) arg_specs) d_mc = true.
Proof.
  intros fuel insts arg_specs ret_w d_mc Hnmul Hsum.
  unfold summarize_rv64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws;
    cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  set (vrf0 := rv_build_init_val_regs 10%N arg_specs) in *.
  assert (Hsp2 : rv_val_read 2%N vrf0 = MSV_StackPtr 0%Z).
  { unfold rv_val_read, vrf0; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity. }
  eapply summarize_rv64_dag_at_wf with (insts := insts) (sp_off := 0%Z);
    [exact (pt_of_list_first_lookup_rv insts)
    | exact Hrw | exact Hnmul | unfold mc_frame_cap; lia | exact Hsp2
    | | apply mc_sym_stack_wf_empty | exact Hsum].
  apply rv_init_val_regs_wf; [| exact Hws].
  intros sp Hsp; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp].
Qed.

Theorem summarize_rv64_dag_sound :
  forall {Pa : Params} fuel rvc code insts arg_specs ret_w d_mc penv foracle rf0 mstk0,
    decode_rv64_bytes rvc code = inr insts ->
    summarize_rv64_dag fuel insts arg_specs ret_w = Some d_mc ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    rv_rf_matches_args penv arg_specs rf0 ->
    exists rf_end mstk_end,
      rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) /\
      rv_callee_saved_preserved rf0 rf_end /\
      rf_end 1%N = rf0 1%N /\
      eval_cfg_dag penv foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))).
Proof.
  intros Pa fuel rvc code insts arg_specs ret_w d_mc penv foracle rf0 mstk0 Hdec Hsum Hsp0 Hm.
  pose proof (decode_rv64_bytes_no_word_mulh rvc code insts Hdec) as Hnmul.
  unfold summarize_rv64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws;
    cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  set (vrf0 := rv_build_init_val_regs 10%N arg_specs) in *.
  assert (Hsp2 : rv_val_read 2%N vrf0 = MSV_StackPtr 0%Z).
  { unfold rv_val_read, vrf0; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity. }
  eapply summarize_rv64_dag_at_sound with (insts := insts) (sp_off := 0%Z);
    [exact (pt_of_list_first_lookup_rv insts)
    | exact Hrw | exact Hnmul | exact Hsp0 | unfold mc_frame_cap; lia | exact Hsp2
    | exact (rv_init_val_regs_agrees penv foracle arg_specs rf0 Hws Hm)
    | apply mc_sym_stack_agrees_empty | exact Hsum].
Qed.

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
  | option_map _ ?x = _ => destruct x as [op |]; cbn [option_map] in H; [| discriminate H]
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
  - apply N.eqb_eq in Er0; subst r; unfold rv_read_reg; cbn [N.eqb]; rewrite eval_ce_const, repr_zero_N; reflexivity.
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
             raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf))))
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
  destruct (dri_inst dec) as [| rd imm | op is_word rd rs1 imm | op is_word rd rs1 rs2 | sz sgn rd rs1 imm | sz rs1 rs2 imm | cond rs1 rs2 rel | rel |] eqn:Ed;
    cbn [rv_inst_regs_lt32] in Hreg; unfold inst_no_word_mulh in Hnmul; rewrite Ed in Hnmul.
  - inversion Hso; subst out; repeat split; intros; try discriminate; match goal with H : _ = RV_Branch _ _ _ _ |- _ => discriminate H end.
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
      apply eval_sym_alu_reg_sound; [exact Hok_m | apply rv_oracle_srf_eval; [exact Hm | lia] | apply rv_oracle_srf_eval; [exact Hm | lia]].
    + intros ? ? ? ? Hbr; discriminate Hbr.
  - discriminate Hso.
  - discriminate Hso.
  - inversion Hso; subst out; cbn [rso_len rso_rd_write rso_pc_kind rso_br_cond rso_rel_bytes].
    split; [reflexivity | split; [intros ? ? Hw; discriminate Hw |]].
    intros cond' rs1' rs2' rel' Hbr; inversion Hbr; subst.
    split; [reflexivity | split; [reflexivity | eexists; split; [reflexivity |]]].
    apply eval_sym_br_cond_sound; apply rv_oracle_srf_eval; [exact Hm | lia | exact Hm | lia].
  - inversion Hso; subst out; repeat split; intros; try discriminate; match goal with H : _ = RV_Branch _ _ _ _ |- _ => discriminate H end.
  - inversion Hso; subst out; repeat split; intros; try discriminate; match goal with H : _ = RV_Branch _ _ _ _ |- _ => discriminate H end.
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
  assert (Hua128 : @Integers.signed 128%positive (@Integers.repr 128%positive (@Integers.unsigned w a)) = @Integers.unsigned w a)
    by (apply (@Integers.signed_repr 128%positive); lia).
  assert (Hub128 : @Integers.signed 128%positive (@Integers.repr 128%positive (@Integers.unsigned w b)) = @Integers.unsigned w b)
    by (apply (@Integers.signed_repr 128%positive); lia).
  assert (Hsa128 : @Integers.signed 128%positive (@Integers.repr 128%positive (@Integers.signed w a)) = @Integers.signed w a)
    by (apply (@Integers.signed_repr 128%positive); lia).
  assert (Hsb128 : @Integers.signed 128%positive (@Integers.repr 128%positive (@Integers.signed w b)) = @Integers.signed w b)
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
           assert (Habsq : (Z.abs (Z.quot (@Integers.signed w a) (@Integers.signed w b)) <= @Integers.half_modulus w / 2)%Z).
           { rewrite <- Z.quot_abs, Z.quot_div_nonneg by lia.
             assert (Hd1 : (Z.abs (@Integers.signed w a) / Z.abs (@Integers.signed w b) <= Z.abs (@Integers.signed w a) / 2)%Z)
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



