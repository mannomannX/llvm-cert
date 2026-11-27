(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Canonical RV64IM+RVC Instruction AST & Total Decoder ([CertValidator.Rv64Decode])

    Purpose:
      Defines the canonical RV64IM+RVC instruction AST ([rv_inst], [decoded_rv_inst]) and the
      total little-endian mixed 16/32-bit byte-stream decoder ([decode_rv64_bytes]).

    Trust Contract & Fail-Closed Boundary:
      [decode_rv64_bytes] fails closed ([inl err]) on empty, odd-length, or (when
      [rvc_enabled = false]) non-4-byte-aligned streams, and on any unsupported or
      unrecognized 16-bit or 32-bit opcode. Extracted to OCaml via [Extract.v].

    Assumptions:
      [Stdlib], [CertValidator.common.Diag], and [CertValidator.{Elf64Spec,McFrameMem,
      McIsaCommon}]; zero Vellvm dependencies and zero custom axioms.

    Section Outline:
      1. Canonical RV64IM+RVC instruction AST; 2. Total mixed 16/32-bit decoder
      ([decode_rvc_hw], [decode_rv32_word], [decode_rv64_bytes]). *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
  List
  Bool
  Lia.
Import ListNotations.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  Elf64Spec
  McFrameMem
  McIsaCommon.

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
      | O => inl (diag "mc-decode" ("RV64 decoder fuel exhausted at offset " ++ diag_N_hex (N.of_nat cur_off)))
      | S fuel' =>
          match take_u16_le cur with
          | None =>
              inl (diag "mc-decode"
                ("truncated RV64 instruction stream at offset " ++ diag_N_hex (N.of_nat cur_off)))
          | Some (hw, rest2) =>
              if negb (N.eqb (N.modulo hw 4%N) 3%N) then
                if negb rvc_enabled then
                  inl (diag "mc-decode"
                    ("16-bit RVC instruction " ++ diag_N_hex hw ++ " at offset " ++
                     diag_N_hex (N.of_nat cur_off) ++ " with RVC disabled"))
                else
                  match decode_rvc_hw hw with
                  | None =>
                      inl (diag "mc-decode"
                        ("unsupported 16-bit RVC instruction " ++ diag_N_hex hw ++
                         " at offset " ++ diag_N_hex (N.of_nat cur_off)))
                  | Some inst =>
                      let acc' := mk_decoded_rv (N.of_nat cur_off) 2%N inst :: acc in
                      decode_rv64_stream_acc fuel' rvc_enabled rest2 (cur_off + 2) acc'
                  end
              else
                match take_u32_le cur with
                | None =>
                    inl (diag "mc-decode"
                      ("truncated 32-bit RV64 instruction at offset " ++ diag_N_hex (N.of_nat cur_off)))
                | Some (w, rest4) =>
                    match decode_rv32_word w with
                    | None =>
                        inl (diag "mc-decode"
                          ("unsupported 32-bit RV64 instruction " ++ diag_N_hex w ++
                           " at offset " ++ diag_N_hex (N.of_nat cur_off)))
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
    inl (diag "mc-decode" ("RV64 function byte length " ++ diag_nat_dec len ++ " must be positive and even"))
  else if negb rvc_enabled && negb (Nat.eqb (Nat.modulo len 4) 0) then
    inl (diag "mc-decode" ("non-RVC RV64 function byte length " ++ diag_nat_dec len ++ " must be a multiple of 4"))
  else
    decode_rv64_stream_acc (Nat.div len 2 + 1) rvc_enabled code 0 [].

