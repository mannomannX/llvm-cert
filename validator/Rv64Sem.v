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

From CertValidator Require Import
  CertFormat
  AlgRules
  CertValidator
  Elf64Spec.

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
    if N.eqb op 1%N then
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
        if N.eqb rd 2%N || N.eqb imm6_raw 0%N then None
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
      else if N.eqb funct3 4%N then
        if N.eqb b12 0%N && N.eqb rs2 0%N then
          if N.eqb rd 1%N then Some RV_Ret else None
        else if N.eqb b12 0%N then
          if N.eqb rd 0%N then None
          else Some (RV_AluReg RAR_Add false rd 0%N rs2)
        else if N.eqb rd 0%N || N.eqb rs2 0%N then None
        else Some (RV_AluReg RAR_Add false rd rd rs2)
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
  else None.

Fixpoint decode_rv64_stream
  (fuel : nat) (rvc_enabled : bool) (code : list N) (cur_off : nat)
  {struct fuel} : string + list decoded_rv_inst :=
  if Nat.eqb cur_off (List.length code) then inr []
  else
    match fuel with
    | O => inl "RV64 decoder fuel exhausted"
    | S fuel' =>
        match read_u16_le code cur_off with
        | None => inl "truncated RV64 instruction stream"
        | Some hw =>
            if negb (N.eqb (N.modulo hw 4%N) 3%N) then
              if negb rvc_enabled then inl "16-bit RVC instruction encountered with RVC disabled"
              else
                match decode_rvc_hw hw with
                | None => inl "unsupported 16-bit RVC instruction"
                | Some inst =>
                    match decode_rv64_stream fuel' rvc_enabled code (cur_off + 2) with
                    | inl err => inl err
                    | inr rest => inr (mk_decoded_rv (N.of_nat cur_off) 2%N inst :: rest)
                    end
                end
            else
              match read_u32_le code cur_off with
              | None => inl "truncated 32-bit RV64 instruction"
              | Some w =>
                  match decode_rv32_word w with
                  | None => inl "unsupported 32-bit RV64 instruction"
                  | Some inst =>
                      match decode_rv64_stream fuel' rvc_enabled code (cur_off + 4) with
                      | inl err => inl err
                      | inr rest => inr (mk_decoded_rv (N.of_nat cur_off) 4%N inst :: rest)
                      end
                  end
              end
        end
    end.

Definition decode_rv64_bytes (rvc_enabled : bool) (code : list N)
  : string + list decoded_rv_inst :=
  let len := List.length code in
  if Nat.eqb len 0 || negb (Nat.eqb (Nat.modulo len 2) 0) then
    inl "RV64 function byte length must be positive and even"
  else if negb rvc_enabled && negb (Nat.eqb (Nat.modulo len 4) 0) then
    inl "non-RVC RV64 function length must be a multiple of 4"
  else
    decode_rv64_stream (Nat.div len 2 + 1) rvc_enabled code 0.

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

Fixpoint rv_exec
  (fuel : nat) (insts : list decoded_rv_inst) (pc : N) (rf : rv_regfile)
  {struct fuel} : option rv_regfile :=
  match fuel with
  | O => None
  | S fuel' =>
      match lookup_rv_inst insts pc with
      | None => None
      | Some dec =>
          let next_pc := (pc + dri_len dec)%N in
          match dri_inst dec with
          | RV_Nop => rv_exec fuel' insts next_pc rf
          | RV_Lui rd imm =>
              rv_exec fuel' insts next_pc (rv_write_reg rd (@Integers.repr 64 imm) rf)
          | RV_AluImm op is_word rd rs1 imm =>
              let v := rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm in
              rv_exec fuel' insts next_pc (rv_write_reg rd v rf)
          | RV_AluReg op is_word rd rs1 rs2 =>
              let v := rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) in
              rv_exec fuel' insts next_pc (rv_write_reg rd v rf)
          | RV_Jal0 rel =>
              match add_rel_off pc rel with
              | None => None
              | Some tgt_pc => rv_exec fuel' insts tgt_pc rf
              end
          | RV_Branch cond rs1 rs2 rel =>
              if rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) then
                match add_rel_off pc rel with
                | None => None
                | Some tgt_pc => rv_exec fuel' insts tgt_pc rf
                end
              else
                rv_exec fuel' insts next_pc rf
          | RV_Ret => Some rf
          end
      end
  end.

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

Fixpoint summarize_rv64_dag_at
  (fuel : nat) (insts : list decoded_rv_inst) (visited : list N)
  (pc : N) (srf : rv_sym_regs) (def : rv_def_mask) (ret_w : positive)
  {struct fuel} : option cfg_dag :=
  if n_in_list pc visited then None
  else
    match fuel with
    | O => None
    | S fuel' =>
        match lookup_rv_inst insts pc with
        | None => None
        | Some dec =>
            let next_pc := (pc + dri_len dec)%N in
            let visited' := pc :: visited in
            match dri_inst dec with
            | RV_Nop =>
                summarize_rv64_dag_at fuel' insts visited' next_pc srf def ret_w
            | RV_Lui rd imm =>
                if rv_is_callee_saved rd then None
                else
                  let srf' := rv_sym_write rd (ce_bv_z 64%positive imm) srf in
                  let def' := rv_def_write rd def in
                  summarize_rv64_dag_at fuel' insts visited' next_pc srf' def' ret_w
            | RV_AluImm op is_word rd rs1 imm =>
                if rv_is_callee_saved rd || negb (rv_def_read rs1 def) then None
                else
                  let e := sym_alu_imm op is_word (rv_sym_read rs1 srf) imm in
                  let srf' := rv_sym_write rd e srf in
                  let def' := rv_def_write rd def in
                  summarize_rv64_dag_at fuel' insts visited' next_pc srf' def' ret_w
            | RV_AluReg op is_word rd rs1 rs2 =>
                if rv_is_callee_saved rd ||
                   negb (rv_def_read rs1 def) ||
                   negb (rv_def_read rs2 def)
                then None
                else
                  let e := sym_alu_reg op is_word (rv_sym_read rs1 srf) (rv_sym_read rs2 srf) in
                  let srf' := rv_sym_write rd e srf in
                  let def' := rv_def_write rd def in
                  summarize_rv64_dag_at fuel' insts visited' next_pc srf' def' ret_w
            | RV_Jal0 rel =>
                match add_rel_off pc rel with
                | None => None
                | Some tgt_pc =>
                    summarize_rv64_dag_at fuel' insts visited' tgt_pc srf def ret_w
                end
            | RV_Branch cond rs1 rs2 rel =>
                if negb (rv_def_read rs1 def) || negb (rv_def_read rs2 def) then None
                else
                  match add_rel_off pc rel with
                  | None => None
                  | Some tgt_pc =>
                      let c_e := sym_br_cond cond (rv_sym_read rs1 srf) (rv_sym_read rs2 srf) in
                      match summarize_rv64_dag_at fuel' insts visited' tgt_pc srf def ret_w,
                            summarize_rv64_dag_at fuel' insts visited' next_pc srf def ret_w
                      with
                      | Some d_t, Some d_f => Some (CD_Branch c_e d_t d_f)
                      | _, _ => None
                      end
                  end
            | RV_Ret =>
                if negb (rv_def_read 10%N def) then None
                else Some (CD_RetScalar ret_w (rv_trunc_ret_expr ret_w (rv_sym_read 10%N srf)))
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
    let '(srf0, def0) := rv_build_init_state 10%N arg_specs in
    summarize_rv64_dag_at fuel insts [] 0%N srf0 def0 ret_w.

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

Definition env_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (srf : rv_sym_regs) (def : rv_def_mask) (rf : rv_regfile) : Prop :=
  forall r,
    rv_def_read r def = true ->
    eval_closed_cert_expr penv foracle (rv_sym_read r srf) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg r rf))).

Lemma env_agrees_zero :
  forall {Pa : Params} (penv : param_env Pa) foracle srf,
    eval_closed_cert_expr penv foracle (rv_sym_read 0%N srf) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg 0%N (fun _ => @Integers.zero 64%positive)))).
Proof.
  intros; unfold rv_sym_read, rv_read_reg; cbn [N.eqb]; rewrite eval_ce_const, repr_zero_N; reflexivity.
Qed.

Lemma env_agrees_write :
  forall {Pa : Params} (penv : param_env Pa) foracle srf def rf rd e v,
    env_agrees penv foracle srf def rf ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v)) ->
    env_agrees penv foracle (rv_sym_write rd e srf) (rv_def_write rd def) (rv_write_reg rd v rf).
Proof.
  intros Pa penv foracle srf def rf rd e v Hag He r Hr.
  unfold rv_sym_read, rv_sym_write, rv_def_read, rv_def_write, rv_read_reg, rv_write_reg in Hr |- *.
  destruct (N.eqb r 0%N) eqn:Er0.
  - rewrite eval_ce_const, repr_zero_N; reflexivity.
  - destruct (N.eqb rd 0%N) eqn:Erd0.
    + pose proof (Hag r) as Hr'; unfold rv_def_read, rv_sym_read, rv_read_reg in Hr'; rewrite Er0 in Hr'; exact (Hr' Hr).
    + destruct (N.eqb r rd) eqn:Erd.
      * exact He.
      * pose proof (Hag r) as Hr'; unfold rv_def_read, rv_sym_read, rv_read_reg in Hr'; rewrite Er0 in Hr'; exact (Hr' Hr).
Qed.

Definition inst_no_word_mulh (d : decoded_rv_inst) : bool :=
  match dri_inst d with
  | RV_AluReg RAR_Mulh true _ _ _
  | RV_AluReg RAR_Mulhsu true _ _ _
  | RV_AluReg RAR_Mulhu true _ _ _ => false
  | _ => true
  end.

Lemma rv_callee_saved_preserved_refl : forall rf,
  rv_callee_saved_preserved rf rf.
Proof.
  intros rf r _; reflexivity.
Qed.

Lemma rv_callee_saved_preserved_step : forall rf rd v,
  rv_is_callee_saved rd = false ->
  rv_callee_saved_preserved rf (rv_write_reg rd v rf).
Proof.
  intros rf rd v Hcs r Hr.
  unfold rv_write_reg.
  destruct (N.eqb rd 0%N); [reflexivity |].
  destruct (N.eqb r rd) eqn:E; [| reflexivity].
  apply N.eqb_eq in E; subst rd; congruence.
Qed.

Lemma rv_callee_saved_preserved_trans : forall rf0 rf1 rf2,
  rv_callee_saved_preserved rf0 rf1 ->
  rv_callee_saved_preserved rf1 rf2 ->
  rv_callee_saved_preserved rf0 rf2.
Proof.
  intros rf0 rf1 rf2 H1 H2 r Hr; rewrite (H2 r Hr); exact (H1 r Hr).
Qed.

Theorem summarize_rv64_dag_at_sound :
  forall {Pa : Params} fuel insts visited pc srf def ret_w d_mc penv foracle rf,
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    env_agrees penv foracle srf def rf ->
    summarize_rv64_dag_at fuel insts visited pc srf def ret_w = Some d_mc ->
    exists rf_end,
      rv_exec fuel insts pc rf = Some rf_end /\
      rv_callee_saved_preserved rf rf_end /\
      eval_cfg_dag penv foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))).
Proof.
  intros Pa fuel; induction fuel as [| fuel' IH];
    intros insts visited pc srf def ret_w d_mc penv foracle rf Hrw Hnmul Hag Hsum;
    cbn [summarize_rv64_dag_at rv_exec] in *.
  - destruct (n_in_list pc visited); discriminate Hsum.
  - destruct (n_in_list pc visited); [discriminate Hsum |].
    destruct (lookup_rv_inst insts pc) as [dec |] eqn:Elook; [| discriminate Hsum].
    assert (Hdec_mulh : inst_no_word_mulh dec = true).
    { clear -Elook Hnmul. induction insts as [| d rest IHl]; cbn in *; [discriminate |].
      apply andb_true_iff in Hnmul as [Hd Hr].
      destruct (N.eqb (dri_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
    destruct (dri_inst dec) as
      [| rd imm
       | op is_word rd rs1 imm
       | op is_word rd rs1 rs2
       | cond rs1 rs2 rel
       | rel
       | ] eqn:Ed.
    + (* RV_Nop *)
      exact (IH insts (pc :: visited) (pc + dri_len dec)%N srf def ret_w d_mc penv foracle rf Hrw Hnmul Hag Hsum).
    + (* RV_Lui *)
      destruct (rv_is_callee_saved rd) eqn:Ecs; [discriminate Hsum |].
      set (rf' := rv_write_reg rd (@Integers.repr 64%positive imm) rf).
      assert (Hag' : env_agrees penv foracle (rv_sym_write rd (ce_bv_z 64%positive imm) srf) (rv_def_write rd def) rf')
        by (apply env_agrees_write; [exact Hag | apply eval_ce_bv_z]).
      destruct (IH insts (pc :: visited) (pc + dri_len dec)%N _ _ ret_w d_mc penv foracle rf' Hrw Hnmul Hag' Hsum)
        as [rf_end [Hex [Hcs Hev]]].
      exists rf_end; repeat split; try assumption.
      eapply rv_callee_saved_preserved_trans; [apply rv_callee_saved_preserved_step; exact Ecs | exact Hcs].
    + (* RV_AluImm *)
      destruct (rv_is_callee_saved rd) eqn:Ecs; [discriminate Hsum |].
      destruct (rv_def_read rs1 def) eqn:Edef1; cbn [negb orb] in Hsum; [| discriminate Hsum].
      pose proof (Hag rs1 Edef1) as Hva.
      set (v := rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm).
      set (e := sym_alu_imm op is_word (rv_sym_read rs1 srf) imm) in *.
      assert (He : eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v)))
        by (apply eval_sym_alu_imm_sound; exact Hva).
      destruct (IH insts (pc :: visited) (pc + dri_len dec)%N _ _ ret_w d_mc penv foracle (rv_write_reg rd v rf)
                  Hrw Hnmul (env_agrees_write _ _ _ _ _ _ _ _ Hag He) Hsum)
        as [rf_end [Hex [Hcs Hev]]].
      exists rf_end; repeat split; try assumption.
      eapply rv_callee_saved_preserved_trans; [apply rv_callee_saved_preserved_step; exact Ecs | exact Hcs].
    + (* RV_AluReg *)
      destruct (rv_is_callee_saved rd) eqn:Ecs; [discriminate Hsum |].
      destruct (rv_def_read rs1 def) eqn:Edef1; cbn [negb orb] in Hsum; [| discriminate Hsum].
      destruct (rv_def_read rs2 def) eqn:Edef2; cbn [negb orb] in Hsum; [| discriminate Hsum].
      assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
      { destruct is_word; [| left; reflexivity].
        right; unfold inst_no_word_mulh in Hdec_mulh; rewrite Ed in Hdec_mulh.
        destruct op; repeat split; intro C; discriminate C || discriminate Hdec_mulh. }
      set (v := rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)).
      set (e := sym_alu_reg op is_word (rv_sym_read rs1 srf) (rv_sym_read rs2 srf)) in *.
      assert (He : eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v)))
        by (apply eval_sym_alu_reg_sound; [exact Hok_m | exact (Hag rs1 Edef1) | exact (Hag rs2 Edef2)]).
      destruct (IH insts (pc :: visited) (pc + dri_len dec)%N _ _ ret_w d_mc penv foracle (rv_write_reg rd v rf)
                  Hrw Hnmul (env_agrees_write _ _ _ _ _ _ _ _ Hag He) Hsum)
        as [rf_end [Hex [Hcs Hev]]].
      exists rf_end; repeat split; try assumption.
      eapply rv_callee_saved_preserved_trans; [apply rv_callee_saved_preserved_step; exact Ecs | exact Hcs].
    + (* RV_Branch *)
      destruct (rv_def_read rs1 def) eqn:Edef1; [| discriminate Hsum].
      destruct (rv_def_read rs2 def) eqn:Edef2; cbn [negb orb] in Hsum; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' insts (pc :: visited) tgt_pc srf def ret_w) as [dt |] eqn:Edt;
        [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' insts (pc :: visited) (pc + dri_len dec)%N srf def ret_w) as [df |] eqn:Edf;
        [| discriminate Hsum].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (eval_sym_br_cond_sound penv foracle cond _ _ _ _ (Hag rs1 Edef1) (Hag rs2 Edef2)) as Hbr.
      cbn [eval_cfg_dag]; rewrite Hbr.
      destruct (rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH insts (pc :: visited) tgt_pc srf def ret_w dt penv foracle rf Hrw Hnmul Hag Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH insts (pc :: visited) (pc + dri_len dec)%N srf def ret_w df penv foracle rf Hrw Hnmul Hag Edf).
    + (* RV_Jal0 *)
      destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hsum].
      exact (IH insts (pc :: visited) tgt_pc srf def ret_w d_mc penv foracle rf Hrw Hnmul Hag Hsum).
    + (* RV_Ret *)
      destruct (rv_def_read 10%N def) eqn:Edef10; cbn [negb] in Hsum; [| discriminate Hsum].
      inversion Hsum; subst d_mc; clear Hsum.
      exists rf; split; [reflexivity | split; [apply rv_callee_saved_preserved_refl |]].
      cbn [eval_cfg_dag]; unfold rv_trunc_ret_expr, rv_trunc_ret_val.
      pose proof (Hag 10%N Edef10) as Ha10.
      destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
      * apply Pos.eqb_eq in Ew64; subst ret_w.
        rewrite Ha10, (@Integers.repr_unsigned 64%positive); reflexivity.
      * assert (Hlt64 : (ret_w <? 64)%positive = true) by (exact (rv_supported_arg_width_lt64 _ Hrw Ew64)).
        rewrite (eval_ce_trunc penv foracle 64%positive ret_w (rv_sym_read 10%N srf) _ Hlt64 Ha10); reflexivity.
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

Lemma wf_sym_regs_write : forall allowed srf def rd e,
  wf_sym_regs allowed srf def ->
  wf_sym_expr allowed 64%positive e ->
  wf_sym_regs allowed (rv_sym_write rd e srf) (rv_def_write rd def).
Proof.
  intros allowed srf def rd e Hw He r Hr.
  unfold rv_sym_read, rv_sym_write, rv_def_read, rv_def_write in Hr |- *.
  destruct (N.eqb r 0%N) eqn:Er0; [apply wf_sym_bv_const |].
  destruct (N.eqb rd 0%N) eqn:Erd0.
  { pose proof (Hw r) as Hr'; unfold rv_def_read, rv_sym_read in Hr'; rewrite Er0 in Hr'; exact (Hr' Hr). }
  destruct (N.eqb r rd); [exact He |].
  pose proof (Hw r) as Hr'; unfold rv_def_read, rv_sym_read in Hr'; rewrite Er0 in Hr'; exact (Hr' Hr).
Qed.

Theorem summarize_rv64_dag_at_wf :
  forall fuel insts visited pc allowed srf def ret_w d_mc,
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    wf_sym_regs allowed srf def ->
    summarize_rv64_dag_at fuel insts visited pc srf def ret_w = Some d_mc ->
    wf_cfg_dag allowed d_mc = true.
Proof.
  induction fuel as [| fuel' IH];
    intros insts visited pc allowed srf def ret_w d_mc Hrw Hnmul Hwf Hsum;
    cbn [summarize_rv64_dag_at] in Hsum.
  - destruct (n_in_list pc visited); discriminate Hsum.
  - destruct (n_in_list pc visited); [discriminate Hsum |].
    destruct (lookup_rv_inst insts pc) as [dec |] eqn:Elook; [| discriminate Hsum].
    assert (Hdec_mulh : inst_no_word_mulh dec = true).
    { clear -Elook Hnmul. induction insts as [| d rest IHl]; cbn in *; [discriminate |].
      apply andb_true_iff in Hnmul as [Hd Hr].
      destruct (N.eqb (dri_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
    destruct (dri_inst dec) as
      [| rd imm
       | op is_word rd rs1 imm
       | op is_word rd rs1 rs2
       | cond rs1 rs2 rel
       | rel
       | ] eqn:Ed.
    + exact (IH insts (pc :: visited) (pc + dri_len dec)%N allowed srf def ret_w d_mc Hrw Hnmul Hwf Hsum).
    + destruct (rv_is_callee_saved rd); [discriminate Hsum |].
      eapply IH; [exact Hrw | exact Hnmul | apply wf_sym_regs_write; [exact Hwf | apply wf_sym_bv_z] | exact Hsum].
    + destruct (rv_is_callee_saved rd); [discriminate Hsum |].
      destruct (rv_def_read rs1 def) eqn:Edef1; cbn [negb orb] in Hsum; [| discriminate Hsum].
      eapply IH; [exact Hrw | exact Hnmul | apply wf_sym_regs_write; [exact Hwf | apply wf_sym_alu_imm; exact (Hwf rs1 Edef1)] | exact Hsum].
    + destruct (rv_is_callee_saved rd); [discriminate Hsum |].
      destruct (rv_def_read rs1 def) eqn:Edef1; cbn [negb orb] in Hsum; [| discriminate Hsum].
      destruct (rv_def_read rs2 def) eqn:Edef2; cbn [negb orb] in Hsum; [| discriminate Hsum].
      assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
      { destruct is_word; [| left; reflexivity].
        right; unfold inst_no_word_mulh in Hdec_mulh; rewrite Ed in Hdec_mulh.
        destruct op; repeat split; intro C; discriminate C || discriminate Hdec_mulh. }
      eapply IH; [exact Hrw | exact Hnmul | apply wf_sym_regs_write; [exact Hwf | apply wf_sym_alu_reg; [exact Hok_m | exact (Hwf rs1 Edef1) | exact (Hwf rs2 Edef2)]] | exact Hsum].
    + destruct (rv_def_read rs1 def) eqn:Edef1; [| discriminate Hsum].
      destruct (rv_def_read rs2 def) eqn:Edef2; cbn [negb orb] in Hsum; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' insts (pc :: visited) tgt_pc srf def ret_w) as [dt |] eqn:Edt; [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' insts (pc :: visited) (pc + dri_len dec)%N srf def ret_w) as [df |] eqn:Edf; [| discriminate Hsum].
      inversion Hsum; subst d_mc; clear Hsum.
      assert (Hbc : wf_sym_expr allowed 1%positive (sym_br_cond cond (rv_sym_read rs1 srf) (rv_sym_read rs2 srf)))
        by (destruct cond; (apply wf_sym_icmp; [exact (Hwf rs1 Edef1) | exact (Hwf rs2 Edef2)])).
      destruct Hbc as (Htc & Hwc & Hlfc & Hvc).
      cbn [wf_cfg_dag]; rewrite Htc, Hwc, Hlfc, Hvc; cbn [Pos.eqb andb].
      rewrite (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hwf Edt), (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hwf Edf); reflexivity.
    + destruct (add_rel_off pc rel); [| discriminate Hsum].
      exact (IH insts (pc :: visited) _ allowed srf def ret_w d_mc Hrw Hnmul Hwf Hsum).
    + destruct (rv_def_read 10%N def) eqn:Edef10; cbn [negb] in Hsum; [| discriminate Hsum].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf 10%N Edef10) as Ha10.
      assert (Hrte : wf_sym_expr allowed ret_w (rv_trunc_ret_expr ret_w (rv_sym_read 10%N srf))).
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

Lemma decode_rv64_stream_no_word_mulh : forall fuel rvc code cur_off insts,
  decode_rv64_stream fuel rvc code cur_off = inr insts ->
  forallb inst_no_word_mulh insts = true.
Proof.
  induction fuel as [| fuel' IH]; intros rvc code cur_off insts H; cbn [decode_rv64_stream] in H.
  - destruct (Nat.eqb cur_off (List.length code)); [inversion H; reflexivity | discriminate H].
  - destruct (Nat.eqb cur_off (List.length code)); [inversion H; reflexivity |].
    destruct (read_u16_le code cur_off) as [hw |]; [| discriminate H].
    destruct (negb (N.eqb (N.modulo hw 4%N) 3%N)).
    + destruct (negb rvc); [discriminate H |].
      destruct (decode_rvc_hw hw) as [inst |] eqn:Edec; [| discriminate H].
      destruct (decode_rv64_stream fuel' rvc code (cur_off + 2)) as [| rest] eqn:Erec; [discriminate H |].
      inversion H; subst insts; clear H.
      cbn [forallb]; rewrite (IH _ _ _ _ Erec), andb_true_r.
      pose proof (decode_rvc_hw_no_word_mulh hw inst Edec) as Hnm.
      unfold inst_no_word_mulh; cbn [dri_inst].
      destruct inst as [| | | op [|] | | |]; try reflexivity; destruct op; try reflexivity; contradiction.
    + destruct (read_u32_le code cur_off) as [w |]; [| discriminate H].
      destruct (decode_rv32_word w) as [inst |] eqn:Edec; [| discriminate H].
      destruct (decode_rv64_stream fuel' rvc code (cur_off + 4)) as [| rest] eqn:Erec; [discriminate H |].
      inversion H; subst insts; clear H.
      cbn [forallb]; rewrite (IH _ _ _ _ Erec), andb_true_r.
      pose proof (decode_rv32_word_no_word_mulh w inst Edec) as Hnm.
      unfold inst_no_word_mulh; cbn [dri_inst].
      destruct inst as [| | | op [|] | | |]; try reflexivity; destruct op; try reflexivity; contradiction.
Qed.

Lemma decode_rv64_bytes_no_word_mulh : forall rvc code insts,
  decode_rv64_bytes rvc code = inr insts ->
  forallb inst_no_word_mulh insts = true.
Proof.
  intros rvc code insts H; unfold decode_rv64_bytes in H.
  destruct (Nat.eqb (List.length code) 0 || negb (Nat.eqb (Nat.modulo (List.length code) 2) 0)); [discriminate H |].
  destruct (negb rvc && negb (Nat.eqb (Nat.modulo (List.length code) 4) 0)); [discriminate H |].
  eapply decode_rv64_stream_no_word_mulh; exact H.
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

Lemma rv_init_state_agrees :
  forall {Pa : Params} (penv : param_env Pa) foracle arg_specs rf,
    forallb rv_valid_arg_spec arg_specs = true ->
    rv_rf_matches_args penv arg_specs rf ->
    env_agrees penv foracle
      (fst (rv_build_init_state 10%N arg_specs))
      (snd (rv_build_init_state 10%N arg_specs)) rf.
Proof.
  intros Pa penv foracle arg_specs rf Hws Hm r Hr.
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
      rv_def_read r0 (snd (rv_build_init_state base specs)) = true ->
      eval_closed_cert_expr penv foracle (rv_sym_read r0 (fst (rv_build_init_state base specs))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg r0 rf)))).
  { clear Hws Hm r Hr.
    intros base specs; revert base; induction specs as [| sp rest IH]; intros base Hge1 Hws' Hm' r0 Hr0;
      cbn [rv_build_init_state fst snd] in *.
    - unfold rv_def_read, rv_sym_read, rv_read_reg in *.
      destruct (N.eqb r0 0%N); [rewrite eval_ce_const, repr_zero_N; reflexivity | discriminate Hr0].
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold rv_valid_arg_spec in Hwsp; apply andb_true_iff in Hwsp as [Hwsp Hnd].
      destruct (rv_build_init_state (N.succ base) rest) as [srf' def'] eqn:Erec.
      cbn [fst snd] in *.
      unfold rv_def_read, rv_sym_read in *.
      destruct (N.eqb r0 0%N) eqn:Er0.
      { rewrite eval_ce_const, repr_zero_N; unfold rv_read_reg; rewrite Er0; reflexivity. }
      destruct (N.eqb r0 base) eqn:Erb.
      + apply N.eqb_eq in Erb; subst base.
        destruct (Hm' 0%nat sp ltac:(cbn; lia) eq_refl) as [v [Hp Hrv]].
        rewrite N.add_0_r in Hrv; rewrite Hrv.
        unfold rv_init_arg_expr.
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
        rewrite Erec in Hrec; cbn [fst snd] in Hrec; rewrite Er0 in Hrec.
        cbn [orb] in Hr0; exact (Hrec Hr0). }
  exact (Hgen 10%N arg_specs ltac:(lia) Hws Hm r Hr).
Qed.

Lemma rv_init_state_wf :
  forall allowed_all arg_specs,
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed_all) ->
    forallb rv_valid_arg_spec arg_specs = true ->
    wf_sym_regs allowed_all
      (fst (rv_build_init_state 10%N arg_specs))
      (snd (rv_build_init_state 10%N arg_specs)).
Proof.
  intros allowed_all arg_specs Hall Hws.
  assert (Hgen : forall base specs,
    (forall sp, In sp specs -> In (ras_name sp, ras_width sp) allowed_all) ->
    forallb rv_valid_arg_spec specs = true ->
    wf_sym_regs allowed_all (fst (rv_build_init_state base specs)) (snd (rv_build_init_state base specs))).
  { intros base specs; revert base; induction specs as [| sp rest IH]; intros base Hin Hws' r Hr;
      cbn [rv_build_init_state fst snd] in *.
    - unfold rv_def_read, rv_sym_read in *; destruct (N.eqb r 0%N); [apply wf_sym_bv_const | discriminate Hr].
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold rv_valid_arg_spec in Hwsp; apply andb_true_iff in Hwsp as [Hwsp Hnd].
      destruct (rv_build_init_state (N.succ base) rest) as [srf' def'] eqn:Erec; cbn [fst snd] in *.
      unfold rv_def_read, rv_sym_read in *.
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
        rewrite Erec in Hrec; cbn [fst snd] in Hrec; unfold rv_def_read, rv_sym_read in Hrec; rewrite Er0 in Hrec.
        cbn [orb] in Hr; exact (Hrec Hr). }
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
  destruct (rv_build_init_state 10%N arg_specs) as [srf0 def0] eqn:Einit.
  eapply summarize_rv64_dag_at_wf; [exact Hrw | exact Hnmul | | exact Hsum].
  replace srf0 with (fst (rv_build_init_state 10%N arg_specs)) by (rewrite Einit; reflexivity).
  replace def0 with (snd (rv_build_init_state 10%N arg_specs)) by (rewrite Einit; reflexivity).
  apply rv_init_state_wf; [| exact Hws].
  intros sp Hsp; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp].
Qed.

Theorem summarize_rv64_dag_sound :
  forall {Pa : Params} fuel rvc code insts arg_specs ret_w d_mc penv foracle rf0,
    decode_rv64_bytes rvc code = inr insts ->
    summarize_rv64_dag fuel insts arg_specs ret_w = Some d_mc ->
    rv_rf_matches_args penv arg_specs rf0 ->
    exists rf_end,
      rv_exec fuel insts 0%N rf0 = Some rf_end /\
      rv_callee_saved_preserved rf0 rf_end /\
      eval_cfg_dag penv foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))).
Proof.
  intros Pa fuel rvc code insts arg_specs ret_w d_mc penv foracle rf0 Hdec Hsum Hm.
  pose proof (decode_rv64_bytes_no_word_mulh rvc code insts Hdec) as Hnmul.
  unfold summarize_rv64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws;
    cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_build_init_state 10%N arg_specs) as [srf0 def0] eqn:Einit.
  eapply summarize_rv64_dag_at_sound; [exact Hrw | exact Hnmul | | exact Hsum].
  replace srf0 with (fst (rv_build_init_state 10%N arg_specs)) by (rewrite Einit; reflexivity).
  replace def0 with (snd (rv_build_init_state 10%N arg_specs)) by (rewrite Einit; reflexivity).
  exact (rv_init_state_agrees penv foracle arg_specs rf0 Hws Hm).
Qed.

