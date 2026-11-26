(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified [AArch64] ([A64]) Core Decoder, Operational Semantics & Symbolic DAG Lowering

    Implements for Milestone M2 of Phase [8.3a] ([CertValidator.A64CoreSem]):
    1. Canonical [A64] core bare-metal AST (arithmetic, shift/extend, logical
       immediate & shifted, move-wide, bitfield, extract, multiply, div/var-shift,
       NZCV conditional compare/select, branches, hints, [ret x30]) and total
       32-bit little-endian decoder ([decode_a64_bytes]).
    2. Concrete ARMv8-A-aligned operational semantics ([a64_exec]) over
       [@Integers.bit_int 64], [@Integers.bit_int 32], and 4-bit [NZCV] flags
       with [x19..x30] callee-saved and [SP] preservation.
    3. Verified AAPCS64-sound symbolic execution ([summarize_a64_dag]) modeling
       unspecified upper bits on [< 64]-bit arguments via fresh [__a64_hi_*]
       symbolic variables plus a 32-bit zero-extension shortcut ([a64_sym_trunc32])
       and exact [SUBS] [NZCV] identities ([Z = eq], [C = uge], [N <> V = slt]).
    4. Machine-checked zero-axiom WF ([summarize_a64_dag_wf]) and semantic
       equivalence ([summarize_a64_dag_sound], zero custom axioms, zero
       [eq_rect_eq]). *)

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
  McFrameMem
  Rv64Sem.

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

(** ** 1. Canonical [A64] Core Instruction AST *)

Variant a64_shift : Set :=
| ASH_Lsl
| ASH_Lsr
| ASH_Asr
| ASH_Ror.

Variant a64_extend : Set :=
| AEX_Uxtb
| AEX_Uxth
| AEX_Uxtw
| AEX_Uxtx
| AEX_Sxtb
| AEX_Sxth
| AEX_Sxtw
| AEX_Sxtx.

Variant a64_logic_op : Set :=
| ALO_And
| ALO_Orr
| ALO_Eor.

Variant a64_movwide : Set :=
| AMW_Movn
| AMW_Movz
| AMW_Movk.

Variant a64_bf_kind : Set :=
| ABF_Sbfm
| ABF_Bfm
| ABF_Ubfm.

Variant a64_dp2_op : Set :=
| ADP2_Udiv
| ADP2_Sdiv
| ADP2_Lslv
| ADP2_Lsrv
| ADP2_Asrv
| ADP2_Rorv.

Variant a64_csel_kind : Set :=
| ACS_Csel
| ACS_Csinc
| ACS_Csinv
| ACS_Csneg.

Variant a64_cond : Set :=
| AC_Eq
| AC_Ne
| AC_Cs
| AC_Cc
| AC_Mi
| AC_Pl
| AC_Vs
| AC_Vc
| AC_Hi
| AC_Ls
| AC_Ge
| AC_Lt
| AC_Gt
| AC_Le
| AC_Al
| AC_Nv.

Variant a64_addr_mode : Set :=
| AAM_SignedOffset
| AAM_PreIndex
| AAM_PostIndex.

Variant a64_inst : Set :=
| A64_Nop
| A64_AddSubImm (sf is_sub set_flags : bool) (rd rn imm : N)
| A64_AddSubShift (sf is_sub set_flags : bool) (rd rn rm : N) (sh : a64_shift) (amt : N)
| A64_AddSubExt (sf is_sub set_flags : bool) (rd rn rm : N) (ext : a64_extend) (amt : N)
| A64_LogicalImm (sf : bool) (op : a64_logic_op) (set_flags : bool) (rd rn mask : N)
| A64_LogicalShift (sf : bool) (op : a64_logic_op) (inv_rm set_flags : bool)
                   (rd rn rm : N) (sh : a64_shift) (amt : N)
| A64_MoveWide (sf : bool) (kind : a64_movwide) (rd imm16 shift : N)
| A64_Bitfield (sf : bool) (kind : a64_bf_kind) (rd rn immr imms : N)
| A64_Extr (sf : bool) (rd rn rm lsb : N)
| A64_MulAddSub (sf is_sub : bool) (rd rn rm ra : N)
| A64_MulWidening (is_signed is_sub : bool) (rd rn rm ra : N)
| A64_DataProc2 (sf : bool) (op : a64_dp2_op) (rd rn rm : N)
| A64_CondSelect (sf : bool) (kind : a64_csel_kind) (cond : a64_cond) (rd rn rm : N)
| A64_CondCompareReg (sf is_sub : bool) (cond : a64_cond) (rn rm nzcv : N)
| A64_CondCompareImm (sf is_sub : bool) (cond : a64_cond) (rn imm5 nzcv : N)
| A64_LdStImm (is_load is_signed sf_dst : bool) (sz : mc_mem_size) (mode : a64_addr_mode)
              (rt rn : N) (imm : Z)
| A64_LdStPair (is_load sf : bool) (mode : a64_addr_mode)
               (rt1 rt2 rn : N) (imm : Z)
| A64_B (rel_bytes : Z)
| A64_BCond (cond : a64_cond) (rel_bytes : Z)
| A64_Cbz (sf is_nz : bool) (rt : N) (rel_bytes : Z)
| A64_Tbz (is_nz : bool) (rt bit : N) (rel_bytes : Z)
| A64_Ret.

Record decoded_a64_inst : Set := mk_decoded_a64_inst {
  dai_off : N;
  dai_inst : a64_inst;
}.

Definition a64_w (sf : bool) : positive :=
  if sf then 64%positive else 32%positive.

Definition a64_w_N (sf : bool) : N :=
  if sf then 64%N else 32%N.

(** ** 2. Total 32-Bit Little-Endian [A64] Core Decoder *)

Definition decode_a64_shift (bits2 : N) : a64_shift :=
  if N.eqb bits2 0%N then ASH_Lsl
  else if N.eqb bits2 1%N then ASH_Lsr
  else if N.eqb bits2 2%N then ASH_Asr
  else ASH_Ror.

Definition decode_a64_extend (bits3 : N) : a64_extend :=
  if N.eqb bits3 0%N then AEX_Uxtb
  else if N.eqb bits3 1%N then AEX_Uxth
  else if N.eqb bits3 2%N then AEX_Uxtw
  else if N.eqb bits3 3%N then AEX_Uxtx
  else if N.eqb bits3 4%N then AEX_Sxtb
  else if N.eqb bits3 5%N then AEX_Sxth
  else if N.eqb bits3 6%N then AEX_Sxtw
  else AEX_Sxtx.

Definition decode_a64_cond (bits4 : N) : a64_cond :=
  if N.eqb bits4 0%N then AC_Eq
  else if N.eqb bits4 1%N then AC_Ne
  else if N.eqb bits4 2%N then AC_Cs
  else if N.eqb bits4 3%N then AC_Cc
  else if N.eqb bits4 4%N then AC_Mi
  else if N.eqb bits4 5%N then AC_Pl
  else if N.eqb bits4 6%N then AC_Vs
  else if N.eqb bits4 7%N then AC_Vc
  else if N.eqb bits4 8%N then AC_Hi
  else if N.eqb bits4 9%N then AC_Ls
  else if N.eqb bits4 10%N then AC_Ge
  else if N.eqb bits4 11%N then AC_Lt
  else if N.eqb bits4 12%N then AC_Gt
  else if N.eqb bits4 13%N then AC_Le
  else if N.eqb bits4 14%N then AC_Al
  else AC_Nv.

Definition highest_bit_pos7 (x : N) : option N :=
  if N.testbit x 6%N then Some 6%N
  else if N.testbit x 5%N then Some 5%N
  else if N.testbit x 4%N then Some 4%N
  else if N.testbit x 3%N then Some 3%N
  else if N.testbit x 2%N then Some 2%N
  else if N.testbit x 1%N then Some 1%N
  else None.

Fixpoint replicate_pattern (fuel : nat) (esize pos pat acc : N) : N :=
  match fuel with
  | O => acc
  | S fuel' =>
      if N.leb 64%N pos then acc
      else replicate_pattern fuel' esize (pos + esize) pat (N.lor acc (N.shiftl pat pos))
  end.

Definition a64_decode_bitmasks (sf : bool) (n_bit : bool) (imms immr : N) : option N :=
  let combined := ((if n_bit then 64%N else 0%N) + (63%N - N.modulo imms 64%N))%N in
  match highest_bit_pos7 combined with
  | None => None
  | Some len =>
      let esize := N.pow 2%N len in
      if negb sf && N.ltb 32%N esize then None
      else
        let levels := (esize - 1%N)%N in
        let s := N.land imms levels in
        let r := N.land immr levels in
        if N.eqb s levels then None
        else
          let welem := N.ones (s + 1%N) in
          let rot := N.modulo r esize in
          let rotated :=
            if N.eqb rot 0%N then welem
            else
              N.land
                (N.lor (N.shiftr welem rot) (N.shiftl welem (esize - rot)))
                (N.ones esize)
          in
          let rep := replicate_pattern 64%nat esize 0%N rotated 0%N in
          Some (if sf then rep else N.land rep 4294967295%N)
  end.

Definition a64_ldst_imm_kind (size opc : N) : option (bool * bool * bool * mc_mem_size * N) :=
  if N.eqb size 0%N then
    if N.eqb opc 0%N then Some (false, false, false, MS_1, 1%N)
    else if N.eqb opc 1%N then Some (true, false, false, MS_1, 1%N)
    else if N.eqb opc 2%N then Some (true, true, true, MS_1, 1%N)
    else Some (true, true, false, MS_1, 1%N)
  else if N.eqb size 1%N then
    if N.eqb opc 0%N then Some (false, false, false, MS_2, 2%N)
    else if N.eqb opc 1%N then Some (true, false, false, MS_2, 2%N)
    else if N.eqb opc 2%N then Some (true, true, true, MS_2, 2%N)
    else Some (true, true, false, MS_2, 2%N)
  else if N.eqb size 2%N then
    if N.eqb opc 0%N then Some (false, false, false, MS_4, 4%N)
    else if N.eqb opc 1%N then Some (true, false, false, MS_4, 4%N)
    else if N.eqb opc 2%N then Some (true, true, true, MS_4, 4%N)
    else None
  else
    if N.eqb opc 0%N then Some (false, false, true, MS_8, 8%N)
    else if N.eqb opc 1%N then Some (true, false, true, MS_8, 8%N)
    else None.

Definition decode_a64_word (w : N) : option a64_inst :=
  let op_top6 := bit_slice w 26%N 6%N in
  let op_26_4 := bit_slice w 26%N 4%N in
  let op_25_6 := bit_slice w 25%N 6%N in
  let op_24_8 := bit_slice w 24%N 8%N in
  let op_24_6 := bit_slice w 24%N 6%N in
  let op_24_5 := bit_slice w 24%N 5%N in
  let op_23_6 := bit_slice w 23%N 6%N in
  let op_21_8 := bit_slice w 21%N 8%N in
  let sf := N.eqb (bit_slice w 31%N 1%N) 1%N in
  let bit30 := N.eqb (bit_slice w 30%N 1%N) 1%N in
  let bit29 := N.eqb (bit_slice w 29%N 1%N) 1%N in
  let bit22 := N.eqb (bit_slice w 22%N 1%N) 1%N in
  let bit21 := N.eqb (bit_slice w 21%N 1%N) 1%N in
  let rd := bit_slice w 0%N 5%N in
  let rn := bit_slice w 5%N 5%N in
  let rm := bit_slice w 16%N 5%N in
  let wbits := a64_w_N sf in
  (* System hints (NOP / YIELD / WFE / SEV / SEVL), rejecting WFI (crm_op2 = 3) *)
  if N.eqb (bit_slice w 12%N 20%N) 872498%N && N.eqb rd 31%N then
    let crm_op2 := bit_slice w 5%N 7%N in
    if N.eqb crm_op2 3%N then None
    else if N.leb crm_op2 7%N then Some A64_Nop
    else None
  (* RET X30 only (0xD65F03C0) *)
  else if N.eqb (bit_slice w 10%N 22%N) 3512256%N && N.eqb rd 0%N then
    if N.eqb rn 30%N then Some A64_Ret else None
  (* Unconditional branch immediate: B (excludes BL) *)
  else if N.eqb op_top6 5%N then
    Some (A64_B (4 * sext_z (bit_slice w 0%N 26%N) 26%N)%Z)
  (* Conditional branch immediate: B.cond *)
  else if N.eqb op_24_8 84%N && N.eqb (bit_slice w 4%N 1%N) 0%N then
    Some (A64_BCond (decode_a64_cond (bit_slice w 0%N 4%N))
                    (4 * sext_z (bit_slice w 5%N 19%N) 19%N)%Z)
  (* Compare and branch: CBZ / CBNZ *)
  else if N.eqb op_25_6 26%N then
    Some (A64_Cbz sf (N.eqb (bit_slice w 24%N 1%N) 1%N) rd
                  (4 * sext_z (bit_slice w 5%N 19%N) 19%N)%Z)
  (* Test bit and branch: TBZ / TBNZ *)
  else if N.eqb op_25_6 27%N then
    let b5 := bit_slice w 31%N 1%N in
    let b40 := bit_slice w 19%N 5%N in
    Some (A64_Tbz (N.eqb (bit_slice w 24%N 1%N) 1%N) rd (b5 * 32%N + b40)%N
                  (4 * sext_z (bit_slice w 5%N 14%N) 14%N)%Z)
  (* Data processing (immediate): ADD/SUB imm (allow 64-bit non-flag SP reads/writes) *)
  else if N.eqb op_24_5 17%N then
    let sh2 := bit_slice w 22%N 2%N in
    let sp_bad :=
      if sf && negb bit29 then false
      else N.eqb rn 31%N || (negb bit29 && N.eqb rd 31%N)
    in
    if N.leb 2%N sh2 || sp_bad then None
    else
      let imm12 := bit_slice w 10%N 12%N in
      let imm := if N.eqb sh2 1%N then (imm12 * 4096%N)%N else imm12 in
      Some (A64_AddSubImm sf bit30 bit29 rd rn imm)
  (* Data processing (immediate): Logical immediate (reject SP writes on non-flag ops) *)
  else if N.eqb op_23_6 36%N then
    let opc := bit_slice w 29%N 2%N in
    if negb sf && bit22 then None
    else
      let immr := bit_slice w 16%N 6%N in
      let imms := bit_slice w 10%N 6%N in
      match a64_decode_bitmasks sf bit22 imms immr with
      | None => None
      | Some mask =>
          let '(lop, sfl) :=
            if N.eqb opc 0%N then (ALO_And, false)
            else if N.eqb opc 1%N then (ALO_Orr, false)
            else if N.eqb opc 2%N then (ALO_Eor, false)
            else (ALO_And, true)
          in
          if negb sfl && N.eqb rd 31%N then None
          else Some (A64_LogicalImm sf lop sfl rd rn mask)
      end
  (* Data processing (immediate): Move wide *)
  else if N.eqb op_23_6 37%N then
    let opc := bit_slice w 29%N 2%N in
    let hw := bit_slice w 21%N 2%N in
    if negb sf && N.leb 2%N hw then None
    else
      let kind_opt :=
        if N.eqb opc 0%N then Some AMW_Movn
        else if N.eqb opc 2%N then Some AMW_Movz
        else if N.eqb opc 3%N then Some AMW_Movk
        else None
      in
      match kind_opt with
      | None => None
      | Some kind =>
          Some (A64_MoveWide sf kind rd (bit_slice w 5%N 16%N) (hw * 16%N)%N)
      end
  (* Data processing (immediate): Bitfield *)
  else if N.eqb op_23_6 38%N then
    let opc := bit_slice w 29%N 2%N in
    if negb (Bool.eqb bit22 sf) then None
    else
      let immr := bit_slice w 16%N 6%N in
      let imms := bit_slice w 10%N 6%N in
      if negb (N.ltb immr wbits && N.ltb imms wbits) then None
      else
        let kind_opt :=
          if N.eqb opc 0%N then Some ABF_Sbfm
          else if N.eqb opc 1%N then Some ABF_Bfm
          else if N.eqb opc 2%N then Some ABF_Ubfm
          else None
        in
        option_map (fun k => A64_Bitfield sf k rd rn immr imms) kind_opt
  (* Data processing (immediate): Extract *)
  else if N.eqb op_23_6 39%N then
    let op21 := bit_slice w 29%N 2%N in
    let lsb := bit_slice w 10%N 6%N in
    if negb (N.eqb op21 0%N && Bool.eqb bit22 sf && negb bit21 && N.ltb lsb wbits) then None
    else Some (A64_Extr sf rd rn rm lsb)
  (* Data processing (register): Logical shifted register *)
  else if N.eqb op_24_5 10%N then
    let opc := bit_slice w 29%N 2%N in
    let sh := decode_a64_shift (bit_slice w 22%N 2%N) in
    let amt := bit_slice w 10%N 6%N in
    if negb (N.ltb amt wbits) then None
    else
      let '(lop, sfl) :=
        if N.eqb opc 0%N then (ALO_And, false)
        else if N.eqb opc 1%N then (ALO_Orr, false)
        else if N.eqb opc 2%N then (ALO_Eor, false)
        else (ALO_And, true)
      in
      Some (A64_LogicalShift sf lop bit21 sfl rd rn rm sh amt)
  (* Data processing (register): ADD/SUB shifted & extended register *)
  else if N.eqb op_24_5 11%N then
    if negb bit21 then
      let sh2 := bit_slice w 22%N 2%N in
      let amt := bit_slice w 10%N 6%N in
      if N.eqb sh2 3%N || negb (N.ltb amt wbits) then None
      else Some (A64_AddSubShift sf bit30 bit29 rd rn rm (decode_a64_shift sh2) amt)
    else
      let opt2 := bit_slice w 22%N 2%N in
      let amt := bit_slice w 10%N 3%N in
      if negb (N.eqb opt2 0%N && N.leb amt 4%N) || N.eqb rn 31%N || (negb bit29 && N.eqb rd 31%N) then None
      else Some (A64_AddSubExt sf bit30 bit29 rd rn rm (decode_a64_extend (bit_slice w 13%N 3%N)) amt)
  (* Conditional compare (register / immediate): CCMP / CCMN *)
  else if N.eqb op_21_8 210%N && bit29 && N.eqb (bit_slice w 10%N 1%N) 0%N && N.eqb (bit_slice w 4%N 1%N) 0%N then
    let cond := decode_a64_cond (bit_slice w 12%N 4%N) in
    let nzcv := bit_slice w 0%N 4%N in
    if N.eqb (bit_slice w 11%N 1%N) 0%N then
      Some (A64_CondCompareReg sf bit30 cond rn rm nzcv)
    else
      Some (A64_CondCompareImm sf bit30 cond rn rm nzcv)
  (* Conditional select: CSEL / CSINC / CSINV / CSNEG *)
  else if N.eqb op_21_8 212%N && negb bit29 && N.eqb (bit_slice w 11%N 1%N) 0%N then
    let o2 := N.eqb (bit_slice w 10%N 1%N) 1%N in
    let kind :=
      match bit30, o2 with
      | false, false => ACS_Csel
      | false, true => ACS_Csinc
      | true, false => ACS_Csinv
      | true, true => ACS_Csneg
      end
    in
    Some (A64_CondSelect sf kind (decode_a64_cond (bit_slice w 12%N 4%N)) rd rn rm)
  (* Data processing (2 source): UDIV / SDIV / LSLV / LSRV / ASRV / RORV *)
  else if N.eqb op_21_8 214%N && negb bit30 && negb bit29 then
    let op6 := bit_slice w 10%N 6%N in
    let dp2_opt :=
      if N.eqb op6 2%N then Some ADP2_Udiv
      else if N.eqb op6 3%N then Some ADP2_Sdiv
      else if N.eqb op6 8%N then Some ADP2_Lslv
      else if N.eqb op6 9%N then Some ADP2_Lsrv
      else if N.eqb op6 10%N then Some ADP2_Asrv
      else if N.eqb op6 11%N then Some ADP2_Rorv
      else None
    in
    option_map (fun op => A64_DataProc2 sf op rd rn rm) dp2_opt
  (* Data processing (3 source): MADD / MSUB / SMADDL / SMSUBL / UMADDL / UMSUBL *)
  else if N.eqb op_24_5 27%N && N.eqb (bit_slice w 29%N 2%N) 0%N then
    let op31 := bit_slice w 21%N 3%N in
    let o0 := N.eqb (bit_slice w 15%N 1%N) 1%N in
    let ra := bit_slice w 10%N 5%N in
    if N.eqb op31 0%N then Some (A64_MulAddSub sf o0 rd rn rm ra)
    else if sf && (N.eqb op31 1%N || N.eqb op31 5%N) then
      Some (A64_MulWidening (N.eqb op31 1%N) o0 rd rn rm ra)
    else None
  (* Load/store pair (STP/LDP 32/64: PostIndex / SignedOffset / PreIndex) *)
  else if N.eqb op_26_4 10%N then
    let opc := bit_slice w 30%N 2%N in
    let am := bit_slice w 23%N 3%N in
    let rt2 := bit_slice w 10%N 5%N in
    let sf_pair_opt :=
      if N.eqb opc 0%N then Some (false, 4%N)
      else if N.eqb opc 2%N then Some (true, 8%N)
      else None
    in
    let mode_opt :=
      if N.eqb am 1%N then Some AAM_PostIndex
      else if N.eqb am 2%N then Some AAM_SignedOffset
      else if N.eqb am 3%N then Some AAM_PreIndex
      else None
    in
    match sf_pair_opt, mode_opt with
    | Some (sf_p, scale), Some mode =>
        let wb := match mode with AAM_SignedOffset => false | _ => true end in
        if (bit22 && N.eqb rd rt2) ||
           (wb && negb (N.eqb rn 31%N) && (N.eqb rd rn || N.eqb rt2 rn))
        then None
        else
          let imm := (sext_z (bit_slice w 15%N 7%N) 7%N * Z.of_N scale)%Z in
          Some (A64_LdStPair bit22 sf_p mode rd rt2 rn imm)
    | _, _ => None
    end
  (* Load/store register (unsigned offset) *)
  else if N.eqb op_24_6 57%N then
    let size := bit_slice w 30%N 2%N in
    let opc := bit_slice w 22%N 2%N in
    match a64_ldst_imm_kind size opc with
    | None => None
    | Some (is_ld, is_sgn, sf_dst, sz, scale) =>
        let imm := Z.of_N (bit_slice w 10%N 12%N * scale) in
        Some (A64_LdStImm is_ld is_sgn sf_dst sz AAM_SignedOffset rd rn imm)
    end
  (* Load/store register (unscaled / post-index / pre-index) *)
  else if N.eqb op_24_6 56%N && negb bit21 then
    let size := bit_slice w 30%N 2%N in
    let opc := bit_slice w 22%N 2%N in
    let idx := bit_slice w 10%N 2%N in
    let mode_opt :=
      if N.eqb idx 0%N then Some AAM_SignedOffset
      else if N.eqb idx 1%N then Some AAM_PostIndex
      else if N.eqb idx 3%N then Some AAM_PreIndex
      else None
    in
    match a64_ldst_imm_kind size opc, mode_opt with
    | Some (is_ld, is_sgn, sf_dst, sz, _), Some mode =>
        let wb := match mode with AAM_SignedOffset => false | _ => true end in
        if wb && N.eqb rd rn && negb (N.eqb rn 31%N) then None
        else
          let imm := sext_z (bit_slice w 12%N 9%N) 9%N in
          Some (A64_LdStImm is_ld is_sgn sf_dst sz mode rd rn imm)
    | _, _ => None
    end
  else None.

Fixpoint decode_a64_stream_acc
  (fuel : nat) (cur : list N) (cur_off : nat) (acc : list decoded_a64_inst)
  {struct fuel} : string + list decoded_a64_inst :=
  match cur with
  | [] => inr (elf_rev_tr acc)
  | _ :: _ =>
      match fuel with
      | O => inl (diag "mc-decode" ("A64 decoder fuel exhausted at offset " ++ diag_N_hex (N.of_nat cur_off)))
      | S fuel' =>
          match take_u32_le cur with
          | None =>
              inl (diag "mc-decode" ("truncated 32-bit A64 instruction at offset " ++ diag_N_hex (N.of_nat cur_off)))
          | Some (w, rest4) =>
              match decode_a64_word w with
              | None =>
                  inl (diag "mc-decode"
                    ("unsupported or forbidden 32-bit A64 instruction " ++ diag_N_hex w ++
                     " at offset " ++ diag_N_hex (N.of_nat cur_off)))
              | Some inst =>
                  let acc' := mk_decoded_a64_inst (N.of_nat cur_off) inst :: acc in
                  decode_a64_stream_acc fuel' rest4 (cur_off + 4) acc'
              end
          end
      end
  end.

Definition decode_a64_bytes (code : list N) : string + list decoded_a64_inst :=
  let len := elf_length_tr code in
  if Nat.eqb len 0 || negb (Nat.eqb (Nat.modulo len 4) 0) then
    inl (diag "mc-decode" ("AArch64 function byte length " ++ diag_nat_dec len ++ " must be a positive multiple of 4"))
  else
    decode_a64_stream_acc (Nat.div len 4 + 1) code 0 [].

Definition a64_inst_valid (d : decoded_a64_inst) : bool :=
  match dai_inst d with
  | A64_AddSubShift sf _ _ _ _ _ sh amt =>
      (match sh with ASH_Ror => false | _ => true end) && N.ltb amt (a64_w_N sf)
  | A64_AddSubExt _ _ _ _ _ _ _ amt => N.leb amt 4%N
  | A64_LogicalShift sf _ _ _ _ _ _ _ amt => N.ltb amt (a64_w_N sf)
  | A64_MoveWide sf _ _ _ shift => N.ltb shift (a64_w_N sf)
  | A64_Bitfield sf _ _ _ immr imms => N.ltb immr (a64_w_N sf) && N.ltb imms (a64_w_N sf)
  | A64_Extr sf _ _ _ lsb => N.ltb lsb (a64_w_N sf)
  | A64_Tbz _ _ bit _ => N.ltb bit 64%N
  | _ => true
  end.

Lemma decode_a64_word_valid : forall w inst,
  decode_a64_word w = Some inst ->
  a64_inst_valid (mk_decoded_a64_inst 0%N inst) = true.
Proof.
  intros w inst H.
  unfold decode_a64_word in H; cbv zeta in H.
  destruct (N.eqb (bit_slice w 12%N 20%N) 872498%N && N.eqb (bit_slice w 0%N 5%N) 31%N).
  { repeat match type of H with
    | Some _ = Some _ => inversion H; subst; reflexivity
    | None = Some _ => discriminate H
    | (if ?b then _ else _) = _ => destruct b
    end. }
  destruct (N.eqb (bit_slice w 10%N 22%N) 3512256%N && N.eqb (bit_slice w 0%N 5%N) 0%N).
  { destruct (N.eqb (bit_slice w 5%N 5%N) 30%N); [inversion H; subst; reflexivity | discriminate H]. }
  destruct (N.eqb (bit_slice w 26%N 6%N) 5%N); [inversion H; subst; reflexivity |].
  destruct (N.eqb (bit_slice w 24%N 8%N) 84%N && N.eqb (bit_slice w 4%N 1%N) 0%N);
    [inversion H; subst; reflexivity |].
  destruct (N.eqb (bit_slice w 25%N 6%N) 26%N); [inversion H; subst; reflexivity |].
  destruct (N.eqb (bit_slice w 25%N 6%N) 27%N).
  { inversion H; subst; cbn [a64_inst_valid dai_inst].
    assert (Hb5 : N.ltb (bit_slice w 31%N 1%N) 2%N = true)
      by (unfold bit_slice; apply N.ltb_lt, N.mod_lt; discriminate).
    assert (Hb40 : N.ltb (bit_slice w 19%N 5%N) 32%N = true)
      by (unfold bit_slice; apply N.ltb_lt, N.mod_lt; discriminate).
    apply N.ltb_lt in Hb5; apply N.ltb_lt in Hb40; apply N.ltb_lt; lia. }
  destruct (N.eqb (bit_slice w 24%N 5%N) 17%N).
  { destruct (N.leb 2%N (bit_slice w 22%N 2%N) ||
              (if N.eqb (bit_slice w 31%N 1%N) 1%N && negb (N.eqb (bit_slice w 29%N 1%N) 1%N) then false
               else N.eqb (bit_slice w 5%N 5%N) 31%N || (negb (N.eqb (bit_slice w 29%N 1%N) 1%N) && N.eqb (bit_slice w 0%N 5%N) 31%N)));
      [discriminate H | inversion H; subst; reflexivity]. }
  destruct (N.eqb (bit_slice w 23%N 6%N) 36%N).
  { destruct (negb (N.eqb (bit_slice w 31%N 1%N) 1%N) && N.eqb (bit_slice w 22%N 1%N) 1%N);
      [discriminate H |].
    destruct (a64_decode_bitmasks _ _ _ _); [| discriminate H].
    destruct (if N.eqb _ 0%N then _ else _) as [lop sfl].
    destruct (negb sfl && N.eqb (bit_slice w 0%N 5%N) 31%N);
      [discriminate H | inversion H; subst; reflexivity]. }
  destruct (N.eqb (bit_slice w 23%N 6%N) 37%N).
  { destruct (negb (N.eqb (bit_slice w 31%N 1%N) 1%N) && N.leb 2%N (bit_slice w 21%N 2%N)) eqn:Ebad;
      [discriminate H |].
    destruct (if N.eqb (bit_slice w 29%N 2%N) 0%N then _ else _) as [k |]; [| discriminate H].
    inversion H; subst; cbn [a64_inst_valid dai_inst]; unfold a64_w_N; apply N.ltb_lt.
    destruct (N.eqb (bit_slice w 31%N 1%N) 1%N) eqn:Esf; cbn [negb andb] in Ebad.
    - assert (Hhw : (bit_slice w 21%N 2%N < 4)%N) by (unfold bit_slice; apply N.mod_lt; discriminate); lia.
    - apply N.leb_gt in Ebad; lia. }
  destruct (N.eqb (bit_slice w 23%N 6%N) 38%N).
  { destruct (N.ltb (bit_slice w 16%N 6%N) _ && N.ltb (bit_slice w 10%N 6%N) _) eqn:Erng;
      [| rewrite Bool.andb_false_r || idtac; destruct (negb _); discriminate H].
    destruct (negb (Bool.eqb _ _)); [discriminate H |].
    destruct (if N.eqb (bit_slice w 29%N 2%N) 0%N then _ else _); cbn [option_map] in H;
      [inversion H; subst; cbn [a64_inst_valid dai_inst]; exact Erng | discriminate H]. }
  destruct (N.eqb (bit_slice w 23%N 6%N) 39%N).
  { destruct (N.ltb (bit_slice w 10%N 6%N) _) eqn:Erng;
      [| rewrite Bool.andb_false_r in H; discriminate H].
    destruct (negb _); [discriminate H | inversion H; subst; cbn [a64_inst_valid dai_inst]; exact Erng]. }
  destruct (N.eqb (bit_slice w 24%N 5%N) 10%N).
  { destruct (N.ltb (bit_slice w 10%N 6%N) _) eqn:Erng; [| discriminate H].
    destruct (if N.eqb (bit_slice w 29%N 2%N) 0%N then _ else _);
      inversion H; subst; cbn [a64_inst_valid dai_inst]; exact Erng. }
  destruct (N.eqb (bit_slice w 24%N 5%N) 11%N).
  { destruct (N.eqb (bit_slice w 21%N 1%N) 1%N) eqn:E21; cbn [negb] in H.
    - destruct (N.eqb (bit_slice w 22%N 2%N) 0%N && N.leb (bit_slice w 10%N 3%N) 4%N) eqn:Eand;
        cbn [negb orb] in H; [| discriminate H].
      destruct (N.eqb (bit_slice w 5%N 5%N) 31%N || (negb (N.eqb (bit_slice w 29%N 1%N) 1%N) && N.eqb (bit_slice w 0%N 5%N) 31%N));
        cbn [orb] in H; [discriminate H |].
      apply andb_true_iff in Eand as [_ He4]; inversion H; subst; cbn [a64_inst_valid dai_inst]; exact He4.
    - destruct (N.eqb (bit_slice w 22%N 2%N) 3%N) eqn:Esh3,
               (N.ltb (bit_slice w 10%N 6%N) _) eqn:Elt;
        cbn [negb orb] in H; try discriminate H.
      inversion H; subst; cbn [a64_inst_valid dai_inst]; unfold decode_a64_shift.
      destruct (N.eqb (bit_slice w 22%N 2%N) 0%N) eqn:Ec0; [exact Elt |].
      destruct (N.eqb (bit_slice w 22%N 2%N) 1%N) eqn:Ec1; [exact Elt |].
      destruct (N.eqb (bit_slice w 22%N 2%N) 2%N) eqn:Ec2; [exact Elt |].
      exfalso; assert (H2b : (bit_slice w 22%N 2%N < 4)%N) by (unfold bit_slice; apply N.mod_lt; discriminate).
      apply N.eqb_neq in Ec0; apply N.eqb_neq in Ec1; apply N.eqb_neq in Ec2; apply N.eqb_neq in Esh3; lia. }
  destruct (N.eqb (bit_slice w 21%N 8%N) 210%N &&
            N.eqb (bit_slice w 29%N 1%N) 1%N &&
            N.eqb (bit_slice w 10%N 1%N) 0%N &&
            N.eqb (bit_slice w 4%N 1%N) 0%N).
  { destruct (N.eqb (bit_slice w 11%N 1%N) 0%N); inversion H; subst; reflexivity. }
  destruct (N.eqb (bit_slice w 21%N 8%N) 212%N &&
            negb (N.eqb (bit_slice w 29%N 1%N) 1%N) &&
            N.eqb (bit_slice w 11%N 1%N) 0%N).
  { destruct (N.eqb (bit_slice w 30%N 1%N) 1%N), (N.eqb (bit_slice w 10%N 1%N) 1%N);
      inversion H; subst; reflexivity. }
  destruct (N.eqb (bit_slice w 21%N 8%N) 214%N &&
            negb (N.eqb (bit_slice w 30%N 1%N) 1%N) &&
            negb (N.eqb (bit_slice w 29%N 1%N) 1%N)).
  { destruct (if N.eqb (bit_slice w 10%N 6%N) 2%N then _ else _) as [op |];
      cbn [option_map] in H; [inversion H; subst; reflexivity | discriminate H]. }
  destruct (N.eqb (bit_slice w 24%N 5%N) 27%N && N.eqb (bit_slice w 29%N 2%N) 0%N).
  { repeat match type of H with
    | Some _ = Some _ => inversion H; subst; reflexivity
    | None = Some _ => discriminate H
    | (if ?b then _ else _) = _ => destruct b
    end. }
  destruct (N.eqb (bit_slice w 26%N 4%N) 10%N).
  { destruct (if N.eqb (bit_slice w 30%N 2%N) 0%N then _ else _) as [[sf_p scale] |]; [| discriminate H].
    destruct (if N.eqb (bit_slice w 23%N 3%N) 1%N then _ else _) as [mode |]; [| discriminate H].
    destruct (_ || _); [discriminate H | inversion H; subst; reflexivity]. }
  destruct (N.eqb (bit_slice w 24%N 6%N) 57%N).
  { destruct (a64_ldst_imm_kind _ _) as [[[[[? ?] ?] ?] ?] |]; [inversion H; subst; reflexivity | discriminate H]. }
  destruct (N.eqb (bit_slice w 24%N 6%N) 56%N && negb (N.eqb (bit_slice w 21%N 1%N) 1%N));
    [| discriminate H].
  destruct (a64_ldst_imm_kind _ _) as [[[[[? ?] ?] ?] ?] |]; [| discriminate H].
  destruct (if N.eqb (bit_slice w 10%N 2%N) 0%N then _ else _) as [mode |]; [| discriminate H].
  destruct (_ && _); [discriminate H | inversion H; subst; reflexivity].
Qed.

Lemma decode_a64_stream_acc_valid : forall fuel cur cur_off acc xs,
  forallb a64_inst_valid acc = true ->
  decode_a64_stream_acc fuel cur cur_off acc = inr xs ->
  forallb a64_inst_valid xs = true.
Proof.
  induction fuel as [| fuel' IH]; intros [| b0 r0] cur_off acc xs Hacc Hs;
    cbn [decode_a64_stream_acc] in Hs.
  - inversion Hs; subst xs; rewrite elf_rev_tr_eq, forallb_forall in *;
      intros x Hx; apply Hacc; rewrite in_rev; exact Hx.
  - discriminate Hs.
  - inversion Hs; subst xs; rewrite elf_rev_tr_eq, forallb_forall in *;
      intros x Hx; apply Hacc; rewrite in_rev; exact Hx.
  - destruct (take_u32_le (b0 :: r0)) as [[w rest4] |]; [| discriminate Hs].
    destruct (decode_a64_word w) as [inst |] eqn:Edec; [| discriminate Hs].
    eapply IH; [| exact Hs].
    cbn [forallb]; rewrite Hacc, andb_true_r; exact (decode_a64_word_valid w inst Edec).
Qed.

Lemma decode_a64_bytes_valid : forall code insts,
  decode_a64_bytes code = inr insts ->
  forallb a64_inst_valid insts = true.
Proof.
  intros code insts H; unfold decode_a64_bytes in H.
  destruct (Nat.eqb (elf_length_tr code) 0 || negb (Nat.eqb (Nat.modulo (elf_length_tr code) 4) 0));
    [discriminate H |].
  eapply decode_a64_stream_acc_valid; [| exact H]; reflexivity.
Qed.

(** ** 3. Concrete ARMv8-A Operational Semantics *)

Definition a64_regfile : Type := N -> @Integers.bit_int 64%positive.

Record a64_flags : Set := mk_a64_flags {
  af_n : bool;
  af_z : bool;
  af_c : bool;
  af_v : bool;
}.

Definition a64_read_reg (r : N) (rf : a64_regfile) : @Integers.bit_int 64%positive :=
  if N.leb 31%N r then @Integers.zero 64%positive else rf r.

Definition a64_read_w (sf : bool) (r : N) (rf : a64_regfile)
  : @Integers.bit_int (a64_w sf) :=
  let x := a64_read_reg r rf in
  if sf return @Integers.bit_int (a64_w sf) then x
  else @Integers.repr 32%positive (@Integers.unsigned 64%positive x).

Definition a64_write_reg (r : N) (v : @Integers.bit_int 64%positive) (rf : a64_regfile)
  : a64_regfile :=
  if N.leb 31%N r then rf else fun r' => if N.eqb r' r then v else rf r'.

Definition a64_write_w (sf : bool) (r : N) (v : @Integers.bit_int (a64_w sf)) (rf : a64_regfile)
  : a64_regfile :=
  let v64 :=
    (if sf return @Integers.bit_int (a64_w sf) -> @Integers.bit_int 64%positive
     then fun x => x
     else fun x => @Integers.repr 64%positive (@Integers.unsigned 32%positive x)) v
  in
  a64_write_reg r v64 rf.

Definition a64_read_reg_sp (r : N) (rf : a64_regfile) (sp : @Integers.bit_int 64%positive)
  : @Integers.bit_int 64%positive :=
  if N.eqb r 31%N then sp else a64_read_reg r rf.

Definition a64_write_reg_sp
  (r : N) (v : @Integers.bit_int 64%positive) (rf : a64_regfile) (sp : @Integers.bit_int 64%positive)
  : a64_regfile * @Integers.bit_int 64%positive :=
  if N.eqb r 31%N then (rf, v) else (a64_write_reg r v rf, sp).

Definition a64_ldst_apply_load (is_signed sf_dst : bool) (v64 : @Integers.bit_int 64%positive)
  : @Integers.bit_int 64%positive :=
  if is_signed && negb sf_dst then
    @Integers.repr 64%positive
      (@Integers.unsigned 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v64)))
  else v64.

Definition a64_is_callee_saved (r : N) : bool :=
  N.leb 19%N r && N.leb r 30%N.

Definition a64_callee_saved_preserved (rf0 rf1 : a64_regfile) : Prop :=
  forall r, a64_is_callee_saved r = true -> rf1 r = rf0 r.

Definition a64_is_reg_forbidden (is_sp : bool) (r : N) : bool :=
  a64_is_callee_saved r || (is_sp && N.eqb r 31%N).

Definition a64_eval_shift
  (w : positive) (v : @Integers.bit_int w) (sh : a64_shift) (amt : N)
  : @Integers.bit_int w :=
  let sam := @Integers.repr w (Z.of_N amt mod Z.pos w) in
  match sh with
  | ASH_Lsl => @Integers.shl w v sam
  | ASH_Lsr => @Integers.shru w v sam
  | ASH_Asr => @Integers.shr w v sam
  | ASH_Ror =>
      let m := N.modulo amt (N.pos w) in
      if N.eqb m 0%N then v
      else
        @Integers.or w
          (@Integers.shru w v (@Integers.repr w (Z.of_N m)))
          (@Integers.shl w v (@Integers.repr w (Z.pos w - Z.of_N m)))
  end.

Definition a64_ext_bits (ext : a64_extend) : positive * bool :=
  match ext with
  | AEX_Uxtb => (8%positive, false)
  | AEX_Uxth => (16%positive, false)
  | AEX_Uxtw => (32%positive, false)
  | AEX_Uxtx => (64%positive, false)
  | AEX_Sxtb => (8%positive, true)
  | AEX_Sxth => (16%positive, true)
  | AEX_Sxtw => (32%positive, true)
  | AEX_Sxtx => (64%positive, true)
  end.

Definition a64_eval_extend
  (w : positive) (v64 : @Integers.bit_int 64%positive) (ext : a64_extend) (amt : N)
  : @Integers.bit_int w :=
  let '(src_bits, sgn) := a64_ext_bits ext in
  let eff := Pos.min src_bits w in
  let sl := @Integers.repr eff (@Integers.unsigned 64%positive v64) in
  let ext_v :=
    if Pos.eqb eff w then @Integers.repr w (@Integers.unsigned eff sl)
    else if sgn then @Integers.repr w (@Integers.signed eff sl)
    else @Integers.repr w (@Integers.unsigned eff sl)
  in
  if N.eqb amt 0%N then ext_v
  else @Integers.shl w ext_v (@Integers.repr w (Z.of_N amt mod Z.pos w)).

Definition a64_eval_add_sub
  (w : positive) (is_sub : bool) (lhs rhs : @Integers.bit_int w)
  : @Integers.bit_int w * a64_flags :=
  let res := if is_sub then @Integers.sub w lhs rhs else @Integers.add w lhs rhs in
  let nf := @Integers.lt w res (@Integers.zero w) in
  let zf := @Integers.eq w res (@Integers.zero w) in
  let cf := if is_sub then negb (@Integers.ltu w lhs rhs) else @Integers.ltu w res lhs in
  let sl := @Integers.lt w lhs (@Integers.zero w) in
  let sr := @Integers.lt w rhs (@Integers.zero w) in
  let sres := @Integers.lt w res (@Integers.zero w) in
  let vf :=
    if is_sub then negb (Bool.eqb sl sr) && negb (Bool.eqb sl sres)
    else Bool.eqb sl sr && negb (Bool.eqb sl sres)
  in
  (res, mk_a64_flags nf zf cf vf).

Definition a64_eval_logic_op
  (w : positive) (op : a64_logic_op) (lhs rhs : @Integers.bit_int w)
  : @Integers.bit_int w :=
  match op with
  | ALO_And => @Integers.and w lhs rhs
  | ALO_Orr => @Integers.or w lhs rhs
  | ALO_Eor => @Integers.xor w lhs rhs
  end.

Definition a64_eval_logic_flags (w : positive) (res : @Integers.bit_int w) : a64_flags :=
  mk_a64_flags
    (@Integers.lt w res (@Integers.zero w))
    (@Integers.eq w res (@Integers.zero w))
    false
    false.

Definition a64_flags_of_imm4 (nzcv : N) : a64_flags :=
  mk_a64_flags (N.testbit nzcv 3%N) (N.testbit nzcv 2%N) (N.testbit nzcv 1%N) (N.testbit nzcv 0%N).

Definition a64_eval_cond (c : a64_cond) (fl : a64_flags) : bool :=
  match c with
  | AC_Eq => af_z fl
  | AC_Ne => negb (af_z fl)
  | AC_Cs => af_c fl
  | AC_Cc => negb (af_c fl)
  | AC_Mi => af_n fl
  | AC_Pl => negb (af_n fl)
  | AC_Vs => af_v fl
  | AC_Vc => negb (af_v fl)
  | AC_Hi => af_c fl && negb (af_z fl)
  | AC_Ls => negb (af_c fl) || af_z fl
  | AC_Ge => Bool.eqb (af_n fl) (af_v fl)
  | AC_Lt => xorb (af_n fl) (af_v fl)
  | AC_Gt => negb (af_z fl) && Bool.eqb (af_n fl) (af_v fl)
  | AC_Le => af_z fl || xorb (af_n fl) (af_v fl)
  | AC_Al | AC_Nv => true
  end.

Definition a64_eval_bitfield
  (w : positive) (kind : a64_bf_kind) (src dst : @Integers.bit_int w) (immr imms : N)
  : @Integers.bit_int w :=
  let wn := N.pos w in
  if N.leb immr imms then
    let len := (imms - immr + 1%N)%N in
    let mask := @Integers.repr w (Z.of_N (N.ones len)) in
    let sh_r := @Integers.shru w src (@Integers.repr w (Z.of_N immr mod Z.pos w)) in
    let low := @Integers.and w sh_r mask in
    match kind with
    | ABF_Ubfm => low
    | ABF_Sbfm =>
        let shl_a := ((wn - 1%N - imms) mod wn)%N in
        let shr_a := ((wn - len) mod wn)%N in
        @Integers.shr w
          (@Integers.shl w src (@Integers.repr w (Z.of_N shl_a)))
          (@Integers.repr w (Z.of_N shr_a))
    | ABF_Bfm =>
        let kept := @Integers.and w dst (@Integers.not w mask) in
        @Integers.or w kept low
    end
  else
    let pos := ((wn - immr) mod wn)%N in
    let len := (imms + 1%N)%N in
    let mask := @Integers.repr w (Z.of_N (N.ones len)) in
    let low_bits := @Integers.and w src mask in
    let pos_i := @Integers.repr w (Z.of_N pos) in
    match kind with
    | ABF_Ubfm => @Integers.shl w low_bits pos_i
    | ABF_Sbfm =>
        let sext_sh := ((wn - len) mod wn)%N in
        let sx :=
          @Integers.shr w
            (@Integers.shl w src (@Integers.repr w (Z.of_N sext_sh)))
            (@Integers.repr w (Z.of_N sext_sh))
        in
        @Integers.shl w sx pos_i
    | ABF_Bfm =>
        let ins_mask := @Integers.shl w mask pos_i in
        let kept := @Integers.and w dst (@Integers.not w ins_mask) in
        @Integers.or w kept (@Integers.shl w low_bits pos_i)
    end.

Definition a64_eval_extr
  (w : positive) (hi lo : @Integers.bit_int w) (lsb : N)
  : @Integers.bit_int w :=
  let m := N.modulo lsb (N.pos w) in
  if N.eqb m 0%N then lo
  else
    @Integers.or w
      (@Integers.shru w lo (@Integers.repr w (Z.of_N m)))
      (@Integers.shl w hi (@Integers.repr w (Z.pos w - Z.of_N m))).

Definition a64_divu_total (w : positive) (a b : @Integers.bit_int w) : @Integers.bit_int w :=
  if Z.eqb (@Integers.unsigned w b) 0%Z then @Integers.zero w
  else @Integers.divu w a b.

Definition a64_divs_total (w : positive) (a b : @Integers.bit_int w) : @Integers.bit_int w :=
  if Z.eqb (@Integers.signed w b) 0%Z then @Integers.zero w
  else if Z.eqb (@Integers.signed w a) (@Integers.min_signed w) &&
          Z.eqb (@Integers.signed w b) (-1)%Z then @Integers.repr w (@Integers.min_signed w)
  else @Integers.divs w a b.

Definition a64_eval_dp2
  (w : positive) (op : a64_dp2_op) (lhs rhs : @Integers.bit_int w)
  : @Integers.bit_int w :=
  let sh := rv_mask_shamt w (@Integers.unsigned w rhs) in
  let inv := rv_mask_shamt w (Z.pos w - @Integers.unsigned w sh) in
  match op with
  | ADP2_Udiv => a64_divu_total w lhs rhs
  | ADP2_Sdiv => a64_divs_total w lhs rhs
  | ADP2_Lslv => @Integers.shl w lhs sh
  | ADP2_Lsrv => @Integers.shru w lhs sh
  | ADP2_Asrv => @Integers.shr w lhs sh
  | ADP2_Rorv =>
      @Integers.or w (@Integers.shru w lhs sh) (@Integers.shl w lhs inv)
  end.

Definition a64_eval_csel
  (w : positive) (kind : a64_csel_kind) (c : a64_cond) (fl : a64_flags)
  (tval mval : @Integers.bit_int w) : @Integers.bit_int w :=
  let fval :=
    match kind with
    | ACS_Csel => mval
    | ACS_Csinc => @Integers.add w mval (@Integers.one w)
    | ACS_Csinv => @Integers.not w mval
    | ACS_Csneg => @Integers.neg w mval
    end
  in
  if a64_eval_cond c fl then tval else fval.

Fixpoint lookup_a64_inst (insts : list decoded_a64_inst) (pc : N) : option decoded_a64_inst :=
  match insts with
  | [] => None
  | d :: rest => if N.eqb (dai_off d) pc then Some d else lookup_a64_inst rest pc
  end.

Fixpoint a64_exec_mem
  (fuel : nat) (insts : list decoded_a64_inst) (pc : N)
  (sp0 : @Integers.bit_int 64%positive) (rf : a64_regfile)
  (sp : @Integers.bit_int 64%positive) (fl : a64_flags) (mstk : mc_stack_mem)
  {struct fuel} : option (a64_regfile * @Integers.bit_int 64%positive * a64_flags * mc_stack_mem) :=
  match fuel with
  | O => None
  | S fuel' =>
      match lookup_a64_inst insts pc with
      | None => None
      | Some dec =>
          let next_pc := (pc + 4%N)%N in
          match dai_inst dec with
          | A64_Nop => a64_exec_mem fuel' insts next_pc sp0 rf sp fl mstk
          | A64_AddSubImm sf is_sub sfl rd rn imm =>
              if sf && negb sfl then
                let lhs := a64_read_reg_sp rn rf sp in
                let rhs := @Integers.repr 64%positive (Z.of_N imm) in
                let res := if is_sub then @Integers.sub 64%positive lhs rhs else @Integers.add 64%positive lhs rhs in
                let '(rf', sp') := a64_write_reg_sp rd res rf sp in
                a64_exec_mem fuel' insts next_pc sp0 rf' sp' fl mstk
              else
                let lhs := a64_read_w sf rn rf in
                let rhs := @Integers.repr (a64_w sf) (Z.of_N imm) in
                let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
                a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp (if sfl then fl' else fl) mstk
          | A64_AddSubShift sf is_sub sfl rd rn rm sh amt =>
              let lhs := a64_read_w sf rn rf in
              let rhs := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt in
              let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp (if sfl then fl' else fl) mstk
          | A64_AddSubExt sf is_sub sfl rd rn rm ext amt =>
              let lhs := a64_read_w sf rn rf in
              let rhs := a64_eval_extend (a64_w sf) (a64_read_reg rm rf) ext amt in
              let '(res, fl') := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp (if sfl then fl' else fl) mstk
          | A64_LogicalImm sf op sfl rd rn mask =>
              let lhs := a64_read_w sf rn rf in
              let rhs := @Integers.repr (a64_w sf) (Z.of_N mask) in
              let res := a64_eval_logic_op (a64_w sf) op lhs rhs in
              let fl' := if sfl then a64_eval_logic_flags (a64_w sf) res else fl in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp fl' mstk
          | A64_LogicalShift sf op inv_rm sfl rd rn rm sh amt =>
              let lhs := a64_read_w sf rn rf in
              let shv := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt in
              let rhs := if inv_rm then @Integers.not (a64_w sf) shv else shv in
              let res := a64_eval_logic_op (a64_w sf) op lhs rhs in
              let fl' := if sfl then a64_eval_logic_flags (a64_w sf) res else fl in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp fl' mstk
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
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp fl mstk
          | A64_Bitfield sf kind rd rn immr imms =>
              let res := a64_eval_bitfield (a64_w sf) kind
                           (a64_read_w sf rn rf) (a64_read_w sf rd rf) immr imms in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp fl mstk
          | A64_Extr sf rd rn rm lsb =>
              let res := a64_eval_extr (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf) lsb in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp fl mstk
          | A64_MulAddSub sf is_sub rd rn rm ra =>
              let w := a64_w sf in
              let p := @Integers.mul w (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
              let a := a64_read_w sf ra rf in
              let res := if is_sub then @Integers.sub w a p else @Integers.add w a p in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp fl mstk
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
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_reg rd res rf) sp fl mstk
          | A64_DataProc2 sf op rd rn rm =>
              let res := a64_eval_dp2 (a64_w sf) op (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp fl mstk
          | A64_CondSelect sf kind cond rd rn rm =>
              let res := a64_eval_csel (a64_w sf) kind cond fl
                           (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
              a64_exec_mem fuel' insts next_pc sp0 (a64_write_w sf rd res rf) sp fl mstk
          | A64_CondCompareReg sf is_sub cond rn rm nzcv =>
              let lhs := a64_read_w sf rn rf in
              let rhs := a64_read_w sf rm rf in
              let '(_, cfl) := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
              let fl' := if a64_eval_cond cond fl then cfl else a64_flags_of_imm4 nzcv in
              a64_exec_mem fuel' insts next_pc sp0 rf sp fl' mstk
          | A64_CondCompareImm sf is_sub cond rn imm5 nzcv =>
              let lhs := a64_read_w sf rn rf in
              let rhs := @Integers.repr (a64_w sf) (Z.of_N imm5) in
              let '(_, cfl) := a64_eval_add_sub (a64_w sf) is_sub lhs rhs in
              let fl' := if a64_eval_cond cond fl then cfl else a64_flags_of_imm4 nzcv in
              a64_exec_mem fuel' insts next_pc sp0 rf sp fl' mstk
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
                  a64_exec_mem fuel' insts next_pc sp0 rf2 sp2 fl mstk1
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
                  a64_exec_mem fuel' insts next_pc sp0 rf2 sp2 fl mstk1
                else None
          | A64_B rel =>
              match add_rel_off pc rel with
              | None => None
              | Some tgt_pc => a64_exec_mem fuel' insts tgt_pc sp0 rf sp fl mstk
              end
          | A64_BCond cond rel =>
              if a64_eval_cond cond fl then
                match add_rel_off pc rel with
                | None => None
                | Some tgt_pc => a64_exec_mem fuel' insts tgt_pc sp0 rf sp fl mstk
                end
              else a64_exec_mem fuel' insts next_pc sp0 rf sp fl mstk
          | A64_Cbz sf is_nz rt rel =>
              let v := a64_read_w sf rt rf in
              let eq0 := @Integers.eq (a64_w sf) v (@Integers.zero (a64_w sf)) in
              let taken := if is_nz then negb eq0 else eq0 in
              if taken then
                match add_rel_off pc rel with
                | None => None
                | Some tgt_pc => a64_exec_mem fuel' insts tgt_pc sp0 rf sp fl mstk
                end
              else a64_exec_mem fuel' insts next_pc sp0 rf sp fl mstk
          | A64_Tbz is_nz rt bit rel =>
              let v := a64_read_reg rt rf in
              let tb := Z.testbit (@Integers.unsigned 64%positive v) (Z.of_N bit) in
              let taken := if is_nz then tb else negb tb in
              if taken then
                match add_rel_off pc rel with
                | None => None
                | Some tgt_pc => a64_exec_mem fuel' insts tgt_pc sp0 rf sp fl mstk
                end
              else a64_exec_mem fuel' insts next_pc sp0 rf sp fl mstk
          | A64_Ret => Some (rf, sp, fl, mstk)
          end
      end
  end.

Definition a64_exec
  (fuel : nat) (insts : list decoded_a64_inst) (pc : N)
  (rf : a64_regfile) (fl : a64_flags) : option (a64_regfile * a64_flags) :=
  let sp0 := @Integers.repr 64%positive mc_frame_cap in
  match a64_exec_mem fuel insts pc sp0 rf sp0 fl mc_empty_stack with
  | None => None
  | Some (rf_end, _, fl_end, _) => Some (rf_end, fl_end)
  end.

(** ** 4. AAPCS64 Argument ABI & Total Symbolic DAG Lowering *)

Definition a64_hi_var_name (nm : string) : string :=
  ("__a64_hi_" ++ nm)%string.

Definition a64_hi_vars (specs : list rv_arg_spec) : list (string * positive) :=
  List.flat_map
    (fun sp =>
       if Pos.eqb (ras_width sp) 64%positive then []
       else [(a64_hi_var_name (ras_name sp), 64%positive)])
    specs.

Definition a64_valid_arg_spec (sp : rv_arg_spec) : bool :=
  rv_supported_arg_width (ras_width sp) &&
  negb (starts_with_dollar (ras_name sp)) &&
  (if Pos.eqb (ras_width sp) 64%positive then
     match ras_ext sp with RAE_None => true | _ => false end
   else if Pos.eqb (ras_width sp) 32%positive then
     match ras_ext sp with RAE_None => true | _ => false end
   else true).

Definition a64_init_arg_expr (sp : rv_arg_spec) : cert_expr :=
  let w := ras_width sp in
  let v := CE_Var (ras_name sp) w in
  if Pos.eqb w 64%positive then v
  else if Pos.eqb w 32%positive then
    let lo := CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags v in
    let hi := CE_BinOp CB_And 64%positive no_binop_flags
                (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive)
                (CE_BvConst 64%positive 18446744069414584320%N) in
    CE_BinOp CB_Or 64%positive no_binop_flags lo hi
  else
    match ras_ext sp with
    | RAE_None =>
        let lo := CE_Cast CCK_ZExt w 64%positive no_cast_flags v in
        let hi_mask := (N.shiftl 1%N 64%N - N.shiftl 1%N (N.pos w))%N in
        let hi := CE_BinOp CB_And 64%positive no_binop_flags
                    (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive)
                    (CE_BvConst 64%positive hi_mask) in
        CE_BinOp CB_Or 64%positive no_binop_flags lo hi
    | RAE_SignExt =>
        let lo32 := CE_Cast CCK_SExt w 32%positive no_cast_flags v in
        let lo := CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags lo32 in
        let hi := CE_BinOp CB_And 64%positive no_binop_flags
                    (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive)
                    (CE_BvConst 64%positive 18446744069414584320%N) in
        CE_BinOp CB_Or 64%positive no_binop_flags lo hi
    | RAE_ZeroExt =>
        let lo32 := CE_Cast CCK_ZExt w 32%positive no_cast_flags v in
        let lo := CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags lo32 in
        let hi := CE_BinOp CB_And 64%positive no_binop_flags
                    (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive)
                    (CE_BvConst 64%positive 18446744069414584320%N) in
        CE_BinOp CB_Or 64%positive no_binop_flags lo hi
    end.

Definition a64_sym_trunc32_match (e : cert_expr) : option cert_expr :=
  match e with
  | CE_Cast CCK_ZExt fw tw _ inner =>
      if Pos.eqb fw 32%positive && Pos.eqb tw 64%positive then Some inner else None
  | CE_BinOp CB_Or w1 _
      (CE_Cast CCK_ZExt fw tw _ inner)
      (CE_BinOp CB_And w2 _ _ (CE_BvConst w3 mask)) =>
      if Pos.eqb w1 64%positive && Pos.eqb fw 32%positive && Pos.eqb tw 64%positive &&
         Pos.eqb w2 64%positive && Pos.eqb w3 64%positive &&
         N.eqb (N.land mask 4294967295%N) 0%N
      then Some inner
      else None
  | _ => None
  end.

Definition a64_sym_trunc32 (e : cert_expr) : cert_expr :=
  match a64_sym_trunc32_match e with
  | Some inner => inner
  | None => ce_trunc64_32 e
  end.

Definition a64_sym_not (w : positive) (e : cert_expr) : cert_expr :=
  CE_BinOp CB_Xor w no_binop_flags e (ce_all_ones w).

Definition a64_sym_neg (w : positive) (e : cert_expr) : cert_expr :=
  CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w 0%N) e.

Definition a64_sym_bool_not (e : cert_expr) : cert_expr :=
  CE_BinOp CB_Xor 1%positive no_binop_flags e (CE_BvConst 1%positive 1%N).

Definition a64_sym_bool_xor (a b : cert_expr) : cert_expr :=
  CE_BinOp CB_Xor 1%positive no_binop_flags a b.

Definition a64_sym_bool_eq (a b : cert_expr) : cert_expr :=
  CE_ICmp CIP_Eq false 1%positive a b.

Definition a64_sym_is_neg (w : positive) (e : cert_expr) : cert_expr :=
  CE_ICmp CIP_Slt false w e (CE_BvConst w 0%N).

Record a64_sym_flags : Set := mk_a64_sym_flags {
  asf_n : cert_expr;
  asf_z : cert_expr;
  asf_c : cert_expr;
  asf_v : cert_expr;
  asf_n_ne_v : cert_expr;
}.

Definition a64_init_sym_flags : a64_sym_flags :=
  let f := CE_BvConst 1%positive 0%N in
  mk_a64_sym_flags f f f f f.

Definition a64_sym_flags_of_imm4 (nzcv : N) : a64_sym_flags :=
  let b n := CE_BvConst 1%positive (if N.testbit nzcv n then 1%N else 0%N) in
  let bn := b 3%N in
  let bv := b 0%N in
  let bn_ne_v := CE_BvConst 1%positive (if xorb (N.testbit nzcv 3%N) (N.testbit nzcv 0%N) then 1%N else 0%N) in
  mk_a64_sym_flags bn (b 2%N) (b 1%N) bv bn_ne_v.

Definition a64_sym_add_sub (w : positive) (is_sub : bool) (lhs rhs : cert_expr)
  : cert_expr * a64_sym_flags :=
  let res := CE_BinOp (if is_sub then CB_Sub else CB_Add) w no_binop_flags lhs rhs in
  let nf := a64_sym_is_neg w res in
  let sl := a64_sym_is_neg w lhs in
  let sr := a64_sym_is_neg w rhs in
  let eq_lr := a64_sym_bool_eq sl sr in
  let diff_lres := a64_sym_bool_xor sl nf in
  let zf :=
    if is_sub then CE_ICmp CIP_Eq false w lhs rhs
    else CE_ICmp CIP_Eq false w res (CE_BvConst w 0%N)
  in
  let cf :=
    if is_sub then CE_ICmp CIP_Uge false w lhs rhs
    else CE_ICmp CIP_Ult false w res lhs
  in
  let vf :=
    if is_sub then CE_BinOp CB_And 1%positive no_binop_flags (a64_sym_bool_xor sl sr) diff_lres
    else CE_BinOp CB_And 1%positive no_binop_flags eq_lr diff_lres
  in
  let n_ne_v :=
    if is_sub then CE_ICmp CIP_Slt false w lhs rhs
    else a64_sym_bool_xor nf vf
  in
  (res, mk_a64_sym_flags nf zf cf vf n_ne_v).

Definition a64_sym_logic_flags (w : positive) (res : cert_expr) : a64_sym_flags :=
  let nf := a64_sym_is_neg w res in
  let zf := CE_ICmp CIP_Eq false w res (CE_BvConst w 0%N) in
  let f0 := CE_BvConst 1%positive 0%N in
  mk_a64_sym_flags nf zf f0 f0 nf.

Definition a64_sym_cond (c : a64_cond) (sf : a64_sym_flags) : cert_expr :=
  match c with
  | AC_Eq => asf_z sf
  | AC_Ne => a64_sym_bool_not (asf_z sf)
  | AC_Cs => asf_c sf
  | AC_Cc => a64_sym_bool_not (asf_c sf)
  | AC_Mi => asf_n sf
  | AC_Pl => a64_sym_bool_not (asf_n sf)
  | AC_Vs => asf_v sf
  | AC_Vc => a64_sym_bool_not (asf_v sf)
  | AC_Hi => CE_BinOp CB_And 1%positive no_binop_flags (asf_c sf) (a64_sym_bool_not (asf_z sf))
  | AC_Ls => CE_BinOp CB_Or 1%positive no_binop_flags (a64_sym_bool_not (asf_c sf)) (asf_z sf)
  | AC_Ge => a64_sym_bool_not (asf_n_ne_v sf)
  | AC_Lt => asf_n_ne_v sf
  | AC_Gt => CE_BinOp CB_And 1%positive no_binop_flags (a64_sym_bool_not (asf_z sf)) (a64_sym_bool_not (asf_n_ne_v sf))
  | AC_Le => CE_BinOp CB_Or 1%positive no_binop_flags (asf_z sf) (asf_n_ne_v sf)
  | AC_Al | AC_Nv => CE_BvConst 1%positive 1%N
  end.

Definition a64_sym_ite_flags (cond : cert_expr) (fl_t fl_f : a64_sym_flags) : a64_sym_flags :=
  mk_a64_sym_flags
    (CE_Select 1%positive cond (asf_n fl_t) (asf_n fl_f))
    (CE_Select 1%positive cond (asf_z fl_t) (asf_z fl_f))
    (CE_Select 1%positive cond (asf_c fl_t) (asf_c fl_f))
    (CE_Select 1%positive cond (asf_v fl_t) (asf_v fl_f))
    (CE_Select 1%positive cond (asf_n_ne_v fl_t) (asf_n_ne_v fl_f)).

Definition a64_sym_shift (w : positive) (e : cert_expr) (sh : a64_shift) (amt : N) : cert_expr :=
  let m := N.modulo amt (N.pos w) in
  match sh with
  | ASH_Lsl =>
      if N.eqb m 0%N then e
      else CE_BinOp CB_Shl w no_binop_flags e (CE_BvConst w m)
  | ASH_Lsr =>
      if N.eqb m 0%N then e
      else CE_BinOp CB_LShr w no_binop_flags e (CE_BvConst w m)
  | ASH_Asr =>
      if N.eqb m 0%N then e
      else CE_BinOp CB_AShr w no_binop_flags e (CE_BvConst w m)
  | ASH_Ror =>
      if N.eqb m 0%N then e
      else
        CE_BinOp CB_Or w no_binop_flags
          (CE_BinOp CB_LShr w no_binop_flags e (CE_BvConst w m))
          (CE_BinOp CB_Shl w no_binop_flags e (CE_BvConst w (N.pos w - m)))
  end.

Definition a64_sym_extend (w : positive) (e64 : cert_expr) (ext : a64_extend) (amt : N) : cert_expr :=
  let '(src_bits, sgn) := a64_ext_bits ext in
  let eff := Pos.min src_bits w in
  let sl :=
    if Pos.eqb eff 64%positive then e64
    else if Pos.eqb eff 32%positive then a64_sym_trunc32 e64
    else CE_Cast CCK_Trunc 64%positive eff no_cast_flags e64
  in
  let ext_e :=
    if Pos.eqb eff w then sl
    else CE_Cast (if sgn then CCK_SExt else CCK_ZExt) eff w no_cast_flags sl
  in
  if N.eqb amt 0%N then ext_e
  else CE_BinOp CB_Shl w no_binop_flags ext_e (CE_BvConst w (N.modulo amt (N.pos w))).

Definition a64_sym_logic_op (w : positive) (op : a64_logic_op) (lhs rhs : cert_expr) : cert_expr :=
  let bop :=
    match op with
    | ALO_And => CB_And
    | ALO_Orr => CB_Or
    | ALO_Eor => CB_Xor
    end
  in
  CE_BinOp bop w no_binop_flags lhs rhs.

Definition a64_sym_bitfield
  (w : positive) (kind : a64_bf_kind) (src dst : cert_expr) (immr imms : N) : cert_expr :=
  let wn := N.pos w in
  if N.leb immr imms then
    let len := (imms - immr + 1%N)%N in
    let mask := CE_BvConst w (N.ones len) in
    let sh_r :=
      if N.eqb immr 0%N then src
      else CE_BinOp CB_LShr w no_binop_flags src (CE_BvConst w immr)
    in
    match kind with
    | ABF_Ubfm =>
        if N.eqb len wn then src
        else if N.eqb imms (wn - 1%N) then sh_r
        else if Pos.eqb w 64%positive && N.eqb immr 0%N && N.eqb imms 31%N then
          CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags (a64_sym_trunc32 src)
        else CE_BinOp CB_And w no_binop_flags sh_r mask
    | ABF_Sbfm =>
        if Pos.eqb w 64%positive && N.eqb immr 0%N && N.eqb imms 31%N then
          CE_Cast CCK_SExt 32%positive 64%positive no_cast_flags (a64_sym_trunc32 src)
        else
          let shl_a := (wn - 1%N - imms)%N in
          let shr_a := (wn - len)%N in
          let sl :=
            if N.eqb shl_a 0%N then src
            else CE_BinOp CB_Shl w no_binop_flags src (CE_BvConst w shl_a)
          in
          if N.eqb shr_a 0%N then sl
          else CE_BinOp CB_AShr w no_binop_flags sl (CE_BvConst w shr_a)
    | ABF_Bfm =>
        let low := CE_BinOp CB_And w no_binop_flags sh_r mask in
        let nmask := a64_sym_not w mask in
        let kept := CE_BinOp CB_And w no_binop_flags dst nmask in
        CE_BinOp CB_Or w no_binop_flags kept low
    end
  else
    let pos := (wn - immr)%N in
    let len := (imms + 1%N)%N in
    let mask := CE_BvConst w (N.ones len) in
    let low_bits := CE_BinOp CB_And w no_binop_flags src mask in
    let pos_e := CE_BvConst w pos in
    match kind with
    | ABF_Ubfm => CE_BinOp CB_Shl w no_binop_flags low_bits pos_e
    | ABF_Sbfm =>
        let sext_sh := (wn - len)%N in
        let sh_e := CE_BvConst w sext_sh in
        let sx := CE_BinOp CB_AShr w no_binop_flags (CE_BinOp CB_Shl w no_binop_flags src sh_e) sh_e in
        CE_BinOp CB_Shl w no_binop_flags sx pos_e
    | ABF_Bfm =>
        let ins_mask := CE_BinOp CB_Shl w no_binop_flags mask pos_e in
        let kept := CE_BinOp CB_And w no_binop_flags dst (a64_sym_not w ins_mask) in
        CE_BinOp CB_Or w no_binop_flags kept (CE_BinOp CB_Shl w no_binop_flags low_bits pos_e)
    end.

Definition a64_sym_extr (w : positive) (hi lo : cert_expr) (lsb : N) : cert_expr :=
  let m := N.modulo lsb (N.pos w) in
  if N.eqb m 0%N then lo
  else
    CE_BinOp CB_Or w no_binop_flags
      (CE_BinOp CB_LShr w no_binop_flags lo (CE_BvConst w m))
      (CE_BinOp CB_Shl w no_binop_flags hi (CE_BvConst w (N.pos w - m))).

Definition a64_sym_div_guarded (is_signed : bool) (w : positive) (a b : cert_expr) : cert_expr :=
  let z0 := CE_BvConst w 0%N in
  let is_z := CE_ICmp CIP_Eq false w b z0 in
  if negb is_signed then
    let sb := CE_Select w is_z (CE_BvConst w 1%N) b in
    CE_Select w is_z z0 (CE_BinOp CB_UDiv w no_binop_flags a sb)
  else
    let ones := ce_all_ones w in
    let imin := ce_int_min w in
    let is_ovf :=
      CE_BinOp CB_And 1%positive no_binop_flags
        (CE_ICmp CIP_Eq false w a imin)
        (CE_ICmp CIP_Eq false w b ones)
    in
    let bad := CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf in
    let sa := CE_Select w is_ovf z0 a in
    let sb := CE_Select w bad (CE_BvConst w 1%N) b in
    CE_Select w is_z z0
      (CE_Select w is_ovf imin (CE_BinOp CB_SDiv w no_binop_flags sa sb)).

Definition a64_sym_dp2 (w : positive) (op : a64_dp2_op) (lhs rhs : cert_expr) : cert_expr :=
  let sh_mask := CE_BvConst w (Z.to_N (Z.pos w - 1)) in
  let sh := CE_BinOp CB_And w no_binop_flags rhs sh_mask in
  let inv :=
    CE_BinOp CB_And w no_binop_flags
      (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w)) sh)
      sh_mask
  in
  match op with
  | ADP2_Udiv => a64_sym_div_guarded false w lhs rhs
  | ADP2_Sdiv => a64_sym_div_guarded true w lhs rhs
  | ADP2_Lslv => CE_BinOp CB_Shl w no_binop_flags lhs sh
  | ADP2_Lsrv => CE_BinOp CB_LShr w no_binop_flags lhs sh
  | ADP2_Asrv => CE_BinOp CB_AShr w no_binop_flags lhs sh
  | ADP2_Rorv =>
      CE_BinOp CB_Or w no_binop_flags
        (CE_BinOp CB_LShr w no_binop_flags lhs sh)
        (CE_BinOp CB_Shl w no_binop_flags lhs inv)
  end.

Definition a64_sym_csel
  (w : positive) (kind : a64_csel_kind) (c : a64_cond) (sf : a64_sym_flags)
  (tval mval : cert_expr) : cert_expr :=
  let fval :=
    match kind with
    | ACS_Csel => mval
    | ACS_Csinc => CE_BinOp CB_Add w no_binop_flags mval (CE_BvConst w 1%N)
    | ACS_Csinv => a64_sym_not w mval
    | ACS_Csneg => a64_sym_neg w mval
    end
  in
  CE_Select w (a64_sym_cond c sf) tval fval.

Definition a64_sym_regs : Type := N -> cert_expr.
Definition a64_def_mask : Type := N -> bool.

Definition a64_sym_read_reg (r : N) (srf : a64_sym_regs) : cert_expr :=
  if N.leb 31%N r then CE_BvConst 64%positive 0%N else srf r.

Definition a64_sym_read_w (sf : bool) (r : N) (srf : a64_sym_regs) : cert_expr :=
  let x := a64_sym_read_reg r srf in
  if sf then x else a64_sym_trunc32 x.

Definition a64_sym_write_reg (r : N) (e : cert_expr) (srf : a64_sym_regs) : a64_sym_regs :=
  if N.leb 31%N r then srf else fun r' => if N.eqb r' r then e else srf r'.

Definition a64_sym_write_w (sf : bool) (r : N) (e : cert_expr) (srf : a64_sym_regs)
  : a64_sym_regs :=
  let e64 :=
    if sf then e
    else CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags e
  in
  a64_sym_write_reg r e64 srf.

Definition a64_def_read (r : N) (def : a64_def_mask) : bool :=
  if N.leb 31%N r then true else def r.

Definition a64_def_write (r : N) (def : a64_def_mask) : a64_def_mask :=
  if N.leb 31%N r then def else fun r' => if N.eqb r' r then true else def r'.

Fixpoint a64_build_init_state (idx : N) (specs : list rv_arg_spec)
  : a64_sym_regs * a64_def_mask :=
  match specs with
  | [] => ((fun _ => CE_BvConst 64%positive 0%N), (fun r => N.leb 31%N r))
  | sp :: rest =>
      let '(srf', def') := a64_build_init_state (N.succ idx) rest in
      let e := a64_init_arg_expr sp in
      ((fun r => if N.eqb r idx then e else srf' r),
       (fun r => N.eqb r idx || def' r))
  end.

Definition a64_val_regs : Type := N -> mc_sym_val.

Definition a64_val_read (r : N) (vrf : a64_val_regs) : mc_sym_val :=
  if N.leb 31%N r then MSV_Expr (CE_BvConst 64%positive 0%N) else vrf r.

Definition a64_val_read_sp (r : N) (vrf : a64_val_regs) (sp_off : Z) : mc_sym_val :=
  if N.eqb r 31%N then MSV_StackPtr sp_off else a64_val_read r vrf.

Definition a64_val_write (r : N) (sv : mc_sym_val) (vrf : a64_val_regs) : a64_val_regs :=
  if N.leb 31%N r then vrf else fun r' => if N.eqb r' r then sv else vrf r'.

Definition a64_val_write_w (sf : bool) (r : N) (e : cert_expr) (vrf : a64_val_regs)
  : a64_val_regs :=
  a64_val_write r
    (MSV_Expr (if sf then e else CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags e))
    vrf.

Definition a64_val_read_expr_w (sf : bool) (r : N) (vrf : a64_val_regs) : option cert_expr :=
  match a64_val_read r vrf with
  | MSV_Expr e => Some (if sf then e else a64_sym_trunc32 e)
  | _ => None
  end.

Definition a64_val_write_sp
  (r : N) (sv : mc_sym_val) (sp_off : Z) (vrf : a64_val_regs) (astk : mc_sym_stack)
  : option (Z * a64_val_regs * mc_sym_stack) :=
  if N.eqb r 31%N then
    match sv with
    | MSV_StackPtr off' =>
        if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then
          Some (off', vrf, mc_sym_stk_prune off' astk)
        else None
    | _ => None
    end
  else Some (sp_off, a64_val_write r sv vrf, astk).

Definition a64_ldst_sym_load (is_signed sf_dst : bool) (sv : mc_sym_val) : option mc_sym_val :=
  if is_signed && negb sf_dst then
    match sv with
    | MSV_Expr e =>
        Some (MSV_Expr (CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags (a64_sym_trunc32 e)))
    | _ => None
    end
  else Some sv.

Definition a64_ldst_store_sym_ok (sz : mc_mem_size) (sv : mc_sym_val) : bool :=
  match sv with
  | MSV_Undef => false
  | MSV_Expr _ => true
  | MSV_SavedReg _ | MSV_StackPtr _ => mc_mem_size_eqb sz MS_8
  end.

Definition a64_is_orr_mov64
  (sf : bool) (op : a64_logic_op) (inv_rm set_fl : bool) (rn : N) (sh : a64_shift) (amt : N) : bool :=
  sf && negb inv_rm && negb set_fl && N.eqb rn 31%N && N.eqb amt 0%N &&
  (match op with ALO_Orr => true | _ => false end) &&
  (match sh with ASH_Lsl => true | _ => false end).

Definition a64_callee_saved_list : list N :=
  [19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30]%N.

Definition a64_sym_epilogue_ok (sp_off : Z) (vrf : a64_val_regs) : bool :=
  Z.eqb sp_off 0%Z &&
  forallb
    (fun r =>
       match a64_val_read r vrf with
       | MSV_SavedReg r0 => N.eqb r0 r
       | _ => false
       end)
    a64_callee_saved_list.

Definition a64_empty_val_regs : a64_val_regs :=
  fun r =>
    if N.leb 31%N r then MSV_Expr (CE_BvConst 64%positive 0%N)
    else if a64_is_callee_saved r then MSV_SavedReg r
    else MSV_Undef.

Fixpoint a64_build_init_val_regs (idx : N) (specs : list rv_arg_spec) : a64_val_regs :=
  match specs with
  | [] => a64_empty_val_regs
  | sp :: rest =>
      let vrf' := a64_build_init_val_regs (N.succ idx) rest in
      let e := a64_init_arg_expr sp in
      fun r => if N.eqb r idx then MSV_Expr e else vrf' r
  end.

Lemma lookup_a64_inst_eq_key : forall insts pc,
  lookup_a64_inst insts pc = lookup_by_key dai_off insts pc.
Proof.
  induction insts as [| d rest IH]; intro pc; cbn; [reflexivity |].
  destruct (N.eqb (dai_off d) pc); [reflexivity | exact (IH pc)].
Qed.

Lemma pt_of_list_first_lookup_a64 : forall insts pc,
  pt_get (N.succ_pos pc) (pt_of_list_first dai_off insts) = lookup_a64_inst insts pc.
Proof.
  intros insts pc; rewrite pt_of_list_first_get, lookup_a64_inst_eq_key; reflexivity.
Qed.

Fixpoint summarize_a64_dag_at
  (fuel : nat) (im : pos_trie decoded_a64_inst) (visited : pos_trie unit)
  (pc : N) (sp_off : Z) (vrf : a64_val_regs) (astk : mc_sym_stack)
  (sfl : a64_sym_flags) (fl_def : bool) (ret_w : positive)
  {struct fuel} : string + cfg_dag :=
  let loc (_ : unit) : string :=
    ("a64 at pc=" ++ diag_N_hex pc ++ " sp-off=" ++ diag_Z_dec sp_off)%string
  in
  if pt_has_n pc visited then
    inl (diag "mc-exec" ("cycle/loop detected in a64 acyclic DAG mode (" ++ loc tt ++ "); provide a (loop ...) certificate"))
  else
    match fuel with
    | O => inl (diag "mc-exec" ("a64 symbolic execution fuel exhausted (" ++ loc tt ++ ")"))
    | S fuel' =>
        match pt_get (N.succ_pos pc) im with
        | None => inl (diag "mc-exec" ("a64 execution escaped function slice (" ++ loc tt ++ ")"))
        | Some dec =>
            let next_pc := (pc + 4%N)%N in
            let visited' := pt_add_n pc visited in
            match dai_inst dec with
            | A64_Nop =>
                summarize_a64_dag_at fuel' im visited' next_pc sp_off vrf astk sfl fl_def ret_w
            | A64_AddSubImm sf is_sub set_fl rd rn imm =>
                if sf && negb set_fl then
                  let sv_opt :=
                    match a64_val_read_sp rn vrf sp_off with
                    | MSV_StackPtr base_off =>
                        let off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z in
                        if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z
                        then Some (MSV_StackPtr off')
                        else None
                    | MSV_SavedReg r0 =>
                        if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
                    | MSV_Expr e =>
                        Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
                    | MSV_Undef => None
                    end
                  in
                  match sv_opt with
                  | None =>
                      inl (diag (if N.eqb rd 31%N || N.eqb rn 31%N then "mc-frame" else "mc-exec")
                            ("unsupported add/sub-imm operand or out-of-frame sp update in a64 (" ++ loc tt ++ ")"))
                  | Some sv =>
                      match a64_val_write_sp rd sv sp_off vrf astk with
                      | None =>
                          inl (diag "mc-frame" ("invalid sp update or frame bound violation in a64 add/sub-imm (" ++ loc tt ++ ")"))
                      | Some (sp_off', vrf', astk') =>
                          summarize_a64_dag_at fuel' im visited' next_pc sp_off' vrf' astk' sfl fl_def ret_w
                      end
                  end
                else if N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N) then
                  inl (diag "mc-frame" ("disallowed sp/xzr access in a64 add/sub-imm (" ++ loc tt ++ ")"))
                else
                  match a64_val_read_expr_w sf rn vrf with
                  | None =>
                      inl (diag "mc-exec" ("undefined/non-expression operand x" ++ diag_N_dec rn ++ " in a64 add/sub-imm (" ++ loc tt ++ ")"))
                  | Some lhs =>
                      let rhs := ce_bv_z (a64_w sf) (Z.of_N imm) in
                      let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
                      summarize_a64_dag_at fuel' im visited' next_pc sp_off
                        (a64_val_write_w sf rd res vrf) astk
                        (if set_fl then sfl' else sfl) (set_fl || fl_def) ret_w
                  end
            | A64_AddSubShift sf is_sub set_fl rd rn rm sh amt =>
                match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
                | Some lhs, Some rm_e =>
                    let rhs := a64_sym_shift (a64_w sf) rm_e sh amt in
                    let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
                    summarize_a64_dag_at fuel' im visited' next_pc sp_off
                      (a64_val_write_w sf rd res vrf) astk
                      (if set_fl then sfl' else sfl) (set_fl || fl_def) ret_w
                | _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 add/sub-shift (" ++ loc tt ++ ")"))
                end
            | A64_AddSubExt sf is_sub set_fl rd rn rm ext amt =>
                if N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N) then
                  inl (diag "mc-frame" ("disallowed sp/xzr access in a64 add/sub-ext (" ++ loc tt ++ ")"))
                else
                  match a64_val_read_expr_w sf rn vrf, a64_val_read rm vrf with
                  | Some lhs, MSV_Expr rm64 =>
                      let rhs := a64_sym_extend (a64_w sf) rm64 ext amt in
                      let '(res, sfl') := a64_sym_add_sub (a64_w sf) is_sub lhs rhs in
                      summarize_a64_dag_at fuel' im visited' next_pc sp_off
                        (a64_val_write_w sf rd res vrf) astk
                        (if set_fl then sfl' else sfl) (set_fl || fl_def) ret_w
                  | _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 add/sub-ext (" ++ loc tt ++ ")"))
                  end
            | A64_LogicalImm sf op set_fl rd rn mask =>
                if negb set_fl && N.eqb rd 31%N then
                  inl (diag "mc-frame" ("disallowed sp write in a64 logical-imm (" ++ loc tt ++ ")"))
                else
                  match a64_val_read_expr_w sf rn vrf with
                  | None => inl (diag "mc-exec" ("undefined/non-expression operand x" ++ diag_N_dec rn ++ " in a64 logical-imm (" ++ loc tt ++ ")"))
                  | Some lhs =>
                      let rhs := ce_bv_z (a64_w sf) (Z.of_N mask) in
                      let res := a64_sym_logic_op (a64_w sf) op lhs rhs in
                      let sfl' := if set_fl then a64_sym_logic_flags (a64_w sf) res else sfl in
                      summarize_a64_dag_at fuel' im visited' next_pc sp_off
                        (a64_val_write_w sf rd res vrf) astk sfl' (set_fl || fl_def) ret_w
                  end
            | A64_LogicalShift sf op inv_rm set_fl rd rn rm sh amt =>
                if a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt then
                  match a64_val_read rm vrf with
                  | MSV_Undef => inl (diag "mc-exec" ("mov source x" ++ diag_N_dec rm ++ " is undefined in a64 (" ++ loc tt ++ ")"))
                  | sv =>
                      summarize_a64_dag_at fuel' im visited' next_pc sp_off
                        (a64_val_write rd sv vrf) astk sfl fl_def ret_w
                  end
                else
                  match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
                  | Some lhs, Some rm_e =>
                      let shv := a64_sym_shift (a64_w sf) rm_e sh amt in
                      let rhs := if inv_rm then a64_sym_not (a64_w sf) shv else shv in
                      let res := a64_sym_logic_op (a64_w sf) op lhs rhs in
                      let sfl' := if set_fl then a64_sym_logic_flags (a64_w sf) res else sfl in
                      summarize_a64_dag_at fuel' im visited' next_pc sp_off
                        (a64_val_write_w sf rd res vrf) astk sfl' (set_fl || fl_def) ret_w
                  | _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 logical-shift (" ++ loc tt ++ ")"))
                  end
            | A64_MoveWide sf kind rd imm16 shift =>
                let w := a64_w sf in
                let imm_e := ce_bv_z w (Z.of_N (N.shiftl imm16 shift)) in
                match kind with
                | AMW_Movz =>
                    summarize_a64_dag_at fuel' im visited' next_pc sp_off
                      (a64_val_write_w sf rd imm_e vrf) astk sfl fl_def ret_w
                | AMW_Movn =>
                    summarize_a64_dag_at fuel' im visited' next_pc sp_off
                      (a64_val_write_w sf rd (a64_sym_not w imm_e) vrf) astk sfl fl_def ret_w
                | AMW_Movk =>
                    match a64_val_read_expr_w sf rd vrf with
                    | None => inl (diag "mc-exec" ("undefined destination x" ++ diag_N_dec rd ++ " in a64 movk (" ++ loc tt ++ ")"))
                    | Some cur =>
                        let clr := a64_sym_not w (ce_bv_z w (Z.of_N (N.shiftl 65535%N shift))) in
                        let res := CE_BinOp CB_Or w no_binop_flags
                                     (CE_BinOp CB_And w no_binop_flags cur clr) imm_e in
                        summarize_a64_dag_at fuel' im visited' next_pc sp_off
                          (a64_val_write_w sf rd res vrf) astk sfl fl_def ret_w
                    end
                end
            | A64_Bitfield sf kind rd rn immr imms =>
                let dst_opt :=
                  match kind with
                  | ABF_Bfm => a64_val_read_expr_w sf rd vrf
                  | _ => Some (CE_BvConst (a64_w sf) 0%N)
                  end
                in
                match a64_val_read_expr_w sf rn vrf, dst_opt with
                | Some src_e, Some dst_e =>
                    let res := a64_sym_bitfield (a64_w sf) kind src_e dst_e immr imms in
                    summarize_a64_dag_at fuel' im visited' next_pc sp_off
                      (a64_val_write_w sf rd res vrf) astk sfl fl_def ret_w
                | _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 bitfield (" ++ loc tt ++ ")"))
                end
            | A64_Extr sf rd rn rm lsb =>
                match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
                | Some hi_e, Some lo_e =>
                    let res := a64_sym_extr (a64_w sf) hi_e lo_e lsb in
                    summarize_a64_dag_at fuel' im visited' next_pc sp_off
                      (a64_val_write_w sf rd res vrf) astk sfl fl_def ret_w
                | _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 extr (" ++ loc tt ++ ")"))
                end
            | A64_MulAddSub sf is_sub rd rn rm ra =>
                match a64_val_read_expr_w sf rn vrf,
                      a64_val_read_expr_w sf rm vrf,
                      a64_val_read_expr_w sf ra vrf with
                | Some en, Some em, Some ea =>
                    let w := a64_w sf in
                    let p := CE_BinOp CB_Mul w no_binop_flags en em in
                    let res := CE_BinOp (if is_sub then CB_Sub else CB_Add) w no_binop_flags ea p in
                    summarize_a64_dag_at fuel' im visited' next_pc sp_off
                      (a64_val_write_w sf rd res vrf) astk sfl fl_def ret_w
                | _, _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 mul-add/sub (" ++ loc tt ++ ")"))
                end
            | A64_MulWidening sgn is_sub rd rn rm ra =>
                match a64_val_read_expr_w false rn vrf,
                      a64_val_read_expr_w false rm vrf,
                      a64_val_read ra vrf with
                | Some en, Some em, MSV_Expr ea =>
                    let ck := if sgn then CCK_SExt else CCK_ZExt in
                    let n64 := CE_Cast ck 32%positive 64%positive no_cast_flags en in
                    let m64 := CE_Cast ck 32%positive 64%positive no_cast_flags em in
                    let p := CE_BinOp CB_Mul 64%positive no_binop_flags n64 m64 in
                    let res := CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags ea p in
                    summarize_a64_dag_at fuel' im visited' next_pc sp_off
                      (a64_val_write rd (MSV_Expr res) vrf) astk sfl fl_def ret_w
                | _, _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 widening mul (" ++ loc tt ++ ")"))
                end
            | A64_DataProc2 sf op rd rn rm =>
                match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
                | Some en, Some em =>
                    let res := a64_sym_dp2 (a64_w sf) op en em in
                    summarize_a64_dag_at fuel' im visited' next_pc sp_off
                      (a64_val_write_w sf rd res vrf) astk sfl fl_def ret_w
                | _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 data-proc2 (" ++ loc tt ++ ")"))
                end
            | A64_CondSelect sf kind cond rd rn rm =>
                if negb fl_def then
                  inl (diag "mc-exec" ("undefined NZCV flags read by a64 csel (" ++ loc tt ++ ")"))
                else
                  match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
                  | Some en, Some em =>
                      let res := a64_sym_csel (a64_w sf) kind cond sfl en em in
                      summarize_a64_dag_at fuel' im visited' next_pc sp_off
                        (a64_val_write_w sf rd res vrf) astk sfl fl_def ret_w
                  | _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 csel (" ++ loc tt ++ ")"))
                  end
            | A64_CondCompareReg sf is_sub cond rn rm nzcv =>
                if negb fl_def then
                  inl (diag "mc-exec" ("undefined NZCV flags read by a64 ccmp-reg (" ++ loc tt ++ ")"))
                else
                  match a64_val_read_expr_w sf rn vrf, a64_val_read_expr_w sf rm vrf with
                  | Some en, Some em =>
                      let '(_, csfl) := a64_sym_add_sub (a64_w sf) is_sub en em in
                      let sfl' := a64_sym_ite_flags (a64_sym_cond cond sfl) csfl (a64_sym_flags_of_imm4 nzcv) in
                      summarize_a64_dag_at fuel' im visited' next_pc sp_off vrf astk sfl' true ret_w
                  | _, _ => inl (diag "mc-exec" ("undefined/non-expression operand in a64 ccmp-reg (" ++ loc tt ++ ")"))
                  end
            | A64_CondCompareImm sf is_sub cond rn imm5 nzcv =>
                if negb fl_def then
                  inl (diag "mc-exec" ("undefined NZCV flags read by a64 ccmp-imm (" ++ loc tt ++ ")"))
                else
                  match a64_val_read_expr_w sf rn vrf with
                  | None => inl (diag "mc-exec" ("undefined/non-expression operand x" ++ diag_N_dec rn ++ " in a64 ccmp-imm (" ++ loc tt ++ ")"))
                  | Some en =>
                      let '(_, csfl) := a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5)) in
                      let sfl' := a64_sym_ite_flags (a64_sym_cond cond sfl) csfl (a64_sym_flags_of_imm4 nzcv) in
                      summarize_a64_dag_at fuel' im visited' next_pc sp_off vrf astk sfl' true ret_w
                  end
            | A64_LdStImm is_load is_signed sf_dst sz mode rt rn imm =>
                if (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false)
                then inl (diag "mc-frame" ("unaligned stack pointer on a64 ldst-imm (" ++ loc tt ++ ")"))
                else
                  match a64_val_read_sp rn vrf sp_off with
                  | MSV_StackPtr base_off =>
                      let wb_off := (base_off + imm)%Z in
                      let wb_ok :=
                        match mode with
                        | AAM_SignedOffset => true
                        | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z
                        end
                      in
                      if negb wb_ok then
                        inl (diag "mc-frame" ("out-of-frame writeback sp+" ++ diag_Z_dec wb_off ++ " in a64 ldst-imm (" ++ loc tt ++ ")"))
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
                              if a64_ldst_store_sym_ok sz sv then
                                Some (vrf, mc_sym_stk_store off sz sv astk)
                              else None
                          in
                          match st_opt with
                          | None =>
                              inl (diag "mc-frame"
                                ((if is_load then "uninitialized or incompatible stack load"
                                  else "invalid or narrow stack store") ++
                                 " at sp+" ++ diag_Z_dec off ++ " in a64 ldst-imm (" ++ loc tt ++ ")"))
                          | Some (vrf1, astk1) =>
                              let '(sp_off2, vrf2, astk2) :=
                                match mode with
                                | AAM_SignedOffset => (sp_off, vrf1, astk1)
                                | AAM_PreIndex | AAM_PostIndex =>
                                    if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
                                    else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
                                end
                              in
                              summarize_a64_dag_at fuel' im visited' next_pc sp_off2 vrf2 astk2 sfl fl_def ret_w
                          end
                        else
                          inl (diag "mc-frame"
                            ("a64 ldst-imm at sp+" ++ diag_Z_dec off ++ " (size " ++ diag_Z_dec (mc_mem_bytes_Z sz) ++
                             ") out of frame bounds (" ++ loc tt ++ ")"))
                  | _ =>
                      inl (diag "mc-frame" ("a64 ldst-imm base register x" ++ diag_N_dec rn ++ " is not a stack pointer (" ++ loc tt ++ ")"))
                  end
            | A64_LdStPair is_load sf mode rt1 rt2 rn imm =>
                if (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false)
                then inl (diag "mc-frame" ("unaligned stack pointer on a64 ldst-pair (" ++ loc tt ++ ")"))
                else
                  match a64_val_read_sp rn vrf sp_off with
                  | MSV_StackPtr base_off =>
                      let wb_off := (base_off + imm)%Z in
                      let wb_ok :=
                        match mode with
                        | AAM_SignedOffset => true
                        | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z
                        end
                      in
                      if negb wb_ok then
                        inl (diag "mc-frame" ("out-of-frame writeback sp+" ++ diag_Z_dec wb_off ++ " in a64 ldst-pair (" ++ loc tt ++ ")"))
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
                        if mc_slot_in_frame sp_chk off sz &&
                           mc_slot_in_frame sp_chk (off + delta) sz
                        then
                          let st_opt :=
                            if is_load then
                              match mc_sym_stk_load off sz false astk,
                                    mc_sym_stk_load (off + delta) sz false astk with
                              | Some sv1, Some sv2 =>
                                  Some (a64_val_write rt2 sv2 (a64_val_write rt1 sv1 vrf), astk)
                              | _, _ => None
                              end
                            else
                              let sv1 := a64_val_read rt1 vrf in
                              let sv2 := a64_val_read rt2 vrf in
                              if a64_ldst_store_sym_ok sz sv1 && a64_ldst_store_sym_ok sz sv2 then
                                Some (vrf, mc_sym_stk_store (off + delta) sz sv2
                                             (mc_sym_stk_store off sz sv1 astk))
                              else None
                          in
                          match st_opt with
                          | None =>
                              inl (diag "mc-frame"
                                ((if is_load then "uninitialized stack load" else "invalid or narrow stack store") ++
                                 " at sp+" ++ diag_Z_dec off ++ " in a64 ldst-pair (" ++ loc tt ++ ")"))
                          | Some (vrf1, astk1) =>
                              let '(sp_off2, vrf2, astk2) :=
                                match mode with
                                | AAM_SignedOffset => (sp_off, vrf1, astk1)
                                | AAM_PreIndex | AAM_PostIndex =>
                                    if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
                                    else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
                                end
                              in
                              summarize_a64_dag_at fuel' im visited' next_pc sp_off2 vrf2 astk2 sfl fl_def ret_w
                          end
                        else
                          inl (diag "mc-frame"
                            ("a64 ldst-pair at sp+" ++ diag_Z_dec off ++ " out of frame bounds (" ++ loc tt ++ ")"))
                  | _ =>
                      inl (diag "mc-frame" ("a64 ldst-pair base register x" ++ diag_N_dec rn ++ " is not a stack pointer (" ++ loc tt ++ ")"))
                  end
            | A64_B rel =>
                match add_rel_off pc rel with
                | None => inl (diag "mc-exec" ("negative a64 jump target (" ++ loc tt ++ ")"))
                | Some tgt_pc =>
                    summarize_a64_dag_at fuel' im visited' tgt_pc sp_off vrf astk sfl fl_def ret_w
                end
            | A64_BCond cond rel =>
                if negb fl_def then
                  inl (diag "mc-exec" ("undefined NZCV flags read by a64 b.cond (" ++ loc tt ++ ")"))
                else
                  match add_rel_off pc rel with
                  | None => inl (diag "mc-exec" ("negative a64 b.cond target (" ++ loc tt ++ ")"))
                  | Some tgt_pc =>
                      let c_e := a64_sym_cond cond sfl in
                      match summarize_a64_dag_at fuel' im visited' tgt_pc sp_off vrf astk sfl fl_def ret_w with
                      | inl err => inl err
                      | inr d_t =>
                          match summarize_a64_dag_at fuel' im visited' next_pc sp_off vrf astk sfl fl_def ret_w with
                          | inl err => inl err
                          | inr d_f => inr (CD_Branch c_e d_t d_f)
                          end
                      end
                  end
            | A64_Cbz sf is_nz rt rel =>
                match a64_val_read_expr_w sf rt vrf with
                | None => inl (diag "mc-exec" ("undefined/non-expression operand x" ++ diag_N_dec rt ++ " in a64 cbz/cbnz (" ++ loc tt ++ ")"))
                | Some rt_e =>
                    match add_rel_off pc rel with
                    | None => inl (diag "mc-exec" ("negative a64 cbz/cbnz target (" ++ loc tt ++ ")"))
                    | Some tgt_pc =>
                        let w := a64_w sf in
                        let c_e := CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false w
                                     rt_e (CE_BvConst w 0%N) in
                        match summarize_a64_dag_at fuel' im visited' tgt_pc sp_off vrf astk sfl fl_def ret_w with
                        | inl err => inl err
                        | inr d_t =>
                            match summarize_a64_dag_at fuel' im visited' next_pc sp_off vrf astk sfl fl_def ret_w with
                            | inl err => inl err
                            | inr d_f => inr (CD_Branch c_e d_t d_f)
                            end
                        end
                    end
                end
            | A64_Tbz is_nz rt bit rel =>
                match a64_val_read rt vrf with
                | MSV_Expr rt_e =>
                    match add_rel_off pc rel with
                    | None => inl (diag "mc-exec" ("negative a64 tbz/tbnz target (" ++ loc tt ++ ")"))
                    | Some tgt_pc =>
                        let masked := CE_BinOp CB_And 64%positive no_binop_flags
                                        rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit)) in
                        let c_e := CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false 64%positive
                                     masked (CE_BvConst 64%positive 0%N) in
                        match summarize_a64_dag_at fuel' im visited' tgt_pc sp_off vrf astk sfl fl_def ret_w with
                        | inl err => inl err
                        | inr d_t =>
                            match summarize_a64_dag_at fuel' im visited' next_pc sp_off vrf astk sfl fl_def ret_w with
                            | inl err => inl err
                            | inr d_f => inr (CD_Branch c_e d_t d_f)
                            end
                        end
                    end
                | _ => inl (diag "mc-exec" ("undefined/non-expression operand x" ++ diag_N_dec rt ++ " in a64 tbz/tbnz (" ++ loc tt ++ ")"))
                end
            | A64_Ret =>
                if a64_sym_epilogue_ok sp_off vrf then
                  match a64_val_read 0%N vrf with
                  | MSV_Expr e_ret =>
                      inr (CD_RetScalar ret_w (rv_trunc_ret_expr ret_w e_ret))
                  | _ =>
                      inl (diag "mc-exec" ("return register x0 does not hold a value expression at a64 ret (" ++ loc tt ++ ")"))
                  end
                else
                  inl (diag "mc-frame"
                    ((if negb (Z.eqb sp_off 0%Z)
                      then "unrestored stack pointer"
                      else "clobbered callee-saved register x19..x30") ++ " at a64 ret (" ++ loc tt ++ ")"))
            end
        end
    end.

Definition summarize_a64_dag
  (fuel : nat) (insts : list decoded_a64_inst)
  (arg_specs : list rv_arg_spec) (ret_w : positive) : string + cfg_dag :=
  if negb (Nat.leb (List.length arg_specs) 8) then
    inl (diag "mc-exec" ("too many argument specs (" ++ diag_nat_dec (List.length arg_specs) ++ " > 8)"))
  else if negb (forallb a64_valid_arg_spec arg_specs) then
    inl (diag "mc-exec" "invalid argument spec for a64 symbolic execution")
  else if negb (rv_supported_arg_width ret_w) then
    inl (diag "mc-exec" ("unsupported return width " ++ diag_pos_dec ret_w ++ " for a64 symbolic execution"))
  else
    let vrf0 := a64_build_init_val_regs 0%N arg_specs in
    let im := pt_of_list_first dai_off insts in
    summarize_a64_dag_at fuel im (@PT_Empty unit) 0%N 0%Z vrf0 [] a64_init_sym_flags false ret_w.

(** ** 5. Bitvector Arithmetic & Semantic Equivalence Proofs ([0 Admitted], [0] Custom Axioms) *)

Lemma a64_supported_arg_width_pos : forall w,
  rv_supported_arg_width w = true ->
  (w = 1%positive \/ w = 8%positive \/ w = 16%positive \/ w = 32%positive \/ w = 64%positive).
Proof.
  intros w Hw.
  do 7 (destruct w as [w|w|]; cbn in Hw; try discriminate Hw; auto 10).
Qed.

Lemma a64_supported_lt32 : forall w,
  rv_supported_arg_width w = true ->
  (w =? 64)%positive = false ->
  (w =? 32)%positive = false ->
  (w <? 32)%positive = true.
Proof.
  intros w Hw H64 H32.
  destruct (a64_supported_arg_width_pos w Hw) as [-> | [-> | [-> | [-> | ->]]]];
    try reflexivity; [rewrite Pos.eqb_refl in H32; discriminate H32
                   | rewrite Pos.eqb_refl in H64; discriminate H64].
Qed.

Lemma a64_w_32_64 : forall sf, (a64_w sf = 32%positive \/ a64_w sf = 64%positive).
Proof.
  intros [|]; [right | left]; reflexivity.
Qed.

Lemma eval_ce_not :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v,
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    eval_closed_cert_expr penv foracle (a64_sym_not w e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.not w v))).
Proof.
  intros Pa penv foracle w e v He; unfold a64_sym_not.
  rewrite eval_ce_binop, He, eval_ce_all_ones; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
  reflexivity.
Qed.

Lemma eval_ce_neg :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v,
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    eval_closed_cert_expr penv foracle (a64_sym_neg w e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.neg w v))).
Proof.
  intros Pa penv foracle w e v He; unfold a64_sym_neg.
  rewrite eval_ce_binop, eval_ce_const, He, repr_zero_N; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.sub Integers.zero Integers.neg].
  pose proof (@Integers.modulus_pos w); unfold Integers.sub, Integers.neg, Integers.zero.
  rewrite (@Integers.unsigned_repr w 0%Z) by (unfold Integers.max_unsigned; lia).
  rewrite Z.sub_0_l; reflexivity.
Qed.

Lemma eval_iop_or_poison_contrad :
  forall {Pa : Params} fl (dvr : @dvalue Pa) v64,
    eval_iop (Or (cbf_disjoint fl)) (DVALUE_Base DVALUE_Poison) dvr =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    False.
Proof.
  intros Pa fl dvr v64 He; cbn [eval_iop] in He.
  destruct dvr as [db | ? ? | vec el2]; try discriminate He.
  - destruct db; cbn in He; discriminate He.
  - destruct vec; cbn in He; try discriminate He.
    destruct (map_monad dvalue_to_dvalue_base el2) as [| | | xs]; unfold bind, ret in He; cbn in He; try discriminate He.
    destruct (vec_loop (eval_iop_integer_base (Or (cbf_disjoint fl)))
               (combine (repeat DVALUE_Poison (Datatypes.length xs)) xs)) as [| | | ans];
      cbn in He; try discriminate He.
    unfold canonicalize_vector in He; destruct (forallb dvalue_is_poison _); discriminate He.
Qed.

Lemma eval_a64_sym_trunc32_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle e v64,
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (a64_sym_trunc32 e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v64)))).
Proof.
  intros Pa penv foracle e v64 He.
  assert (Hfall : eval_closed_cert_expr penv foracle (ce_trunc64_32 e) =
                  raise_ret (DVALUE_Base (@DVALUE_I Pa 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v64)))))
    by (eapply eval_ce_trunc; [reflexivity | exact He]).
  unfold a64_sym_trunc32.
  destruct (a64_sym_trunc32_match e) as [inner |] eqn:Em; [| exact Hfall].
  destruct e as [| | | op w1 fl l r | | k fw tw fl o | | |];
    cbn [a64_sym_trunc32_match] in Em; try discriminate Em.
  - destruct op; try discriminate Em.
    destruct l as [| | | | | kl fw tw fll ol | | |]; try discriminate Em.
    destruct kl; try discriminate Em.
    destruct r as [| | | opr w2 flr lr rr | | | | |]; try discriminate Em.
    destruct opr; try discriminate Em.
    destruct rr as [w3 mask | | | | | | | |]; try discriminate Em.
    destruct (Pos.eqb w1 64%positive && Pos.eqb fw 32%positive && Pos.eqb tw 64%positive &&
              Pos.eqb w2 64%positive && Pos.eqb w3 64%positive &&
              N.eqb (N.land mask 4294967295%N) 0%N) eqn:Eok; [| discriminate Em].
    inversion Em; subst inner; clear Em.
    rewrite !andb_true_iff in Eok; destruct Eok as (((((Ew1 & Efw) & Etw) & Ew2) & Ew3) & Emask).
    apply Pos.eqb_eq in Ew1; apply Pos.eqb_eq in Efw; apply Pos.eqb_eq in Etw;
      apply Pos.eqb_eq in Ew2; apply Pos.eqb_eq in Ew3; apply N.eqb_eq in Emask; subst w1 fw tw w2 w3.
    unfold eval_closed_cert_expr in He |- *; cbn [eval_cert_expr] in He.
    destruct (eval_cert_expr penv [] foracle ol) as [| | | dvol] eqn:Eol; cbn [eou_bind] in He;
      try discriminate He.
    destruct (convert_pure (cert_to_pure_conv CCK_ZExt fll) (DTYPE_I 32) dvol (DTYPE_I 64))
      as [| | | dv_ext] eqn:Ecp; cbn [eou_bind] in He; try discriminate He.
    destruct (eval_cert_expr penv [] foracle lr) as [| | | dvlr] eqn:Elr; cbn [eou_bind] in He;
      try discriminate He.
    destruct (eval_iop (cert_to_ibinop CB_And flr) dvlr (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.repr 64%positive (Z.of_N mask)))))
      as [| | | dvr] eqn:Eand; cbn [eou_bind] in He; try discriminate He.
    destruct dvol as [[| wol iol | | | | | |] | [|] elts |];
      cbn [convert_pure cert_to_pure_conv get_base_conversion_type convert_pure_base get_vector_conversion_type] in Ecp;
      try discriminate Ecp.
    -- destruct (Pos.eqb 32%positive wol) eqn:Ewol; [| unfold fmap in Ecp; cbn in Ecp; discriminate Ecp].
       apply Pos.eqb_eq in Ewol; subst wol.
       destruct (ccf_nneg fll && (Integers.signed iol <? 0)%Z); unfold fmap, ret in Ecp; cbn in Ecp;
         [inversion Ecp; subst dv_ext; cbn [cert_to_ibinop] in He; exfalso; eapply eval_iop_or_poison_contrad; exact He |].
       inversion Ecp; subst dv_ext; clear Ecp.
       destruct dvlr as [[p | wlr ilr | ? | ? | ? | | | ? ?] | ? ? | vec_lr elr_lr];
         cbn [eval_iop cert_to_ibinop] in Eand; unfold fmap, ret in Eand; cbn [eou_bind] in Eand; try discriminate Eand;
         try (unfold eval_iop_integer_base in Eand; cbn in Eand;
              inversion Eand as [Heqv]; rewrite <- Heqv in He;
              cbn [eval_iop cert_to_ibinop] in He; unfold fmap, ret in He; cbn in He; discriminate He).
       all: try (destruct vec_lr; cbn in Eand; try discriminate Eand;
                 destruct (map_monad dvalue_to_dvalue_base elr_lr) as [| | | xslr]; cbn in Eand; try discriminate Eand;
                 destruct (vec_loop And (combine xslr (repeat (DVALUE_I 64 (Integers.repr (Z.of_N mask))) (Datatypes.length xslr)))) as [| | | anslr]; cbn in Eand; try discriminate Eand;
                 inversion Eand as [Heqv]; rewrite <- Heqv in He; unfold canonicalize_vector in He;
                 destruct (forallb dvalue_is_poison (map DVALUE_Base anslr));
                 cbn [eval_iop cert_to_ibinop] in He; unfold fmap, ret in He; cbn in He; discriminate He).
       destruct (Pos.eq_dec wlr 64%positive) as [-> | Hne];
         [| unfold eval_iop_integer_base in Eand; destruct (Pos.eq_dec wlr 64%positive); [contradiction | cbn in Eand; discriminate Eand]].
       rewrite eval_iop_integer_base_same_width in Eand; unfold fmap, ret in Eand; cbn [eou_bind eval_int_op] in Eand.
       inversion Eand; subst dvr; clear Eand.
       cbn [eval_iop cert_to_ibinop] in He; unfold fmap, ret in He; cbn [eou_bind] in He.
       rewrite eval_iop_integer_base_same_width in He.
       cbn - [Integers.or Integers.and Integers.xor Integers.eq Integers.repr Integers.unsigned] in He.
       assert (Hinv : v64 = @Integers.or 64%positive
                              (@Integers.repr 64%positive (@Integers.unsigned 32%positive iol))
                              (@Integers.and 64%positive ilr (@Integers.repr 64%positive (Z.of_N mask)))).
       { destruct (cbf_disjoint fl) eqn:Edisj;
           [destruct (Integers.eq (Integers.or (Integers.repr (Integers.unsigned iol)) (Integers.and ilr (Integers.repr (Z.of_N mask))))
                                  (Integers.xor (Integers.repr (Integers.unsigned iol)) (Integers.and ilr (Integers.repr (Z.of_N mask)))));
            cbn in He; [| discriminate He] |];
           apply alg_ret_dvalue_I_inj in He; symmetry; exact He. }
       subst v64; clear He.
       do 3 f_equal.
       apply Integers.same_bits_eq; intros i Hi.
       assert (Hi32 : (0 <= i < 32)%Z) by (replace 32%Z with (@Integers.zwordsize 32%positive) by reflexivity; exact Hi).
       assert (Hi64 : (0 <= i < @Integers.zwordsize 64%positive)%Z) by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
       rewrite (@Integers.testbit_repr 32%positive _ i Hi).
       change (Z.testbit (@Integers.unsigned 64%positive
                 (@Integers.or 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive iol))
                   (@Integers.and 64%positive ilr (@Integers.repr 64%positive (Z.of_N mask))))) i)
         with (@Integers.testbit 64%positive
                 (@Integers.or 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive iol))
                   (@Integers.and 64%positive ilr (@Integers.repr 64%positive (Z.of_N mask)))) i).
       rewrite (@Integers.bits_or 64%positive _ _ i Hi64), (@Integers.bits_and 64%positive _ _ i Hi64).
       rewrite (@Integers.testbit_repr 64%positive _ i Hi64), (@Integers.testbit_repr 64%positive _ i Hi64).
       change (Z.testbit (@Integers.unsigned 32%positive iol) i) with (@Integers.testbit 32%positive iol i).
       assert (Hmk : Z.testbit (Z.of_N mask) i = false).
       { replace 4294967295%N with (N.ones 32%N) in Emask by reflexivity.
         pose proof (N.land_spec mask (N.ones 32%N) (Z.to_N i)) as Hls.
         rewrite Emask, N.bits_0, N.ones_spec_low in Hls by lia.
         destruct (N.testbit mask (Z.to_N i)) eqn:Et; [rewrite andb_true_r in Hls; discriminate |].
         rewrite <- N2Z.inj_testbit, Z2N.id in Et by lia; exact Et. }
       rewrite Hmk, andb_false_r, orb_false_r; reflexivity.
    -- unfold fmap, ret in Ecp; cbn in Ecp; inversion Ecp; subst dv_ext; cbn [cert_to_ibinop] in He;
         exfalso; eapply eval_iop_or_poison_contrad; exact He.
    -- unfold fmap, ret in Ecp; cbn in Ecp; destruct vector; discriminate Ecp.
  - destruct k; try discriminate Em.
    destruct (Pos.eqb fw 32%positive && Pos.eqb tw 64%positive) eqn:Eok; [| discriminate Em].
    inversion Em; subst inner; clear Em.
    apply andb_true_iff in Eok as [Efw Etw]; apply Pos.eqb_eq in Efw; apply Pos.eqb_eq in Etw; subst fw tw.
    unfold eval_closed_cert_expr in He |- *; cbn [eval_cert_expr] in He.
    destruct (eval_cert_expr penv [] foracle o) as [| | | dvo] eqn:Eo; cbn [eou_bind] in He;
      try discriminate He.
    destruct dvo as [[| wo io | | | | | |] | ? ? | vec_o ?];
      cbn [convert_pure cert_to_pure_conv get_base_conversion_type convert_pure_base get_vector_conversion_type] in He;
      unfold fmap, ret in He; cbn in He; try discriminate He;
      [| destruct vec_o; discriminate He].
    destruct (Pos.eqb 32%positive wo) eqn:Ewo; [| cbn in He; discriminate He].
    apply Pos.eqb_eq in Ewo; subst wo.
    destruct (ccf_nneg fl && (Integers.signed io <? 0)%Z); cbn in He; [discriminate He |].
    apply alg_ret_dvalue_I_inj in He; subst v64.
    do 3 f_equal.
    apply Integers.same_bits_eq; intros i Hi.
    assert (Hi32 : (0 <= i < 32)%Z) by (replace 32%Z with (@Integers.zwordsize 32%positive) by reflexivity; exact Hi).
    assert (Hi64 : (0 <= i < @Integers.zwordsize 64%positive)%Z) by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
    rewrite (@Integers.testbit_repr 32%positive _ i Hi).
    change (Z.testbit (@Integers.unsigned 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive io))) i)
      with (@Integers.testbit 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive io)) i).
    rewrite (@Integers.testbit_repr 64%positive _ i Hi64).
    change (Z.testbit (@Integers.unsigned 32%positive io) i) with (@Integers.testbit 32%positive io i); reflexivity.
Qed.

Lemma bool_to_bv1_eqb : forall (b1 b2 : bool),
  @Integers.eq 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive)
                          (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive) = Bool.eqb b1 b2.
Proof.
  intros [|] [|]; compute; reflexivity.
Qed.

Lemma bool_to_bv1_xor : forall (b1 b2 : bool),
  @Integers.xor 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive)
                           (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive) =
  (if xorb b1 b2 then @Integers.one 1%positive else @Integers.zero 1%positive).
Proof.
  intros [|] [|]; compute; reflexivity.
Qed.

Lemma subs_z_eq_iff : forall w (lhs rhs : @Integers.bit_int w),
  @Integers.eq w (@Integers.sub w lhs rhs) (@Integers.zero w) = @Integers.eq w lhs rhs.
Proof.
  intros w lhs rhs.
  destruct (@Integers.eq w (@Integers.sub w lhs rhs) (@Integers.zero w)) eqn:Es,
           (@Integers.eq w lhs rhs) eqn:Ee; try reflexivity.
  - pose proof (@Integers.eq_spec w (@Integers.sub w lhs rhs) (@Integers.zero w)) as Hs; rewrite Es in Hs.
    assert (Hu : @Integers.unsigned w lhs = @Integers.unsigned w rhs).
    { pose proof (@Integers.unsigned_range w lhs) as Hrl.
      pose proof (@Integers.unsigned_range w rhs) as Hrr.
      assert (Hm : ((@Integers.unsigned w lhs - @Integers.unsigned w rhs) mod @Integers.modulus w = 0)%Z).
      { unfold Integers.sub in Hs; apply (f_equal (@Integers.unsigned w)) in Hs.
        rewrite Integers.unsigned_repr_eq, Integers.unsigned_zero in Hs; exact Hs. }
      rewrite Z.mod_divide in Hm by (pose proof (@Integers.modulus_pos w); lia).
      destruct Hm as [q Hq]; destruct (Z.eq_dec q 0) as [-> | Hnz]; [lia |].
      exfalso; pose proof (@Integers.modulus_pos w); nia. }
    assert (Heq : lhs = rhs) by (rewrite <- (@Integers.repr_unsigned w lhs), <- (@Integers.repr_unsigned w rhs), Hu; reflexivity).
    subst rhs; rewrite Integers.eq_true in Ee; discriminate Ee.
  - pose proof (@Integers.eq_spec w lhs rhs) as He; rewrite Ee in He; subst rhs.
    rewrite Integers.sub_idem, Integers.eq_true in Es; discriminate Es.
Qed.

Lemma subs_n_xor_v_slt_iff : forall w (lhs rhs : @Integers.bit_int w),
  let res := @Integers.sub w lhs rhs in
  let sl := @Integers.lt w lhs (@Integers.zero w) in
  let sr := @Integers.lt w rhs (@Integers.zero w) in
  let sres := @Integers.lt w res (@Integers.zero w) in
  xorb sres (negb (Bool.eqb sl sr) && negb (Bool.eqb sl sres)) = @Integers.lt w lhs rhs.
Proof.
  intros w lhs rhs res sl sr sres.
  pose proof (@Integers.signed_range w lhs) as Hrl.
  pose proof (@Integers.signed_range w rhs) as Hrr.
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  unfold sl, sr, sres, res, Integers.lt; rewrite !Integers.signed_zero.
  destruct (zlt (@Integers.signed w lhs) 0%Z),
           (zlt (@Integers.signed w rhs) 0%Z),
           (zlt (@Integers.signed w lhs) (@Integers.signed w rhs));
    try lia; try (cbn [Bool.eqb negb andb]; destruct (zlt _ 0%Z); reflexivity).
  all: cbn [Bool.eqb negb andb];
       rewrite Integers.sub_signed, Integers.signed_repr
         by (unfold Integers.min_signed, Integers.max_signed in *; lia);
       destruct (zlt _ 0%Z); [lia || reflexivity | lia || reflexivity].
Qed.

Definition sym_flags_agree {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (sfl : a64_sym_flags) (fl : a64_flags) : Prop :=
  eval_closed_cert_expr penv foracle (asf_n sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_n fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  eval_closed_cert_expr penv foracle (asf_z sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_z fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  eval_closed_cert_expr penv foracle (asf_c sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_c fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  eval_closed_cert_expr penv foracle (asf_v sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_v fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  eval_closed_cert_expr penv foracle (asf_n_ne_v sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if xorb (af_n fl) (af_v fl) then @Integers.one 1%positive else @Integers.zero 1%positive))).

Lemma eval_a64_sym_is_neg_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v,
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    eval_closed_cert_expr penv foracle (a64_sym_is_neg w e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
      (if @Integers.lt w v (@Integers.zero w) then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle w e v He; unfold a64_sym_is_neg.
  apply (eval_ce_icmp_eq_bool _ _ CIP_Slt); [exact He | rewrite eval_ce_const, repr_zero_N; reflexivity].
Qed.

Lemma eval_a64_sym_bool_not_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle e (b : bool),
    eval_closed_cert_expr penv foracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (a64_sym_bool_not e) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if negb b then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle e b He; unfold a64_sym_bool_not.
  rewrite eval_ce_binop, He, eval_ce_const, repr_one_N; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.xor Integers.one Integers.zero].
  pose proof (bool_to_bv1_xor b true) as Hx; rewrite xorb_true_r in Hx; rewrite Hx; reflexivity.
Qed.

Lemma eval_a64_sym_bool_xor_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle e1 e2 (b1 b2 : bool),
    eval_closed_cert_expr penv foracle e1 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle e2 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (a64_sym_bool_xor e1 e2) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if xorb b1 b2 then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle e1 e2 b1 b2 H1 H2; unfold a64_sym_bool_xor.
  rewrite eval_ce_binop, H1, H2; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.xor Integers.one Integers.zero].
  rewrite bool_to_bv1_xor; reflexivity.
Qed.

Lemma eval_a64_sym_bool_eq_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle e1 e2 (b1 b2 : bool),
    eval_closed_cert_expr penv foracle e1 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle e2 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (a64_sym_bool_eq e1 e2) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if Bool.eqb b1 b2 then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle e1 e2 b1 b2 H1 H2; unfold a64_sym_bool_eq.
  rewrite (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ H1 H2), bool_to_bv1_eqb; reflexivity.
Qed.

Lemma eval_a64_sym_bool_and_or :
  forall {Pa : Params} (penv : param_env Pa) foracle e1 e2 (b1 b2 : bool),
    eval_closed_cert_expr penv foracle e1 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle e2 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (CE_BinOp CB_And 1%positive no_binop_flags e1 e2) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 && b2 then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
    eval_closed_cert_expr penv foracle (CE_BinOp CB_Or 1%positive no_binop_flags e1 e2) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 || b2 then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle e1 e2 b1 b2 H1 H2; split;
    rewrite eval_ce_binop, H1, H2; cbn [eou_bind];
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op];
    destruct b1, b2; reflexivity.
Qed.

Lemma eval_a64_sym_add_sub_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w is_sub lhs rhs vl vr,
    eval_closed_cert_expr penv foracle lhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w vl)) ->
    eval_closed_cert_expr penv foracle rhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w vr)) ->
    eval_closed_cert_expr penv foracle (fst (a64_sym_add_sub w is_sub lhs rhs)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (fst (a64_eval_add_sub w is_sub vl vr)))) /\
    sym_flags_agree penv foracle (snd (a64_sym_add_sub w is_sub lhs rhs))
                                 (snd (a64_eval_add_sub w is_sub vl vr)).
Proof.
  intros Pa penv foracle w is_sub lhs rhs vl vr Hl Hr.
  unfold a64_sym_add_sub, a64_eval_add_sub; cbn [fst snd].
  assert (Hres : eval_closed_cert_expr penv foracle
                   (CE_BinOp (if is_sub then CB_Sub else CB_Add) w no_binop_flags lhs rhs) =
                 raise_ret (DVALUE_Base (@DVALUE_I Pa w (if is_sub then @Integers.sub w vl vr else @Integers.add w vl vr)))).
  { rewrite eval_ce_binop, Hl, Hr; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct is_sub; reflexivity. }
  split; [exact Hres |].
  pose proof (eval_a64_sym_is_neg_sound _ _ _ _ _ Hres) as Hn.
  pose proof (eval_a64_sym_is_neg_sound _ _ _ _ _ Hl) as Hsl.
  pose proof (eval_a64_sym_is_neg_sound _ _ _ _ _ Hr) as Hsr.
  pose proof (eval_a64_sym_bool_eq_sound _ _ _ _ _ _ Hsl Hsr) as Heqlr.
  pose proof (eval_a64_sym_bool_xor_sound _ _ _ _ _ _ Hsl Hsr) as Hxorlr.
  pose proof (eval_a64_sym_bool_xor_sound _ _ _ _ _ _ Hsl Hn) as Hdif.
  repeat split; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v af_n af_z af_c af_v].
  - exact Hn.
  - destruct is_sub; cbn [af_z].
    + rewrite subs_z_eq_iff.
      exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hl Hr).
    + exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hres (eval_ce_const _ _ _ 0%N)).
  - destruct is_sub; cbn [af_c].
    + exact (eval_ce_icmp_eq_bool _ _ CIP_Uge _ _ _ _ _ Hl Hr).
    + exact (eval_ce_icmp_eq_bool _ _ CIP_Ult _ _ _ _ _ Hres Hl).
  - destruct is_sub; cbn [af_v].
    + destruct (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hxorlr Hdif) as [Ha _].
      destruct (@Integers.lt w vl (@Integers.zero w)),
               (@Integers.lt w vr (@Integers.zero w)),
               (@Integers.lt w (@Integers.sub w vl vr) (@Integers.zero w)); exact Ha.
    + destruct (eval_a64_sym_bool_and_or _ _ _ _ _ _ Heqlr Hdif) as [Ha _].
      destruct (@Integers.lt w vl (@Integers.zero w)),
               (@Integers.lt w vr (@Integers.zero w)),
               (@Integers.lt w (@Integers.add w vl vr) (@Integers.zero w)); exact Ha.
  - destruct is_sub; cbn [af_n af_v].
    + rewrite subs_n_xor_v_slt_iff.
      exact (eval_ce_icmp_eq_bool _ _ CIP_Slt _ _ _ _ _ Hl Hr).
    + destruct (eval_a64_sym_bool_and_or _ _ _ _ _ _ Heqlr Hdif) as [Ha _].
      pose proof (eval_a64_sym_bool_xor_sound _ _ _ _ _ _ Hn Ha) as Hnxv.
      destruct (@Integers.lt w (@Integers.add w vl vr) (@Integers.zero w)),
               (@Integers.lt w vl (@Integers.zero w)),
               (@Integers.lt w vr (@Integers.zero w)); exact Hnxv.
Qed.

Lemma eval_a64_sym_logic_flags_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w res v,
    eval_closed_cert_expr penv foracle res = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    sym_flags_agree penv foracle (a64_sym_logic_flags w res) (a64_eval_logic_flags w v).
Proof.
  intros Pa penv foracle w res v Hres; unfold a64_sym_logic_flags, a64_eval_logic_flags.
  pose proof (eval_a64_sym_is_neg_sound _ _ _ _ _ Hres) as Hn.
  pose proof (eval_ce_icmp_eq_bool _ _ CIP_Eq w res (CE_BvConst w 0%N) v (@Integers.zero w) Hres ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hz.
  unfold sym_flags_agree; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v af_n af_z af_c af_v].
  split; [exact Hn | split; [exact Hz | split; [rewrite eval_ce_const, repr_zero_N; reflexivity
        | split; [rewrite eval_ce_const, repr_zero_N; reflexivity | rewrite xorb_false_r; exact Hn]]]].
Qed.

Lemma eval_a64_sym_cond_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle c sfl fl,
    sym_flags_agree penv foracle sfl fl ->
    eval_closed_cert_expr penv foracle (a64_sym_cond c sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
      (if a64_eval_cond c fl then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle c sfl fl (Hn & Hz & Hc & Hv & Hnxv).
  destruct c; unfold a64_sym_cond, a64_eval_cond.
  - exact Hz.
  - exact (eval_a64_sym_bool_not_sound _ _ _ _ Hz).
  - exact Hc.
  - exact (eval_a64_sym_bool_not_sound _ _ _ _ Hc).
  - exact Hn.
  - exact (eval_a64_sym_bool_not_sound _ _ _ _ Hn).
  - exact Hv.
  - exact (eval_a64_sym_bool_not_sound _ _ _ _ Hv).
  - pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hz) as Hnz.
    exact (proj1 (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hc Hnz)).
  - pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hc) as Hnc.
    exact (proj2 (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hnc Hz)).
  - pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hnxv) as Hn_eq_v.
    destruct (af_n fl), (af_v fl); exact Hn_eq_v.
  - exact Hnxv.
  - pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hz) as Hnz.
    pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hnxv) as Hn_eq_v.
    destruct (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hnz Hn_eq_v) as [Ha _].
    destruct (af_z fl), (af_n fl), (af_v fl); exact Ha.
  - exact (proj2 (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hz Hnxv)).
  - rewrite eval_ce_const, repr_one_N; reflexivity.
  - rewrite eval_ce_const, repr_one_N; reflexivity.
Qed.

Lemma eval_a64_sym_flags_imm4_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle nzcv,
    sym_flags_agree penv foracle (a64_sym_flags_of_imm4 nzcv) (a64_flags_of_imm4 nzcv).
Proof.
  intros Pa penv foracle nzcv; unfold a64_sym_flags_of_imm4, a64_flags_of_imm4, sym_flags_agree;
    cbn [asf_n asf_z asf_c asf_v asf_n_ne_v af_n af_z af_c af_v];
    repeat split; rewrite eval_ce_const;
    [ destruct (N.testbit nzcv 3%N)
    | destruct (N.testbit nzcv 2%N)
    | destruct (N.testbit nzcv 1%N)
    | destruct (N.testbit nzcv 0%N)
    | destruct (xorb (N.testbit nzcv 3%N) (N.testbit nzcv 0%N)) ];
    try rewrite repr_one_N; try rewrite repr_zero_N; reflexivity.
Qed.

Lemma eval_a64_sym_ite_flags_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle c (b : bool) st sf tfl ffl,
    eval_closed_cert_expr penv foracle c =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    sym_flags_agree penv foracle st tfl ->
    sym_flags_agree penv foracle sf ffl ->
    sym_flags_agree penv foracle (a64_sym_ite_flags c st sf) (if b then tfl else ffl).
Proof.
  intros Pa penv foracle c b st sf tfl ffl Hc
    (Htn & Htz & Htc & Htv & Htnxv) (Hfn & Hfz & Hfc & Hfv & Hfnxv).
  unfold a64_sym_ite_flags, sym_flags_agree;
    cbn [asf_n asf_z asf_c asf_v asf_n_ne_v].
  repeat split;
    [ pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htn Hfn) as H
    | pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htz Hfz) as H
    | pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htc Hfc) as H
    | pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htv Hfv) as H
    | pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htnxv Hfnxv) as H ];
    destruct b; exact H.
Qed.

Lemma eval_a64_sym_shift_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v sh amt,
    (w = 32%positive \/ w = 64%positive) ->
    (amt < N.pos w)%N ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    eval_closed_cert_expr penv foracle (a64_sym_shift w e sh amt) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_shift w v sh amt))).
Proof.
  intros Pa penv foracle w e v sh amt Hw Hamt He.
  unfold a64_sym_shift, a64_eval_shift.
  assert (Hmod : N.modulo amt (N.pos w) = amt) by (apply N.mod_small; exact Hamt).
  assert (HmodZ : (Z.of_N amt mod Z.pos w = Z.of_N amt)%Z) by (apply Z.mod_small; lia).
  rewrite Hmod, HmodZ.
  pose proof (mod_lt_32_64 w Hw) as Hm3264.
  destruct sh; destruct (N.eqb amt 0%N) eqn:Ez.
  - apply N.eqb_eq in Ez; subst amt; rewrite He;
      change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shl_zero; reflexivity.
  - rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.of_N].
    rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
    replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity.
  - apply N.eqb_eq in Ez; subst amt; rewrite He;
      change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shru_zero; reflexivity.
  - rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.of_N].
    rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
    replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity.
  - apply N.eqb_eq in Ez; subst amt; rewrite He;
      change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shr_zero; reflexivity.
  - rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shr Integers.unsigned Integers.repr Z.geb Z.of_N].
    rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
    replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity.
  - exact He.
  - apply N.eqb_neq in Ez.
    assert (H1 : eval_closed_cert_expr penv foracle (CE_BinOp CB_LShr w no_binop_flags e (CE_BvConst w amt)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shru w v (@Integers.repr w (Z.of_N amt)))))).
    { rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.of_N].
      rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
      replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity. }
    assert (H2 : eval_closed_cert_expr penv foracle (CE_BinOp CB_Shl w no_binop_flags e (CE_BvConst w (N.pos w - amt))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shl w v (@Integers.repr w (Z.pos w - Z.of_N amt)))))).
    { set (d := (N.pos w - amt)%N).
      assert (HdZ : Z.of_N d = (Z.pos w - Z.of_N amt)%Z) by (unfold d; lia).
      rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [d N.sub Z.sub Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.of_N].
      rewrite HdZ, (@Integers.unsigned_repr w (Z.pos w - Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
      replace (Z.pos w - Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity. }
    rewrite eval_ce_binop, H1, H2; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
Qed.

Lemma eval_a64_sym_extend_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w e64 v64 ext amt,
    (w = 32%positive \/ w = 64%positive) ->
    (amt <= 4)%N ->
    eval_closed_cert_expr penv foracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (a64_sym_extend w e64 ext amt) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_extend w v64 ext amt))).
Proof.
  intros Pa penv foracle w e64 v64 ext amt Hw Hamt He64.
  unfold a64_sym_extend, a64_eval_extend.
  destruct (a64_ext_bits ext) as [src_bits sgn].
  remember (Pos.min src_bits w) as eff eqn:Heff.
  assert (Hle64 : (eff <= 64)%positive)
    by (rewrite Heff; destruct Hw as [-> | ->]; [pose proof (Pos.le_min_r src_bits 32%positive) | pose proof (Pos.le_min_r src_bits 64%positive)]; lia).
  assert (Hsl : eval_closed_cert_expr penv foracle
    (if Pos.eqb eff 64%positive then e64
     else if Pos.eqb eff 32%positive then a64_sym_trunc32 e64
     else CE_Cast CCK_Trunc 64%positive eff no_cast_flags e64) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa eff (@Integers.repr eff (@Integers.unsigned 64%positive v64))))).
  { destruct (Pos.eqb eff 64%positive) eqn:E64.
    - apply Pos.eqb_eq in E64; clear Heff; subst eff; rewrite He64; do 3 f_equal; symmetry; apply (@Integers.repr_unsigned 64%positive).
    - destruct (Pos.eqb eff 32%positive) eqn:E32.
      + apply Pos.eqb_eq in E32; clear Heff; subst eff; exact (eval_a64_sym_trunc32_sound _ _ _ _ He64).
      + apply eval_ce_trunc; [| exact He64].
        apply Pos.ltb_lt; apply Pos.eqb_neq in E64; lia. }
  set (sl_e := if Pos.eqb eff 64%positive then e64
               else if Pos.eqb eff 32%positive then a64_sym_trunc32 e64
               else CE_Cast CCK_Trunc 64%positive eff no_cast_flags e64) in *.
  set (sl_v := @Integers.repr eff (@Integers.unsigned 64%positive v64)) in *.
  assert (Hext : eval_closed_cert_expr penv foracle
    (if Pos.eqb eff w then sl_e else CE_Cast (if sgn then CCK_SExt else CCK_ZExt) eff w no_cast_flags sl_e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w
      (if Pos.eqb eff w then @Integers.repr w (@Integers.unsigned eff sl_v)
       else if sgn then @Integers.repr w (@Integers.signed eff sl_v)
       else @Integers.repr w (@Integers.unsigned eff sl_v))))).
  { destruct (Pos.eqb eff w) eqn:Eew.
    - apply Pos.eqb_eq in Eew; clear Heff; subst sl_e sl_v; subst eff; rewrite Hsl; do 3 f_equal; symmetry; apply (@Integers.repr_unsigned w).
    - assert (Hltw : (eff <? w)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.eqb_neq in Eew; rewrite Heff in *; pose proof (Pos.le_min_r src_bits w); lia).
      destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; assumption. }
  destruct (N.eqb amt 0%N) eqn:Ez; [exact Hext |].
  pose proof (mod_lt_32_64 w Hw) as Hm3264.
  assert (Hamtm : N.modulo amt (N.pos w) = amt /\ (Z.of_N amt mod Z.pos w = Z.of_N amt)%Z)
    by (split; [apply N.mod_small | apply Z.mod_small]; destruct Hw as [-> | ->]; lia).
  destruct Hamtm as [HmN HmZ]; rewrite HmN, HmZ.
  rewrite eval_ce_binop, Hext, eval_ce_const; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  cbn - [Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.of_N].
  rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; destruct Hw as [-> | ->]; lia).
  replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; destruct Hw as [-> | ->]; lia).
  reflexivity.
Qed.

Lemma a64_sxtw_bitfield_eq : forall v : @Integers.bit_int 64%positive,
  @Integers.shr 64%positive
    (@Integers.shl 64%positive v (@Integers.repr 64%positive 32%Z))
    (@Integers.repr 64%positive 32%Z) =
  @Integers.repr 64%positive (@Integers.signed 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v))).
Proof.
  intro v; apply Integers.same_bits_eq; intros i Hi.
  assert (Hi64 : (0 <= i < 64)%Z) by (replace 64%Z with (@Integers.zwordsize 64%positive) by reflexivity; exact Hi).
  assert (Hu32 : @Integers.unsigned 64%positive (@Integers.repr 64%positive 32%Z) = 32%Z)
    by (apply Integers.unsigned_repr; compute; split; discriminate).
  rewrite Integers.bits_shr by exact Hi.
  rewrite Hu32, (@Integers.testbit_repr 64%positive _ i Hi), Integers.bits_signed
    by (change (@Integers.zwordsize 32%positive) with 32%Z; lia).
  change (@Integers.zwordsize 32%positive) with 32%Z in *.
  change (@Integers.zwordsize 64%positive) with 64%Z in *.
  destruct (zlt (i + 32) 64) as [Hl | Hge]; destruct (zlt i 32) as [Hli | Hgi]; try lia.
  - rewrite Integers.bits_shl by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
    rewrite Hu32; destruct (zlt (i + 32) 32); [lia |].
    replace (i + 32 - 32)%Z with i by lia.
    rewrite (@Integers.testbit_repr 32%positive _ i ltac:(change (@Integers.zwordsize 32%positive) with 32%Z; lia)); reflexivity.
  - rewrite Integers.bits_shl by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
    rewrite Hu32; replace (64 - 1)%Z with 63%Z by lia; destruct (zlt 63 32); [lia |].
    replace (63 - 32)%Z with 31%Z by lia; replace (32 - 1)%Z with 31%Z by lia.
    rewrite (@Integers.testbit_repr 32%positive (@Integers.unsigned 64%positive v) 31%Z ltac:(change (@Integers.zwordsize 32%positive) with 32%Z; lia)); reflexivity.
Qed.

Lemma a64_uxtw_bitfield_eq : forall v : @Integers.bit_int 64%positive,
  @Integers.and 64%positive
    (@Integers.shru 64%positive v (@Integers.repr 64%positive 0%Z))
    (@Integers.repr 64%positive (Z.of_N (N.ones 32%N))) =
  @Integers.repr 64%positive (@Integers.unsigned 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v))).
Proof.
  intro v; change (@Integers.repr 64%positive 0%Z) with (@Integers.zero 64%positive).
  rewrite Integers.shru_zero; apply Integers.same_bits_eq; intros i Hi.
  assert (Hi64 : (0 <= i < 64)%Z) by (replace 64%Z with (@Integers.zwordsize 64%positive) by reflexivity; exact Hi).
  rewrite Integers.bits_and, (@Integers.testbit_repr 64%positive _ i Hi), (@Integers.testbit_repr 64%positive _ i Hi) by exact Hi.
  change (Z.testbit (@Integers.unsigned 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v))) i)
    with (@Integers.testbit 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v)) i).
  replace (Z.of_N (N.ones 32%N)) with (Z.ones 32%Z) by reflexivity.
  destruct (Z.ltb i 32) eqn:Ei32.
  - apply Z.ltb_lt in Ei32; rewrite Z.ones_spec_low by lia; rewrite andb_true_r.
    rewrite (@Integers.testbit_repr 32%positive _ i ltac:(change (@Integers.zwordsize 32%positive) with 32%Z; lia)); reflexivity.
  - apply Z.ltb_ge in Ei32; rewrite Z.ones_spec_high by lia; rewrite andb_false_r.
    rewrite Integers.bits_above by (change (@Integers.zwordsize 32%positive) with 32%Z; lia); reflexivity.
Qed.

Lemma shamt_eval_const_lt :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v k,
    (w = 32%positive \/ w = 64%positive) ->
    (k < N.pos w)%N ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    (forall op, (op = CB_Shl \/ op = CB_LShr \/ op = CB_AShr) ->
      eval_closed_cert_expr penv foracle (CE_BinOp op w no_binop_flags e (CE_BvConst w k)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (match op with
         | CB_Shl => @Integers.shl w v (@Integers.repr w (Z.of_N k))
         | CB_LShr => @Integers.shru w v (@Integers.repr w (Z.of_N k))
         | _ => @Integers.shr w v (@Integers.repr w (Z.of_N k))
         end)))).
Proof.
  intros Pa penv foracle w e v k Hw Hk He op Hop.
  pose proof (mod_lt_32_64 w Hw) as Hm.
  assert (Hlt : (Z.of_N k < Z.pos w)%Z) by lia.
  rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  destruct Hop as [-> | [-> | ->]];
    cbn - [Integers.shl Integers.shru Integers.shr Integers.unsigned Integers.repr Z.geb Z.gtb Z.of_N];
    rewrite (@Integers.unsigned_repr w (Z.of_N k)) by (unfold Integers.max_unsigned; lia);
    replace (Z.of_N k >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity.
Qed.

Lemma eval_a64_sym_bitfield_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle sf kind src dst vsrc vdst immr imms,
    (immr < a64_w_N sf)%N ->
    (imms < a64_w_N sf)%N ->
    eval_closed_cert_expr penv foracle src = raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) vsrc)) ->
    eval_closed_cert_expr penv foracle dst = raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) vdst)) ->
    eval_closed_cert_expr penv foracle (a64_sym_bitfield (a64_w sf) kind src dst immr imms) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_eval_bitfield (a64_w sf) kind vsrc vdst immr imms))).
Proof.
  intros Pa penv foracle sf kind src dst vsrc vdst immr imms Hlr Hls Hsrc Hdst.
  set (w := a64_w sf) in *; set (wn := N.pos w) in *.
  assert (Hwn : wn = a64_w_N sf) by (destruct sf; reflexivity).
  assert (Hw3264 : w = 32%positive \/ w = 64%positive) by (destruct sf; auto).
  assert (Hmr : (Z.of_N immr mod Z.pos w = Z.of_N immr)%Z) by (apply Z.mod_small; lia).
  unfold a64_sym_bitfield, a64_eval_bitfield; fold w wn.
  rewrite Hmr.
  destruct (N.leb immr imms) eqn:Ele.
  - apply N.leb_le in Ele.
    set (len := (imms - immr + 1%N)%N).
    assert (Hlen_pos : (1 <= len <= wn)%N) by (unfold len; lia).
    assert (Hshr : eval_closed_cert_expr penv foracle
      (if N.eqb immr 0%N then src else CE_BinOp CB_LShr w no_binop_flags src (CE_BvConst w immr)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shru w vsrc (@Integers.repr w (Z.of_N immr)))))).
    { destruct (N.eqb immr 0%N) eqn:Ez.
      - apply N.eqb_eq in Ez; subst immr; rewrite Hsrc;
          change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shru_zero; reflexivity.
      - apply (shamt_eval_const_lt penv foracle w src vsrc immr Hw3264 ltac:(lia) Hsrc CB_LShr (or_intror (or_introl eq_refl))). }
    destruct kind.
    + (* ABF_Sbfm *)
      assert (Hgen : eval_closed_cert_expr penv foracle
        (let shl_a := (wn - 1%N - imms)%N in
         let shr_a := (wn - len)%N in
         let sl := if N.eqb shl_a 0%N then src else CE_BinOp CB_Shl w no_binop_flags src (CE_BvConst w shl_a) in
         if N.eqb shr_a 0%N then sl else CE_BinOp CB_AShr w no_binop_flags sl (CE_BvConst w shr_a)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.shr w (@Integers.shl w vsrc (@Integers.repr w (Z.of_N ((wn - 1%N - imms) mod wn))))
                           (@Integers.repr w (Z.of_N ((wn - len) mod wn))))))).
      { assert (Hshl_m : ((wn - 1 - imms) mod wn = wn - 1 - imms)%N) by (apply N.mod_small; lia).
        assert (Hshr_m : ((wn - len) mod wn = wn - len)%N) by (apply N.mod_small; lia).
        rewrite Hshl_m, Hshr_m.
        assert (Hsl : eval_closed_cert_expr penv foracle
          (if N.eqb (wn - 1 - imms) 0%N then src else CE_BinOp CB_Shl w no_binop_flags src (CE_BvConst w (wn - 1 - imms))) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shl w vsrc (@Integers.repr w (Z.of_N (wn - 1 - imms))))))).
        { destruct (N.eqb (wn - 1 - imms) 0%N) eqn:E0.
          - apply N.eqb_eq in E0; rewrite E0, Hsrc;
              change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shl_zero; reflexivity.
          - apply (shamt_eval_const_lt penv foracle w src vsrc (wn - 1 - imms) Hw3264 ltac:(lia) Hsrc CB_Shl (or_introl eq_refl)). }
        cbv zeta; destruct (N.eqb (wn - len) 0%N) eqn:E0'.
        - apply N.eqb_eq in E0'; rewrite E0', Hsl;
            change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shr_zero; reflexivity.
        - apply (shamt_eval_const_lt penv foracle w _ _ (wn - len) Hw3264 ltac:(lia) Hsl CB_AShr (or_intror (or_intror eq_refl))). }
      destruct (Pos.eqb w 64%positive && N.eqb immr 0%N && N.eqb imms 31%N) eqn:Esxtw; [| exact Hgen].
      rewrite !andb_true_iff in Esxtw; destruct Esxtw as ([Ew64 Er0] & Es31).
      apply Pos.eqb_eq in Ew64; apply N.eqb_eq in Er0; apply N.eqb_eq in Es31.
      destruct sf; [| discriminate Ew64].
      subst immr imms; clear Hlr Hls Ele; cbn [wn len].
      rewrite (eval_ce_sext _ _ 32%positive 64%positive _ _ eq_refl (eval_a64_sym_trunc32_sound _ _ _ _ Hsrc)).
      rewrite <- a64_sxtw_bitfield_eq; reflexivity.
    + (* ABF_Bfm *)
      assert (Hlow : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And w no_binop_flags
          (if N.eqb immr 0%N then src else CE_BinOp CB_LShr w no_binop_flags src (CE_BvConst w immr))
          (CE_BvConst w (N.ones len))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.and w (@Integers.shru w vsrc (@Integers.repr w (Z.of_N immr)))
                           (@Integers.repr w (Z.of_N (N.ones len))))))).
      { rewrite eval_ce_binop, Hshr, eval_ce_const; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      assert (Hkept : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And w no_binop_flags dst (a64_sym_not w (CE_BvConst w (N.ones len)))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.and w vdst (@Integers.not w (@Integers.repr w (Z.of_N (N.ones len)))))))).
      { rewrite eval_ce_binop, Hdst, (eval_ce_not _ _ w _ _ (eval_ce_const _ _ _ _)); cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      rewrite eval_ce_binop, Hkept, Hlow; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
    + (* ABF_Ubfm *)
      assert (Hlow : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And w no_binop_flags
          (if N.eqb immr 0%N then src else CE_BinOp CB_LShr w no_binop_flags src (CE_BvConst w immr))
          (CE_BvConst w (N.ones len))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.and w (@Integers.shru w vsrc (@Integers.repr w (Z.of_N immr)))
                           (@Integers.repr w (Z.of_N (N.ones len))))))).
      { rewrite eval_ce_binop, Hshr, eval_ce_const; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      assert (Hmask_all : forall x : @Integers.bit_int w,
        len = wn -> @Integers.and w x (@Integers.repr w (Z.of_N (N.ones len))) = x).
      { intros x Hlw; rewrite Hlw; apply Integers.same_bits_eq; intros i Hi.
        rewrite Integers.bits_and, (@Integers.testbit_repr w _ i Hi) by exact Hi.
        replace (Z.of_N (N.ones wn)) with (Z.ones (Z.pos w)) by (unfold wn; rewrite Z.ones_equiv, N2Z.inj_pos || idtac; destruct Hw3264 as [-> | ->]; reflexivity).
        rewrite Z.ones_spec_low by (destruct Hw3264 as [-> | ->]; change (@Integers.zwordsize 32%positive) with 32%Z in Hi; change (@Integers.zwordsize 64%positive) with 64%Z in Hi; lia).
        rewrite andb_true_r; reflexivity. }
      destruct (N.eqb len wn) eqn:Ewn.
      { apply N.eqb_eq in Ewn; assert (Hr0 : immr = 0%N) by (unfold len in Ewn; lia).
        rewrite Hr0; change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w);
          rewrite Integers.shru_zero, Hmask_all by exact Ewn; exact Hsrc. }
      destruct (N.eqb imms (wn - 1%N)) eqn:Etop.
      { apply N.eqb_eq in Etop; rewrite Hshr; do 3 f_equal; symmetry.
        apply Integers.same_bits_eq; intros i Hi.
        assert (Hzw : @Integers.zwordsize w = Z.pos w) by (destruct Hw3264 as [-> | ->]; reflexivity).
        rewrite Integers.bits_and, (@Integers.testbit_repr w _ i Hi) by exact Hi.
        destruct (Z.ltb i (Z.of_N len)) eqn:Eil.
        - apply Z.ltb_lt in Eil.
          assert (Htb : Z.testbit (Z.of_N (N.ones len)) i = true).
          { rewrite <- (Z2N.id i ltac:(lia)), N2Z.inj_testbit, N.ones_spec_low by lia; reflexivity. }
          rewrite Htb, andb_true_r; reflexivity.
        - apply Z.ltb_ge in Eil; rewrite Integers.bits_shru by (rewrite Hzw in Hi |- *; lia).
          assert (Himmr_lt : (immr < N.pos w)%N) by (unfold w, a64_w, a64_w_N in *; destruct sf; lia).
          rewrite (@Integers.unsigned_repr w (Z.of_N immr))
            by (unfold Integers.max_unsigned; destruct Hw3264 as [-> | ->];
                [change (@Integers.modulus 32%positive) with (2 ^ 32)%Z | change (@Integers.modulus 64%positive) with (2 ^ 64)%Z]; lia).
          assert (Htb : Z.testbit (Z.of_N (N.ones len)) i = false)
            by (rewrite <- (Z2N.id i ltac:(lia)), N2Z.inj_testbit, N.ones_spec_high by lia; reflexivity).
          rewrite Htb, andb_false_r.
          assert (Hge : (i + Z.of_N immr >= Z.pos w)%Z) by (unfold len in Eil; rewrite Etop in Eil; lia).
          destruct (zlt (i + Z.of_N immr) (@Integers.zwordsize w)); [lia | reflexivity]. }
      destruct (Pos.eqb w 64%positive && N.eqb immr 0%N && N.eqb imms 31%N) eqn:Euxtw; [| exact Hlow].
      rewrite !andb_true_iff in Euxtw; destruct Euxtw as ([Ew64 Er0] & Es31).
      apply Pos.eqb_eq in Ew64; apply N.eqb_eq in Er0; apply N.eqb_eq in Es31.
      destruct sf; [| discriminate Ew64].
      subst immr imms; clear Hlr Hls Ele Ewn Etop; cbn [wn len].
      rewrite (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl (eval_a64_sym_trunc32_sound _ _ _ _ Hsrc)).
      rewrite <- a64_uxtw_bitfield_eq; reflexivity.
  - (* imms < immr *)
    apply N.leb_gt in Ele.
    set (pos := (wn - immr)%N); set (len := (imms + 1%N)%N).
    assert (Hpos_m : (pos mod wn = pos)%N) by (unfold pos; apply N.mod_small; lia).
    rewrite Hpos_m.
    assert (Hlow : eval_closed_cert_expr penv foracle (CE_BinOp CB_And w no_binop_flags src (CE_BvConst w (N.ones len))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.and w vsrc (@Integers.repr w (Z.of_N (N.ones len))))))).
    { rewrite eval_ce_binop, Hsrc, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
    destruct kind.
    + (* ABF_Sbfm *)
      assert (Hsex_m : ((wn - len) mod wn = wn - len)%N) by (apply N.mod_small; unfold len; lia).
      rewrite Hsex_m.
      pose proof (shamt_eval_const_lt penv foracle w src vsrc (wn - len) Hw3264 ltac:(unfold len; lia) Hsrc CB_Shl (or_introl eq_refl)) as Hs1.
      pose proof (shamt_eval_const_lt penv foracle w _ _ (wn - len) Hw3264 ltac:(unfold len; lia) Hs1 CB_AShr (or_intror (or_intror eq_refl))) as Hs2.
      exact (shamt_eval_const_lt penv foracle w _ _ pos Hw3264 ltac:(unfold pos; lia) Hs2 CB_Shl (or_introl eq_refl)).
    + (* ABF_Bfm *)
      pose proof (shamt_eval_const_lt penv foracle w _ _ pos Hw3264 ltac:(unfold pos; lia) (eval_ce_const penv foracle w (N.ones len)) CB_Shl (or_introl eq_refl)) as Hmask.
      pose proof (eval_ce_not penv foracle w _ _ Hmask) as Hnmask.
      assert (Hkept : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And w no_binop_flags dst (a64_sym_not w (CE_BinOp CB_Shl w no_binop_flags (CE_BvConst w (N.ones len)) (CE_BvConst w pos)))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.and w vdst (@Integers.not w (@Integers.shl w (@Integers.repr w (Z.of_N (N.ones len))) (@Integers.repr w (Z.of_N pos)))))))).
      { rewrite eval_ce_binop, Hdst, Hnmask; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      pose proof (shamt_eval_const_lt penv foracle w _ _ pos Hw3264 ltac:(unfold pos; lia) Hlow CB_Shl (or_introl eq_refl)) as Hins.
      rewrite eval_ce_binop, Hkept, Hins; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
    + (* ABF_Ubfm *)
      exact (shamt_eval_const_lt penv foracle w _ _ pos Hw3264 ltac:(unfold pos; lia) Hlow CB_Shl (or_introl eq_refl)).
Qed.

Lemma eval_a64_sym_extr_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w hi lo vhi vlo lsb,
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle hi = raise_ret (DVALUE_Base (@DVALUE_I Pa w vhi)) ->
    eval_closed_cert_expr penv foracle lo = raise_ret (DVALUE_Base (@DVALUE_I Pa w vlo)) ->
    eval_closed_cert_expr penv foracle (a64_sym_extr w hi lo lsb) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_extr w vhi vlo lsb))).
Proof.
  intros Pa penv foracle w hi lo vhi vlo lsb Hw Hhi Hlo.
  unfold a64_sym_extr, a64_eval_extr.
  set (m := N.modulo lsb (N.pos w)).
  assert (Hm_lt : (m < N.pos w)%N) by (unfold m; apply N.mod_lt; discriminate).
  destruct (N.eqb m 0%N) eqn:Ez; [exact Hlo | apply N.eqb_neq in Ez].
  pose proof (shamt_eval_const_lt penv foracle w lo vlo m Hw Hm_lt Hlo CB_LShr (or_intror (or_introl eq_refl))) as Hshr.
  pose proof (shamt_eval_const_lt penv foracle w hi vhi (N.pos w - m) Hw ltac:(lia) Hhi CB_Shl (or_introl eq_refl)) as Hshl.
  rewrite eval_ce_binop, Hshr, Hshl; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  replace (Z.of_N (N.pos w - m)) with (Z.pos w - Z.of_N m)%Z by lia; reflexivity.
Qed.

Lemma eval_a64_sym_div_guarded_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle is_signed w a b va vb,
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa w vb)) ->
    eval_closed_cert_expr penv foracle (a64_sym_div_guarded is_signed w a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w
      (if is_signed then a64_divs_total w va vb else a64_divu_total w va vb))).
Proof.
  intros Pa penv foracle is_signed w a b va vb Hw Ha Hb.
  assert (Hzw : (@Integers.zwordsize w > 1)%Z)
    by (destruct Hw as [-> | ->];
        [replace (@Integers.zwordsize 32%positive) with 32%Z by reflexivity
        | replace (@Integers.zwordsize 64%positive) with 64%Z by reflexivity]; lia).
  set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
  destruct is_signed; cbn [a64_sym_div_guarded]; fold is_z.
  - (* signed *)
    set (imin := ce_int_min w).
    set (is_ovf := CE_BinOp CB_And 1%positive no_binop_flags
                     (CE_ICmp CIP_Eq false w a imin)
                     (CE_ICmp CIP_Eq false w b (ce_all_ones w))).
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
      cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct (@Integers.eq w va (@Integers.repr w (@Integers.min_signed w))) eqn:Ea,
               (@Integers.eq w vb (@Integers.mone w)) eqn:Eb,
               (Z.eqb (@Integers.signed w va) (@Integers.min_signed w)) eqn:Esa,
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
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if (cz || co)%bool then @Integers.one 1%positive else @Integers.zero 1%positive))))
      by exact (proj2 (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hisz Hovf)).
    assert (Hsa : eval_closed_cert_expr penv foracle (CE_Select w is_ovf (CE_BvConst w 0%N) a) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if co then @Integers.zero w else va))))
      by (eapply eval_ce_select_int; [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Ha]).
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if (cz || co)%bool then @Integers.one w else vb))))
      by (eapply eval_ce_select_int; [exact Hbad | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]).
    assert (Hsdiv : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_SDiv w no_binop_flags (CE_Select w is_ovf (CE_BvConst w 0%N) a)
        (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.divs w (if co then @Integers.zero w else va) (if (cz || co)%bool then @Integers.one w else vb))))).
    { rewrite eval_ce_binop, Hsa, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.signed Integers.min_signed Integers.divs Z.eqb].
      destruct (cz || co)%bool eqn:Ebc.
      - rewrite (@Integers.signed_one w) by exact Hzw; cbn [Z.eqb]; rewrite andb_false_r; reflexivity.
      - apply orb_false_iff in Ebc as [Hcz Hco]; unfold cz in Hcz; rewrite Hcz, Hco.
        rewrite (Z.eqb_sym (@Integers.min_signed w) (@Integers.signed w va)); unfold co in Hco; rewrite Hco; reflexivity. }
    unfold a64_divs_total; fold cz co.
    assert (Hzc : eval_closed_cert_expr penv foracle (CE_BvConst w 0%N) = raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
      by (rewrite eval_ce_const, repr_zero_N; reflexivity).
    destruct cz; [eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hisz | exact Hzc | eapply eval_ce_select_int; [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]] |].
    destruct co; [eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact Hzc | eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]]
                 | eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact Hzc | eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]]].
  - (* unsigned *)
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if @Integers.eq w vb (@Integers.zero w) then @Integers.one 1%positive else @Integers.zero 1%positive))))
      by (unfold is_z; apply (eval_ce_icmp_eq_bool _ _ CIP_Eq); [exact Hb | rewrite eval_ce_const, repr_zero_N; reflexivity]).
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w is_z (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if @Integers.eq w vb (@Integers.zero w) then @Integers.one w else vb))))
      by (eapply eval_ce_select_int; [exact Hisz | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]).
    assert (Hzc : eval_closed_cert_expr penv foracle (CE_BvConst w 0%N) = raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
      by (rewrite eval_ce_const, repr_zero_N; reflexivity).
    unfold a64_divu_total.
    destruct (@Integers.eq w vb (@Integers.zero w)) eqn:Ez.
    + apply integers_eq_zero_iff in Ez; rewrite Ez; cbn [Z.eqb].
      unfold a64_sym_div_guarded; cbn [negb]; fold is_z.
      eapply (eval_ce_select_int _ _ _ _ _ _ true); [rewrite Hisz; reflexivity | exact Hzc |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.divu Integers.unsigned]; rewrite (@Integers.unsigned_one w); reflexivity.
    + assert (Hnz : (@Integers.unsigned w vb =? 0)%Z = false)
        by (destruct (Z.eqb (@Integers.unsigned w vb) 0%Z) eqn:Eb; [apply Z.eqb_eq, integers_eq_zero_iff in Eb; congruence | reflexivity]).
      rewrite Hnz.
      unfold a64_sym_div_guarded; cbn [negb]; fold is_z.
      eapply (eval_ce_select_int _ _ _ _ _ _ false); [rewrite Hisz; reflexivity | exact Hzc |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.divu Integers.unsigned]; rewrite Hnz; reflexivity.
Qed.

Lemma eval_a64_sym_dp2_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w op lhs rhs vl vr,
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle lhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w vl)) ->
    eval_closed_cert_expr penv foracle rhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w vr)) ->
    eval_closed_cert_expr penv foracle (a64_sym_dp2 w op lhs rhs) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_dp2 w op vl vr))).
Proof.
  intros Pa penv foracle w op lhs rhs vl vr Hw Hl Hr.
  unfold a64_sym_dp2, a64_eval_dp2.
  assert (Hsh : eval_closed_cert_expr penv foracle
    (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.land (@Integers.unsigned w vr) (Z.pos w - 1)))))).
  { rewrite eval_ce_binop, Hr, eval_ce_const; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct Hw as [-> | ->]; cbn - [Integers.and Integers.unsigned Integers.repr Z.land]; unfold Integers.and;
      [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
      | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)]; reflexivity. }
  destruct (land_mask_w_mod w vr Hw) as [Hsh_eq Hsh_lt].
  destruct op.
  - exact (eval_a64_sym_div_guarded_sound _ _ false _ _ _ _ _ Hw Hl Hr).
  - exact (eval_a64_sym_div_guarded_sound _ _ true _ _ _ _ _ Hw Hl Hr).
  - rewrite eval_ce_binop, Hl, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    unfold a64_eval_dp2; cbn - [Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.land Z.sub].
    rewrite Hsh_lt, Hsh_eq; reflexivity.
  - rewrite eval_ce_binop, Hl, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    unfold a64_eval_dp2; cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.land Z.sub].
    rewrite Hsh_lt, Hsh_eq; reflexivity.
  - rewrite eval_ce_binop, Hl, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    unfold a64_eval_dp2; cbn - [Integers.shr Integers.unsigned Integers.repr Z.geb Z.land Z.sub].
    rewrite Hsh_lt, Hsh_eq; reflexivity.
  - (* ADP2_Rorv *)
    assert (Hsub : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w))
        (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1))))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.sub w (@Integers.repr w (Z.pos w)) (rv_mask_shamt w (@Integers.unsigned w vr)))))).
    { rewrite eval_ce_binop, eval_ce_const, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn [eval_int_op cert_to_ibinop]; rewrite Hsh_eq; reflexivity. }
    assert (Hinv : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And w no_binop_flags
        (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w))
          (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
        (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.repr w (Z.land (@Integers.unsigned w (@Integers.sub w (@Integers.repr w (Z.pos w)) (rv_mask_shamt w (@Integers.unsigned w vr)))) (Z.pos w - 1)))))).
    { rewrite eval_ce_binop, Hsub, eval_ce_const; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      destruct Hw as [-> | ->]; cbn - [Integers.and Integers.unsigned Integers.repr Z.land]; unfold Integers.and;
        [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
        | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)]; reflexivity. }
    set (shv := rv_mask_shamt w (@Integers.unsigned w vr)) in *.
    set (inv_sub := @Integers.sub w (@Integers.repr w (Z.pos w)) shv) in *.
    destruct (land_mask_w_mod w inv_sub Hw) as [Hi_eq Hi_lt].
    assert (Heq_inv : rv_mask_shamt w (@Integers.unsigned w inv_sub) = rv_mask_shamt w (Z.pos w - @Integers.unsigned w shv)).
    { unfold inv_sub, rv_mask_shamt, Integers.sub; pose proof (mod_lt_32_64 w Hw) as Hm.
      rewrite (@Integers.unsigned_repr w (Z.pos w)) by (unfold Integers.max_unsigned; lia).
      rewrite Integers.unsigned_repr_eq.
      apply Integers.same_bits_eq; intros i Hi; rewrite !(@Integers.testbit_repr w _ i Hi).
      destruct Hw as [-> | ->].
      - change (@Integers.zwordsize 32%positive) with 32%Z in Hi.
        change (Z.pos 32) with (2 ^ 5)%Z; change (@Integers.modulus 32%positive) with (2 ^ 32)%Z.
        destruct (Z.ltb i 5) eqn:Ei5;
          [apply Z.ltb_lt in Ei5; rewrite !Z.mod_pow2_bits_low by lia; reflexivity
          | apply Z.ltb_ge in Ei5; rewrite !Z.mod_pow2_bits_high by lia; reflexivity].
      - change (@Integers.zwordsize 64%positive) with 64%Z in Hi.
        change (Z.pos 64) with (2 ^ 6)%Z; change (@Integers.modulus 64%positive) with (2 ^ 64)%Z.
        destruct (Z.ltb i 6) eqn:Ei6;
          [apply Z.ltb_lt in Ei6; rewrite !Z.mod_pow2_bits_low by lia; reflexivity
          | apply Z.ltb_ge in Ei6; rewrite !Z.mod_pow2_bits_high by lia; reflexivity]. }
    assert (H1 : eval_closed_cert_expr penv foracle (CE_BinOp CB_LShr w no_binop_flags lhs (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1))))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shru w vl shv)))).
    { rewrite eval_ce_binop, Hl, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.land Z.sub]; rewrite Hsh_lt, Hsh_eq; reflexivity. }
    assert (H2 : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_Shl w no_binop_flags lhs
        (CE_BinOp CB_And w no_binop_flags
          (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w))
            (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
          (CE_BvConst w (Z.to_N (Z.pos w - 1))))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shl w vl (rv_mask_shamt w (Z.pos w - @Integers.unsigned w shv)))))).
    { rewrite eval_ce_binop, Hl, Hinv; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [inv_sub Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.land Z.sub]; rewrite Hi_lt, Hi_eq, Heq_inv; reflexivity. }
    cbn [a64_eval_dp2]; fold shv.
    rewrite eval_ce_binop, H1, H2; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
Qed.

Lemma eval_a64_sym_csel_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w kind cond sfl fl t_e m_e vt vm,
    sym_flags_agree penv foracle sfl fl ->
    eval_closed_cert_expr penv foracle t_e = raise_ret (DVALUE_Base (@DVALUE_I Pa w vt)) ->
    eval_closed_cert_expr penv foracle m_e = raise_ret (DVALUE_Base (@DVALUE_I Pa w vm)) ->
    eval_closed_cert_expr penv foracle (a64_sym_csel w kind cond sfl t_e m_e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_csel w kind cond fl vt vm))).
Proof.
  intros Pa penv foracle w kind cond sfl fl t_e m_e vt vm Hfl Ht Hm.
  unfold a64_sym_csel, a64_eval_csel.
  eapply eval_ce_select_int; [exact (eval_a64_sym_cond_sound _ _ cond _ _ Hfl) | exact Ht |].
  destruct kind.
  - exact Hm.
  - rewrite eval_ce_binop, Hm, eval_ce_const, repr_one_N; cbn [eou_bind];
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
  - exact (eval_ce_not _ _ w _ _ Hm).
  - exact (eval_ce_neg _ _ w _ _ Hm).
Qed.

Lemma a64_orr_xzr_lsl0 : forall v : @Integers.bit_int 64%positive,
  @Integers.or 64%positive (@Integers.zero 64%positive)
    (a64_eval_shift 64%positive v ASH_Lsl 0%N) = v.
Proof.
  intro v; unfold a64_eval_shift.
  change (Z.of_N 0%N mod Z.pos 64)%Z with 0%Z.
  change (@Integers.repr 64%positive 0%Z) with (@Integers.zero 64%positive).
  rewrite Integers.shl_zero, Integers.or_zero_l; reflexivity.
Qed.

Definition a64_env_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (srf : a64_sym_regs) (def : a64_def_mask) (rf : a64_regfile) : Prop :=
  forall r,
    a64_def_read r def = true ->
    eval_closed_cert_expr penv foracle (a64_sym_read_reg r srf) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg r rf))).

Lemma a64_env_agrees_read_w :
  forall {Pa : Params} (penv : param_env Pa) foracle srf def rf sf r,
    a64_env_agrees penv foracle srf def rf ->
    a64_def_read r def = true ->
    eval_closed_cert_expr penv foracle (a64_sym_read_w sf r srf) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_read_w sf r rf))).
Proof.
  intros Pa penv foracle srf def rf [|] r Hag Hr; cbn [a64_sym_read_w a64_read_w a64_w].
  - exact (Hag r Hr).
  - exact (eval_a64_sym_trunc32_sound _ _ _ _ (Hag r Hr)).
Qed.

Definition a64_val_regs_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (rf0 : a64_regfile) (sp0 : @Integers.bit_int 64%positive)
  (vrf : a64_val_regs) (rf : a64_regfile) : Prop :=
  forall r,
    mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0
      (a64_val_read r vrf) (a64_read_reg r rf).

Lemma a64_val_regs_agrees_write {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 vrf rf rd sv v,
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv v ->
    a64_val_regs_agrees penv foracle rf0 sp0 (a64_val_write rd sv vrf) (a64_write_reg rd v rf).
Proof.
  intros penv foracle rf0 sp0 vrf rf rd sv v Hag Hv r.
  unfold a64_val_read, a64_val_write, a64_read_reg, a64_write_reg.
  destruct (N.leb 31%N r) eqn:Er31;
    [cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity |].
  destruct (N.leb 31%N rd) eqn:Erd31.
  - pose proof (Hag r) as Hr; unfold a64_val_read, a64_read_reg in Hr; rewrite Er31 in Hr; exact Hr.
  - destruct (N.eqb r rd); [exact Hv |].
    pose proof (Hag r) as Hr; unfold a64_val_read, a64_read_reg in Hr; rewrite Er31 in Hr; exact Hr.
Qed.

Lemma a64_val_regs_agrees_write_w {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 vrf rf sf rd e v,
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) v)) ->
    a64_val_regs_agrees penv foracle rf0 sp0 (a64_val_write_w sf rd e vrf) (a64_write_w sf rd v rf).
Proof.
  intros penv foracle rf0 sp0 vrf rf sf rd e v Hag He.
  unfold a64_val_write_w, a64_write_w.
  apply a64_val_regs_agrees_write; [exact Hag |].
  destruct sf; cbn [a64_w mc_sym_val_agrees] in He |- *;
    [exact He | exact (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl He)].
Qed.

Lemma a64_val_read_expr_w_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 vrf rf sf r e,
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    a64_val_read_expr_w sf r vrf = Some e ->
    eval_closed_cert_expr penv foracle e =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_read_w sf r rf))).
Proof.
  intros penv foracle rf0 sp0 vrf rf sf r e Hag He.
  unfold a64_val_read_expr_w in He.
  destruct (a64_val_read r vrf) as [| e64 | |] eqn:Er; try discriminate He.
  inversion He; subst e; clear He.
  pose proof (Hag r) as H64; rewrite Er in H64; cbn [mc_sym_val_agrees] in H64.
  destruct sf; cbn [a64_read_w a64_w]; [exact H64 | exact (eval_a64_sym_trunc32_sound _ _ _ _ H64)].
Qed.

Lemma a64_val_read_sp_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 sp_off vrf rf sp r sv,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    a64_val_read_sp r vrf sp_off = sv ->
    mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv (a64_read_reg_sp r rf sp).
Proof.
  intros penv foracle rf0 sp0 sp_off vrf rf sp r sv Hrng Hsp Hag Hsv.
  unfold a64_val_read_sp, a64_read_reg_sp in *.
  destruct (N.eqb r 31%N); subst sv; [cbn [mc_sym_val_agrees]; split; assumption | exact (Hag r)].
Qed.

Lemma a64_val_write_sp_bounds : forall r sv sp_off vrf astk sp_off' vrf' astk',
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  a64_val_write_sp r sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
  (- mc_frame_cap <= sp_off' <= 0)%Z.
Proof.
  intros r sv sp_off vrf astk sp_off' vrf' astk' Hrng Hst.
  unfold a64_val_write_sp in Hst; destruct (N.eqb r 31%N).
  - destruct sv; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z) eqn:Eb; [| discriminate Hst].
    apply andb_true_iff in Eb as [Eb1 Eb2]; apply Z.leb_le in Eb1; apply Z.leb_le in Eb2.
    inversion Hst; subst; lia.
  - inversion Hst; subst; exact Hrng.
Qed.

Lemma a64_val_write_sp_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 rd sv v sp_off vrf astk rf sp mstk sp_off' vrf' astk',
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv v ->
    a64_val_write_sp rd sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
    let '(rf', sp') := a64_write_reg_sp rd v rf sp in
    sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
    a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk.
Proof.
  intros penv foracle rf0 sp0 rd sv v sp_off vrf astk rf sp mstk sp_off' vrf' astk' Hsp Hag Hastk Hv Hst.
  unfold a64_val_write_sp in Hst; unfold a64_write_reg_sp.
  destruct (N.eqb rd 31%N) eqn:Ed31.
  - destruct sv as [| | | off']; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z); [| discriminate Hst].
    inversion Hst; subst; cbn [mc_sym_val_agrees] in Hv; destruct Hv as [_ Hvp].
    repeat split; [exact Hvp | exact Hag | apply mc_sym_stk_prune_agrees; exact Hastk].
  - inversion Hst; subst sp_off' vrf' astk'; split; [exact Hsp | split; [apply a64_val_regs_agrees_write; assumption | exact Hastk]].
Qed.

Lemma a64_ldst_sym_load_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle (read_init : N -> @Integers.bit_int 64%positive)
         sp0 is_signed sf_dst sv0 sv1 v,
    mc_sym_val_agrees penv foracle read_init sp0 sv0 v ->
    a64_ldst_sym_load is_signed sf_dst sv0 = Some sv1 ->
    mc_sym_val_agrees penv foracle read_init sp0 sv1 (a64_ldst_apply_load is_signed sf_dst v).
Proof.
  intros penv foracle read_init sp0 is_signed sf_dst sv0 sv1 v Hag Hld.
  unfold a64_ldst_sym_load in Hld; unfold a64_ldst_apply_load.
  destruct (is_signed && negb sf_dst).
  - destruct sv0 as [| e | |]; try discriminate Hld; inversion Hld; subst sv1; clear Hld.
    cbn [mc_sym_val_agrees] in Hag |- *.
    exact (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl (eval_a64_sym_trunc32_sound _ _ _ _ Hag)).
  - inversion Hld; subst sv1; exact Hag.
Qed.

Lemma a64_ldst_writeback_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    (match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end) ->
    wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1 ->
    let '(sp_off2, vrf2, astk2) :=
      match mode with
      | AAM_SignedOffset => (sp_off, vrf1, astk1)
      | AAM_PreIndex | AAM_PostIndex =>
          if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
          else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
      end in
    let '(rf2, sp2) :=
      match mode with
      | AAM_SignedOffset => (rf1, sp)
      | AAM_PreIndex | AAM_PostIndex => a64_write_reg_sp rn wb_addr rf1 sp
      end in
    (- mc_frame_cap <= sp_off2 <= 0)%Z /\
    sp2 = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off2) /\
    a64_val_regs_agrees penv foracle rf0 sp0 vrf2 rf2 /\
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk2 mstk1.
Proof.
  intros penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr Hrng Hsp Hwb Hwba Hag1 Hastk1.
  destruct mode; [repeat split; try lia; assumption | |].
  - unfold a64_write_reg_sp; destruct (N.eqb rn 31%N).
    + repeat split; try lia; try assumption; apply mc_sym_stk_prune_agrees; exact Hastk1.
    + repeat split; try lia; try assumption; apply a64_val_regs_agrees_write;
        [exact Hag1 | cbn [mc_sym_val_agrees]; split; assumption].
  - unfold a64_write_reg_sp; destruct (N.eqb rn 31%N).
    + repeat split; try lia; try assumption; apply mc_sym_stk_prune_agrees; exact Hastk1.
    + repeat split; try lia; try assumption; apply a64_val_regs_agrees_write;
        [exact Hag1 | cbn [mc_sym_val_agrees]; split; assumption].
Qed.

Lemma a64_sym_epilogue_ok_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 sp_off vrf rf sp,
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    a64_sym_epilogue_ok sp_off vrf = true ->
    sp = sp0 /\ a64_callee_saved_preserved rf0 rf.
Proof.
  intros penv foracle rf0 sp0 sp_off vrf rf sp Hsp Hag Hep.
  unfold a64_sym_epilogue_ok in Hep; apply andb_true_iff in Hep as [Hz Hforall].
  apply Z.eqb_eq in Hz; subst sp_off.
  split; [rewrite Hsp, mc_add_ptr_zero; reflexivity |].
  intros r Hcs; rewrite forallb_forall in Hforall.
  assert (Hin : In r a64_callee_saved_list).
  { unfold a64_is_callee_saved in Hcs; apply andb_true_iff in Hcs as [Hge Hle];
      apply N.leb_le in Hge; apply N.leb_le in Hle; cbn [a64_callee_saved_list In].
    assert (r = 19%N \/ r = 20%N \/ r = 21%N \/ r = 22%N \/ r = 23%N \/ r = 24%N \/
            r = 25%N \/ r = 26%N \/ r = 27%N \/ r = 28%N \/ r = 29%N \/ r = 30%N) by lia.
    repeat destruct H as [-> | H]; auto 15. }
  pose proof (Hforall r Hin) as Hm; destruct (a64_val_read r vrf) as [| | r0 |] eqn:Er; try discriminate Hm.
  apply N.eqb_eq in Hm; subst r0.
  pose proof (Hag r) as Hagr; rewrite Er in Hagr; cbn [mc_sym_val_agrees] in Hagr.
  unfold a64_is_callee_saved in Hcs; apply andb_true_iff in Hcs as [_ Hle]; apply N.leb_le in Hle.
  unfold a64_read_reg in Hagr; replace (N.leb 31%N r) with false in Hagr by (symmetry; apply N.leb_gt; lia); exact Hagr.
Qed.

Theorem summarize_a64_dag_at_sound :
  forall {Pa : Params} fuel insts im visited pc sp_off vrf astk sfl fl_def ret_w d_mc
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
    summarize_a64_dag_at fuel im visited pc sp_off vrf astk sfl fl_def ret_w = inr d_mc ->
    exists rf_end fl_end mstk_end,
      a64_exec_mem fuel insts pc sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
      a64_callee_saved_preserved rf0 rf_end /\
      eval_cfg_dag penv foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))).
Proof.
  intros Pa fuel insts im visited pc sp_off vrf astk sfl fl_def ret_w d_mc
         penv foracle rf0 sp0 rf sp fl mstk Him.
  revert visited pc sp_off vrf astk sfl fl_def ret_w d_mc penv foracle rf0 sp0 rf sp fl mstk.
  induction fuel as [| fuel' IH];
    intros visited pc sp_off vrf astk sfl fl_def ret_w d_mc
           penv foracle rf0 sp0 rf sp fl mstk
           Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Hsum;
    cbn [summarize_a64_dag_at a64_exec_mem] in *.
  - destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook; rewrite Elook.
    assert (Hdec_val : a64_inst_valid dec = true).
    { clear -Elook Hval; induction insts as [| d rest IHl]; cbn in *; [discriminate |].
      apply andb_true_iff in Hval as [Hd Hr]; destruct (N.eqb (dai_off d) pc);
        [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
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
        | rel
        | cond rel
        | sf is_nz rt rel
        | is_nz rt bit rel
        | ] eqn:Ed.
    + (* A64_Nop *)
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Hsum).
    + (* A64_AddSubImm *)
      destruct (sf && negb set_fl) eqn:E64n.
      * set (sv_opt :=
          match a64_val_read_sp rn vrf sp_off with
          | MSV_StackPtr base_off =>
              let off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z in
              if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
          | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
          | MSV_Expr e =>
              Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
          | MSV_Undef => None
          end) in *.
        destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
        destruct (a64_val_write_sp rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
          [| discriminate Hsum].
        assert (Hsv_ag : mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv
          (if is_sub then @Integers.sub 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive (Z.of_N imm))
           else @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive (Z.of_N imm)))).
        { pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag eq_refl) as Hrn.
          subst sv_opt; destruct (a64_val_read_sp rn vrf sp_off) as [| e | r0 | base_off] eqn:Ern; try discriminate Esv.
          - inversion Esv; subst sv; clear Esv.
            cbn [mc_sym_val_agrees] in Hrn |- *.
            pose proof (eval_a64_sym_add_sub_sound penv foracle 64%positive is_sub _ _ _ _ Hrn (eval_ce_bv_z _ _ 64%positive (Z.of_N imm))) as [Hres _].
            cbn [a64_eval_add_sub fst] in Hres; exact Hres.
          - destruct (N.eqb imm 0%N) eqn:Ez; [| discriminate Esv].
            apply N.eqb_eq in Ez; subst imm; inversion Esv; subst sv; clear Esv.
            cbn [mc_sym_val_agrees] in Hrn |- *.
            destruct is_sub.
            + unfold Integers.sub; change (Z.of_N 0%N) with 0%Z; rewrite (@Integers.unsigned_repr 64%positive 0%Z) by (compute; split; discriminate); rewrite Z.sub_0_r, Integers.repr_unsigned; exact Hrn.
            + rewrite Hrn, mc_add_ptr_zero; reflexivity.
          - cbv zeta in Esv.
            set (off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z) in *.
            destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z) eqn:Erng; [| discriminate Esv].
            apply andb_true_iff in Erng as [Er1 Er2]; apply Z.leb_le in Er1; apply Z.leb_le in Er2.
            inversion Esv; subst sv; clear Esv.
            cbn [mc_sym_val_agrees] in Hrn |- *; destruct Hrn as [_ Hptr]; split; [lia |].
            unfold off'; rewrite Hptr; destruct is_sub; [apply mc_sub_ptr_off | apply mc_add_ptr_off]. }
        pose proof (a64_val_write_sp_bounds _ _ _ _ _ _ _ _ Hrng Est) as Hrng'.
        pose proof (a64_val_write_sp_sound penv foracle rf0 sp0 rd sv _ sp_off vrf astk rf sp mstk sp_off' vrf' astk' Hsp Hag Hastk Hsv_ag Est) as Hwr.
        destruct (a64_write_reg_sp rd _ rf sp) as [rf' sp'] eqn:Ewr.
        destruct Hwr as (Hsp' & Hag' & Hastk').
        exact (IH _ _ sp_off' vrf' astk' sfl fl_def ret_w d_mc penv foracle rf0 sp0 rf' sp' fl mstk
                  Hrw Hval Hsp0 Hrng' Hsp' Hag' Hastk' Hfl Hsum).
      * destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hsum |].
        destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
        destruct (a64_sym_add_sub (a64_w sf) is_sub lhs (ce_bv_z (a64_w sf) (Z.of_N imm))) as [se sfl'] eqn:Esas.
        destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm))) as [vr fl'] eqn:Eeas.
        pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                      (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                      (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm))) as [Hres Hfl'].
        rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
        assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle (if set_fl then sfl' else sfl) (if set_fl then fl' else fl))
          by (intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]).
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_AddSubShift *)
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hsum].
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply andb_true_iff in Hdec_val as [_ Hamt]; apply N.ltb_lt in Hamt.
      pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf) ltac:(destruct sf; exact Hamt)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hsh.
      destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl'] eqn:Eeas.
      pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) Hsh) as [Hres Hfl'].
      rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
      assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle (if set_fl then sfl' else sfl) (if set_fl then fl' else fl))
        by (intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_AddSubExt *)
      destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hsum |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read rm vrf) as [| rm64 | |] eqn:Erm; try discriminate Hsum.
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.leb_le in Hdec_val.
      pose proof (Hag rm) as Hm64; rewrite Erm in Hm64; cbn [mc_sym_val_agrees] in Hm64.
      pose proof (eval_a64_sym_extend_sound _ _ (a64_w sf) _ _ ext amt (a64_w_32_64 sf) Hdec_val Hm64) as Hext.
      destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl'] eqn:Eeas.
      pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) Hext) as [Hres Hfl'].
      rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
      assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle (if set_fl then sfl' else sfl) (if set_fl then fl' else fl))
        by (intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_LogicalImm *)
      destruct (negb set_fl && N.eqb rd 31%N); [discriminate Hsum |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      assert (Hres : eval_closed_cert_expr penv foracle (a64_sym_logic_op (a64_w sf) op lhs (ce_bv_z (a64_w sf) (Z.of_N mask))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
          (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N mask)))))).
      { unfold a64_sym_logic_op, a64_eval_logic_op; rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), eval_ce_bv_z; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
      assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle
        (if set_fl then a64_sym_logic_flags (a64_w sf) _ else sfl)
        (if set_fl then a64_eval_logic_flags (a64_w sf) _ else fl))
        by (intro Hs; destruct set_fl; [exact (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) | exact (Hfl Hs)]).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_LogicalShift *)
      destruct (a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt) eqn:Emov.
      * unfold a64_is_orr_mov64 in Emov; rewrite !andb_true_iff in Emov.
        destruct Emov as ((((((Esf & Hinv) & Hsfl) & Hrn31) & Hamt0) & Hop) & Hsh).
        apply negb_true_iff in Hinv; apply negb_true_iff in Hsfl;
          apply N.eqb_eq in Hrn31; apply N.eqb_eq in Hamt0; subst sf inv_rm set_fl rn amt.
        destruct op; try discriminate Hop; destruct sh; try discriminate Hsh.
        destruct (a64_val_read rm vrf) eqn:Erm; try discriminate Hsum.
        all: cbn [a64_w a64_read_w a64_eval_logic_op a64_write_w];
          replace (a64_read_reg 31%N rf) with (@Integers.zero 64%positive) by reflexivity;
          rewrite a64_orr_xzr_lsl0;
          exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                    (a64_val_regs_agrees_write _ _ _ _ _ _ rd _ _ Hag ltac:(pose proof (Hag rm) as Hm0; rewrite Erm in Hm0; exact Hm0))
                    Hastk Hfl Hsum).
      * destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
        destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hsum].
        unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.ltb_lt in Hdec_val.
        pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf) ltac:(destruct sf; exact Hdec_val)
                      (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hsh.
        assert (Hrhs : eval_closed_cert_expr penv foracle (if inv_rm then a64_sym_not (a64_w sf) _ else _) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
            (if inv_rm then @Integers.not (a64_w sf) (a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt)
             else a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt))))
          by (destruct inv_rm; [exact (eval_ce_not _ _ _ _ _ Hsh) | exact Hsh]).
        set (vr_shift := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt) in *.
        set (se_shift := a64_sym_shift (a64_w sf) rm_e sh amt) in *.
        set (vr_rhs := if inv_rm then @Integers.not (a64_w sf) vr_shift else vr_shift) in *.
        set (se_rhs := if inv_rm then a64_sym_not (a64_w sf) se_shift else se_shift) in *.
        assert (Hres : eval_closed_cert_expr penv foracle (a64_sym_logic_op (a64_w sf) op lhs se_rhs) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) vr_rhs)))).
        { unfold a64_sym_logic_op, a64_eval_logic_op; rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), Hrhs; cbn [eou_bind].
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
        assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle
          (if set_fl then a64_sym_logic_flags (a64_w sf) _ else sfl)
          (if set_fl then a64_eval_logic_flags (a64_w sf) _ else fl))
          by (intro Hs; destruct set_fl; [exact (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) | exact (Hfl Hs)]).
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_MoveWide *)
      destruct kind.
      * pose proof (eval_ce_not penv foracle (a64_w sf) _ _ (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N (N.shiftl imm16 shift)))) as Hres.
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
      * pose proof (eval_ce_bv_z penv foracle (a64_w sf) (Z.of_N (N.shiftl imm16 shift))) as Hres.
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
      * destruct (a64_val_read_expr_w sf rd vrf) as [cur |] eqn:Erd; [| discriminate Hsum].
        assert (Hand : eval_closed_cert_expr penv foracle
          (CE_BinOp CB_And (a64_w sf) no_binop_flags cur
            (a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl 65535%N shift))))) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
            (@Integers.and (a64_w sf) (a64_read_w sf rd rf)
              (@Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))))).
        { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erd),
                  (eval_ce_not _ _ _ _ _ (eval_ce_bv_z _ _ _ _)); cbn [eou_bind].
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
        assert (Hres : eval_closed_cert_expr penv foracle
          (CE_BinOp CB_Or (a64_w sf) no_binop_flags
            (CE_BinOp CB_And (a64_w sf) no_binop_flags cur
              (a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))
            (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl imm16 shift)))) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
            (@Integers.or (a64_w sf)
              (@Integers.and (a64_w sf) (a64_read_w sf rd rf) (@Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))
              (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl imm16 shift))))))).
        { rewrite eval_ce_binop, Hand, eval_ce_bv_z; cbn [eou_bind].
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_Bitfield *)
      destruct (a64_val_read_expr_w sf rn vrf) as [src_e |] eqn:Ern; [| discriminate Hsum].
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply andb_true_iff in Hdec_val as [Hr1 Hs1];
        apply N.ltb_lt in Hr1; apply N.ltb_lt in Hs1.
      set (dst_opt := match kind with ABF_Bfm => a64_val_read_expr_w sf rd vrf | _ => Some (CE_BvConst (a64_w sf) 0%N) end) in *.
      destruct dst_opt as [dst_e |] eqn:Edst; [| discriminate Hsum].
      assert (Hres : eval_closed_cert_expr penv foracle (a64_sym_bitfield (a64_w sf) kind src_e dst_e immr imms) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_eval_bitfield (a64_w sf) kind (a64_read_w sf rn rf) (a64_read_w sf rd rf) immr imms)))).
      { destruct kind.
        - subst dst_opt; inversion Edst; subst dst_e.
          epose proof (eval_a64_sym_bitfield_sound penv foracle sf ABF_Sbfm src_e (CE_BvConst (a64_w sf) 0%N) _ (@Integers.zero (a64_w sf)) immr imms Hr1 Hs1
                         (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hbf.
          cbn [a64_sym_bitfield a64_eval_bitfield] in Hbf |- *; destruct (N.leb immr imms); exact Hbf.
        - subst dst_opt; exact (eval_a64_sym_bitfield_sound _ _ sf ABF_Bfm _ _ _ _ _ _ Hr1 Hs1
                                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Edst)).
        - subst dst_opt; inversion Edst; subst dst_e.
          epose proof (eval_a64_sym_bitfield_sound penv foracle sf ABF_Ubfm src_e (CE_BvConst (a64_w sf) 0%N) _ (@Integers.zero (a64_w sf)) immr imms Hr1 Hs1
                         (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hbf.
          cbn [a64_sym_bitfield a64_eval_bitfield] in Hbf |- *; destruct (N.leb immr imms); exact Hbf. }
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_Extr *)
      destruct (a64_val_read_expr_w sf rn vrf) as [hi_e |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [lo_e |] eqn:Erm; [| discriminate Hsum].
      pose proof (eval_a64_sym_extr_sound _ _ (a64_w sf) _ _ _ _ lsb (a64_w_32_64 sf)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hres.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_MulAddSub *)
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf ra vrf) as [ea |] eqn:Era; [| discriminate Hsum].
      assert (Hmul : eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul (a64_w sf) no_binop_flags en em) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (@Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf))))).
      { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern),
                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm); cbn [eou_bind].
        destruct sf; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
          cbn - [Integers.mul a64_read_w]; reflexivity. }
      assert (Hres : eval_closed_cert_expr penv foracle
        (CE_BinOp (if is_sub then CB_Sub else CB_Add) (a64_w sf) no_binop_flags ea
          (CE_BinOp CB_Mul (a64_w sf) no_binop_flags en em)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
          (let p := @Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
           let a := a64_read_w sf ra rf in
           if is_sub then @Integers.sub (a64_w sf) a p else @Integers.add (a64_w sf) a p)))).
      { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Era), Hmul; cbn [eou_bind].
        destruct sf, is_sub; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
          cbn - [Integers.mul Integers.add Integers.sub a64_read_w]; reflexivity. }
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_MulWidening *)
      destruct (a64_val_read_expr_w false rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w false rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_val_read ra vrf) as [| ea | |] eqn:Era; try discriminate Hsum.
      set (en64 := CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags en).
      set (em64 := CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags em).
      set (vn64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive (a64_read_w false rn rf)
                                               else @Integers.unsigned 32%positive (a64_read_w false rn rf))).
      set (vm64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive (a64_read_w false rm rf)
                                               else @Integers.unsigned 32%positive (a64_read_w false rm rf))).
      assert (Hn64 : eval_closed_cert_expr penv foracle en64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vn64)))
        by (unfold en64, vn64; destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; exact (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)).
      assert (Hm64 : eval_closed_cert_expr penv foracle em64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vm64)))
        by (unfold em64, vm64; destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; exact (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)).
      assert (Hmul : eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul 64%positive no_binop_flags en64 em64) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.mul 64%positive vn64 vm64)))).
      { rewrite eval_ce_binop, Hn64, Hm64; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
          cbn - [Integers.mul vn64 vm64]; reflexivity. }
      pose proof (Hag ra) as Ha; rewrite Era in Ha; cbn [mc_sym_val_agrees] in Ha.
      assert (Hres : eval_closed_cert_expr penv foracle
        (CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags ea
          (CE_BinOp CB_Mul 64%positive no_binop_flags en64 em64)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
          (let p := @Integers.mul 64%positive vn64 vm64 in
           let a := a64_read_reg ra rf in
           if is_sub then @Integers.sub 64%positive a p else @Integers.add 64%positive a p)))).
      { rewrite eval_ce_binop, Ha, Hmul; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct is_sub;
          cbn - [Integers.mul Integers.add Integers.sub vn64 vm64 a64_read_reg]; reflexivity. }
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write _ _ _ _ _ _ rd (MSV_Expr _) _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_DataProc2 *)
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      pose proof (eval_a64_sym_dp2_sound _ _ (a64_w sf) op _ _ _ _ (a64_w_32_64 sf)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hres.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_CondSelect *)
      destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      pose proof (eval_a64_sym_csel_sound _ _ (a64_w sf) kind cond sfl fl _ _ _ _ (Hfl eq_refl)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hres.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_CondCompareReg *)
      destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub en em) as [se csfl] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (a64_read_w sf rm rf)) as [vr cfl] eqn:Eeas.
      pose proof (eval_a64_sym_add_sub_sound _ _ (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as [_ Hcsfl].
      rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
      pose proof (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _ (eval_a64_sym_cond_sound _ _ cond _ _ (Hfl eq_refl)) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv)) as Hite.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk (fun _ => Hite) Hsum).
    + (* A64_CondCompareImm *)
      destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5))) as [se csfl] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm5))) as [vr cfl] eqn:Eeas.
      pose proof (eval_a64_sym_add_sub_sound _ _ (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm5))) as [_ Hcsfl].
      rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
      pose proof (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _ (eval_a64_sym_cond_sound _ _ cond _ _ (Hfl eq_refl)) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv)) as Hite.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk (fun _ => Hite) Hsum).
    + (* A64_LdStImm *)
      destruct Hsp0 as [Hsp0_cap Hsp0_al].
      assert (Hsp_to_off : mc_addr_to_off sp0 sp = sp_off)
        by (rewrite Hsp; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
      rewrite Hsp_to_off.
      destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hsum |].
      destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off] eqn:Ern; try discriminate Hsum.
      pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag Ern) as Hrn_ag.
      cbn [mc_sym_val_agrees] in Hrn_ag; destruct Hrn_ag as [Hbase_rng Hbase_ptr].
      set (wb_off := (base_off + imm)%Z) in *.
      set (wb_addr := @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive imm)) in *.
      assert (Hwb_ptr : wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off))
        by (unfold wb_addr, wb_off; rewrite Hbase_ptr, mc_add_ptr_off; reflexivity).
      set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
      destruct wb_ok eqn:Ewb; cbn [negb] in Hsum; [| discriminate Hsum].
      assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
      { destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
      destruct pair_off as [off sp_chk] eqn:Epo.
      cbv zeta in Hsum.
      assert (Hpo_eq : match mode with
                       | AAM_SignedOffset => (wb_off, sp_off)
                       | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                       | AAM_PostIndex => (base_off, sp_off)
                       end = (off, sp_chk)) by exact Epo.
      rewrite Hpo_eq in Hsum; cbv iota in Hsum.
      destruct (mc_slot_in_frame sp_chk off sz) eqn:Eslot; [| discriminate Hsum].
      pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
      assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
      assert (Hc_eq :
        mc_addr_to_off sp0 (match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end) = off /\
        mc_addr_to_off sp0 (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end) = sp_chk).
      { destruct mode; inversion Epo; subst off sp_chk; split.
        - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
        - exact Hsp_to_off.
        - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
        - destruct (N.eqb rn 31%N); [rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia] | exact Hsp_to_off].
        - rewrite Hbase_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hbase_rng].
        - exact Hsp_to_off. }
      destruct Hc_eq as [Hoff_c Hspchk_c].
      replace (match mode with AAM_SignedOffset => (wb_addr, sp) | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp) | AAM_PostIndex => (a64_read_reg_sp rn rf sp, sp) end)
        with ((match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end),
              (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end))
        by (destruct mode; reflexivity).
      cbn [fst snd] in *; rewrite Hoff_c, Hspchk_c, Eslot.
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
          if a64_ldst_store_sym_ok sz (a64_val_read rt vrf) then Some (vrf, mc_sym_stk_store off sz (a64_val_read rt vrf) astk) else None) in *.
      destruct st_opt as [[vrf1 astk1] |] eqn:Est;
        [try (rewrite Est in Hsum; cbv iota in Hsum) | try rewrite Est in Hsum; discriminate Hsum].
      assert (Hstep1 :
        let '(rf1, mstk1) :=
          if is_load then (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk)
          else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf)) in
        a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1).
      { destruct is_load; unfold st_opt in Est.
        - destruct (mc_sym_stk_load off sz is_signed astk) as [sv0 |] eqn:Esl0; [| discriminate Est].
          destruct (a64_ldst_sym_load is_signed sf_dst sv0) as [sv1 |] eqn:Esl1; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          pose proof (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl0) as Hsv0.
          pose proof (a64_ldst_sym_load_sound _ _ _ _ _ _ _ _ _ Hsv0 Esl1) as Hsv1.
          split; [apply a64_val_regs_agrees_write; assumption | exact Hastk].
        - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt vrf)) eqn:Eok; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          assert (Hszm : match a64_val_read rt vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end).
          { destruct (a64_val_read rt vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok. }
          split; [exact Hag | apply mc_sym_stk_store_agrees; [exact Hszm | exact (Hag rt) | exact Hastk]]. }
      set (rf1 := if is_load then a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf else rf) in *.
      set (mstk1 := if is_load then mstk else mc_stk_store mstk off sz (a64_read_reg rt rf)) in *.
      assert (Hstep1' : a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
                        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1)
        by (destruct is_load; exact Hstep1).
      destruct Hstep1' as [Hag1 Hastk1].
      pose proof (a64_ldst_writeback_sound penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr
                    Hrng Hsp Hwb_rng Hwb_ptr Hag1 Hastk1) as Hwb_s.
      destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
        as [[sp_off2 vrf2] astk2] eqn:Ewbs.
      destruct (match mode with AAM_SignedOffset => (rf1, sp) | _ => a64_write_reg_sp rn wb_addr rf1 sp end)
        as [rf2 sp2] eqn:Ewbc.
      try rewrite Ewbs in Hwb_s; try rewrite Ewbc in Hwb_s; cbv iota in Hwb_s.
      try (rewrite Ewbs in Hsum; cbv iota in Hsum).
      destruct Hwb_s as (Hrng2 & Hsp2 & Hag2 & Hastk2).
      replace (if is_load then (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk) else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf)))
        with (rf1, mstk1) by (destruct is_load; reflexivity).
      rewrite Ewbc; exact (IH _ _ sp_off2 vrf2 astk2 sfl fl_def ret_w d_mc penv foracle rf0 sp0 rf2 sp2 fl mstk1
                             Hrw Hval (conj Hsp0_cap Hsp0_al) Hrng2 Hsp2 Hag2 Hastk2 Hfl Hsum).
    + (* A64_LdStPair *)
      destruct Hsp0 as [Hsp0_cap Hsp0_al].
      assert (Hsp_to_off : mc_addr_to_off sp0 sp = sp_off)
        by (rewrite Hsp; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
      rewrite Hsp_to_off.
      destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hsum |].
      destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off] eqn:Ern; try discriminate Hsum.
      pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag Ern) as Hrn_ag.
      cbn [mc_sym_val_agrees] in Hrn_ag; destruct Hrn_ag as [Hbase_rng Hbase_ptr].
      set (wb_off := (base_off + imm)%Z) in *.
      set (wb_addr := @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive imm)) in *.
      assert (Hwb_ptr : wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off))
        by (unfold wb_addr, wb_off; rewrite Hbase_ptr, mc_add_ptr_off; reflexivity).
      set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
      destruct wb_ok eqn:Ewb; cbn [negb] in Hsum; [| discriminate Hsum].
      assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
      { destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
      destruct pair_off as [off sp_chk] eqn:Epo.
      cbv zeta in Hsum.
      assert (Hpo_eq : match mode with
                       | AAM_SignedOffset => (wb_off, sp_off)
                       | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                       | AAM_PostIndex => (base_off, sp_off)
                       end = (off, sp_chk)) by exact Epo.
      rewrite Hpo_eq in Hsum; cbv iota in Hsum.
      set (sz := if sf then MS_8 else MS_4) in *; set (delta := mc_mem_bytes_Z sz) in *.
      destruct (mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz) eqn:Eslots; [| discriminate Hsum].
      apply andb_true_iff in Eslots as [Esl1 Esl2].
      pose proof (mc_slot_in_frame_bounds _ _ _ Esl1) as (Hb1 & Hb2 & Hb3 & _).
      pose proof (mc_slot_in_frame_bounds _ _ _ Esl2) as (_ & Hb2' & Hb3' & _).
      assert (Hsz_pos : (1 <= delta)%Z) by (unfold delta, sz; destruct sf; cbn; lia).
      assert (Hc_eq :
        mc_addr_to_off sp0 (match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end) = off /\
        mc_addr_to_off sp0 (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end) = sp_chk).
      { destruct mode; inversion Epo; subst off sp_chk; split.
        - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
        - exact Hsp_to_off.
        - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
        - destruct (N.eqb rn 31%N); [rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia] | exact Hsp_to_off].
        - rewrite Hbase_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hbase_rng].
        - exact Hsp_to_off. }
      destruct Hc_eq as [Hoff_c Hspchk_c].
      replace (match mode with AAM_SignedOffset => (wb_addr, sp) | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp) | AAM_PostIndex => (a64_read_reg_sp rn rf sp, sp) end)
        with ((match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end),
              (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end))
        by (destruct mode; reflexivity).
      cbn [fst snd] in *; rewrite Hoff_c, Hspchk_c, Esl1, Esl2; cbn [andb].
      set (st_opt :=
        if is_load then
          match mc_sym_stk_load off sz false astk, mc_sym_stk_load (off + delta) sz false astk with
          | Some sv1, Some sv2 => Some (a64_val_write rt2 sv2 (a64_val_write rt1 sv1 vrf), astk)
          | _, _ => None
          end
        else
          if a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf) then
            Some (vrf, mc_sym_stk_store (off + delta) sz (a64_val_read rt2 vrf) (mc_sym_stk_store off sz (a64_val_read rt1 vrf) astk))
          else None) in *.
      destruct st_opt as [[vrf1 astk1] |] eqn:Est;
        [try (rewrite Est in Hsum; cbv iota in Hsum) | try rewrite Est in Hsum; discriminate Hsum].
      assert (Hstep1 :
        let '(rf1, mstk1) :=
          if is_load then (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk)
          else (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)) in
        a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1).
      { destruct is_load; unfold st_opt in Est.
        - destruct (mc_sym_stk_load off sz false astk) as [sv1 |] eqn:Esl_1; [| discriminate Est].
          destruct (mc_sym_stk_load (off + delta) sz false astk) as [sv2 |] eqn:Esl_2; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          pose proof (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl_1) as Hsv1.
          pose proof (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl_2) as Hsv2.
          split; [apply a64_val_regs_agrees_write; [apply a64_val_regs_agrees_write; assumption | exact Hsv2] | exact Hastk].
        - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf)) eqn:Eok;
            [| discriminate Est].
          apply andb_true_iff in Eok as [Eok1 Eok2].
          inversion Est; subst vrf1 astk1; clear Est.
          assert (Hszm1 : match a64_val_read rt1 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
            by (destruct (a64_val_read rt1 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok1).
          assert (Hszm2 : match a64_val_read rt2 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
            by (destruct (a64_val_read rt2 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok2).
          split; [exact Hag |].
          apply mc_sym_stk_store_agrees; [exact Hszm2 | exact (Hag rt2) |].
          apply mc_sym_stk_store_agrees; [exact Hszm1 | exact (Hag rt1) | exact Hastk]. }
      set (rf1 := if is_load then a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf) else rf) in *.
      set (mstk1 := if is_load then mstk else mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)) in *.
      assert (Hstep1' : a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
                        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1)
        by (destruct is_load; exact Hstep1).
      destruct Hstep1' as [Hag1 Hastk1].
      pose proof (a64_ldst_writeback_sound penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr
                    Hrng Hsp Hwb_rng Hwb_ptr Hag1 Hastk1) as Hwb_s.
      destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
        as [[sp_off2 vrf2] astk2] eqn:Ewbs.
      destruct (match mode with AAM_SignedOffset => (rf1, sp) | _ => a64_write_reg_sp rn wb_addr rf1 sp end)
        as [rf2 sp2] eqn:Ewbc.
      try rewrite Ewbs in Hwb_s; try rewrite Ewbc in Hwb_s; cbv iota in Hwb_s.
      try (rewrite Ewbs in Hsum; cbv iota in Hsum).
      destruct Hwb_s as (Hrng2 & Hsp2 & Hag2 & Hastk2).
      replace (if is_load then (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk)
               else (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)))
        with (rf1, mstk1) by (destruct is_load; reflexivity).
      rewrite Ewbc; exact (IH _ _ sp_off2 vrf2 astk2 sfl fl_def ret_w d_mc penv foracle rf0 sp0 rf2 sp2 fl mstk1
                             Hrw Hval (conj Hsp0_cap Hsp0_al) Hrng2 Hsp2 Hag2 Hastk2 Hfl Hsum).
    + (* A64_B *)
      destruct (add_rel_off pc rel); [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Hsum).
    + (* A64_BCond *)
      destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl true ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl true ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (eval_a64_sym_cond_sound penv foracle cond sfl fl (Hfl eq_refl)) as Hc.
      cbn [eval_cfg_dag]; cbn [N.shiftl] in Hc; rewrite Hc.
      destruct (a64_eval_cond cond fl).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edf).
    + (* A64_Cbz *)
      destruct (a64_val_read_expr_w sf rt vrf) as [rt_e |] eqn:Ert; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl fl_def ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      assert (Hc : eval_closed_cert_expr penv foracle
        (CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false (a64_w sf) rt_e (CE_BvConst (a64_w sf) 0%N)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
          (if (if is_nz then negb (@Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf)))
               else @Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf)))
           then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { destruct is_nz;
          [exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ert) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))
          | exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ert) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))]. }
      cbn [eval_cfg_dag]; cbn [N.shiftl] in Hc; rewrite Hc.
      destruct (if is_nz then negb (@Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf)))
                else @Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf))).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edf).
    + (* A64_Tbz *)
      destruct (a64_val_read rt vrf) as [| rt_e | |] eqn:Ert; try discriminate Hsum.
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl fl_def ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.ltb_lt in Hdec_val.
      pose proof (Hag rt) as Hrt; rewrite Ert in Hrt; cbn [mc_sym_val_agrees] in Hrt.
      assert (Hm : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
          (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))))).
      { rewrite eval_ce_binop, Hrt, eval_ce_const; cbn [eou_bind];
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      assert (Heq_tb : negb (@Integers.eq 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))) (@Integers.zero 64%positive)) =
                       Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)).
      { pose proof (integers_eq_zero_iff 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) as Hiz.
        destruct (@Integers.eq 64%positive _ _) eqn:Ez,
                 (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)) eqn:Etb;
          try reflexivity.
        - exfalso; pose proof (proj1 Hiz eq_refl) as Hz.
          assert (Hb : Z.testbit (@Integers.unsigned 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) (Z.of_N bit) = false)
            by (rewrite Hz; apply Z.testbit_0_l).
          change (Z.testbit (@Integers.unsigned 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) (Z.of_N bit))
            with (@Integers.testbit 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))) (Z.of_N bit)) in Hb.
          rewrite Integers.bits_and, (@Integers.testbit_repr 64%positive _ (Z.of_N bit)) in Hb
            by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
          rewrite N.shiftl_1_l, N2Z.inj_pow, Z.pow2_bits_true in Hb by lia.
          unfold Integers.testbit in Hb; rewrite Etb in Hb; discriminate Hb.
        - exfalso; assert (Hnz : @Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))) = @Integers.zero 64%positive).
          { apply Integers.same_bits_eq; intros i Hi; rewrite Integers.bits_zero, Integers.bits_and by exact Hi.
            rewrite (@Integers.testbit_repr 64%positive _ i Hi).
            change (@Integers.zwordsize 64%positive) with 64%Z in Hi.
            rewrite N.shiftl_1_l, N2Z.inj_pow; destruct (Z.eq_dec i (Z.of_N bit)) as [-> | Hne].
            - unfold Integers.testbit; rewrite Etb; reflexivity.
            - rewrite Z.pow2_bits_false by (try lia; exact Hne); rewrite andb_false_r; reflexivity. }
          pose proof (proj2 Hiz ltac:(rewrite Hnz, (@Integers.unsigned_zero 64%positive); reflexivity)) as Htru.
          discriminate Htru. }
      assert (Hc : eval_closed_cert_expr penv foracle
        (CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false 64%positive
          (CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit)))
          (CE_BvConst 64%positive 0%N)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
          (if (if is_nz then Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)
               else negb (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)))
           then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { rewrite <- Heq_tb.
        destruct is_nz.
        - exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ Hm ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)).
        - rewrite negb_involutive; exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hm ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)). }
      cbn [eval_cfg_dag]; cbn [N.shiftl] in Hc; rewrite Hc.
      destruct (if is_nz then Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)
                else negb (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit))).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edf).
    + (* A64_Ret *)
      destruct (a64_sym_epilogue_ok sp_off vrf) eqn:Hep; [| discriminate Hsum].
      destruct (a64_val_read 0%N vrf) as [| e_ret | |] eqn:Er0; try discriminate Hsum.
      inversion Hsum; subst d_mc; clear Hsum.
      destruct (a64_sym_epilogue_ok_sound penv foracle rf0 sp0 sp_off vrf rf sp Hsp Hag Hep) as [Hsp_end Hcs].
      rewrite Hsp_end; exists rf, fl, mstk; split; [reflexivity | split; [exact Hcs |]].
      cbn [eval_cfg_dag]; unfold rv_trunc_ret_expr, rv_trunc_ret_val.
      pose proof (Hag 0%N) as Ha0; rewrite Er0 in Ha0; cbn [mc_sym_val_agrees] in Ha0.
      destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
      * apply Pos.eqb_eq in Ew64; subst ret_w; rewrite Ha0, (@Integers.repr_unsigned 64%positive); reflexivity.
      * assert (Hlt64 : (ret_w <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hrw Ew64).
        rewrite (eval_ce_trunc penv foracle 64%positive ret_w _ _ Hlt64 Ha0); reflexivity.
Qed.

(** *** 5.2 Zero-Axiom Symbolic Well-Formedness *)

Definition wf_sym_flags (allowed : list (string * positive)) (sfl : a64_sym_flags) : Prop :=
  wf_sym_expr allowed 1%positive (asf_n sfl) /\
  wf_sym_expr allowed 1%positive (asf_z sfl) /\
  wf_sym_expr allowed 1%positive (asf_c sfl) /\
  wf_sym_expr allowed 1%positive (asf_v sfl) /\
  wf_sym_expr allowed 1%positive (asf_n_ne_v sfl).

Definition wf_a64_val_regs (allowed : list (string * positive)) (vrf : a64_val_regs) : Prop :=
  forall r, mc_sym_val_wf allowed (a64_val_read r vrf).

Lemma a64_wf_sym_binop : forall allowed op w a b,
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (CE_BinOp op w no_binop_flags a b).
Proof.
  intros allowed op w a b (Hta & Hwa & Hlfa & Hva) (Htb & Hwb & Hlfb & Hvb).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - destruct op; rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl; reflexivity.
  - reflexivity.
  - rewrite Hlfa, Hlfb; reflexivity.
  - apply vars_subset_app; assumption.
Qed.

Lemma wf_a64_sym_trunc32 : forall allowed e,
  wf_sym_expr allowed 64%positive e ->
  wf_sym_expr allowed 32%positive (a64_sym_trunc32 e).
Proof.
  intros allowed e Hwf.
  assert (Hfall : wf_sym_expr allowed 32%positive (ce_trunc64_32 e)) by (apply wf_sym_cast; [reflexivity | exact Hwf]).
  unfold a64_sym_trunc32.
  destruct (a64_sym_trunc32_match e) as [inner |] eqn:Em; [| exact Hfall].
  destruct e as [| | | op w1 fl l r | | k fw tw fl o | | |];
    cbn [a64_sym_trunc32_match] in Em; try discriminate Em.
  - destruct op; try discriminate Em.
    destruct l as [| | | | | kl fw tw fll ol | | |]; try discriminate Em.
    destruct kl; try discriminate Em.
    destruct r as [| | | opr w2 flr lr rr | | | | |]; try discriminate Em.
    destruct opr; try discriminate Em.
    destruct rr as [w3 mask | | | | | | | |]; try discriminate Em.
    destruct (Pos.eqb w1 64%positive && Pos.eqb fw 32%positive && Pos.eqb tw 64%positive &&
              Pos.eqb w2 64%positive && Pos.eqb w3 64%positive &&
              N.eqb (N.land mask 4294967295%N) 0%N) eqn:Eok; [| discriminate Em].
    inversion Em; subst inner; clear Em.
    rewrite !andb_true_iff in Eok; destruct Eok as (((((Ew1 & Efw) & Etw) & Ew2) & Ew3) & _).
    apply Pos.eqb_eq in Ew1; apply Pos.eqb_eq in Efw; apply Pos.eqb_eq in Etw;
      apply Pos.eqb_eq in Ew2; apply Pos.eqb_eq in Ew3; subst w1 fw tw w2 w3.
    destruct Hwf as (Hwt & _ & Hlf & Hvs);
      cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hvs;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
      match goal with H : (cert_expr_bit_width ol =? 32)%positive = true |- _ => apply Pos.eqb_eq in H end;
      unfold vars_subset_b in Hvs; rewrite forallb_app in Hvs; apply andb_true_iff in Hvs as [Hvo _];
      repeat split; assumption.
  - destruct k; try discriminate Em.
    destruct (Pos.eqb fw 32%positive && Pos.eqb tw 64%positive) eqn:Eok; [| discriminate Em].
    inversion Em; subst inner; clear Em.
    apply andb_true_iff in Eok as [Efw _]; apply Pos.eqb_eq in Efw; subst fw.
    destruct Hwf as (Hwt & _ & Hlf & Hvs);
      cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hvs;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
      match goal with H : (cert_expr_bit_width o =? 32)%positive = true |- _ => apply Pos.eqb_eq in H end;
      repeat split; assumption.
Qed.

Lemma wf_a64_val_write : forall allowed vrf rd sv,
  wf_a64_val_regs allowed vrf ->
  mc_sym_val_wf allowed sv ->
  wf_a64_val_regs allowed (a64_val_write rd sv vrf).
Proof.
  intros allowed vrf rd sv Hwf Hsv r.
  unfold a64_val_read, a64_val_write.
  destruct (N.leb 31%N r) eqn:Er31; [apply wf_sym_bv_const |].
  destruct (N.leb 31%N rd) eqn:Erd31.
  - pose proof (Hwf r) as Hr; unfold a64_val_read in Hr; rewrite Er31 in Hr; exact Hr.
  - destruct (N.eqb r rd); [exact Hsv | pose proof (Hwf r) as Hr; unfold a64_val_read in Hr; rewrite Er31 in Hr; exact Hr].
Qed.

Lemma wf_a64_val_write_w : forall allowed vrf sf rd e,
  wf_a64_val_regs allowed vrf ->
  wf_sym_expr allowed (a64_w sf) e ->
  wf_a64_val_regs allowed (a64_val_write_w sf rd e vrf).
Proof.
  intros allowed vrf sf rd e Hwf He.
  apply wf_a64_val_write; [exact Hwf |].
  destruct sf; cbn [mc_sym_val_wf a64_w] in He |- *;
    [exact He | apply wf_sym_cast; [reflexivity | exact He]].
Qed.

Lemma wf_a64_val_read_expr_w : forall allowed vrf sf r e,
  wf_a64_val_regs allowed vrf ->
  a64_val_read_expr_w sf r vrf = Some e ->
  wf_sym_expr allowed (a64_w sf) e.
Proof.
  intros allowed vrf sf r e Hwf He; unfold a64_val_read_expr_w in He.
  destruct (a64_val_read r vrf) as [| e64 | |] eqn:Er; try discriminate He.
  inversion He; subst e; clear He.
  pose proof (Hwf r) as H64; rewrite Er in H64; cbn [mc_sym_val_wf] in H64.
  destruct sf; cbn [a64_w]; [exact H64 | exact (wf_a64_sym_trunc32 _ _ H64)].
Qed.

Lemma wf_a64_val_read_sp : forall allowed vrf sp_off r sv,
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  wf_a64_val_regs allowed vrf ->
  a64_val_read_sp r vrf sp_off = sv ->
  mc_sym_val_wf allowed sv.
Proof.
  intros allowed vrf sp_off r sv Hrng Hwf Hsv.
  unfold a64_val_read_sp in Hsv; destruct (N.eqb r 31%N); subst sv;
    [cbn [mc_sym_val_wf]; exact Hrng | exact (Hwf r)].
Qed.

Lemma a64_val_write_sp_wf : forall allowed rd sv sp_off vrf astk sp_off' vrf' astk',
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  mc_sym_val_wf allowed sv ->
  wf_a64_val_regs allowed vrf ->
  mc_sym_stack_wf allowed sp_off astk ->
  a64_val_write_sp rd sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
  (- mc_frame_cap <= sp_off' <= 0)%Z /\
  wf_a64_val_regs allowed vrf' /\
  mc_sym_stack_wf allowed sp_off' astk'.
Proof.
  intros allowed rd sv sp_off vrf astk sp_off' vrf' astk' Hrng Hsv Hwf Hstk Hst.
  unfold a64_val_write_sp in Hst; destruct (N.eqb rd 31%N).
  - destruct sv as [| | | off']; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z) eqn:Eb; [| discriminate Hst].
    apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
    inversion Hst; subst; repeat split; [lia | lia | exact Hwf | eapply mc_sym_stk_prune_wf; [lia | exact Hstk]].
  - inversion Hst; subst; repeat split; [lia | lia | apply wf_a64_val_write; assumption | exact Hstk].
Qed.

Lemma a64_ldst_sym_load_wf : forall allowed is_signed sf_dst sv0 sv1,
  mc_sym_val_wf allowed sv0 ->
  a64_ldst_sym_load is_signed sf_dst sv0 = Some sv1 ->
  mc_sym_val_wf allowed sv1.
Proof.
  intros allowed is_signed sf_dst sv0 sv1 Hwf Hld.
  unfold a64_ldst_sym_load in Hld; destruct (is_signed && negb sf_dst).
  - destruct sv0 as [| e | |]; try discriminate Hld; inversion Hld; subst sv1.
    cbn [mc_sym_val_wf] in Hwf |- *; apply wf_sym_cast; [reflexivity | exact (wf_a64_sym_trunc32 _ _ Hwf)].
  - inversion Hld; subst sv1; exact Hwf.
Qed.

Lemma a64_ldst_writeback_wf : forall allowed sp_off vrf1 astk1 mode rn wb_off,
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  (match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end) ->
  wf_a64_val_regs allowed vrf1 ->
  mc_sym_stack_wf allowed sp_off astk1 ->
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
  intros allowed sp_off vrf1 astk1 mode rn wb_off Hrng Hwb Hwf1 Hstk1.
  destruct mode; [repeat split; [lia | lia | exact Hwf1 | exact Hstk1] | |].
  - destruct (N.eqb rn 31%N); repeat split;
      try lia; try assumption;
      [eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]
      | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb]].
  - destruct (N.eqb rn 31%N); repeat split;
      try lia; try assumption;
      [eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]
      | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb]].
Qed.

Lemma wf_a64_sym_add_sub : forall allowed w is_sub l r,
  wf_sym_expr allowed w l ->
  wf_sym_expr allowed w r ->
  wf_sym_expr allowed w (fst (a64_sym_add_sub w is_sub l r)) /\
  wf_sym_flags allowed (snd (a64_sym_add_sub w is_sub l r)).
Proof.
  intros allowed w [|] l r Hl Hr; unfold a64_sym_add_sub; cbn [fst snd].
  - assert (Hres : wf_sym_expr allowed w (CE_BinOp CB_Sub w no_binop_flags l r)) by (apply a64_wf_sym_binop; assumption).
    assert (Hn : wf_sym_expr allowed 1%positive (a64_sym_is_neg w (CE_BinOp CB_Sub w no_binop_flags l r))) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
    assert (Hsl : wf_sym_expr allowed 1%positive (a64_sym_is_neg w l)) by (apply wf_sym_icmp; [exact Hl | apply wf_sym_bv_const]).
    assert (Hsr : wf_sym_expr allowed 1%positive (a64_sym_is_neg w r)) by (apply wf_sym_icmp; [exact Hr | apply wf_sym_bv_const]).
    assert (Hdif : wf_sym_expr allowed 1%positive (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Sub w no_binop_flags l r))))
      by (unfold a64_sym_bool_xor; apply a64_wf_sym_binop; assumption).
    assert (Hz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w l r)) by (apply wf_sym_icmp; assumption).
    assert (Hc : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Uge false w l r)) by (apply wf_sym_icmp; assumption).
    assert (Hxor : wf_sym_expr allowed 1%positive (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w r)))
      by (unfold a64_sym_bool_xor; apply a64_wf_sym_binop; assumption).
    assert (Hv : wf_sym_expr allowed 1%positive (CE_BinOp CB_And 1%positive no_binop_flags (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w r)) (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Sub w no_binop_flags l r))))) by (apply a64_wf_sym_binop; assumption).
    assert (Hnx : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Slt false w l r)) by (apply wf_sym_icmp; assumption).
    split; [exact Hres | unfold wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v]; split; [exact Hn | split; [exact Hz | split; [exact Hc | split; [exact Hv | exact Hnx]]]]].
  - assert (Hres : wf_sym_expr allowed w (CE_BinOp CB_Add w no_binop_flags l r)) by (apply a64_wf_sym_binop; assumption).
    assert (Hn : wf_sym_expr allowed 1%positive (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r))) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
    assert (Hsl : wf_sym_expr allowed 1%positive (a64_sym_is_neg w l)) by (apply wf_sym_icmp; [exact Hl | apply wf_sym_bv_const]).
    assert (Hsr : wf_sym_expr allowed 1%positive (a64_sym_is_neg w r)) by (apply wf_sym_icmp; [exact Hr | apply wf_sym_bv_const]).
    assert (Hdif : wf_sym_expr allowed 1%positive (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r))))
      by (unfold a64_sym_bool_xor; apply a64_wf_sym_binop; assumption).
    assert (Hz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w (CE_BinOp CB_Add w no_binop_flags l r) (CE_BvConst w 0%N))) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
    assert (Hc : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Ult false w (CE_BinOp CB_Add w no_binop_flags l r) l)) by (apply wf_sym_icmp; [exact Hres | exact Hl]).
    assert (Heqlr : wf_sym_expr allowed 1%positive (a64_sym_bool_eq (a64_sym_is_neg w l) (a64_sym_is_neg w r)))
      by (unfold a64_sym_bool_eq; apply wf_sym_icmp; assumption).
    assert (Hv : wf_sym_expr allowed 1%positive (CE_BinOp CB_And 1%positive no_binop_flags (a64_sym_bool_eq (a64_sym_is_neg w l) (a64_sym_is_neg w r)) (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r))))) by (apply a64_wf_sym_binop; assumption).
    assert (Hnx : wf_sym_expr allowed 1%positive (a64_sym_bool_xor (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r)) (CE_BinOp CB_And 1%positive no_binop_flags (a64_sym_bool_eq (a64_sym_is_neg w l) (a64_sym_is_neg w r)) (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r))))))
      by (unfold a64_sym_bool_xor; apply a64_wf_sym_binop; assumption).
    split; [exact Hres | unfold wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v]; split; [exact Hn | split; [exact Hz | split; [exact Hc | split; [exact Hv | exact Hnx]]]]].
Qed.

Lemma wf_a64_sym_logic_flags : forall allowed w res,
  wf_sym_expr allowed w res ->
  wf_sym_flags allowed (a64_sym_logic_flags w res).
Proof.
  intros allowed w res Hres; unfold a64_sym_logic_flags, wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v].
  assert (Hn : wf_sym_expr allowed 1%positive (a64_sym_is_neg w res)) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
  assert (Hz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w res (CE_BvConst w 0%N))) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
  assert (Hf0 : wf_sym_expr allowed 1%positive (CE_BvConst 1%positive 0%N)) by apply wf_sym_bv_const.
  split; [exact Hn | split; [exact Hz | split; [exact Hf0 | split; [exact Hf0 | exact Hn]]]].
Qed.

Lemma wf_a64_sym_cond : forall allowed c sfl,
  wf_sym_flags allowed sfl ->
  wf_sym_expr allowed 1%positive (a64_sym_cond c sfl).
Proof.
  intros allowed c sfl (Hn & Hz & Hc & Hv & Hnxv).
  destruct c; unfold a64_sym_cond;
    repeat (first [assumption | apply wf_sym_bv_const | apply a64_wf_sym_binop]).
Qed.

Lemma wf_a64_sym_ite_flags : forall allowed c st sf,
  wf_sym_expr allowed 1%positive c ->
  wf_sym_flags allowed st ->
  wf_sym_flags allowed sf ->
  wf_sym_flags allowed (a64_sym_ite_flags c st sf).
Proof.
  intros allowed c st sf Hc (Htn & Htz & Htc & Htv & Htnxv) (Hfn & Hfz & Hfc & Hfv & Hfnxv).
  unfold a64_sym_ite_flags, wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v].
  split; [apply wf_sym_select; assumption
        | split; [apply wf_sym_select; assumption
        | split; [apply wf_sym_select; assumption
        | split; [apply wf_sym_select; assumption
        | apply wf_sym_select; assumption]]]].
Qed.

Lemma wf_a64_sym_shift : forall allowed w e sh amt,
  wf_sym_expr allowed w e ->
  wf_sym_expr allowed w (a64_sym_shift w e sh amt).
Proof.
  intros allowed w e sh amt He; unfold a64_sym_shift.
  destruct sh, (N.eqb (N.modulo amt (N.pos w)) 0%N); try exact He;
    repeat apply a64_wf_sym_binop; first [exact He | apply wf_sym_bv_const].
Qed.

Lemma wf_a64_sym_extend : forall allowed w e64 ext amt,
  (w = 32%positive \/ w = 64%positive) ->
  wf_sym_expr allowed 64%positive e64 ->
  wf_sym_expr allowed w (a64_sym_extend w e64 ext amt).
Proof.
  intros allowed w e64 ext amt Hw He64; unfold a64_sym_extend.
  destruct (a64_ext_bits ext) as [sb sgn]; set (eff := Pos.min sb w).
  set (sl := if Pos.eqb eff 64%positive then e64
             else if Pos.eqb eff 32%positive then a64_sym_trunc32 e64
             else CE_Cast CCK_Trunc 64%positive eff no_cast_flags e64).
  assert (Hsl : wf_sym_expr allowed eff sl).
  { unfold sl; destruct (Pos.eqb eff 64%positive) eqn:E64.
    - apply Pos.eqb_eq in E64; rewrite E64; exact He64.
    - destruct (Pos.eqb eff 32%positive) eqn:E32.
      + apply Pos.eqb_eq in E32; rewrite E32; exact (wf_a64_sym_trunc32 _ _ He64).
      + apply wf_sym_cast; [| exact He64].
        apply Pos.ltb_lt; apply Pos.eqb_neq in E64; unfold eff in *; destruct Hw as [-> | ->];
          [pose proof (Pos.le_min_r sb 32%positive) | pose proof (Pos.le_min_r sb 64%positive)]; lia. }
  assert (Hext : wf_sym_expr allowed w
    (if Pos.eqb eff w then sl else CE_Cast (if sgn then CCK_SExt else CCK_ZExt) eff w no_cast_flags sl)).
  { destruct (Pos.eqb eff w) eqn:Eew.
    - apply Pos.eqb_eq in Eew; rewrite <- Eew; exact Hsl.
    - assert (Hlt : (eff <? w)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.eqb_neq in Eew; unfold eff in *; pose proof (Pos.le_min_r sb w); lia).
      destruct sgn; apply wf_sym_cast; assumption. }
  destruct (N.eqb amt 0%N); [exact Hext | apply a64_wf_sym_binop; [exact Hext | apply wf_sym_bv_const]].
Qed.

Lemma wf_a64_sym_flags_imm4 : forall allowed nzcv,
  wf_sym_flags allowed (a64_sym_flags_of_imm4 nzcv).
Proof.
  intros allowed nzcv; unfold a64_sym_flags_of_imm4, wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v];
    split; [apply wf_sym_bv_const | split; [apply wf_sym_bv_const | split; [apply wf_sym_bv_const | split; [apply wf_sym_bv_const | apply wf_sym_bv_const]]]].
Qed.

Lemma wf_a64_sym_bitfield : forall allowed sf kind src dst immr imms,
  wf_sym_expr allowed (a64_w sf) src ->
  wf_sym_expr allowed (a64_w sf) dst ->
  wf_sym_expr allowed (a64_w sf) (a64_sym_bitfield (a64_w sf) kind src dst immr imms).
Proof.
  intros allowed sf kind src dst immr imms Hs Hd; unfold a64_sym_bitfield.
  destruct (N.leb immr imms).
  - assert (Hshr : wf_sym_expr allowed (a64_w sf)
      (if N.eqb immr 0%N then src else CE_BinOp CB_LShr (a64_w sf) no_binop_flags src (CE_BvConst (a64_w sf) immr)))
      by (destruct (N.eqb immr 0%N); [exact Hs | apply a64_wf_sym_binop; [exact Hs | apply wf_sym_bv_const]]).
    destruct kind.
    + destruct (Pos.eqb (a64_w sf) 64%positive && N.eqb immr 0%N && N.eqb imms 31%N) eqn:Esx.
      * rewrite !andb_true_iff in Esx; destruct Esx as ([Ew64 _] & _); apply Pos.eqb_eq in Ew64.
        rewrite Ew64 in Hs |- *; apply wf_sym_cast; [reflexivity | exact (wf_a64_sym_trunc32 _ _ Hs)].
      * destruct (N.eqb (N.pos (a64_w sf) - 1%N - imms) 0%N), (N.eqb (N.pos (a64_w sf) - (imms - immr + 1%N)) 0%N);
          repeat apply a64_wf_sym_binop; first [exact Hs | apply wf_sym_bv_const].
    + unfold a64_sym_not; apply a64_wf_sym_binop;
        [apply a64_wf_sym_binop; [exact Hd | apply a64_wf_sym_binop; apply wf_sym_bv_const]
        | apply a64_wf_sym_binop; [exact Hshr | apply wf_sym_bv_const]].
    + destruct (N.eqb (imms - immr + 1%N) (N.pos (a64_w sf))); [exact Hs |].
      destruct (N.eqb imms (N.pos (a64_w sf) - 1%N)); [exact Hshr |].
      destruct (Pos.eqb (a64_w sf) 64%positive && N.eqb immr 0%N && N.eqb imms 31%N) eqn:Eux.
      * rewrite !andb_true_iff in Eux; destruct Eux as ([Ew64 _] & _); apply Pos.eqb_eq in Ew64.
        rewrite Ew64 in Hs |- *; apply wf_sym_cast; [reflexivity | exact (wf_a64_sym_trunc32 _ _ Hs)].
      * apply a64_wf_sym_binop; [exact Hshr | apply wf_sym_bv_const].
  - destruct kind; unfold a64_sym_not.
    + apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact Hs | apply wf_sym_bv_const] | apply wf_sym_bv_const] | apply wf_sym_bv_const].
    + apply a64_wf_sym_binop;
        [apply a64_wf_sym_binop; [exact Hd | apply a64_wf_sym_binop; [apply a64_wf_sym_binop; apply wf_sym_bv_const | apply wf_sym_bv_const]]
        | apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact Hs | apply wf_sym_bv_const] | apply wf_sym_bv_const]].
    + apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact Hs | apply wf_sym_bv_const] | apply wf_sym_bv_const].
Qed.

Lemma wf_a64_sym_div_guarded : forall allowed is_signed w a b,
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (a64_sym_div_guarded is_signed w a b).
Proof.
  intros allowed is_signed w a b Ha Hb; unfold a64_sym_div_guarded.
  assert (Hz : wf_sym_expr allowed w (CE_BvConst w 0%N)) by apply wf_sym_bv_const.
  assert (H1 : wf_sym_expr allowed w (CE_BvConst w 1%N)) by apply wf_sym_bv_const.
  assert (Hiz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)))
    by (apply wf_sym_icmp; assumption).
  destruct is_signed; cbn [negb].
  - assert (Hovf : wf_sym_expr allowed 1%positive
      (CE_BinOp CB_And 1%positive no_binop_flags (CE_ICmp CIP_Eq false w a (ce_int_min w)) (CE_ICmp CIP_Eq false w b (ce_all_ones w))))
      by (apply a64_wf_sym_binop; apply wf_sym_icmp; try assumption; apply wf_sym_bv_const).
    assert (Hbad : wf_sym_expr allowed 1%positive
      (CE_BinOp CB_Or 1%positive no_binop_flags (CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N))
        (CE_BinOp CB_And 1%positive no_binop_flags (CE_ICmp CIP_Eq false w a (ce_int_min w)) (CE_ICmp CIP_Eq false w b (ce_all_ones w)))))
      by (apply a64_wf_sym_binop; assumption).
    apply wf_sym_select; [exact Hiz | exact Hz |].
    apply wf_sym_select; [exact Hovf | apply wf_sym_bv_const |].
    apply a64_wf_sym_binop; [apply wf_sym_select; assumption | apply wf_sym_select; assumption].
  - apply wf_sym_select; [exact Hiz | exact Hz |].
    apply a64_wf_sym_binop; [exact Ha | apply wf_sym_select; assumption].
Qed.

Lemma wf_a64_sym_dp2 : forall allowed w op l r,
  wf_sym_expr allowed w l ->
  wf_sym_expr allowed w r ->
  wf_sym_expr allowed w (a64_sym_dp2 w op l r).
Proof.
  intros allowed w op l r Hl Hr; unfold a64_sym_dp2.
  assert (Hsh : wf_sym_expr allowed w (CE_BinOp CB_And w no_binop_flags r (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
    by (apply a64_wf_sym_binop; [exact Hr | apply wf_sym_bv_const]).
  assert (Hinv : wf_sym_expr allowed w
    (CE_BinOp CB_And w no_binop_flags
      (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w))
        (CE_BinOp CB_And w no_binop_flags r (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
      (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
    by (apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [apply wf_sym_bv_const | exact Hsh] | apply wf_sym_bv_const]).
  destruct op;
    [ exact (wf_a64_sym_div_guarded _ false _ _ _ Hl Hr)
    | exact (wf_a64_sym_div_guarded _ true _ _ _ Hl Hr)
    | apply a64_wf_sym_binop; assumption
    | apply a64_wf_sym_binop; assumption
    | apply a64_wf_sym_binop; assumption
    | apply a64_wf_sym_binop; apply a64_wf_sym_binop; assumption ].
Qed.

Lemma wf_a64_sym_csel : forall allowed w kind cond sfl t m,
  wf_sym_flags allowed sfl ->
  wf_sym_expr allowed w t ->
  wf_sym_expr allowed w m ->
  wf_sym_expr allowed w (a64_sym_csel w kind cond sfl t m).
Proof.
  intros allowed w kind cond sfl t m Hfl Ht Hm; unfold a64_sym_csel, a64_sym_not, a64_sym_neg.
  apply wf_sym_select; [exact (wf_a64_sym_cond _ cond _ Hfl) | exact Ht |].
  destruct kind; [exact Hm | apply a64_wf_sym_binop; [exact Hm | apply wf_sym_bv_const]
                 | apply a64_wf_sym_binop; [exact Hm | apply wf_sym_bv_const]
                 | apply a64_wf_sym_binop; [apply wf_sym_bv_const | exact Hm]].
Qed.

Lemma wf_cfg_branch : forall allowed c dt df,
  wf_sym_expr allowed 1%positive c ->
  wf_cfg_dag allowed dt = true ->
  wf_cfg_dag allowed df = true ->
  wf_cfg_dag allowed (CD_Branch c dt df) = true.
Proof.
  intros allowed c dt df (Ht & Hw & Hlf & Hv) Hdt Hdf.
  cbn [wf_cfg_dag]; rewrite Ht, Hw, Hlf, Hv, Hdt, Hdf; reflexivity.
Qed.

Lemma mc_sym_stack_wf_mono : forall allowed sp1 sp2 stk,
  (- mc_frame_cap <= sp1)%Z ->
  (sp1 <= sp2)%Z ->
  mc_sym_stack_wf allowed sp2 stk ->
  mc_sym_stack_wf allowed sp1 stk.
Proof.
  intros allowed sp1 sp2 stk Hcap Hle Hstk.
  unfold mc_sym_stack_wf in *; apply Forall_forall; intros [[o s] sv] Hin.
  rewrite Forall_forall in Hstk; destruct (Hstk (o, s, sv) Hin) as [Hsl Hwf].
  split; [eapply mc_slot_in_frame_mono; [exact Hle | exact Hcap | exact Hsl] | exact Hwf].
Qed.

Theorem summarize_a64_dag_at_wf :
  forall fuel insts im visited pc allowed sp_off vrf astk sfl fl_def ret_w d_mc,
    (forall q, pt_get (N.succ_pos q) im = lookup_a64_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    summarize_a64_dag_at fuel im visited pc sp_off vrf astk sfl fl_def ret_w = inr d_mc ->
    wf_cfg_dag allowed d_mc = true.
Proof.
  intros fuel insts im visited pc allowed sp_off vrf astk sfl fl_def ret_w d_mc Him.
  revert visited pc allowed sp_off vrf astk sfl fl_def ret_w d_mc.
  induction fuel as [| fuel' IH];
    intros visited pc allowed sp_off vrf astk sfl fl_def ret_w d_mc Hrw Hrng Hwf Hstk Hfl Hsum;
    cbn [summarize_a64_dag_at] in Hsum.
  - destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook.
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
        | rel
        | cond rel
        | sf is_nz rt rel
        | is_nz rt bit rel
        | ].
    + exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Hsum).
    + destruct (sf && negb set_fl) eqn:E64n.
      * set (sv_opt :=
          match a64_val_read_sp rn vrf sp_off with
          | MSV_StackPtr base_off =>
              let off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z in
              if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
          | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
          | MSV_Expr e => Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
          | MSV_Undef => None
          end) in *.
        destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
        destruct (a64_val_write_sp rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
          [| discriminate Hsum].
        assert (Hsv_wf : mc_sym_val_wf allowed sv).
        { subst sv_opt; destruct (a64_val_read_sp rn vrf sp_off) as [| e | r0 | base_off] eqn:Ern; try discriminate Esv.
          - inversion Esv; subst sv; clear Esv.
            pose proof (wf_a64_val_read_sp _ _ _ _ _ Hrng Hwf Ern) as He.
            exact (proj1 (wf_a64_sym_add_sub allowed 64%positive is_sub e _ He (wf_sym_bv_z allowed 64%positive (Z.of_N imm)))).
          - destruct (N.eqb imm 0%N); [inversion Esv; exact I | discriminate Esv].
          - cbv zeta in Esv.
            destruct (Z.leb (- mc_frame_cap) _ && Z.leb _ 0%Z) eqn:Eb; [| discriminate Esv].
            apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
            inversion Esv; cbn [mc_sym_val_wf]; lia. }
        destruct (a64_val_write_sp_wf _ _ _ _ _ _ _ _ _ Hrng Hsv_wf Hwf Hstk Est) as (Hrng' & Hwf' & Hstk').
        exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng' Hwf' Hstk' Hfl Hsum).
      * destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hsum |].
        destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
        destruct (a64_sym_add_sub (a64_w sf) is_sub lhs (ce_bv_z (a64_w sf) (Z.of_N imm))) as [se sfl'] eqn:Esas.
        pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _ (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z allowed (a64_w sf) (Z.of_N imm))) as [Hre Hfl'].
        rewrite Esas in Hre, Hfl'; cbn [fst snd] in Hre, Hfl'.
        eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
        intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)].
    + destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se sfl'] eqn:Esas.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                    (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
                    (wf_a64_sym_shift _ _ _ sh amt (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm))) as [Hre Hfl'].
      rewrite Esas in Hre, Hfl'; cbn [fst snd] in Hre, Hfl'.
      eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
      intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)].
    + destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hsum |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read rm vrf) as [| rm64 | |] eqn:Erm; try discriminate Hsum.
      pose proof (Hwf rm) as Hm64; rewrite Erm in Hm64; cbn [mc_sym_val_wf] in Hm64.
      destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se sfl'] eqn:Esas.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                    (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
                    (wf_a64_sym_extend _ _ _ ext amt (a64_w_32_64 sf) Hm64)) as [Hre Hfl'].
      rewrite Esas in Hre, Hfl'; cbn [fst snd] in Hre, Hfl'.
      eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
      intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)].
    + destruct (negb set_fl && N.eqb rd 31%N); [discriminate Hsum |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      assert (Hre : wf_sym_expr allowed (a64_w sf) (a64_sym_logic_op (a64_w sf) op lhs (ce_bv_z (a64_w sf) (Z.of_N mask))))
        by (unfold a64_sym_logic_op; apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | apply wf_sym_bv_z]).
      eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
      intro Hs; destruct set_fl; [exact (wf_a64_sym_logic_flags _ _ _ Hre) | exact (Hfl Hs)].
    + destruct (a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt).
      * destruct (a64_val_read rm vrf) eqn:Erm; try discriminate Hsum;
          (eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write; [exact Hwf | pose proof (Hwf rm) as Hm0; rewrite Erm in Hm0; exact Hm0] | exact Hstk | exact Hfl | exact Hsum]).
      * destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
        destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hsum].
        assert (Hrhs : wf_sym_expr allowed (a64_w sf)
          (if inv_rm then a64_sym_not (a64_w sf) (a64_sym_shift (a64_w sf) rm_e sh amt)
           else a64_sym_shift (a64_w sf) rm_e sh amt)).
        { pose proof (wf_a64_sym_shift allowed (a64_w sf) _ sh amt (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)) as Hsh.
          destruct inv_rm; [apply a64_wf_sym_binop; [exact Hsh | apply wf_sym_bv_const] | exact Hsh]. }
        assert (Hre : wf_sym_expr allowed (a64_w sf) (a64_sym_logic_op (a64_w sf) op lhs _))
          by (unfold a64_sym_logic_op; apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact Hrhs]).
        eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
        intro Hs; destruct set_fl; [exact (wf_a64_sym_logic_flags _ _ _ Hre) | exact (Hfl Hs)].
    + destruct kind.
      * eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; apply wf_sym_bv_const] | exact Hstk | exact Hfl | exact Hsum].
      * eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write_w; [exact Hwf | apply wf_sym_bv_const] | exact Hstk | exact Hfl | exact Hsum].
      * destruct (a64_val_read_expr_w sf rd vrf) as [cur |] eqn:Erd; [| discriminate Hsum].
        eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erd) | unfold a64_sym_not; apply a64_wf_sym_binop; apply wf_sym_bv_const] | apply wf_sym_bv_const]] | exact Hstk | exact Hfl | exact Hsum].
    + destruct (a64_val_read_expr_w sf rn vrf) as [src_e |] eqn:Ern; [| discriminate Hsum].
      set (dst_opt := match kind with ABF_Bfm => a64_val_read_expr_w sf rd vrf | _ => Some (CE_BvConst (a64_w sf) 0%N) end) in *.
      destruct dst_opt as [dst_e |] eqn:Edst; [| discriminate Hsum].
      assert (Hd_wf : wf_sym_expr allowed (a64_w sf) dst_e).
      { destruct kind; subst dst_opt;
          [inversion Edst; apply wf_sym_bv_const
          | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Edst)
          | inversion Edst; apply wf_sym_bv_const]. }
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng
                (wf_a64_val_write_w _ _ sf rd _ Hwf
                   (wf_a64_sym_bitfield allowed sf kind src_e dst_e immr imms
                      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) Hd_wf))
                Hstk Hfl Hsum).
    + destruct (a64_val_read_expr_w sf rn vrf) as [hi_e |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [lo_e |] eqn:Erm; [| discriminate Hsum].
      assert (Hex : wf_sym_expr allowed (a64_w sf) (a64_sym_extr (a64_w sf) hi_e lo_e lsb)).
      { unfold a64_sym_extr; destruct (N.eqb (N.modulo lsb (N.pos (a64_w sf))) 0%N);
          [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)
          | apply a64_wf_sym_binop; apply a64_wf_sym_binop; first [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm) | apply wf_sym_bv_const]]. }
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng (wf_a64_val_write_w _ _ sf rd _ Hwf Hex) Hstk Hfl Hsum).
    + destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf ra vrf) as [ea |] eqn:Era; [| discriminate Hsum].
      eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Era) | apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)]]] | exact Hstk | exact Hfl | exact Hsum].
    + destruct (a64_val_read_expr_w false rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w false rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_val_read ra vrf) as [| ea | |] eqn:Era; try discriminate Hsum.
      pose proof (Hwf ra) as Ha; rewrite Era in Ha; cbn [mc_sym_val_wf] in Ha.
      assert (Hre : wf_sym_expr allowed 64%positive
        (CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags ea
          (CE_BinOp CB_Mul 64%positive no_binop_flags
            (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags en)
            (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags em)))).
      { apply a64_wf_sym_binop; [exact Ha | apply a64_wf_sym_binop; destruct sgn; apply wf_sym_cast; try reflexivity; first [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)]]. }
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng (wf_a64_val_write _ _ rd (MSV_Expr _) Hwf Hre) Hstk Hfl Hsum).
    + destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng
                (wf_a64_val_write_w _ _ sf rd _ Hwf (wf_a64_sym_dp2 _ _ op _ _ (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)))
                Hstk Hfl Hsum).
    + destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng
                (wf_a64_val_write_w _ _ sf rd _ Hwf (wf_a64_sym_csel _ _ kind cond sfl _ _ (Hfl eq_refl) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)))
                Hstk Hfl Hsum).
    + destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub en em) as [se csfl] eqn:Esas.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _ (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)) as [_ Hcsfl].
      rewrite Esas in Hcsfl; cbn [snd] in Hcsfl.
      pose proof (wf_a64_sym_ite_flags allowed (a64_sym_cond cond sfl) csfl (a64_sym_flags_of_imm4 nzcv)
                    (wf_a64_sym_cond _ cond _ (Hfl eq_refl)) Hcsfl (wf_a64_sym_flags_imm4 allowed nzcv)) as Hfl'.
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk (fun _ => Hfl') Hsum).
    + destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5))) as [se csfl] eqn:Esas.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _ (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z allowed (a64_w sf) (Z.of_N imm5))) as [_ Hcsfl].
      rewrite Esas in Hcsfl; cbn [snd] in Hcsfl.
      pose proof (wf_a64_sym_ite_flags allowed (a64_sym_cond cond sfl) csfl (a64_sym_flags_of_imm4 nzcv)
                    (wf_a64_sym_cond _ cond _ (Hfl eq_refl)) Hcsfl (wf_a64_sym_flags_imm4 allowed nzcv)) as Hfl'.
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk (fun _ => Hfl') Hsum).
    + (* A64_LdStImm *)
      destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hsum |].
      destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off]; try discriminate Hsum.
      set (wb_off := (base_off + imm)%Z) in *.
      set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
      destruct wb_ok eqn:Ewb; cbn [negb] in Hsum; [| discriminate Hsum].
      assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
      { destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
      destruct pair_off as [off sp_chk] eqn:Epo.
      cbv zeta in Hsum.
      assert (Hpo_eq : match mode with
                       | AAM_SignedOffset => (wb_off, sp_off)
                       | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                       | AAM_PostIndex => (base_off, sp_off)
                       end = (off, sp_chk)) by exact Epo.
      rewrite Hpo_eq in Hsum; cbv iota in Hsum.
      destruct (mc_slot_in_frame sp_chk off sz) eqn:Eslot; [| discriminate Hsum].
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
          if a64_ldst_store_sym_ok sz (a64_val_read rt vrf) then Some (vrf, mc_sym_stk_store off sz (a64_val_read rt vrf) astk) else None) in *.
      destruct st_opt as [[vrf1 astk1] |] eqn:Est;
        [try (rewrite Est in Hsum; cbv iota in Hsum) | try rewrite Est in Hsum; discriminate Hsum].
      assert (Hstep1 : wf_a64_val_regs allowed vrf1 /\ mc_sym_stack_wf allowed sp_min astk1).
      { destruct is_load; unfold st_opt in Est.
        - destruct (mc_sym_stk_load off sz is_signed astk) as [sv0 |] eqn:Esl0; [| discriminate Est].
          destruct (a64_ldst_sym_load is_signed sf_dst sv0) as [sv1 |] eqn:Esl1; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl0) as Hsv0.
          pose proof (a64_ldst_sym_load_wf _ _ _ _ _ Hsv0 Esl1) as Hsv1.
          split; [apply wf_a64_val_write; assumption | exact Hstk_min].
        - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt vrf)); [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          split; [exact Hwf | exact (mc_sym_stk_store_wf _ _ _ _ _ _ Hslot_min (Hwf rt) Hstk_min)]. }
      destruct Hstep1 as [Hwf1 Hstk1].
      assert (Hwb2 :
        let '(sp_off2, vrf2, astk2) :=
          match mode with
          | AAM_SignedOffset => (sp_off, vrf1, astk1)
          | AAM_PreIndex | AAM_PostIndex =>
              if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
              else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
          end in
        (- mc_frame_cap <= sp_off2 <= 0)%Z /\ wf_a64_val_regs allowed vrf2 /\ mc_sym_stack_wf allowed sp_off2 astk2).
      { destruct mode; inversion Epo; subst off sp_chk.
        - assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1.
          repeat split; [lia | lia | exact Hwf1 | exact Hstk1].
        - destruct (N.eqb rn 31%N);
            [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]]
            | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
              repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]].
        - destruct (N.eqb rn 31%N);
            [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]]
            | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
              repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]]. }
      destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
        as [[sp_off2 vrf2] astk2] eqn:Ewbs.
      try rewrite Ewbs in Hwb2; cbv iota in Hwb2.
      try (rewrite Ewbs in Hsum; cbv iota in Hsum).
      destruct Hwb2 as (Hrng2 & Hwf2 & Hstk2).
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng2 Hwf2 Hstk2 Hfl Hsum).
    + (* A64_LdStPair *)
      destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hsum |].
      destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off]; try discriminate Hsum.
      set (wb_off := (base_off + imm)%Z) in *.
      set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
      destruct wb_ok eqn:Ewb; cbn [negb] in Hsum; [| discriminate Hsum].
      assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
      { destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
      destruct pair_off as [off sp_chk] eqn:Epo.
      cbv zeta in Hsum.
      assert (Hpo_eq : match mode with
                       | AAM_SignedOffset => (wb_off, sp_off)
                       | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                       | AAM_PostIndex => (base_off, sp_off)
                       end = (off, sp_chk)) by exact Epo.
      rewrite Hpo_eq in Hsum; cbv iota in Hsum.
      set (sz := if sf then MS_8 else MS_4) in *; set (delta := mc_mem_bytes_Z sz) in *.
      destruct (mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz) eqn:Eslots; [| discriminate Hsum].
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
          if a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf) then
            Some (vrf, mc_sym_stk_store (off + delta) sz (a64_val_read rt2 vrf) (mc_sym_stk_store off sz (a64_val_read rt1 vrf) astk))
          else None) in *.
      destruct st_opt as [[vrf1 astk1] |] eqn:Est;
        [try (rewrite Est in Hsum; cbv iota in Hsum) | try rewrite Est in Hsum; discriminate Hsum].
      assert (Hstep1 : wf_a64_val_regs allowed vrf1 /\ mc_sym_stack_wf allowed sp_min astk1).
      { destruct is_load; unfold st_opt in Est.
        - destruct (mc_sym_stk_load off sz false astk) as [sv1 |] eqn:Esl_1; [| discriminate Est].
          destruct (mc_sym_stk_load (off + delta) sz false astk) as [sv2 |] eqn:Esl_2; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl_1) as Hsv1.
          pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl_2) as Hsv2.
          split; [apply wf_a64_val_write; [apply wf_a64_val_write; assumption | exact Hsv2] | exact Hstk_min].
        - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf));
            [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          split; [exact Hwf |].
          apply mc_sym_stk_store_wf; [exact Hslot2_min | exact (Hwf rt2) |].
          apply mc_sym_stk_store_wf; [exact Hslot1_min | exact (Hwf rt1) | exact Hstk_min]. }
      destruct Hstep1 as [Hwf1 Hstk1].
      assert (Hwb2 :
        let '(sp_off2, vrf2, astk2) :=
          match mode with
          | AAM_SignedOffset => (sp_off, vrf1, astk1)
          | AAM_PreIndex | AAM_PostIndex =>
              if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
              else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
          end in
        (- mc_frame_cap <= sp_off2 <= 0)%Z /\ wf_a64_val_regs allowed vrf2 /\ mc_sym_stack_wf allowed sp_off2 astk2).
      { destruct mode; inversion Epo; subst off sp_chk.
        - assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1.
          repeat split; [lia | lia | exact Hwf1 | exact Hstk1].
        - destruct (N.eqb rn 31%N);
            [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]]
            | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
              repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]].
        - destruct (N.eqb rn 31%N);
            [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]]
            | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
              repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]]. }
      destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
        as [[sp_off2 vrf2] astk2] eqn:Ewbs.
      try rewrite Ewbs in Hwb2; cbv iota in Hwb2.
      try (rewrite Ewbs in Hsum; cbv iota in Hsum).
      destruct Hwb2 as (Hrng2 & Hwf2 & Hstk2).
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng2 Hwf2 Hstk2 Hfl Hsum).
    + destruct (add_rel_off pc rel); [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Hsum).
    + destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl true ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl true ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      exact (wf_cfg_branch allowed _ _ _ (wf_a64_sym_cond allowed cond sfl (Hfl eq_refl))
               (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edt) (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edf)).
    + destruct (a64_val_read_expr_w sf rt vrf) as [rt_e |] eqn:Ert; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl fl_def ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      apply wf_cfg_branch;
        [apply wf_sym_icmp; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ert) | apply wf_sym_bv_const]
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edt)
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edf)].
    + destruct (a64_val_read rt vrf) as [| rt_e | |] eqn:Ert; try discriminate Hsum.
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl fl_def ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf rt) as Hrt; rewrite Ert in Hrt; cbn [mc_sym_val_wf] in Hrt.
      assert (Hmsk : wf_sym_expr allowed 64%positive (CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit))))
        by (apply a64_wf_sym_binop; [exact Hrt | apply wf_sym_bv_const]).
      apply wf_cfg_branch;
        [apply wf_sym_icmp; [exact Hmsk | apply wf_sym_bv_const]
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edt)
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edf)].
    + destruct (a64_sym_epilogue_ok sp_off vrf); [| discriminate Hsum].
      destruct (a64_val_read 0%N vrf) as [| e_ret | |] eqn:Er0; try discriminate Hsum.
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf 0%N) as Ha0; rewrite Er0 in Ha0; cbn [mc_sym_val_wf] in Ha0.
      assert (Hrte : wf_sym_expr allowed ret_w (rv_trunc_ret_expr ret_w e_ret)).
      { unfold rv_trunc_ret_expr; destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
        - apply Pos.eqb_eq in Ew64; subst ret_w; exact Ha0.
        - apply wf_sym_cast; [exact (rv_supported_arg_width_lt64 _ Hrw Ew64) | exact Ha0]. }
      destruct Hrte as (Hte & Hwe & Hlfe & Hve).
      cbn [wf_cfg_dag]; rewrite Hte, Hwe, Hlfe, Hve, Pos.eqb_refl; reflexivity.
Qed.

(** *** 5.3 AAPCS64 Upper-Bits Extension Environment & Top-Level [A64] Theorems *)

Definition a64_rf_matches_args {Pa : Params}
  (penv : param_env Pa) (specs : list rv_arg_spec) (rf : a64_regfile) : Prop :=
  forall (k : nat) sp,
    (k < List.length specs)%nat ->
    nth_error specs k = Some sp ->
    exists v : @Integers.bit_int (ras_width sp),
      penv (ras_name sp) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
      | true, RAE_None =>
          a64_read_reg (N.of_nat k) rf = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
      | false, RAE_None =>
          @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive (a64_read_reg (N.of_nat k) rf)) = v
      | false, RAE_SignExt =>
          @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (N.of_nat k) rf)) =
          @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
      | false, RAE_ZeroExt =>
          @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (N.of_nat k) rf)) =
          @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
      | _, _ => False
      end.

Fixpoint a64_extend_penv_with_hi_at {Pa : Params}
  (idx : nat) (specs : list rv_arg_spec) (rf : a64_regfile) (penv : param_env Pa)
  : param_env Pa :=
  match specs with
  | [] => penv
  | sp :: rest =>
      let penv' := a64_extend_penv_with_hi_at (S idx) rest rf penv in
      if Pos.eqb (ras_width sp) 64%positive then penv'
      else
        let hnm := a64_hi_var_name (ras_name sp) in
        let rk := a64_read_reg (N.of_nat idx) rf in
        fun x =>
          if String.eqb x hnm then Some (DVALUE_Base (@DVALUE_I Pa 64%positive rk))
          else penv' x
  end.

Definition a64_extend_penv_with_hi {Pa : Params}
  (penv : param_env Pa) (specs : list rv_arg_spec) (rf : a64_regfile)
  : param_env Pa :=
  a64_extend_penv_with_hi_at 0%nat specs rf penv.

Lemma a64_hi_var_name_inj : forall s1 s2,
  a64_hi_var_name s1 = a64_hi_var_name s2 -> s1 = s2.
Proof.
  intros s1 s2 H; unfold a64_hi_var_name in H.
  do 9 (inversion H as [H']; clear H; rename H' into H).
  exact H.
Qed.

Lemma a64_extend_penv_at_orig :
  forall {Pa : Params} idx specs rf (penv : param_env Pa) nm,
    (forall sp, In sp specs -> a64_hi_var_name (ras_name sp) <> nm) ->
    a64_extend_penv_with_hi_at idx specs rf penv nm = penv nm.
Proof.
  intros Pa idx specs rf penv nm Hdis; revert idx; induction specs as [| sp rest IH]; intro idx; cbn; [reflexivity |].
  assert (Hrest : forall s, In s rest -> a64_hi_var_name (ras_name s) <> nm)
    by (intros s Hs; apply Hdis; right; exact Hs).
  destruct (Pos.eqb (ras_width sp) 64%positive); [exact (IH Hrest (S idx)) |].
  destruct (String.eqb nm (a64_hi_var_name (ras_name sp))) eqn:Eeq.
  - apply String.eqb_eq in Eeq; exfalso; eapply Hdis; [left; reflexivity | symmetry; exact Eeq].
  - exact (IH Hrest (S idx)).
Qed.

Lemma a64_extend_penv_at_hi :
  forall {Pa : Params} idx k specs sp rf (penv : param_env Pa),
    NoDup (List.map ras_name specs) ->
    nth_error specs k = Some sp ->
    (ras_width sp =? 64)%positive = false ->
    a64_extend_penv_with_hi_at idx specs rf penv (a64_hi_var_name (ras_name sp)) =
    Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (N.of_nat (idx + k)) rf))).
Proof.
  intros Pa idx k specs sp rf penv; revert idx k;
    induction specs as [| s0 rest IH]; intros idx k Hnd Hnth Hw64; cbn [nth_error] in Hnth.
  - destruct k; discriminate Hnth.
  - cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
    destruct k as [| k']; cbn [a64_extend_penv_with_hi_at].
    + inversion Hnth; subst s0; clear Hnth.
      rewrite Hw64, String.eqb_refl, Nat.add_0_r; reflexivity.
    + destruct (Pos.eqb (ras_width s0) 64%positive).
      * replace (idx + S k')%nat with (S idx + k')%nat by lia; exact (IH _ _ Hnd_rest Hnth Hw64).
      * destruct (String.eqb (a64_hi_var_name (ras_name sp)) (a64_hi_var_name (ras_name s0))) eqn:Eeq.
        -- apply String.eqb_eq, a64_hi_var_name_inj in Eeq.
           exfalso; apply Hnin; rewrite <- Eeq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In rest k' Hnth)].
        -- replace (idx + S k')%nat with (S idx + k')%nat by lia; exact (IH _ _ Hnd_rest Hnth Hw64).
Qed.

Lemma or_low_hi_mask_eq :
  forall (k : positive) (rk : @Integers.bit_int 64%positive) (vlo : @Integers.bit_int k) (hi_mask : N),
    (k < 64)%positive ->
    hi_mask = (N.shiftl 1%N 64%N - N.shiftl 1%N (N.pos k))%N ->
    vlo = @Integers.repr k (@Integers.unsigned 64%positive rk) ->
    @Integers.or 64%positive
      (@Integers.repr 64%positive (@Integers.unsigned k vlo))
      (@Integers.and 64%positive rk (@Integers.repr 64%positive (Z.of_N hi_mask))) = rk.
Proof.
  intros k rk vlo hi_mask Hlt Hhm Hvlo.
  apply Integers.same_bits_eq; intros i Hi.
  assert (Hi64 : (0 <= i < 64)%Z) by (replace 64%Z with (@Integers.zwordsize 64%positive) by reflexivity; exact Hi).
  rewrite Integers.bits_or, Integers.bits_and, !(@Integers.testbit_repr 64%positive _ i Hi) by exact Hi.
  assert (Hhm_eq : Z.of_N hi_mask = (2 ^ 64 - 2 ^ Z.pos k)%Z).
  { rewrite Hhm, N2Z.inj_sub by (rewrite !N.shiftl_1_l; apply N.pow_le_mono_r; lia).
    rewrite !N.shiftl_1_l, !N2Z.inj_pow; reflexivity. }
  assert (Hhm_bits : Z.testbit (Z.of_N hi_mask) i = Z.leb (Z.pos k) i).
  { rewrite Hhm_eq.
    assert (Hones : (Z.ones (64 - Z.pos k) = 2 ^ (64 - Z.pos k) - 1)%Z)
      by (rewrite Z.ones_equiv; lia).
    replace (2 ^ 64 - 2 ^ Z.pos k)%Z with (Z.shiftl (Z.ones (64 - Z.pos k)) (Z.pos k))
      by (rewrite Z.shiftl_mul_pow2, Hones, Z.mul_sub_distr_r, Z.mul_1_l, <- Z.pow_add_r by lia;
          replace (64 - Z.pos k + Z.pos k)%Z with 64%Z by lia; reflexivity).
    rewrite Z.shiftl_spec by lia.
    destruct (Z.ltb i (Z.pos k)) eqn:Eik.
    - apply Z.ltb_lt in Eik.
      destruct (i - Z.pos k)%Z eqn:Ediff; try lia; symmetry; apply Z.leb_gt; lia.
    - apply Z.ltb_ge in Eik; rewrite Z.ones_spec_low by lia; symmetry; apply Z.leb_le; lia. }
  rewrite Hhm_bits.
  change (Z.testbit (@Integers.unsigned k vlo) i) with (@Integers.testbit k vlo i).
  assert (Hzwk : @Integers.zwordsize k = Z.pos k) by reflexivity.
  destruct (Z.ltb i (Z.pos k)) eqn:Eik.
  - apply Z.ltb_lt in Eik; replace (Z.leb (Z.pos k) i) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r, orb_false_r, Hvlo, (@Integers.testbit_repr k _ i) by (rewrite Hzwk; lia).
    change (Z.testbit (@Integers.unsigned 64%positive rk) i) with (@Integers.testbit 64%positive rk i); reflexivity.
  - apply Z.ltb_ge in Eik; replace (Z.leb (Z.pos k) i) with true by (symmetry; apply Z.leb_le; lia).
    rewrite andb_true_r, Integers.bits_above by (rewrite Hzwk; lia); rewrite orb_false_l.
    change (Z.testbit (@Integers.unsigned 64%positive rk) i) with (@Integers.testbit 64%positive rk i); reflexivity.
Qed.

Lemma a64_init_val_regs_wf : forall allowed_all specs,
  (forall sp, In sp specs -> In (ras_name sp, ras_width sp) allowed_all /\
                             (ras_width sp <> 64%positive -> In (a64_hi_var_name (ras_name sp), 64%positive) allowed_all)) ->
  forallb a64_valid_arg_spec specs = true ->
  wf_a64_val_regs allowed_all (a64_build_init_val_regs 0%N specs).
Proof.
  intros allowed_all specs Hall Hws.
  assert (Hgen : forall base xs,
    (forall sp, In sp xs -> In (ras_name sp, ras_width sp) allowed_all /\
                            (ras_width sp <> 64%positive -> In (a64_hi_var_name (ras_name sp), 64%positive) allowed_all)) ->
    forallb a64_valid_arg_spec xs = true ->
    wf_a64_val_regs allowed_all (a64_build_init_val_regs base xs)).
  { intros base xs; revert base; induction xs as [| sp rest IH]; intros base Hin Hws' r;
      cbn [a64_build_init_val_regs] in *.
    - unfold a64_val_read, a64_empty_val_regs.
      destruct (N.leb 31%N r); [apply wf_sym_bv_const | destruct (a64_is_callee_saved r); exact I].
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold a64_valid_arg_spec in Hwsp; rewrite !andb_true_iff in Hwsp; destruct Hwsp as ([Hwsp Hnd] & _).
      unfold a64_val_read in *.
      destruct (N.leb 31%N r) eqn:Er31; [apply wf_sym_bv_const |].
      destruct (N.eqb r base) eqn:Erb.
      + destruct (Hin sp (or_introl eq_refl)) as [Hin_lo Hin_hi].
        assert (Hvar : wf_sym_expr allowed_all (ras_width sp) (CE_Var (ras_name sp) (ras_width sp))).
        { split; [| split; [| split]]; cbn [wt_cert_expr lookup_let_width]; try exact Hnd; try reflexivity.
          apply incl_vars_subset_b; intros [nm0 w0] H0; cbn in H0; destruct H0 as [H0 | []]; inversion H0; subst; exact Hin_lo. }
        unfold a64_init_arg_expr.
        destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; rewrite Ew64 in Hvar |- *; exact Hvar.
        * assert (Hhi_var : wf_sym_expr allowed_all 64%positive (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive)).
          { split; [| split; [| split]]; cbn [wt_cert_expr lookup_let_width]; try reflexivity.
            apply incl_vars_subset_b; intros [nm0 w0] H0; cbn in H0; destruct H0 as [H0 | []]; inversion H0; subst.
            apply Hin_hi; intro C; rewrite C in Ew64; discriminate Ew64. }
          destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
          -- apply Pos.eqb_eq in Ew32; rewrite Ew32 in Hvar |- *.
             apply a64_wf_sym_binop; [apply wf_sym_cast; [reflexivity | exact Hvar] | apply a64_wf_sym_binop; [exact Hhi_var | apply wf_sym_bv_const]].
          -- assert (Hlt32 : (ras_width sp <? 32)%positive = true) by exact (a64_supported_lt32 _ Hwsp Ew64 Ew32).
             assert (Hlt64 : (ras_width sp <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             destruct (ras_ext sp).
             ++ apply a64_wf_sym_binop; [apply wf_sym_cast; [exact Hlt64 | exact Hvar] | apply a64_wf_sym_binop; [exact Hhi_var | apply wf_sym_bv_const]].
             ++ apply a64_wf_sym_binop; [apply wf_sym_cast; [reflexivity | apply wf_sym_cast; [exact Hlt32 | exact Hvar]] | apply a64_wf_sym_binop; [exact Hhi_var | apply wf_sym_bv_const]].
             ++ apply a64_wf_sym_binop; [apply wf_sym_cast; [reflexivity | apply wf_sym_cast; [exact Hlt32 | exact Hvar]] | apply a64_wf_sym_binop; [exact Hhi_var | apply wf_sym_bv_const]].
      + pose proof (IH (N.succ base) (fun s Hs => Hin s (or_intror Hs)) Hwrest r) as Hrec.
        unfold a64_val_read in Hrec; rewrite Er31 in Hrec; exact Hrec. }
  exact (Hgen 0%N specs Hall Hws).
Qed.

Lemma a64_init_val_regs_agrees :
  forall {Pa : Params} (penv : param_env Pa) foracle specs rf sp0,
    forallb a64_valid_arg_spec specs = true ->
    NoDup (List.map ras_name specs) ->
    (forall sp, In sp specs -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name specs)) ->
    a64_rf_matches_args penv specs rf ->
    a64_val_regs_agrees (a64_extend_penv_with_hi penv specs rf) foracle rf sp0
      (a64_build_init_val_regs 0%N specs) rf.
Proof.
  intros Pa penv foracle specs rf sp0 Hws Hnd Hdis Hm.
  unfold a64_extend_penv_with_hi.
  set (penv' := a64_extend_penv_with_hi_at 0%nat specs rf penv).
  assert (Hp_lo : forall sp, In sp specs -> penv' (ras_name sp) = penv (ras_name sp)).
  { intros sp Hsp; unfold penv'; apply a64_extend_penv_at_orig; intros s Hs Heq.
    apply (Hdis s Hs); rewrite Heq; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]. }
  assert (Hp_hi : forall k sp, nth_error specs k = Some sp -> (ras_width sp =? 64)%positive = false ->
    penv' (a64_hi_var_name (ras_name sp)) =
    Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (N.of_nat k) rf)))).
  { intros k sp Hnth Hw64; unfold penv'; rewrite (a64_extend_penv_at_hi 0%nat k specs sp rf penv Hnd Hnth Hw64); reflexivity. }
  assert (Hgen : forall base xs,
    (forall (j : nat) sp, (j < List.length xs)%nat -> nth_error xs j = Some sp ->
      exists v : @Integers.bit_int (ras_width sp),
        penv' (ras_name sp) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
        ((ras_width sp =? 64)%positive = false ->
          penv' (a64_hi_var_name (ras_name sp)) =
          Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (base + N.of_nat j) rf)))) /\
        match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
        | true, RAE_None =>
            a64_read_reg (base + N.of_nat j) rf = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
        | false, RAE_None =>
            @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive (a64_read_reg (base + N.of_nat j) rf)) = v
        | false, RAE_SignExt =>
            @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (base + N.of_nat j) rf)) =
            @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
        | false, RAE_ZeroExt =>
            @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (base + N.of_nat j) rf)) =
            @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
        | _, _ => False
        end) ->
    forallb a64_valid_arg_spec xs = true ->
    a64_val_regs_agrees penv' foracle rf sp0 (a64_build_init_val_regs base xs) rf).
  { intros base xs; revert base; induction xs as [| sp rest IH]; intros base Hm' Hws' r;
      cbn [a64_build_init_val_regs] in *.
    - unfold a64_val_read, a64_empty_val_regs, a64_read_reg.
      destruct (N.leb 31%N r) eqn:Er31; [cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity |].
      destruct (a64_is_callee_saved r); [cbn [mc_sym_val_agrees]; rewrite Er31; reflexivity | exact I].
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold a64_valid_arg_spec in Hwsp; rewrite !andb_true_iff in Hwsp; destruct Hwsp as ([Hwsp _] & Hext_ok).
      unfold a64_val_read in *.
      destruct (N.leb 31%N r) eqn:Er31; [unfold a64_read_reg; rewrite Er31; cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity |].
      destruct (N.eqb r base) eqn:Erb.
      + apply N.eqb_eq in Erb; subst base.
        destruct (Hm' 0%nat sp ltac:(cbn; lia) eq_refl) as (v & Hpv & Hphi & Hmatch).
        rewrite N.add_0_r in Hphi, Hmatch.
        assert (Hvar : eval_closed_cert_expr penv' foracle (CE_Var (ras_name sp) (ras_width sp)) =
                       raise_ret (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v))).
        { unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hpv; cbn [lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl; reflexivity. }
        cbn [mc_sym_val_agrees]; unfold a64_init_arg_expr.
        destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; destruct sp as [nm w ext]; cbn [ras_name ras_width ras_ext] in *; subst w.
          destruct ext; try contradiction; rewrite Hmatch, (@Integers.repr_unsigned 64%positive); exact Hvar.
        * pose proof (Hphi eq_refl) as Hhi_lk.
          assert (Hhi_var : eval_closed_cert_expr penv' foracle (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive) =
                            raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg r rf)))).
          { unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hhi_lk; cbn [lookup_let_val check_scalar_width]; reflexivity. }
          assert (Hhi_and : forall msk,
            eval_closed_cert_expr penv' foracle (CE_BinOp CB_And 64%positive no_binop_flags (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive) (CE_BvConst 64%positive msk)) =
            raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.and 64%positive (a64_read_reg r rf) (@Integers.repr 64%positive (Z.of_N msk)))))).
          { intro msk; rewrite eval_ce_binop, Hhi_var, eval_ce_const; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
          destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
          -- apply Pos.eqb_eq in Ew32; destruct sp as [nm w ext]; cbn [ras_name ras_width ras_ext] in *; subst w.
             destruct ext; try discriminate Hext_ok.
             rewrite eval_ce_binop, (eval_ce_zext _ _ 32%positive 64%positive _ v eq_refl Hvar), Hhi_and; cbn [eou_bind].
             unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op cert_to_ibinop]; cbn - [Integers.or Integers.and Integers.unsigned Integers.repr].
             do 3 f_equal; apply (@or_low_hi_mask_eq 32%positive (a64_read_reg r rf) v 18446744069414584320%N); [lia | reflexivity | symmetry; exact Hmatch].
          -- assert (Hlt32 : (ras_width sp <? 32)%positive = true) by exact (a64_supported_lt32 _ Hwsp Ew64 Ew32).
             assert (Hlt64 : (ras_width sp <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             destruct (ras_ext sp).
             ++ rewrite eval_ce_binop, (eval_ce_zext _ _ _ 64%positive _ v Hlt64 Hvar), Hhi_and; cbn [eou_bind].
                unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op cert_to_ibinop]; cbn - [Integers.or Integers.and Integers.unsigned Integers.repr].
                do 3 f_equal; apply (@or_low_hi_mask_eq (ras_width sp) (a64_read_reg r rf) v _); [apply Pos.ltb_lt; exact Hlt64 | reflexivity | symmetry; exact Hmatch].
             ++ rewrite eval_ce_binop, (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl (eval_ce_sext _ _ _ 32%positive _ v Hlt32 Hvar)), Hhi_and; cbn [eou_bind].
                unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op cert_to_ibinop]; cbn - [Integers.or Integers.and Integers.unsigned Integers.repr].
                do 3 f_equal; apply (@or_low_hi_mask_eq 32%positive (a64_read_reg r rf) _ 18446744069414584320%N); [lia | reflexivity | symmetry; exact Hmatch].
             ++ rewrite eval_ce_binop, (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl (eval_ce_zext _ _ _ 32%positive _ v Hlt32 Hvar)), Hhi_and; cbn [eou_bind].
                unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op cert_to_ibinop]; cbn - [Integers.or Integers.and Integers.unsigned Integers.repr].
                do 3 f_equal; apply (@or_low_hi_mask_eq 32%positive (a64_read_reg r rf) _ 18446744069414584320%N); [lia | reflexivity | symmetry; exact Hmatch].
      + assert (Hm_rec : forall (j : nat) sp0, (j < List.length rest)%nat -> nth_error rest j = Some sp0 ->
          exists v : @Integers.bit_int (ras_width sp0),
            penv' (ras_name sp0) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp0) v)) /\
            ((ras_width sp0 =? 64)%positive = false ->
              penv' (a64_hi_var_name (ras_name sp0)) =
              Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (N.succ base + N.of_nat j) rf)))) /\
            match Pos.eqb (ras_width sp0) 64%positive, ras_ext sp0 with
            | true, RAE_None => a64_read_reg (N.succ base + N.of_nat j) rf = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp0) v)
            | false, RAE_None => @Integers.repr (ras_width sp0) (@Integers.unsigned 64%positive (a64_read_reg (N.succ base + N.of_nat j) rf)) = v
            | false, RAE_SignExt => @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (N.succ base + N.of_nat j) rf)) = @Integers.repr 32%positive (@Integers.signed (ras_width sp0) v)
            | false, RAE_ZeroExt => @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (N.succ base + N.of_nat j) rf)) = @Integers.repr 32%positive (@Integers.unsigned (ras_width sp0) v)
            | _, _ => False
            end).
        { intros j sp1 Hj Hn; destruct (Hm' (S j) sp1 ltac:(cbn; lia) Hn) as (v & Hp0 & Hph0 & Hmt0).
          exists v; split; [exact Hp0 |]; replace (N.succ base + N.of_nat j)%N with (base + N.of_nat (S j))%N by lia; split; assumption. }
        pose proof (IH (N.succ base) Hm_rec Hwrest r) as Hrec.
        unfold a64_val_read in Hrec; rewrite Er31 in Hrec; exact Hrec. }
  apply (Hgen 0%N specs); [| exact Hws].
  intros j sp Hj Hnth.
  destruct (Hm j sp Hj Hnth) as [v [Hpv Hmt]].
  exists v; split; [rewrite (Hp_lo sp (nth_error_In _ _ Hnth)); exact Hpv |].
  split; [intro Hw64; rewrite N.add_0_l; exact (Hp_hi j sp Hnth Hw64) |].
  rewrite N.add_0_l; exact Hmt.
Qed.

Theorem summarize_a64_dag_wf :
  forall fuel insts arg_specs ret_w d_mc,
    forallb a64_inst_valid insts = true ->
    summarize_a64_dag fuel insts arg_specs ret_w = inr d_mc ->
    wf_cfg_dag
      (List.map (fun sp => (ras_name sp, ras_width sp)) arg_specs ++ a64_hi_vars arg_specs)
      d_mc = true.
Proof.
  intros fuel insts arg_specs ret_w d_mc _ Hsum.
  unfold summarize_a64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb a64_valid_arg_spec arg_specs) eqn:Hws; cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  eapply summarize_a64_dag_at_wf with (insts := insts) (sp_off := 0%Z) (fl_def := false);
    [exact (pt_of_list_first_lookup_a64 insts)
    | exact Hrw | unfold mc_frame_cap; lia | | apply mc_sym_stack_wf_empty | intros H; discriminate H | exact Hsum].
  apply a64_init_val_regs_wf; [| exact Hws].
  intros sp Hsp; split.
  - apply in_app_iff; left; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp].
  - intro Hw64; apply in_app_iff; right; unfold a64_hi_vars; apply in_flat_map; exists sp; split; [exact Hsp |].
    destruct (Pos.eqb (ras_width sp) 64%positive) eqn:E64;
      [apply Pos.eqb_eq in E64; contradiction | left; reflexivity].
Qed.

Theorem summarize_a64_dag_sound :
  forall {Pa : Params} fuel raw_bytes insts arg_specs ret_w d_mc penv foracle rf0 sp0 fl0 mstk0,
    decode_a64_bytes raw_bytes = inr insts ->
    NoDup (List.map ras_name arg_specs) ->
    (forall sp, In sp arg_specs -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name arg_specs)) ->
    summarize_a64_dag fuel insts arg_specs ret_w = inr d_mc ->
    mc_valid_sp0 sp0 ->
    a64_rf_matches_args penv arg_specs rf0 ->
    exists rf_end fl_end mstk_end,
      a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp0, fl_end, mstk_end) /\
      a64_callee_saved_preserved rf0 rf_end /\
      eval_cfg_dag (a64_extend_penv_with_hi penv arg_specs rf0) foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))).
Proof.
  intros Pa fuel raw_bytes insts arg_specs ret_w d_mc penv foracle rf0 sp0 fl0 mstk0 Hdec Hnd Hdis Hsum Hsp0 Hm.
  pose proof (decode_a64_bytes_valid raw_bytes insts Hdec) as Hval.
  unfold summarize_a64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb a64_valid_arg_spec arg_specs) eqn:Hws; cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  eapply summarize_a64_dag_at_sound with (insts := insts) (sp_off := 0%Z) (fl_def := false);
    [exact (pt_of_list_first_lookup_a64 insts)
    | exact Hrw | exact Hval | exact Hsp0 | unfold mc_frame_cap; lia | rewrite mc_add_ptr_zero; reflexivity
    | exact (a64_init_val_regs_agrees penv foracle arg_specs rf0 sp0 Hws Hnd Hdis Hm)
    | apply mc_sym_stack_agrees_empty | intros H; discriminate H | exact Hsum].
Qed.

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
  destruct (dai_inst dec) as [| sf ? ? ? ? ? | | | | | | | | | | | | | | ? ? ? ? ? ? ? | ? ? ? ? ? ? ? | rel | cond rel | ? ? ? rel | ? ? ? rel |];
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
  destruct (dai_inst dec) as [| sf ? ? ? ? ? | | | | | | | | | | | | | | ? ? ? ? ? ? ? | ? ? ? ? ? ? ? | rel | cond rel | ? ? ? rel | ? ? ? rel |];
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
    destruct (a64_exec_one_nonret d sp0 pc0 rf0 sp_a fl0 m0) as [[[[[pc' rf'] sp'] fl'] m'] |] eqn:Hs; [| discriminate H1].
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
    destruct (a64_exec_one_nonret dec sp0 pc0 rf0 sp_a fl0 m0) as [[[[[pc' rf'] sp'] fl'] m'] |] eqn:Hs; [| discriminate H1].
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
    destruct (a64_exec_one_nonret dec sp0 pc0 rf0 sp_a fl0 m0) as [[[[[pc' rf'] sp'] fl'] m'] |] eqn:Hst; [| discriminate Hs].
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
| ASSR_Next (next_pc : N) (sp_off' : Z) (vrf' : a64_val_regs) (astk' : mc_sym_stack) (sfl' : a64_sym_flags) (fl_def' : bool)
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
          | MSV_Expr e => Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
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
      let dst_opt := match kind with ABF_Bfm => a64_val_read_expr_w sf rd vrf | _ => Some (CE_BvConst (a64_w sf) 0%N) end in
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
            let wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end in
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
            let wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end in
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
              let cond_e := CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false (a64_w sf) rt_e (CE_BvConst (a64_w sf) 0%N) in
              Some (ASSR_Branch cond_e tgt_pc next_pc fl_def)
          end
      end
  | A64_Tbz is_nz rt bit rel =>
      match a64_val_read rt vrf with
      | MSV_Expr rt_e =>
          match add_rel_off pc rel with
          | None => None
          | Some tgt_pc =>
              let masked := CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit)) in
              let cond_e := CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false 64%positive masked (CE_BvConst 64%positive 0%N) in
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
  unfold a64_sym_step_one in Hstep.
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
  - inversion Hstep; subst; split; [exact Hrng | split; [exact Hwf | split; [exact Hstk | exact Hfl]]].
  - destruct (sf && negb set_fl).
    + set (sv_opt := match a64_val_read_sp rn vrf sp_off with
        | MSV_StackPtr base_off =>
            if Z.leb (- mc_frame_cap) (if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z) &&
               Z.leb (if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z) 0%Z
            then Some (MSV_StackPtr (if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z)) else None
        | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
        | MSV_Expr e => Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
        | MSV_Undef => None end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hstep].
      destruct (a64_val_write_sp rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
      inversion Hstep; subst res; clear Hstep.
      assert (Hsv : mc_sym_val_wf allowed sv).
      { subst sv_opt; destruct (a64_val_read_sp rn vrf sp_off) as [| e | r0 | base_off] eqn:Ern; try discriminate Esv.
        - inversion Esv; pose proof (wf_a64_val_read_sp allowed vrf sp_off rn _ Hrng Hwf Ern) as Hwfe; cbn [mc_sym_val_wf] in Hwfe |- *;
            exact (proj1 (wf_a64_sym_add_sub allowed 64%positive is_sub _ _ Hwfe (wf_sym_bv_z _ _ _))).
        - destruct (N.eqb imm 0%N); [inversion Esv; exact I | discriminate Esv].
        - cbv zeta in Esv; destruct (Z.leb (- mc_frame_cap) _ && Z.leb _ 0%Z) eqn:Eb; [| discriminate Esv].
          apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; inversion Esv; cbn [mc_sym_val_wf]; lia. }
      destruct (a64_val_write_sp_wf allowed rd sv sp_off vrf astk _ _ _ Hrng Hsv Hwf Hstk Est) as (Hr & Hw & Hs);
        split; [exact Hr | split; [exact Hw | split; [exact Hs | exact Hfl]]].
    + destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hstep |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
      destruct (a64_sym_add_sub (a64_w sf) is_sub lhs (ce_bv_z (a64_w sf) (Z.of_N imm))) as [se sfl'] eqn:Esas.
      inversion Hstep; subst; clear Hstep.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                    (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z _ _ (Z.of_N imm))) as Hwe; rewrite Esas in Hwe; destruct Hwe as [Hse Hsfl].
      split; [exact Hrng | split; [apply wf_a64_val_write_w; assumption | split; [exact Hstk | intro Hfs; destruct set_fl; [exact Hsfl | exact (Hfl Hfs)]]]].
  - destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                  (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
                  (wf_a64_sym_shift _ _ _ sh amt (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm))) as Hwe;
      rewrite Esas in Hwe; destruct Hwe as [Hse Hsfl].
    split; [exact Hrng | split; [apply wf_a64_val_write_w; assumption | split; [exact Hstk | intro Hfs; destruct set_fl; [exact Hsfl | exact (Hfl Hfs)]]]].
  - destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read rm vrf) as [| rm64 | |] eqn:Erm; try discriminate Hstep.
    destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (Hwf rm) as Hm64; rewrite Erm in Hm64; cbn [mc_sym_val_wf] in Hm64.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                  (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
                  (wf_a64_sym_extend _ _ _ ext amt (a64_w_32_64 sf) Hm64)) as Hwe;
      rewrite Esas in Hwe; destruct Hwe as [Hse Hsfl].
    split; [exact Hrng | split; [apply wf_a64_val_write_w; assumption | split; [exact Hstk | intro Hfs; destruct set_fl; [exact Hsfl | exact (Hfl Hfs)]]]].
  - destruct (negb set_fl && N.eqb rd 31%N); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_logic_op allowed (a64_w sf) op _ _
                  (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z _ _ (Z.of_N mask))) as Hres.
    split; [exact Hrng | split; [apply wf_a64_val_write_w; assumption | split; [exact Hstk |
      intro Hfs; destruct set_fl; [apply wf_a64_sym_logic_flags; assumption | exact (Hfl Hfs)]]]].
  - destruct (a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt).
    + destruct (a64_val_read rm vrf) eqn:Erm; try discriminate Hstep;
        match goal with |- _ =>
          inversion Hstep; subst; clear Hstep;
          split; [exact Hrng | split; [apply wf_a64_val_write; [exact Hwf | pose proof (Hwf rm) as Hm; rewrite Erm in Hm; exact Hm] | split; [exact Hstk | exact Hfl]]]
        end.
    + destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
      destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hstep].
      inversion Hstep; subst; clear Hstep.
      pose proof (wf_a64_sym_shift allowed (a64_w sf) rm_e sh amt (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)) as Hsh.
      assert (Hrhs : wf_sym_expr allowed (a64_w sf) (if inv_rm then a64_sym_not (a64_w sf) (a64_sym_shift (a64_w sf) rm_e sh amt) else a64_sym_shift (a64_w sf) rm_e sh amt))
        by (destruct inv_rm; [unfold a64_sym_not; apply a64_wf_sym_binop; [exact Hsh | apply wf_sym_bv_const] | exact Hsh]).
      pose proof (wf_a64_sym_logic_op allowed (a64_w sf) op _ _
                    (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) Hrhs) as Hres.
      split; [exact Hrng | split; [apply wf_a64_val_write_w; assumption | split; [exact Hstk |
        intro Hfs; destruct set_fl; [apply wf_a64_sym_logic_flags; exact Hres | exact (Hfl Hfs)]]]].
  - destruct kind.
    + inversion Hstep; subst; split; [exact Hrng | split; [apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; apply wf_sym_bv_const] | split; [exact Hstk | exact Hfl]]].
    + inversion Hstep; subst; split; [exact Hrng | split; [apply wf_a64_val_write_w; [exact Hwf | apply wf_sym_bv_const] | split; [exact Hstk | exact Hfl]]].
    + destruct (a64_val_read_expr_w sf rd vrf) as [cur |] eqn:Erd; [| discriminate Hstep].
      inversion Hstep; subst; split; [exact Hrng | split;
        [apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erd) | unfold a64_sym_not; apply a64_wf_sym_binop; apply wf_sym_bv_const] | apply wf_sym_bv_const]]
        | split; [exact Hstk | exact Hfl]]].
  - set (dst_opt := match kind with ABF_Bfm => a64_val_read_expr_w sf rd vrf | _ => Some (CE_BvConst (a64_w sf) 0%N) end) in *.
    destruct (a64_val_read_expr_w sf rn vrf) as [src_e |] eqn:Ern; [| discriminate Hstep].
    destruct dst_opt as [dst_e |] eqn:Edst; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    assert (Hdst : wf_sym_expr allowed (a64_w sf) dst_e)
      by (unfold dst_opt in Edst; destruct kind;
          [inversion Edst; subst; apply wf_sym_bv_const
          | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Edst)
          | inversion Edst; subst; apply wf_sym_bv_const]).
    split; [exact Hrng | split; [apply wf_a64_val_write_w; [exact Hwf | apply wf_a64_sym_bitfield; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact Hdst]] | split; [exact Hstk | exact Hfl]]].
  - destruct (a64_val_read_expr_w sf rn vrf) as [hi_e |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [lo_e |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    split; [exact Hrng | split; [apply wf_a64_val_write_w;
      [exact Hwf | unfold a64_sym_extr; destruct (N.eqb (N.modulo lsb (N.pos (a64_w sf))) 0%N);
        [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)
        | apply a64_wf_sym_binop; apply a64_wf_sym_binop; first [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm) | apply wf_sym_bv_const]]] | split; [exact Hstk | exact Hfl]]].
  - destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf ra vrf) as [ea |] eqn:Era; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    split; [exact Hrng | split; [apply wf_a64_val_write_w; [exact Hwf | destruct is_sub; apply a64_wf_sym_binop; try apply a64_wf_sym_binop;
      exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Era) || exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) || exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)] | split; [exact Hstk | exact Hfl]]].
  - destruct (a64_val_read_expr_w false rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w false rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_val_read ra vrf) as [| ea | |] eqn:Era; try discriminate Hstep.
    inversion Hstep; subst; clear Hstep.
    pose proof (Hwf ra) as Hra; rewrite Era in Hra; cbn [mc_sym_val_wf] in Hra.
    split; [exact Hrng | split; [apply wf_a64_val_write; [exact Hwf | cbn [mc_sym_val_wf];
      destruct is_sub; (apply a64_wf_sym_binop; [exact Hra | apply a64_wf_sym_binop; destruct sgn; (apply wf_sym_cast; [reflexivity | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) || exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)])])] | split; [exact Hstk | exact Hfl]]].
  - destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    split; [exact Hrng | split; [apply wf_a64_val_write_w;
      [exact Hwf | apply wf_a64_sym_dp2; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)]] | split; [exact Hstk | exact Hfl]]].
  - destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    split; [exact Hrng | split; [apply wf_a64_val_write_w;
      [exact Hwf | apply wf_a64_sym_csel; [exact (Hfl eq_refl) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)]] | split; [exact Hstk | exact Hfl]]].
  - destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub en em) as [csres csfl] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                  (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)) as [_ Hcsfl];
      rewrite Esas in Hcsfl.
    split; [exact Hrng | split; [exact Hwf | split; [exact Hstk | intro; apply wf_a64_sym_ite_flags;
      [exact (wf_a64_sym_cond allowed cond sfl (Hfl eq_refl)) | exact Hcsfl | apply wf_a64_sym_flags_imm4]]]].
  - destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5))) as [csres csfl] eqn:Esas.
    inversion Hstep; subst; clear Hstep.
    pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                  (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z _ _ (Z.of_N imm5))) as [_ Hcsfl];
      rewrite Esas in Hcsfl.
    split; [exact Hrng | split; [exact Hwf | split; [exact Hstk | intro; apply wf_a64_sym_ite_flags;
      [exact (wf_a64_sym_cond allowed cond sfl (Hfl eq_refl)) | exact Hcsfl | apply wf_a64_sym_flags_imm4]]]].
  - destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hstep |].
    destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off]; try discriminate Hstep.
    set (wb_off := (base_off + imm)%Z) in *.
    set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
    destruct wb_ok eqn:Ewb; cbn [negb] in Hstep; [| discriminate Hstep].
    assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end)
      by (destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia).
    set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
    destruct pair_off as [off sp_chk] eqn:Epo; cbv zeta in Hstep.
    assert (Hpo_eq : match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end = (off, sp_chk)) by exact Epo.
    rewrite Hpo_eq in Hstep; cbv iota in Hstep.
    destruct (mc_slot_in_frame sp_chk off sz) eqn:Eslot; [| discriminate Hstep].
    pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hchk_cap & _).
    set (sp_min := Z.min sp_off sp_chk).
    assert (Hstk_min : mc_sym_stack_wf allowed sp_min astk)
      by (eapply mc_sym_stack_wf_mono with (sp2 := sp_off); [unfold sp_min; lia | unfold sp_min; lia | exact Hstk]).
    assert (Hslot_min : mc_slot_in_frame sp_min off sz = true)
      by (eapply mc_slot_in_frame_mono with (sp2 := sp_chk); [unfold sp_min; lia | unfold sp_min; lia | exact Eslot]).
    set (st_opt := if is_load then match mc_sym_stk_load off sz is_signed astk with None => None | Some sv0 => match a64_ldst_sym_load is_signed sf_dst sv0 with None => None | Some sv1 => Some (a64_val_write rt sv1 vrf, astk) end end else if a64_ldst_store_sym_ok sz (a64_val_read rt vrf) then Some (vrf, mc_sym_stk_store off sz (a64_val_read rt vrf) astk) else None) in *.
    destruct st_opt as [[vrf1 astk1] |] eqn:Est;
      [try (rewrite Est in Hstep; cbv iota in Hstep) | try rewrite Est in Hstep; discriminate Hstep].
    assert (Hstep1 : wf_a64_val_regs allowed vrf1 /\ mc_sym_stack_wf allowed sp_min astk1).
    { destruct is_load; unfold st_opt in Est.
      - destruct (mc_sym_stk_load off sz is_signed astk) as [sv0 |] eqn:Esl0; [| discriminate Est].
        destruct (a64_ldst_sym_load is_signed sf_dst sv0) as [sv1 |] eqn:Esl1; [| discriminate Est].
        inversion Est; subst vrf1 astk1; split; [apply wf_a64_val_write; [exact Hwf | exact (a64_ldst_sym_load_wf _ _ _ _ _ (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl0) Esl1)] | exact Hstk_min].
      - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt vrf)); [| discriminate Est];
          inversion Est; subst vrf1 astk1; split; [exact Hwf | exact (mc_sym_stk_store_wf _ _ _ _ _ _ Hslot_min (Hwf rt) Hstk_min)]. }
    destruct Hstep1 as [Hwf1 Hstk1].
    assert (Hwb2 :
      let '(sp_off2, vrf2, astk2) :=
        match mode with
        | AAM_SignedOffset => (sp_off, vrf1, astk1)
        | AAM_PreIndex | AAM_PostIndex =>
            if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
            else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
        end in
      (- mc_frame_cap <= sp_off2 <= 0)%Z /\ wf_a64_val_regs allowed vrf2 /\ mc_sym_stack_wf allowed sp_off2 astk2).
    { unfold pair_off in Epo; destruct mode; inversion Epo; subst off sp_chk.
      - assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1.
        repeat split; [lia | lia | exact Hwf1 | exact Hstk1].
      - destruct (N.eqb rn 31%N);
          [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [unfold sp_min; lia | exact Hstk1]]
          | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
            repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]].
      - destruct (N.eqb rn 31%N);
          [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [unfold sp_min; lia | exact Hstk1]]
          | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
            repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]]. }
    destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
      as [[sp_off2 vrf2] astk2] eqn:Ewbs.
    try rewrite Ewbs in Hwb2; cbv iota in Hwb2.
    inversion Hstep; subst; clear Hstep.
    destruct Hwb2 as (Hr2 & Hw2 & Hs2); split; [exact Hr2 | split; [exact Hw2 | split; [exact Hs2 | exact Hfl]]].
  - destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hstep |].
    destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off]; try discriminate Hstep.
    set (wb_off := (base_off + imm)%Z) in *.
    set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
    destruct wb_ok eqn:Ewb; cbn [negb] in Hstep; [| discriminate Hstep].
    assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end)
      by (destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia).
    set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
    destruct pair_off as [off sp_chk] eqn:Epo; cbv zeta in Hstep.
    assert (Hpo_eq : match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end = (off, sp_chk)) by exact Epo.
    rewrite Hpo_eq in Hstep; cbv iota in Hstep.
    set (sz := if sf then MS_8 else MS_4) in *; set (delta := mc_mem_bytes_Z sz) in *.
    destruct (mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz) eqn:Eslots; [| discriminate Hstep].
    apply andb_true_iff in Eslots as [Esl1 Esl2].
    pose proof (mc_slot_in_frame_bounds _ _ _ Esl1) as (Hchk_cap & _).
    set (sp_min := Z.min sp_off sp_chk).
    assert (Hstk_min : mc_sym_stack_wf allowed sp_min astk)
      by (eapply mc_sym_stack_wf_mono with (sp2 := sp_off); [unfold sp_min; lia | unfold sp_min; lia | exact Hstk]).
    assert (Hslot1_min : mc_slot_in_frame sp_min off sz = true)
      by (eapply mc_slot_in_frame_mono with (sp2 := sp_chk); [unfold sp_min; lia | unfold sp_min; lia | exact Esl1]).
    assert (Hslot2_min : mc_slot_in_frame sp_min (off + delta) sz = true)
      by (eapply mc_slot_in_frame_mono with (sp2 := sp_chk); [unfold sp_min; lia | unfold sp_min; lia | exact Esl2]).
    set (st_opt := if is_load then match mc_sym_stk_load off sz false astk, mc_sym_stk_load (off + delta) sz false astk with Some sv1, Some sv2 => Some (a64_val_write rt2 sv2 (a64_val_write rt1 sv1 vrf), astk) | _, _ => None end else if a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf) then Some (vrf, mc_sym_stk_store (off + delta) sz (a64_val_read rt2 vrf) (mc_sym_stk_store off sz (a64_val_read rt1 vrf) astk)) else None) in *.
    destruct st_opt as [[vrf1 astk1] |] eqn:Est;
      [try (rewrite Est in Hstep; cbv iota in Hstep) | try rewrite Est in Hstep; discriminate Hstep].
    assert (Hstep1 : wf_a64_val_regs allowed vrf1 /\ mc_sym_stack_wf allowed sp_min astk1).
    { destruct is_load; unfold st_opt in Est.
      - destruct (mc_sym_stk_load off sz false astk) as [sv1 |] eqn:Esl_1; [| discriminate Est].
        destruct (mc_sym_stk_load (off + delta) sz false astk) as [sv2 |] eqn:Esl_2; [| discriminate Est].
        inversion Est; subst vrf1 astk1; split; [apply wf_a64_val_write; [apply wf_a64_val_write; [exact Hwf | exact (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl_1)] | exact (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl_2)] | exact Hstk_min].
      - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf)); [| discriminate Est].
        inversion Est; subst vrf1 astk1; split; [exact Hwf | apply mc_sym_stk_store_wf; [exact Hslot2_min | exact (Hwf rt2) | apply mc_sym_stk_store_wf; [exact Hslot1_min | exact (Hwf rt1) | exact Hstk_min]]]. }
    destruct Hstep1 as [Hwf1 Hstk1].
    assert (Hwb2 :
      let '(sp_off2, vrf2, astk2) :=
        match mode with
        | AAM_SignedOffset => (sp_off, vrf1, astk1)
        | AAM_PreIndex | AAM_PostIndex =>
            if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
            else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
        end in
      (- mc_frame_cap <= sp_off2 <= 0)%Z /\ wf_a64_val_regs allowed vrf2 /\ mc_sym_stack_wf allowed sp_off2 astk2).
    { unfold pair_off in Epo; destruct mode; inversion Epo; subst off sp_chk.
      - assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1.
        repeat split; [lia | lia | exact Hwf1 | exact Hstk1].
      - destruct (N.eqb rn 31%N);
          [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [unfold sp_min; lia | exact Hstk1]]
          | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
            repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]].
      - destruct (N.eqb rn 31%N);
          [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [unfold sp_min; lia | exact Hstk1]]
          | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
            repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]]. }
    destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
      as [[sp_off2 vrf2] astk2] eqn:Ewbs.
    try rewrite Ewbs in Hwb2; cbv iota in Hwb2.
    inversion Hstep; subst; clear Hstep.
    destruct Hwb2 as (Hr2 & Hw2 & Hs2); split; [exact Hr2 | split; [exact Hw2 | split; [exact Hs2 | exact Hfl]]].
  - destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst; split; [exact Hrng | split; [exact Hwf | split; [exact Hstk | exact Hfl]]].
  - destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst; split; [exact (wf_a64_sym_cond allowed cond sfl (Hfl eq_refl)) | intro Hf; exact Hf].
  - destruct (a64_val_read_expr_w sf rt vrf) as [rt_e |] eqn:Ert; [| discriminate Hstep].
    destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst; split; [apply wf_sym_icmp; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ert) | apply wf_sym_bv_const] | intro Hf; exact Hf].
  - destruct (a64_val_read rt vrf) as [| rt_e | |] eqn:Ert; try discriminate Hstep.
    destruct (add_rel_off pc rel); [| discriminate Hstep].
    inversion Hstep; subst; pose proof (Hwf rt) as Hrt; rewrite Ert in Hrt; cbn [mc_sym_val_wf] in Hrt.
    split; [apply wf_sym_icmp; [apply a64_wf_sym_binop; [exact Hrt | apply wf_sym_bv_const] | apply wf_sym_bv_const] | intro Hf; exact Hf].
  - destruct (a64_sym_epilogue_ok sp_off vrf); [| discriminate Hstep].
    destruct (a64_val_read 0%N vrf) as [| e_ret | |] eqn:Er0; try discriminate Hstep.
    inversion Hstep; subst; pose proof (Hwf 0%N) as Ha0; rewrite Er0 in Ha0; cbn [mc_sym_val_wf] in Ha0.
    unfold rv_trunc_ret_expr; destruct (Pos.eqb ret_w 64%positive) eqn:Ew64;
      [apply Pos.eqb_eq in Ew64; subst ret_w; exact Ha0 | apply wf_sym_cast; [exact (rv_supported_arg_width_lt64 _ Hrw Ew64) | exact Ha0]].
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
  unfold a64_sym_step_one in Hstep.
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
      | rel | cond rel | sf is_nz rt rel | is_nz rt bit rel | ] eqn:Ed;
    try (unfold a64_exec_one_nonret; rewrite Ed).
  - inversion Hstep; subst; eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [exact Hag | split; [exact Hastk | exact Hfl]]]]].
  - destruct (sf && negb set_fl) eqn:E64n.
    + set (sv_opt := match a64_val_read_sp rn vrf sp_off with
        | MSV_StackPtr base_off =>
            if Z.leb (- mc_frame_cap) (if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z) &&
               Z.leb (if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z) 0%Z
            then Some (MSV_StackPtr (if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z)) else None
        | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
        | MSV_Expr e => Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
        | MSV_Undef => None end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hstep].
      destruct (a64_val_write_sp rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hstep].
      inversion Hstep; subst res; clear Hstep.
      assert (Hsv_ag : mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv
        (if is_sub then @Integers.sub 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive (Z.of_N imm))
         else @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive (Z.of_N imm)))).
      { pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag eq_refl) as Hrn.
        subst sv_opt; destruct (a64_val_read_sp rn vrf sp_off) as [| e | r0 | base_off] eqn:Ern; try discriminate Esv.
        - inversion Esv; subst sv; clear Esv; cbn [mc_sym_val_agrees] in Hrn |- *.
          pose proof (eval_a64_sym_add_sub_sound penv foracle 64%positive is_sub _ _ _ _ Hrn (eval_ce_bv_z _ _ 64%positive (Z.of_N imm))) as [Hres _]; exact Hres.
        - destruct (N.eqb imm 0%N) eqn:Ez; [| discriminate Esv]; apply N.eqb_eq in Ez; subst imm; inversion Esv; subst sv; clear Esv.
          cbn [mc_sym_val_agrees] in Hrn |- *; destruct is_sub.
          + unfold Integers.sub; change (Z.of_N 0%N) with 0%Z; rewrite (@Integers.unsigned_repr 64%positive 0%Z) by (compute; split; discriminate); rewrite Z.sub_0_r, Integers.repr_unsigned; exact Hrn.
          + rewrite Hrn, mc_add_ptr_zero; reflexivity.
        - cbv zeta in Esv; destruct (Z.leb (- mc_frame_cap) _ && Z.leb _ 0%Z) eqn:Erng; [| discriminate Esv].
          apply andb_true_iff in Erng as [Er1 Er2]; apply Z.leb_le in Er1; apply Z.leb_le in Er2; inversion Esv; subst sv; clear Esv.
          cbn [mc_sym_val_agrees] in Hrn |- *; destruct Hrn as [_ Hptr]; split; [lia | rewrite Hptr; destruct is_sub; [apply mc_sub_ptr_off | apply mc_add_ptr_off]]. }
      pose proof (a64_val_write_sp_bounds _ _ _ _ _ _ _ _ Hrng Est) as Hrng'.
      pose proof (a64_val_write_sp_sound penv foracle rf0 sp0 rd sv _ sp_off vrf astk rf sp mstk sp_off' vrf' astk' Hsp Hag Hastk Hsv_ag Est) as Hwr.
      destruct (a64_write_reg_sp rd _ rf sp) as [rf' sp'] eqn:Ewr.
      destruct Hwr as (Hsp' & Hag' & Hastk').
      eexists _, _, _, _; split; [reflexivity | split; [exact Hrng' | split; [exact Hsp' | split; [exact Hag' | split; [exact Hastk' | exact Hfl]]]]].
    + destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hstep |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
      destruct (a64_sym_add_sub (a64_w sf) is_sub lhs (ce_bv_z (a64_w sf) (Z.of_N imm))) as [se sfl'] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm))) as [vr fl'] eqn:Eeas.
      inversion Hstep; subst; clear Hstep.
      pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm))) as [Hres Hfl'].
      rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
      eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]]]]]].
  - destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hstep].
    unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply andb_true_iff in Hdec_val as [_ Hamt]; apply N.ltb_lt in Hamt.
    pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf) ltac:(destruct sf; exact Hamt)
                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hsh.
    destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl'] eqn:Eeas.
    inversion Hstep; subst; clear Hstep.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _ (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) Hsh) as [Hres Hfl'].
    rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]]]]]].
  - destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read rm vrf) as [| rm64 | |] eqn:Erm; try discriminate Hstep.
    unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.leb_le in Hdec_val.
    pose proof (Hag rm) as Hm64; rewrite Erm in Hm64; cbn [mc_sym_val_agrees] in Hm64.
    pose proof (eval_a64_sym_extend_sound _ _ (a64_w sf) _ _ ext amt (a64_w_32_64 sf) Hdec_val Hm64) as Hext.
    destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl'] eqn:Eeas.
    inversion Hstep; subst; clear Hstep.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _ (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) Hext) as [Hres Hfl'].
    rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]]]]]].
  - destruct (negb set_fl && N.eqb rd 31%N); [discriminate Hstep |].
    destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    assert (Hres : eval_closed_cert_expr penv foracle (a64_sym_logic_op (a64_w sf) op lhs (ce_bv_z (a64_w sf) (Z.of_N mask))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
        (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N mask)))))).
    { unfold a64_sym_logic_op, a64_eval_logic_op; rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), eval_ce_bv_z; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | intro Hs; destruct set_fl; [exact (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) | exact (Hfl Hs)]]]]]].
  - destruct (a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt) eqn:Emov.
    + unfold a64_is_orr_mov64 in Emov; rewrite !andb_true_iff in Emov;
      destruct Emov as ((((((Esf & Hninv) & Hnsfl) & Hrn) & Hamt) & Hop) & Hsh);
      apply negb_true_iff in Hninv; apply negb_true_iff in Hnsfl; apply N.eqb_eq in Hrn; apply N.eqb_eq in Hamt;
      subst sf inv_rm set_fl rn amt; destruct op; try discriminate Hop; destruct sh; try discriminate Hsh.
      pose proof (Hag rm) as Hrm;
      destruct (a64_val_read rm vrf) eqn:Erm; try discriminate Hstep;
        match goal with |- _ =>
          inversion Hstep; subst; clear Hstep;
          cbn [a64_w a64_read_w a64_eval_logic_op a64_write_w];
          replace (a64_read_reg 31%N rf) with (@Integers.zero 64%positive) by reflexivity;
          rewrite a64_orr_xzr_lsl0;
          eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write; assumption | split; [exact Hastk | exact Hfl]]]]]
        end.
    + destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hstep].
      destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hstep].
      inversion Hstep; subst; clear Hstep.
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.ltb_lt in Hdec_val.
      pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf) ltac:(destruct sf; exact Hdec_val)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hsh.
      assert (Hrhs : eval_closed_cert_expr penv foracle (if inv_rm then a64_sym_not (a64_w sf) (a64_sym_shift (a64_w sf) rm_e sh amt) else a64_sym_shift (a64_w sf) rm_e sh amt) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
          (if inv_rm then @Integers.not (a64_w sf) (a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt)
           else a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt))))
        by (destruct inv_rm; [exact (eval_ce_not _ _ _ _ _ Hsh) | exact Hsh]).
      assert (Hres : eval_closed_cert_expr penv foracle
                (a64_sym_logic_op (a64_w sf) op lhs
                  (if inv_rm then a64_sym_not (a64_w sf) (a64_sym_shift (a64_w sf) rm_e sh amt)
                   else a64_sym_shift (a64_w sf) rm_e sh amt)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
          (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf)
            (if inv_rm then @Integers.not (a64_w sf) (a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt)
             else a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt))))).
      { unfold a64_sym_logic_op, a64_eval_logic_op; rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), Hrhs; cbn [eou_bind];
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
      eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | intro Hs; destruct set_fl; [exact (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) | exact (Hfl Hs)]]]]]].
  - destruct kind.
    + inversion Hstep; subst; clear Hstep; eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; [exact Hag | exact (eval_ce_not _ _ _ _ _ (eval_ce_bv_z _ _ _ _))] | split; [exact Hastk | exact Hfl]]]]].
    + inversion Hstep; subst; clear Hstep; eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; [exact Hag | exact (eval_ce_bv_z _ _ _ _)] | split; [exact Hastk | exact Hfl]]]]].
    + destruct (a64_val_read_expr_w sf rd vrf) as [cur |] eqn:Erd; [| discriminate Hstep].
      inversion Hstep; subst; clear Hstep; eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [| split; [exact Hastk | exact Hfl]]]]].
      apply a64_val_regs_agrees_write_w; [exact Hag |].
      change (Z.pos (Pos.shiftl 65535 shift)) with (Z.of_N (N.shiftl 65535%N shift)).
      assert (Hand : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And (a64_w sf) no_binop_flags cur (a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl 65535%N shift))))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
          (@Integers.and (a64_w sf) (a64_read_w sf rd rf) (@Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))))).
      { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erd), (eval_ce_not _ _ _ _ _ (eval_ce_bv_z _ _ _ _));
          cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      rewrite eval_ce_binop, Hand, eval_ce_bv_z; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
  - set (dst_opt := match kind with ABF_Bfm => a64_val_read_expr_w sf rd vrf | _ => Some (CE_BvConst (a64_w sf) 0%N) end) in *.
    destruct (a64_val_read_expr_w sf rn vrf) as [src_e |] eqn:Ern; [| discriminate Hstep].
    destruct dst_opt as [dst_e |] eqn:Edst; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply andb_true_iff in Hdec_val as [Hr1 Hs1]; apply N.ltb_lt in Hr1; apply N.ltb_lt in Hs1.
    assert (Hres : eval_closed_cert_expr penv foracle (a64_sym_bitfield (a64_w sf) kind src_e dst_e immr imms) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_eval_bitfield (a64_w sf) kind (a64_read_w sf rn rf) (a64_read_w sf rd rf) immr imms)))).
    { destruct kind.
      - subst dst_opt; inversion Edst; subst dst_e.
        epose proof (eval_a64_sym_bitfield_sound penv foracle sf ABF_Sbfm src_e (CE_BvConst (a64_w sf) 0%N) _ (@Integers.zero (a64_w sf)) immr imms Hr1 Hs1
                       (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hbf.
        cbn [a64_sym_bitfield a64_eval_bitfield] in Hbf |- *; destruct (N.leb immr imms); exact Hbf.
      - subst dst_opt; exact (eval_a64_sym_bitfield_sound _ _ sf ABF_Bfm _ _ _ _ _ _ Hr1 Hs1
                                (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                                (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Edst)).
      - subst dst_opt; inversion Edst; subst dst_e.
        epose proof (eval_a64_sym_bitfield_sound penv foracle sf ABF_Ubfm src_e (CE_BvConst (a64_w sf) 0%N) _ (@Integers.zero (a64_w sf)) immr imms Hr1 Hs1
                       (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hbf.
        cbn [a64_sym_bitfield a64_eval_bitfield] in Hbf |- *; destruct (N.leb immr imms); exact Hbf. }
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | exact Hfl]]]]].
  - destruct (a64_val_read_expr_w sf rn vrf) as [hi_e |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [lo_e |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; [exact Hag |
      exact (eval_a64_sym_extr_sound _ _ (a64_w sf) _ _ _ _ lsb (a64_w_32_64 sf)
               (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm))] | split; [exact Hastk | exact Hfl]]]]].
  - destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf ra vrf) as [ea |] eqn:Era; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    assert (Hmul : eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul (a64_w sf) no_binop_flags en em) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (@Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf)))))
      by (rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm); cbn [eou_bind]; destruct sf; unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.mul a64_read_w]; reflexivity).
    assert (Hres : eval_closed_cert_expr penv foracle (CE_BinOp (if is_sub then CB_Sub else CB_Add) (a64_w sf) no_binop_flags ea (CE_BinOp CB_Mul (a64_w sf) no_binop_flags en em)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (let p := @Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf) in if is_sub then @Integers.sub (a64_w sf) (a64_read_w sf ra rf) p else @Integers.add (a64_w sf) (a64_read_w sf ra rf) p))))
      by (rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Era), Hmul; cbn [eou_bind]; destruct sf, is_sub; unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.mul Integers.add Integers.sub a64_read_w]; reflexivity).
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; assumption | split; [exact Hastk | exact Hfl]]]]].
  - destruct (a64_val_read_expr_w false rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w false rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_val_read ra vrf) as [| ea | |] eqn:Era; try discriminate Hstep.
    inversion Hstep; subst; clear Hstep.
    pose proof (Hag ra) as Hra; rewrite Era in Hra; cbn [mc_sym_val_agrees] in Hra.
    set (n64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive (a64_read_w false rn rf) else @Integers.unsigned 32%positive (a64_read_w false rn rf))).
    set (m64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive (a64_read_w false rm rf) else @Integers.unsigned 32%positive (a64_read_w false rm rf))).
    assert (Hn64 : eval_closed_cert_expr penv foracle (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags en) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive n64)))
      by (unfold n64; destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; exact (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)).
    assert (Hm64 : eval_closed_cert_expr penv foracle (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags em) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive m64)))
      by (unfold m64; destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; exact (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)).
    assert (Hmul : eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul 64%positive no_binop_flags _ _) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.mul 64%positive n64 m64))))
      by (rewrite eval_ce_binop, Hn64, Hm64; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.mul n64 m64]; reflexivity).
    assert (Hres : eval_closed_cert_expr penv foracle (CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags ea (CE_BinOp CB_Mul 64%positive no_binop_flags _ _)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (if is_sub then @Integers.sub 64%positive (a64_read_reg ra rf) (@Integers.mul 64%positive n64 m64) else @Integers.add 64%positive (a64_read_reg ra rf) (@Integers.mul 64%positive n64 m64)))))
      by (rewrite eval_ce_binop, Hra, Hmul; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct is_sub; cbn - [Integers.mul Integers.add Integers.sub n64 m64 a64_read_reg]; reflexivity).
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write; assumption | split; [exact Hastk | exact Hfl]]]]].
  - destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; [exact Hag |
      exact (eval_a64_sym_dp2_sound _ _ (a64_w sf) op _ _ _ _ (a64_w_32_64 sf)
               (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm))] | split; [exact Hastk | exact Hfl]]]]].
  - destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    inversion Hstep; subst; clear Hstep.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [apply a64_val_regs_agrees_write_w; [exact Hag |
      exact (eval_a64_sym_csel_sound _ _ (a64_w sf) kind cond sfl fl _ _ _ _ (Hfl eq_refl)
               (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm))] | split; [exact Hastk | exact Hfl]]]]].
  - destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub en em) as [csres csfl] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (a64_read_w sf rm rf)) as [cvr cfl] eqn:Eeas.
    inversion Hstep; subst; clear Hstep.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as [_ Hcsfl].
    rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [exact Hag | split; [exact Hastk |
      intro; exact (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _ (eval_a64_sym_cond_sound _ _ cond _ _ (Hfl eq_refl)) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv))]]]]].
  - destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hstep].
    destruct (a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5))) as [csres csfl] eqn:Esas.
    destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm5))) as [cvr cfl] eqn:Eeas.
    inversion Hstep; subst; clear Hstep.
    pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm5))) as [_ Hcsfl].
    rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng | split; [reflexivity | split; [exact Hag | split; [exact Hastk |
      intro; exact (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _ (eval_a64_sym_cond_sound _ _ cond _ _ (Hfl eq_refl)) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv))]]]]].
  - destruct Hsp0 as [Hsp0_cap Hsp0_al].
    assert (Hsp_to_off : mc_addr_to_off sp0 sp = sp_off) by (rewrite Hsp; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
    rewrite Hsp_to_off.
    destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hstep |].
    destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off] eqn:Ern; try discriminate Hstep.
    pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag Ern) as Hrn_ag.
    cbn [mc_sym_val_agrees] in Hrn_ag; destruct Hrn_ag as [Hbase_rng Hbase_ptr].
    set (wb_off := (base_off + imm)%Z) in *.
    set (wb_addr := @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive imm)) in *.
    assert (Hwb_ptr : wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off))
      by (unfold wb_addr, wb_off; rewrite Hbase_ptr, mc_add_ptr_off; reflexivity).
    set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
    destruct wb_ok eqn:Ewb; cbn [negb] in Hstep; [| discriminate Hstep].
    assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end)
      by (destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia).
    set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
    destruct pair_off as [off sp_chk] eqn:Epo; cbv zeta in Hstep.
    assert (Hpo_eq : match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end = (off, sp_chk)) by exact Epo.
    rewrite Hpo_eq in Hstep; cbv iota in Hstep.
    destruct (mc_slot_in_frame sp_chk off sz) eqn:Eslot; [| discriminate Hstep].
    pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
    assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
    assert (Hc_eq : mc_addr_to_off sp0 (match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end) = off /\
                    mc_addr_to_off sp0 (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end) = sp_chk).
    { unfold pair_off in Epo; destruct mode; inversion Epo; subst off sp_chk; split;
        try (rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia]);
        try exact Hsp_to_off;
        try (destruct (N.eqb rn 31%N); [rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia] | exact Hsp_to_off]);
        rewrite Hbase_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hbase_rng]. }
    destruct Hc_eq as [Hoff_c Hspchk_c].
    replace (match mode with AAM_SignedOffset => (wb_addr, sp) | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp) | AAM_PostIndex => (a64_read_reg_sp rn rf sp, sp) end)
      with ((match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end),
            (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end))
      by (destruct mode; reflexivity).
    cbn [fst snd]; rewrite Hoff_c, Hspchk_c, Eslot.
    set (st_opt := if is_load then match mc_sym_stk_load off sz is_signed astk with None => None | Some sv0 => match a64_ldst_sym_load is_signed sf_dst sv0 with None => None | Some sv1 => Some (a64_val_write rt sv1 vrf, astk) end end else if a64_ldst_store_sym_ok sz (a64_val_read rt vrf) then Some (vrf, mc_sym_stk_store off sz (a64_val_read rt vrf) astk) else None) in *.
    destruct st_opt as [[vrf1 astk1] |] eqn:Est;
      [try (rewrite Est in Hstep; cbv iota in Hstep) | try rewrite Est in Hstep; discriminate Hstep].
    assert (Hstep1 :
      let '(rf1, mstk1) :=
        if is_load then (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk)
        else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf)) in
      a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
      mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1).
    { destruct is_load; unfold st_opt in Est.
      - destruct (mc_sym_stk_load off sz is_signed astk) as [sv0 |] eqn:Esl0; [| discriminate Est].
        destruct (a64_ldst_sym_load is_signed sf_dst sv0) as [sv1 |] eqn:Esl1; [| discriminate Est].
        inversion Est; subst vrf1 astk1; split;
          [apply a64_val_regs_agrees_write; [exact Hag | exact (a64_ldst_sym_load_sound _ _ _ _ _ _ _ _ _ (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl0) Esl1)] | exact Hastk].
      - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt vrf)) eqn:Eok; [| discriminate Est]; inversion Est; subst vrf1 astk1.
        assert (Hszm : match a64_val_read rt vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
          by (destruct (a64_val_read rt vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok).
        split; [exact Hag | apply mc_sym_stk_store_agrees; [exact Hszm | exact (Hag rt) | exact Hastk]]. }
    set (rf1 := if is_load then a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf else rf) in *.
    set (mstk1 := if is_load then mstk else mc_stk_store mstk off sz (a64_read_reg rt rf)) in *.
    assert (Hstep1' : a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\ mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1)
      by (destruct is_load; exact Hstep1).
    destruct Hstep1' as [Hag1 Hastk1].
    pose proof (a64_ldst_writeback_sound penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr Hrng Hsp Hwb_rng Hwb_ptr Hag1 Hastk1) as Hwb_s.
    destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
      as [[sp_off2 vrf2] astk2] eqn:Ewbs.
    destruct (match mode with AAM_SignedOffset => (rf1, sp) | _ => a64_write_reg_sp rn wb_addr rf1 sp end) as [rf2 sp2] eqn:Ewbc.
    try rewrite Ewbs in Hwb_s; try rewrite Ewbc in Hwb_s; cbv iota in Hwb_s; inversion Hstep; subst res; clear Hstep.
    destruct Hwb_s as (Hrng2 & Hsp2 & Hag2 & Hastk2).
    replace (if is_load then (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk) else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf)))
      with (rf1, mstk1) by (destruct is_load; reflexivity); rewrite Ewbc.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng2 | split; [exact Hsp2 | split; [exact Hag2 | split; [exact Hastk2 | exact Hfl]]]]].
  - destruct Hsp0 as [Hsp0_cap Hsp0_al].
    assert (Hsp_to_off : mc_addr_to_off sp0 sp = sp_off) by (rewrite Hsp; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
    rewrite Hsp_to_off.
    destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hstep |].
    destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off] eqn:Ern; try discriminate Hstep.
    pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag Ern) as Hrn_ag.
    cbn [mc_sym_val_agrees] in Hrn_ag; destruct Hrn_ag as [Hbase_rng Hbase_ptr].
    set (wb_off := (base_off + imm)%Z) in *.
    set (wb_addr := @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive imm)) in *.
    assert (Hwb_ptr : wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off))
      by (unfold wb_addr, wb_off; rewrite Hbase_ptr, mc_add_ptr_off; reflexivity).
    set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
    destruct wb_ok eqn:Ewb; cbn [negb] in Hstep; [| discriminate Hstep].
    assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end)
      by (destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia).
    set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
    destruct pair_off as [off sp_chk] eqn:Epo; cbv zeta in Hstep.
    assert (Hpo_eq : match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end = (off, sp_chk)) by exact Epo.
    rewrite Hpo_eq in Hstep; cbv iota in Hstep.
    set (sz := if sf then MS_8 else MS_4) in *; set (delta := mc_mem_bytes_Z sz) in *.
    destruct (mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz) eqn:Eslots; [| discriminate Hstep].
    apply andb_true_iff in Eslots as [Esl1 Esl2].
    pose proof (mc_slot_in_frame_bounds _ _ _ Esl1) as (Hb1 & Hb2 & Hb3 & _).
    pose proof (mc_slot_in_frame_bounds _ _ _ Esl2) as (_ & Hb2' & Hb3' & _).
    assert (Hsz_pos : (1 <= delta)%Z) by (unfold delta, sz; destruct sf; cbn; lia).
    assert (Hc_eq : mc_addr_to_off sp0 (match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end) = off /\
                    mc_addr_to_off sp0 (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end) = sp_chk).
    { unfold pair_off in Epo; destruct mode; inversion Epo; subst off sp_chk; split;
        try (rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia]);
        try exact Hsp_to_off;
        try (destruct (N.eqb rn 31%N); [rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia] | exact Hsp_to_off]);
        rewrite Hbase_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hbase_rng]. }
    destruct Hc_eq as [Hoff_c Hspchk_c].
    replace (match mode with AAM_SignedOffset => (wb_addr, sp) | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp) | AAM_PostIndex => (a64_read_reg_sp rn rf sp, sp) end)
      with ((match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end),
            (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end))
      by (destruct mode; reflexivity).
    cbn [fst snd]; rewrite Hoff_c, Hspchk_c, Esl1, Esl2; cbn [andb].
    set (st_opt := if is_load then match mc_sym_stk_load off sz false astk, mc_sym_stk_load (off + delta) sz false astk with Some sv1, Some sv2 => Some (a64_val_write rt2 sv2 (a64_val_write rt1 sv1 vrf), astk) | _, _ => None end else if a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf) then Some (vrf, mc_sym_stk_store (off + delta) sz (a64_val_read rt2 vrf) (mc_sym_stk_store off sz (a64_val_read rt1 vrf) astk)) else None) in *.
    destruct st_opt as [[vrf1 astk1] |] eqn:Est;
      [try (rewrite Est in Hstep; cbv iota in Hstep) | try rewrite Est in Hstep; discriminate Hstep].
    assert (Hstep1 :
      let '(rf1, mstk1) :=
        if is_load then (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk)
        else (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)) in
      a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
      mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1).
    { destruct is_load; unfold st_opt in Est.
      - destruct (mc_sym_stk_load off sz false astk) as [sv1 |] eqn:Esl_1; [| discriminate Est].
        destruct (mc_sym_stk_load (off + delta) sz false astk) as [sv2 |] eqn:Esl_2; [| discriminate Est].
        inversion Est; subst vrf1 astk1; split;
          [apply a64_val_regs_agrees_write; [apply a64_val_regs_agrees_write; [exact Hag | exact (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl_1)] | exact (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl_2)] | exact Hastk].
      - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf)) eqn:Eok; [| discriminate Est].
        apply andb_true_iff in Eok as [Eok1 Eok2]; inversion Est; subst vrf1 astk1.
        assert (Hszm1 : match a64_val_read rt1 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
          by (destruct (a64_val_read rt1 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok1).
        assert (Hszm2 : match a64_val_read rt2 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
          by (destruct (a64_val_read rt2 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok2).
        split; [exact Hag | apply mc_sym_stk_store_agrees; [exact Hszm2 | exact (Hag rt2) | apply mc_sym_stk_store_agrees; [exact Hszm1 | exact (Hag rt1) | exact Hastk]]]. }
    set (rf1 := if is_load then a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf) else rf) in *.
    set (mstk1 := if is_load then mstk else mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)) in *.
    assert (Hstep1' : a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\ mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1)
      by (destruct is_load; exact Hstep1).
    destruct Hstep1' as [Hag1 Hastk1].
    pose proof (a64_ldst_writeback_sound penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr Hrng Hsp Hwb_rng Hwb_ptr Hag1 Hastk1) as Hwb_s.
    destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
      as [[sp_off2 vrf2] astk2] eqn:Ewbs.
    destruct (match mode with AAM_SignedOffset => (rf1, sp) | _ => a64_write_reg_sp rn wb_addr rf1 sp end) as [rf2 sp2] eqn:Ewbc.
    try rewrite Ewbs in Hwb_s; try rewrite Ewbc in Hwb_s; cbv iota in Hwb_s; inversion Hstep; subst res; clear Hstep.
    destruct Hwb_s as (Hrng2 & Hsp2 & Hag2 & Hastk2).
    replace (if is_load then (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk) else (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)))
      with (rf1, mstk1) by (destruct is_load; reflexivity); rewrite Ewbc.
    eexists _, _, _, _; split; [reflexivity | split; [exact Hrng2 | split; [exact Hsp2 | split; [exact Hag2 | split; [exact Hastk2 | exact Hfl]]]]].
  - destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep]; inversion Hstep; subst.
    eexists _, _, _, _; split; [cbv zeta iota; try rewrite Erel; reflexivity | split; [exact Hrng | split; [reflexivity | split; [exact Hag | split; [exact Hastk | exact Hfl]]]]].
  - destruct fl_def eqn:Efld; cbn [negb] in Hstep; [| discriminate Hstep].
    destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep]; inversion Hstep; subst; clear Hstep.
    exists (a64_eval_cond cond fl); split; [exact (eval_a64_sym_cond_sound penv foracle cond sfl fl (Hfl eq_refl)) |].
    split; [cbv zeta iota; destruct (a64_eval_cond cond fl); try rewrite Erel; reflexivity | intro; reflexivity].
  - destruct (a64_val_read_expr_w sf rt vrf) as [rt_e |] eqn:Ert; [| discriminate Hstep].
    destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep]; inversion Hstep; subst; clear Hstep.
    set (b := if is_nz then negb (@Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf))) else @Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf))).
    exists b; split; [| split; [| intro Hf; exact Hf]].
    + unfold b; destruct is_nz;
        [exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ert) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))
        | exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ert) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))].
    + cbv zeta iota; destruct b; try rewrite Erel; reflexivity.
  - destruct (a64_val_read rt vrf) as [| rt_e | |] eqn:Ert; try discriminate Hstep.
    destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hstep]; inversion Hstep; subst; clear Hstep.
    unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.ltb_lt in Hdec_val.
    pose proof (Hag rt) as Hrt; rewrite Ert in Hrt; cbn [mc_sym_val_agrees] in Hrt.
    assert (Hm : eval_closed_cert_expr penv foracle (CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))))))
      by (rewrite eval_ce_binop, Hrt, eval_ce_const; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity).
    assert (Heq_tb : negb (@Integers.eq 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))) (@Integers.zero 64%positive)) =
                     Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)).
    { pose proof (integers_eq_zero_iff 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) as Hiz.
      destruct (@Integers.eq 64%positive _ _) eqn:Ez, (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)) eqn:Etb; try reflexivity.
      - exfalso; pose proof (proj1 Hiz eq_refl) as Hz.
        assert (Hb : Z.testbit (@Integers.unsigned 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) (Z.of_N bit) = false)
          by (rewrite Hz; apply Z.testbit_0_l).
        change (Z.testbit (@Integers.unsigned 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) (Z.of_N bit))
          with (@Integers.testbit 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))) (Z.of_N bit)) in Hb.
        rewrite Integers.bits_and, (@Integers.testbit_repr 64%positive _ (Z.of_N bit)) in Hb by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
        rewrite N.shiftl_1_l, N2Z.inj_pow, Z.pow2_bits_true in Hb by lia; unfold Integers.testbit in Hb; rewrite Etb in Hb; discriminate Hb.
      - exfalso; assert (Hnz : @Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))) = @Integers.zero 64%positive).
        { apply Integers.same_bits_eq; intros i Hi; rewrite Integers.bits_zero, Integers.bits_and by exact Hi.
          rewrite (@Integers.testbit_repr 64%positive _ i Hi); change (@Integers.zwordsize 64%positive) with 64%Z in Hi.
          rewrite N.shiftl_1_l, N2Z.inj_pow; destruct (Z.eq_dec i (Z.of_N bit)) as [-> | Hne];
            [unfold Integers.testbit; rewrite Etb; reflexivity | rewrite Z.pow2_bits_false by (try lia; exact Hne); rewrite andb_false_r; reflexivity]. }
        pose proof (proj2 Hiz ltac:(rewrite Hnz, (@Integers.unsigned_zero 64%positive); reflexivity)) as Htru; discriminate Htru. }
    set (b := if is_nz then Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit) else negb (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit))).
    exists b; split; [| split; [| intro Hf; exact Hf]].
    + unfold b; rewrite <- Heq_tb; destruct is_nz;
        [exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ Hm ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))
        | rewrite negb_involutive; exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hm ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))].
    + cbv zeta iota; destruct b; try rewrite Erel; reflexivity.
  - destruct (a64_sym_epilogue_ok sp_off vrf) eqn:Hep; [| discriminate Hstep].
    destruct (a64_val_read 0%N vrf) as [| e_ret | |] eqn:Er0; try discriminate Hstep; inversion Hstep; subst res; clear Hstep.
    destruct (a64_sym_epilogue_ok_sound penv foracle rf0 sp0 sp_off vrf rf sp Hsp Hag Hep) as [Hsp_end Hcs].
    repeat split; try assumption; unfold rv_trunc_ret_expr, rv_trunc_ret_val.
    pose proof (Hag 0%N) as Ha0; rewrite Er0 in Ha0; cbn [mc_sym_val_agrees] in Ha0.
    destruct (Pos.eqb ret_w 64%positive) eqn:Ew64;
      [apply Pos.eqb_eq in Ew64; subst ret_w; rewrite Ha0, (@Integers.repr_unsigned 64%positive); reflexivity
      | assert (Hlt64 : (ret_w <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hrw Ew64);
        rewrite (eval_ce_trunc penv foracle 64%positive ret_w _ _ Hlt64 Ha0); reflexivity].
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
                summarize_a64_seg_at seg_name fuel' im cut_pc false visited' next_pc sp_off' vrf' astk' sfl' fl_def' ret_w
            | Some (ASSR_Branch cond tgt_pc next_pc fl_def') =>
                match summarize_a64_seg_at seg_name fuel' im cut_pc false visited' tgt_pc sp_off vrf astk sfl fl_def' ret_w with
                | inl err => inl err
                | inr dt =>
                    match summarize_a64_seg_at seg_name fuel' im cut_pc false visited' next_pc sp_off vrf astk sfl fl_def' ret_w with
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
  - destruct (negb req_step && N.eqb pc cut_pc); [inversion Hsum; subst; split; [exact Hrng | split; [exact Hwf | exact Hstk]] |].
    destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc); [inversion Hsum; subst; split; [exact Hrng | split; [exact Hwf | exact Hstk]] |].
    destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook.
    destruct (a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w) as [res |] eqn:Est; [| discriminate Hsum].
    pose proof (a64_sym_step_one_wf allowed dec pc sp_off vrf astk sfl fl_def ret_w res Hrw Hrng Hwf Hstk Hfl Est) as Hres.
    destruct res.
    + destruct Hres as (Hrng' & Hwf' & Hstk' & Hfl').
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hrng' Hwf' Hstk' Hfl' Hsum).
    + destruct (summarize_a64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def' ret_w) as [| dt] eqn:Edt; [discriminate Hsum |].
      destruct (summarize_a64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited) next_pc sp_off vrf astk sfl fl_def' ret_w) as [| df] eqn:Edf; [discriminate Hsum |].
      destruct Hres as [Hres Hfd]; inversion Hsum; subst; split;
        [exact Hres
        | split; [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk (fun Hf => Hfl (Hfd Hf)) Edt)
                 | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk (fun Hf => Hfl (Hfd Hf)) Edf)]].
    + inversion Hsum; subst; exact Hres.
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
    exists (1 + n)%nat, rf', sp', fl', mstk';
      split; [intro; lia | split; [exact (a64_exec_steps_trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 Hn) | split; [exact Hrng | split; [exact Hsp' | split; [exact Hag | exact Hastk]]]]].
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
      exists 0%nat, rf, sp, fl, mstk; split; [intro C; discriminate C | split; [reflexivity | split; [exact Hrng | split; [exact Hsp | split; [exact Hag | exact Hastk]]]]].
    + destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (negb req_step && N.eqb pc cut_pc) eqn:Ecut.
    + apply andb_true_iff in Ecut as [Hreq Hpc]; apply N.eqb_eq in Hpc; subst pc.
      destruct req_step; [discriminate Hreq |]; inversion Hsum; subst seg; clear Hsum.
      exists 0%nat, rf, sp, fl, mstk; split; [intro C; discriminate C | split; [reflexivity | split; [exact Hrng | split; [exact Hsp | split; [exact Hag | exact Hastk]]]]].
    + destruct (pt_has_n pc visited); [discriminate Hsum |].
      destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
      rewrite Him in Elook.
      assert (Hdec_val : a64_inst_valid dec = true).
      { clear -Elook Hval; induction insts as [| d rest IHl]; cbn in *; [discriminate |].
        apply andb_true_iff in Hval as [Hd Hr]; destruct (N.eqb (dai_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
      destruct (a64_sym_step_one dec pc sp_off vrf astk sfl fl_def ret_w) as [res |] eqn:Est; [| discriminate Hsum].
      pose proof (a64_sym_step_one_sound dec pc sp_off vrf astk sfl fl_def ret_w res penv foracle rf0 sp0 rf sp fl mstk
                    Hrw Hdec_val Hsp0 Hrng Hsp Hag Hastk Hfl Est) as Hres.
      destruct res.
      * destruct Hres as (rf1 & sp1 & fl1 & mstk1 & Hone & Hrng' & Hsp' & Hag' & Hastk' & Hfl').
        assert (H1 : a64_exec_steps 1 insts sp0 pc rf sp fl mstk = Some (next_pc, rf1, sp1, fl1, mstk1))
          by (cbn [a64_exec_steps]; rewrite Elook, Hone; reflexivity).
        eapply a64_seg_exec_spec_step_front; [exact H1 |].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng' Hsp' Hag' Hastk' Hfl' Hsum).
      * destruct (summarize_a64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def' ret_w) as [| dt] eqn:Edt; [discriminate Hsum |].
        destruct (summarize_a64_seg_at seg_name fuel' im cut_pc false (pt_add_n pc visited) next_pc sp_off vrf astk sfl fl_def' ret_w) as [| df] eqn:Edf; [discriminate Hsum |].
        inversion Hsum; subst seg; clear Hsum.
        destruct Hres as [b [Hbc [Hone Hfd]]].
        cbn [a64_seg_exec_spec]; exists b; split; [exact Hbc |].
        assert (H1 : a64_exec_steps 1 insts sp0 pc rf sp fl mstk = Some ((if b then tgt_pc else next_pc), rf, sp, fl, mstk))
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