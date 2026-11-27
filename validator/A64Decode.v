(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified [AArch64] ([A64]) Core AST & 32-Bit Little-Endian Decoder

    Implements for Milestone M2/M4 ([CertValidator.A64Decode]):
    canonical [A64] core bare-metal AST, total 32-bit little-endian decoder
    ([decode_a64_bytes]), and instruction validity invariants
    ([decode_a64_word_valid], [decode_a64_bytes_valid]). *)

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

