(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * AArch64 (A64) Semantics & Symbolic DAG Lowering ([CertValidator.A64ExecSym])

    Purpose:
      Defines concrete ARMv8-A operational semantics ([a64_exec]) over 64/32-bit registers,
      4-bit [NZCV] flags, and private stack memory, plus AAPCS64-sound symbolic execution and
      DAG lowering ([summarize_a64_dag]).

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml directly. [summarize_a64_dag] fails closed
      ([inl err]) on unsupported instructions, undefined-register/flag reads, invalid stack or
      epilogue state, or fuel exhaustion, emitting UB/poison-free [cfg_dag] terms.

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{CertFormat,AigLrat,
      AlgRules,CfgDag,Elf64Spec,McFrameMem,McIsaCommon,A64Decode}]; zero custom axioms.

    Section Outline:
      3. Concrete ARMv8-A operational semantics ([a64_exec]); 4. AAPCS64 argument ABI & total
      symbolic DAG lowering ([summarize_a64_dag_at], [summarize_a64_dag]). *)

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
  A64Decode.

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

