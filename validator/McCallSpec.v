(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Direct Call Specifications, Decoders & Tree Summarizers ([CertValidator.McCallSpec])

    Purpose:
      Defines direct non-recursive call-site decoders ([decode_rv64_bytes_with_calls],
      [decode_a64_bytes_with_calls]), callee prototype/ABI contract checks, call-trace
      operational semantics, acyclic call-tree summarizers, and obligation validators/emitters.

    Trust Contract & Fail-Closed Boundary:
      Proof-only specification module (re-exported by [McCall]). Decoders and validators fail
      closed ([inl err]) on unbound/stray call relocations, ABI/attribute mismatches, cycles or
      fuel exhaustion, and failed SAT/LRAT obligation discharge.

    Assumptions:
      [Stdlib], [ITree], [Vellvm], and [CertValidator] ([Diag], [McFormat], [McOblDischarger],
      RV64/A64 modules); uses [Section IRCallStep] over [Pa : Params] with zero custom axioms.

    Section Outline:
      1. Call-site decoders (1.1 RV64, 1.2 A64); 2. Callee contracts & call-trace semantics;
      3. Width-tagged call vars & summarizers; 4. Obligation builders & validators. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.Ascii
  Strings.String
  Numbers.DecimalString
  Numbers.DecimalZ
  List
  Bool
  Lia.
Import ListNotations.

From ITree Require Import
  ITree
  ITreeFacts
  Events.Exception.

From Vellvm Require Import
  Utils
  Utils.ITreeUtil
  Utils.Assoc
  Utils.ListUtil
  Numeric.Zbits
  Numeric.Integers
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.DynamicTypes
  Syntax.TypToDtyp
  Syntax.RawIdMaps
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Attributes
  Semantics.Denotation
  Semantics.LLVMEvents
  Semantics.IntrinsicsDefinitions.

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  CertValidator
  Elf64Spec
  McFrameMem
  McIsaCommon
  Rv64Decode
  Rv64ExecSym
  Rv64DagProof
  Rv64LoopSeg
  A64Decode
  A64ExecSym
  A64DagProof
  A64LoopSeg
  McFormat
  Diag
  McOblDischarger.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.eqb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments Z.eqb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments Nat.leb _ _ : simpl nomatch.
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
#[local] Arguments Integers.add : simpl never.
#[local] Arguments Integers.sub : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.


(** ** 1. Shared ELF Relocation/Symbol Lookup & Call-Site Decoders *)

Definition mcc_sum_map {E A B : Type} (f : A -> B) (r : E + A) : E + B :=
  match r with
  | inl err => inl err
  | inr a => inr (f a)
  end.

Definition mcc_sym_val_kind (v : mc_sym_val) : string :=
  match v with
  | MSV_Undef => "undef"
  | MSV_Expr _ => "expr"
  | MSV_SavedReg _ => "saved-reg"
  | MSV_StackPtr _ => "stack-ptr"
  end.

Fixpoint lookup_call_reloc (relocs : list (N * string)) (off : N) : option string :=
  match relocs with
  | [] => None
  | (ro, cn) :: rest =>
      if N.eqb ro off then Some cn else lookup_call_reloc rest off
  end.

Definition find_unique_callee_by_addr (addrs : list (string * N)) (addr : N) : option string :=
  let hits := List.filter (fun '(_, a) => N.eqb a addr) addrs in
  match hits with
  | [(cn, _)] => Some cn
  | _ => None
  end.

Definition resolve_pc_rel_callee
  (addrs : list (string * N)) (call_pc : N) (rel_bytes : Z) : option string :=
  let tgt_z := (Z.of_N call_pc + rel_bytes)%Z in
  if Z.leb 0%Z tgt_z then find_unique_callee_by_addr addrs (Z.to_N tgt_z)
  else None.

Definition resolve_pc_rel_callee_diag
  (addrs : list (string * N)) (call_pc : N) (rel_bytes : Z) : string + string :=
  let tgt_z := (Z.of_N call_pc + rel_bytes)%Z in
  if Z.leb 0%Z tgt_z then
    let tgt := Z.to_N tgt_z in
    match find_unique_diag (fun '(_, a) => N.eqb a tgt) addrs with
    | UM_Missing =>
        inl (diag "mc-call-decode"
          ("unresolved PC-relative call target " ++ diag_N_hex tgt ++
           " at ELF offset " ++ diag_N_hex call_pc))
    | UM_Unique (cn, _) => inr cn
    | UM_Duplicate (cn1, _) (cn2, _) =>
        inl (diag "mc-call-decode"
          ("ambiguous PC-relative call target " ++ diag_N_hex tgt ++
           " at ELF offset " ++ diag_N_hex call_pc ++
           " (matches '" ++ cn1 ++ "' and '" ++ cn2 ++ "')"))
    end
  else
    inl (diag "mc-call-decode"
      ("PC-relative call target underflow at ELF offset " ++ diag_N_hex call_pc)).

(** *** 1.1 RISC-V RV64IM+RVC Call-Site Decoder *)

Variant rv_call_inst : Type :=
| RCI_Core (i : rv_inst)
| RCI_Call (callee : string).

Record decoded_rv_call_inst : Type := mk_decoded_rv_call_inst {
  drci_off : N;
  drci_len : N;
  drci_inst : rv_call_inst;
}.

Fixpoint lookup_rv_call_inst (insts : list decoded_rv_call_inst) (pc : N)
  : option decoded_rv_call_inst :=
  match insts with
  | [] => None
  | d :: rest => if N.eqb (drci_off d) pc then Some d else lookup_rv_call_inst rest pc
  end.

Definition rv_call_inst_no_word_mulh (d : decoded_rv_call_inst) : bool :=
  match drci_inst d with
  | RCI_Core i => inst_no_word_mulh (mk_decoded_rv (drci_off d) (drci_len d) i)
  | RCI_Call _ => true
  end.

Definition all_relocs_bound_to_rv_calls
  (relocs : list (N * string)) (insts : list decoded_rv_call_inst) : bool :=
  forallb (fun '(off, cn) =>
    existsb (fun d =>
      N.eqb (drci_off d) off &&
      match drci_inst d with
      | RCI_Call cn' => String.eqb cn cn'
      | RCI_Core _ => false
      end) insts) relocs.

Definition find_stray_rv_call_reloc
  (relocs : list (N * string)) (insts : list decoded_rv_call_inst) : option (N * string) :=
  List.find (fun '(off, cn) =>
    negb (existsb (fun d =>
      N.eqb (drci_off d) off &&
      match drci_inst d with
      | RCI_Call cn' => String.eqb cn cn'
      | RCI_Core _ => false
      end) insts)) relocs.

Definition decode_rv_auipc_jalr_call
  (kind : elf_kind) (fn_lo : N) (ci : elf_call_info)
  (cur_off : nat) (w1 w2 : N) : option (string + string) :=
  let op1 := bit_slice w1 0%N 7%N in
  let rd1 := bit_slice w1 7%N 5%N in
  let op2 := bit_slice w2 0%N 7%N in
  let rd2 := bit_slice w2 7%N 5%N in
  let f3_2 := bit_slice w2 12%N 3%N in
  let rs1_2 := bit_slice w2 15%N 5%N in
  if N.eqb op1 23%N && N.eqb rd1 1%N &&
     N.eqb op2 103%N && N.eqb rd2 1%N && N.eqb rs1_2 1%N && N.eqb f3_2 0%N then
    let cur_n := N.of_nat cur_off in
    let imm20 := bit_slice w1 12%N 20%N in
    let imm12 := bit_slice w2 20%N 12%N in
    Some
      match kind with
      | EK_Rel =>
          match lookup_call_reloc (eci_relocs ci) cur_n,
                lookup_call_reloc (eci_relocs ci) (cur_n + 4%N)%N with
          | Some cname, None =>
              if N.eqb imm20 0%N && N.eqb imm12 0%N then inr cname
              else
                inl (diag "mc-call-decode"
                  ("non-zero immediate in ET_REL RV64 auipc+jalr call to '" ++ cname ++
                   "' at offset " ++ diag_N_hex cur_n))
          | Some cname, Some cname2 =>
              inl (diag "mc-call-decode"
                ("unexpected second relocation '" ++ cname2 ++ "' inside ET_REL RV64 auipc+jalr call to '" ++
                 cname ++ "' at offset " ++ diag_N_hex cur_n))
          | None, _ =>
              inl (diag "mc-call-decode"
                ("missing call relocation on ET_REL RV64 auipc+jalr call at offset " ++ diag_N_hex cur_n))
          end
      | EK_Exec | EK_Dyn =>
          let rel := (sext_z (imm20 * 4096%N) 32%N + sext_z imm12 12%N)%Z in
          resolve_pc_rel_callee_diag (eci_sym_addrs ci) (fn_lo + cur_n)%N rel
      end
  else None.

Definition decode_rv_jal_ra_call
  (kind : elf_kind) (fn_lo : N) (ci : elf_call_info)
  (cur_off : nat) (w : N) : option (string + string) :=
  let op := bit_slice w 0%N 7%N in
  let rd := bit_slice w 7%N 5%N in
  if N.eqb op 111%N && N.eqb rd 1%N then
    let cur_n := N.of_nat cur_off in
    let j21 :=
      (bit_slice w 31%N 1%N * 1048576%N +
       bit_slice w 12%N 8%N * 4096%N +
       bit_slice w 20%N 1%N * 2048%N +
       bit_slice w 21%N 10%N * 2%N)%N in
    Some
      match kind with
      | EK_Rel =>
          match lookup_call_reloc (eci_relocs ci) cur_n with
          | Some cname =>
              if N.eqb j21 0%N then inr cname
              else
                inl (diag "mc-call-decode"
                  ("non-zero offset in ET_REL RV64 jal ra call to '" ++ cname ++
                   "' at offset " ++ diag_N_hex cur_n))
          | None =>
              inl (diag "mc-call-decode"
                ("missing call relocation on ET_REL RV64 jal ra call at offset " ++ diag_N_hex cur_n))
          end
      | EK_Exec | EK_Dyn =>
          resolve_pc_rel_callee_diag (eci_sym_addrs ci) (fn_lo + cur_n)%N (sext_z j21 21%N)
      end
  else None.

Fixpoint decode_rv64_stream_with_calls_acc
  (fuel : nat) (rvc_enabled : bool) (kind : elf_kind) (fn_lo : N)
  (ci : elf_call_info) (rem : list N) (cur_off : nat)
  (acc : list decoded_rv_call_inst)
  {struct fuel} : string + list decoded_rv_call_inst :=
  match rem with
  | [] => inr (elf_rev_tr acc)
  | _ :: _ =>
      match fuel with
      | O =>
          inl (diag "mc-call-decode"
            ("RV64 call decoder fuel exhausted at offset " ++ diag_N_hex (N.of_nat cur_off)))
      | S fuel' =>
          match take_u16_le rem with
          | None =>
              inl (diag "mc-call-decode"
                ("truncated RV64 instruction stream at offset " ++ diag_N_hex (N.of_nat cur_off)))
          | Some (hw, rem2) =>
              if negb (N.eqb (N.modulo hw 4%N) 3%N) then
                if negb rvc_enabled then
                  inl (diag "mc-call-decode"
                    ("16-bit RVC instruction " ++ diag_N_hex hw ++
                     " encountered with RVC disabled at offset " ++ diag_N_hex (N.of_nat cur_off)))
                else
                  match decode_rvc_hw hw with
                  | None =>
                      inl (diag "mc-call-decode"
                        ("unsupported 16-bit RVC instruction " ++ diag_N_hex hw ++
                         " at offset " ++ diag_N_hex (N.of_nat cur_off)))
                  | Some inst =>
                      decode_rv64_stream_with_calls_acc fuel' rvc_enabled kind fn_lo ci
                        rem2 (cur_off + 2)
                        (mk_decoded_rv_call_inst (N.of_nat cur_off) 2%N (RCI_Core inst) :: acc)
                  end
              else
                match take_u32_le rem with
                | None =>
                    inl (diag "mc-call-decode"
                      ("truncated 32-bit RV64 instruction at offset " ++ diag_N_hex (N.of_nat cur_off)))
                | Some (w1, rem4) =>
                    let pair_res :=
                      match take_u32_le rem4 with
                      | Some (w2, rem8) =>
                          match decode_rv_auipc_jalr_call kind fn_lo ci cur_off w1 w2 with
                          | Some res => Some (res, rem8)
                          | None => None
                          end
                      | None => None
                      end in
                    match pair_res with
                    | Some (inl err, _) => inl err
                    | Some (inr cname, rem8) =>
                        decode_rv64_stream_with_calls_acc fuel' rvc_enabled kind fn_lo ci
                          rem8 (cur_off + 8)
                          (mk_decoded_rv_call_inst (N.of_nat cur_off) 8%N (RCI_Call cname) :: acc)
                    | None =>
                        match decode_rv_jal_ra_call kind fn_lo ci cur_off w1 with
                        | Some (inl err) => inl err
                        | Some (inr cname) =>
                            decode_rv64_stream_with_calls_acc fuel' rvc_enabled kind fn_lo ci
                              rem4 (cur_off + 4)
                              (mk_decoded_rv_call_inst (N.of_nat cur_off) 4%N (RCI_Call cname) :: acc)
                        | None =>
                            match decode_rv32_word w1 with
                            | None =>
                                inl (diag "mc-call-decode"
                                  ("unsupported 32-bit RV64 instruction " ++ diag_N_hex w1 ++
                                   " at offset " ++ diag_N_hex (N.of_nat cur_off)))
                            | Some inst =>
                                decode_rv64_stream_with_calls_acc fuel' rvc_enabled kind fn_lo ci
                                  rem4 (cur_off + 4)
                                  (mk_decoded_rv_call_inst (N.of_nat cur_off) 4%N (RCI_Core inst) :: acc)
                            end
                        end
                    end
                end
          end
      end
  end.

Definition decode_rv64_bytes_with_calls
  (rvc_enabled : bool) (kind : elf_kind) (fn_lo : N)
  (ci : elf_call_info) (code : list N)
  : string + list decoded_rv_call_inst :=
  let len := elf_length_tr code in
  if Nat.eqb len 0 || negb (Nat.eqb (Nat.modulo len 2) 0) then
    inl (diag "mc-call-decode"
      ("RV64 function byte length must be positive and even (got " ++ diag_nat_dec len ++ ")"))
  else if negb rvc_enabled && negb (Nat.eqb (Nat.modulo len 4) 0) then
    inl (diag "mc-call-decode"
      ("non-RVC RV64 function byte length must be a multiple of 4 (got " ++ diag_nat_dec len ++ ")"))
  else
    match decode_rv64_stream_with_calls_acc (Nat.div len 2 + 1) rvc_enabled kind fn_lo ci code 0 [] with
    | inl err => inl err
    | inr insts =>
        match kind with
        | EK_Rel =>
            if all_relocs_bound_to_rv_calls (eci_relocs ci) insts then inr insts
            else
              let msg :=
                match find_stray_rv_call_reloc (eci_relocs ci) insts with
                | Some (off, cn) =>
                    ("stray call relocation to '" ++ cn ++ "' at offset " ++ diag_N_hex off ++
                     " outside RV64 call instruction")%string
                | None => "stray call relocation outside RV64 call instruction"
                end in
              inl (diag "mc-call-decode" msg)
        | EK_Exec | EK_Dyn => inr insts
        end
    end.

Local Lemma mcc_forallb_rev {A : Type} (p : A -> bool) (xs : list A) :
  forallb p (List.rev xs) = forallb p xs.
Proof.
  induction xs as [| x xs IH]; [reflexivity |].
  cbn [List.rev forallb]; rewrite forallb_app, IH; cbn [forallb]; rewrite Bool.andb_true_r, Bool.andb_comm; reflexivity.
Qed.

Lemma decode_rv64_stream_with_calls_acc_no_word_mulh :
  forall fuel rvc kind fn_lo ci rem cur_off acc insts,
    forallb rv_call_inst_no_word_mulh acc = true ->
    decode_rv64_stream_with_calls_acc fuel rvc kind fn_lo ci rem cur_off acc = inr insts ->
    forallb rv_call_inst_no_word_mulh insts = true.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros rvc kind fn_lo ci rem cur_off acc insts Hacc Hdec;
    cbn [decode_rv64_stream_with_calls_acc] in Hdec;
    destruct rem as [| b0 r0];
    [inversion Hdec; rewrite elf_rev_tr_eq, mcc_forallb_rev; exact Hacc
    | discriminate Hdec
    | inversion Hdec; rewrite elf_rev_tr_eq, mcc_forallb_rev; exact Hacc |].
  destruct (take_u16_le (b0 :: r0)) as [[hw rem2] |]; [| discriminate Hdec].
  destruct (negb (N.eqb (N.modulo hw 4%N) 3%N)).
  - destruct (negb rvc); [discriminate Hdec |].
    destruct (decode_rvc_hw hw) as [inst |] eqn:Ec; [| discriminate Hdec].
    eapply IH; [| exact Hdec].
    cbn [forallb]; rewrite Hacc, Bool.andb_true_r.
    pose proof (decode_rvc_hw_no_word_mulh hw inst Ec) as Hnm.
    assert (Hmul1 : inst_no_word_mulh (mk_decoded_rv (N.of_nat cur_off) 2%N inst) = true).
    { unfold inst_no_word_mulh; cbn [dri_inst]; destruct inst; try reflexivity;
        repeat match goal with o : rv_alu_reg_op |- _ => destruct o | b : bool |- _ => destruct b end;
        try reflexivity; contradiction Hnm. }
    exact Hmul1.
  - destruct (take_u32_le (b0 :: r0)) as [[w1 rem4] |]; [| discriminate Hdec].
    destruct (match take_u32_le rem4 with
              | Some (w2, rem8) =>
                  match decode_rv_auipc_jalr_call kind fn_lo ci cur_off w1 w2 with
                  | Some res => Some (res, rem8)
                  | None => None
                  end
              | None => None
              end) as [[[| cname] rem8] |].
    + discriminate Hdec.
    + eapply IH; [| exact Hdec]; cbn [forallb rv_call_inst_no_word_mulh]; exact Hacc.
    + destruct (decode_rv_jal_ra_call kind fn_lo ci cur_off w1) as [[| cname] |].
      * discriminate Hdec.
      * eapply IH; [| exact Hdec]; cbn [forallb rv_call_inst_no_word_mulh]; exact Hacc.
      * destruct (decode_rv32_word w1) as [inst |] eqn:Ew; [| discriminate Hdec].
        eapply IH; [| exact Hdec].
        cbn [forallb]; rewrite Hacc, Bool.andb_true_r.
        pose proof (decode_rv32_word_no_word_mulh w1 inst Ew) as Hnm.
        assert (Hmul1 : inst_no_word_mulh (mk_decoded_rv (N.of_nat cur_off) 4%N inst) = true).
        { unfold inst_no_word_mulh; cbn [dri_inst]; destruct inst; try reflexivity;
            repeat match goal with o : rv_alu_reg_op |- _ => destruct o | b : bool |- _ => destruct b end;
            try reflexivity; contradiction Hnm. }
        exact Hmul1.
Qed.

Lemma decode_rv64_bytes_with_calls_no_word_mulh :
  forall rvc kind fn_lo ci code insts,
    decode_rv64_bytes_with_calls rvc kind fn_lo ci code = inr insts ->
    forallb rv_call_inst_no_word_mulh insts = true.
Proof.
  intros rvc kind fn_lo ci code insts H; unfold decode_rv64_bytes_with_calls in H.
  destruct (Nat.eqb (elf_length_tr code) 0 || negb (Nat.eqb (Nat.modulo (elf_length_tr code) 2) 0));
    [discriminate H |].
  destruct (negb rvc && negb (Nat.eqb (Nat.modulo (elf_length_tr code) 4) 0));
    [discriminate H |].
  destruct (decode_rv64_stream_with_calls_acc _ _ _ _ _ _ _ _) as [| xs] eqn:Hs; [discriminate H |].
  pose proof (decode_rv64_stream_with_calls_acc_no_word_mulh _ _ _ _ _ _ _ [] xs eq_refl Hs) as Hmul.
  destruct kind;
    [destruct (all_relocs_bound_to_rv_calls (eci_relocs ci) xs); inversion H; subst; exact Hmul
    | inversion H; subst; exact Hmul
    | inversion H; subst; exact Hmul].
Qed.

(** *** 1.2 AArch64 Call-Site Decoder ([BL imm26]) *)

Variant a64_call_inst : Type :=
| ACI_Core (i : a64_inst)
| ACI_Call (callee : string).

Record decoded_a64_call_inst : Type := mk_decoded_a64_call_inst {
  daci_off : N;
  daci_inst : a64_call_inst;
}.

Fixpoint lookup_a64_call_inst (insts : list decoded_a64_call_inst) (pc : N)
  : option decoded_a64_call_inst :=
  match insts with
  | [] => None
  | d :: rest => if N.eqb (daci_off d) pc then Some d else lookup_a64_call_inst rest pc
  end.

Definition a64_call_inst_valid (d : decoded_a64_call_inst) : bool :=
  match daci_inst d with
  | ACI_Core i => a64_inst_valid (mk_decoded_a64_inst (daci_off d) i)
  | ACI_Call _ => true
  end.

Definition all_relocs_bound_to_a64_calls
  (relocs : list (N * string)) (insts : list decoded_a64_call_inst) : bool :=
  forallb (fun '(off, cn) =>
    existsb (fun d =>
      N.eqb (daci_off d) off &&
      match daci_inst d with
      | ACI_Call cn' => String.eqb cn cn'
      | ACI_Core _ => false
      end) insts) relocs.

Definition find_stray_a64_call_reloc
  (relocs : list (N * string)) (insts : list decoded_a64_call_inst) : option (N * string) :=
  List.find (fun '(off, cn) =>
    negb (existsb (fun d =>
      N.eqb (daci_off d) off &&
      match daci_inst d with
      | ACI_Call cn' => String.eqb cn cn'
      | ACI_Core _ => false
      end) insts)) relocs.

Definition decode_a64_bl_call
  (kind : elf_kind) (fn_lo : N) (ci : elf_call_info)
  (cur_off : nat) (w : N) : option (string + string) :=
  if N.eqb (bit_slice w 26%N 6%N) 37%N then
    let cur_n := N.of_nat cur_off in
    let imm26 := bit_slice w 0%N 26%N in
    Some
      match kind with
      | EK_Rel =>
          match lookup_call_reloc (eci_relocs ci) cur_n with
          | Some cname =>
              if N.eqb imm26 0%N then inr cname
              else
                inl (diag "mc-call-decode"
                  ("non-zero imm26 in ET_REL AArch64 BL call to '" ++ cname ++
                   "' at offset " ++ diag_N_hex cur_n))
          | None =>
              inl (diag "mc-call-decode"
                ("missing call relocation on ET_REL AArch64 BL call at offset " ++ diag_N_hex cur_n))
          end
      | EK_Exec | EK_Dyn =>
          let rel := (4%Z * sext_z imm26 26%N)%Z in
          resolve_pc_rel_callee_diag (eci_sym_addrs ci) (fn_lo + cur_n)%N rel
      end
  else None.

Fixpoint decode_a64_stream_with_calls_acc
  (fuel : nat) (kind : elf_kind) (fn_lo : N)
  (ci : elf_call_info) (rem : list N) (cur_off : nat)
  (acc : list decoded_a64_call_inst)
  {struct fuel} : string + list decoded_a64_call_inst :=
  match rem with
  | [] => inr (elf_rev_tr acc)
  | _ :: _ =>
      match fuel with
      | O =>
          inl (diag "mc-call-decode"
            ("AArch64 call decoder fuel exhausted at offset " ++ diag_N_hex (N.of_nat cur_off)))
      | S fuel' =>
          match take_u32_le rem with
          | None =>
              inl (diag "mc-call-decode"
                ("truncated 32-bit A64 instruction at offset " ++ diag_N_hex (N.of_nat cur_off)))
          | Some (w, rem4) =>
              match decode_a64_bl_call kind fn_lo ci cur_off w with
              | Some (inl err) => inl err
              | Some (inr cname) =>
                  decode_a64_stream_with_calls_acc fuel' kind fn_lo ci rem4 (cur_off + 4)
                    (mk_decoded_a64_call_inst (N.of_nat cur_off) (ACI_Call cname) :: acc)
              | None =>
                  match decode_a64_word w with
                  | None =>
                      inl (diag "mc-call-decode"
                        ("unsupported AArch64 instruction " ++ diag_N_hex w ++
                         " at offset " ++ diag_N_hex (N.of_nat cur_off)))
                  | Some inst =>
                      decode_a64_stream_with_calls_acc fuel' kind fn_lo ci rem4 (cur_off + 4)
                        (mk_decoded_a64_call_inst (N.of_nat cur_off) (ACI_Core inst) :: acc)
                  end
              end
          end
      end
  end.

Definition decode_a64_bytes_with_calls
  (kind : elf_kind) (fn_lo : N) (ci : elf_call_info) (code : list N)
  : string + list decoded_a64_call_inst :=
  let len := elf_length_tr code in
  if Nat.eqb len 0 || negb (Nat.eqb (Nat.modulo len 4) 0) then
    inl (diag "mc-call-decode"
      ("AArch64 function byte length must be a positive multiple of 4 (got " ++ diag_nat_dec len ++ ")"))
  else
    match decode_a64_stream_with_calls_acc (Nat.div len 4 + 1) kind fn_lo ci code 0 [] with
    | inl err => inl err
    | inr insts =>
        match kind with
        | EK_Rel =>
            if all_relocs_bound_to_a64_calls (eci_relocs ci) insts then inr insts
            else
              let msg :=
                match find_stray_a64_call_reloc (eci_relocs ci) insts with
                | Some (off, cn) =>
                    ("stray call relocation to '" ++ cn ++ "' at offset " ++ diag_N_hex off ++
                     " outside AArch64 BL instruction")%string
                | None => "stray call relocation outside AArch64 BL instruction"
                end in
              inl (diag "mc-call-decode" msg)
        | EK_Exec | EK_Dyn => inr insts
        end
    end.

Lemma decode_a64_stream_with_calls_acc_valid :
  forall fuel kind fn_lo ci rem cur_off acc insts,
    forallb a64_call_inst_valid acc = true ->
    decode_a64_stream_with_calls_acc fuel kind fn_lo ci rem cur_off acc = inr insts ->
    forallb a64_call_inst_valid insts = true.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros kind fn_lo ci rem cur_off acc insts Hacc Hdec;
    cbn [decode_a64_stream_with_calls_acc] in Hdec;
    destruct rem as [| b0 r0];
    [inversion Hdec; rewrite elf_rev_tr_eq, mcc_forallb_rev; exact Hacc
    | discriminate Hdec
    | inversion Hdec; rewrite elf_rev_tr_eq, mcc_forallb_rev; exact Hacc |].
  destruct (take_u32_le (b0 :: r0)) as [[w rem4] |]; [| discriminate Hdec].
  destruct (decode_a64_bl_call kind fn_lo ci cur_off w) as [[| cname] |].
  - discriminate Hdec.
  - eapply IH; [| exact Hdec]; cbn [forallb a64_call_inst_valid]; exact Hacc.
  - destruct (decode_a64_word w) as [inst |] eqn:Ew; [| discriminate Hdec].
    eapply IH; [| exact Hdec].
    cbn [forallb a64_call_inst_valid daci_inst]; rewrite Hacc, Bool.andb_true_r.
    pose proof (decode_a64_word_valid w inst Ew) as Hv.
    unfold a64_inst_valid in Hv; cbn [dai_inst] in Hv; exact Hv.
Qed.

Lemma decode_a64_bytes_with_calls_valid :
  forall kind fn_lo ci code insts,
    decode_a64_bytes_with_calls kind fn_lo ci code = inr insts ->
    forallb a64_call_inst_valid insts = true.
Proof.
  intros kind fn_lo ci code insts H; unfold decode_a64_bytes_with_calls in H.
  destruct (Nat.eqb (elf_length_tr code) 0 || negb (Nat.eqb (Nat.modulo (elf_length_tr code) 4) 0));
    [discriminate H |].
  destruct (decode_a64_stream_with_calls_acc _ _ _ _ _ _ _) as [| xs] eqn:Hs; [discriminate H |].
  pose proof (decode_a64_stream_with_calls_acc_valid _ _ _ _ _ _ [] xs eq_refl Hs) as Hval.
  destruct kind;
    [destruct (all_relocs_bound_to_a64_calls (eci_relocs ci) xs); inversion H; subst; exact Hval
    | inversion H; subst; exact Hval
    | inversion H; subst; exact Hval].
Qed.

(** ** 2. Callee ABI Contracts & Call-Aware Operational Semantics *)

Definition mc_call_attr_is_signext (a : param_attr) : bool :=
  match a with
  | PARAMATTR_Signext => true
  | _ => false
  end.

Definition mc_call_attr_is_zeroext (a : param_attr) : bool :=
  match a with
  | PARAMATTR_Zeroext => true
  | _ => false
  end.

Fixpoint find_unique_decl_in_list {A : Type}
  (proj : A -> declaration typ) (cname : string)
  (xs : list A) (found : option (declaration typ))
  : option (option (declaration typ)) :=
  match xs with
  | [] => Some found
  | x :: rest =>
      let d := proj x in
      if cert_fn_matches_raw_id cname (dc_name d) then
        match found with
        | None => find_unique_decl_in_list proj cname rest (Some d)
        | Some _ => None
        end
      else find_unique_decl_in_list proj cname rest found
  end.

Definition find_unique_callee_decl (ir_m : CFG.mcfg typ) (cname : string)
  : option (declaration typ) :=
  match find_unique_decl_in_list (fun d => d) cname (m_declarations ir_m) None with
  | None => None
  | Some found1 =>
      match find_unique_decl_in_list df_prototype cname (m_definitions ir_m) found1 with
      | Some (Some d) => Some d
      | _ => None
      end
  end.

Definition check_callee_ret_ext (w : positive) (rattrs : list param_attr) (ext : rv_arg_ext) : bool :=
  let se := existsb mc_call_attr_is_signext rattrs in
  let ze := existsb mc_call_attr_is_zeroext rattrs in
  if Pos.eqb w 64%positive then
    match ext with
    | RAE_None => negb se && negb ze
    | _ => false
    end
  else
    match ext with
    | RAE_SignExt => se && negb ze
    | RAE_ZeroExt => ze && negb se
    | RAE_None => true
    end.

Definition check_callee_arg_contract
  (arch : elf_arch) (dt : dtyp) (pattrs : list param_attr) (sp : rv_arg_spec) : bool :=
  rv_valid_arg_spec sp &&
  dtyp_eqb dt (DTYPE_Base (DTYPE_I (ras_width sp))) &&
  let se := existsb mc_call_attr_is_signext pattrs in
  let ze := existsb mc_call_attr_is_zeroext pattrs in
  match arch with
  | EA_Riscv64 =>
      if Pos.eqb (ras_width sp) 64%positive then
        match ras_ext sp with RAE_None => negb se && negb ze | _ => false end
      else
        match ras_ext sp with
        | RAE_SignExt => se && negb ze
        | RAE_ZeroExt => ze && negb se
        | RAE_None => false
        end
  | EA_AArch64 =>
      if Pos.eqb (ras_width sp) 64%positive || Pos.eqb (ras_width sp) 32%positive then
        match ras_ext sp with RAE_None => negb se && negb ze | _ => false end
      else
        match ras_ext sp with
        | RAE_SignExt => se && negb ze
        | RAE_ZeroExt => ze && negb se
        | RAE_None => true
        end
  end.

Fixpoint check_callee_args_list
  (arch : elf_arch) (arg_dtys : list dtyp) (pattrs : list (list param_attr)) (specs : list rv_arg_spec)
  {struct specs} : bool :=
  match arg_dtys, pattrs, specs with
  | [], [], [] => true
  | dt :: rd, pa :: rp, sp :: rs =>
      check_callee_arg_contract arch dt pa sp && check_callee_args_list arch rd rp rs
  | _, _, _ => false
  end.

Definition check_one_callee_contract
  (tenv : list (ident * typ)) (ir_m : CFG.mcfg typ) (arch : elf_arch) (c : mc_callee_spec) : bool :=
  match find_unique_callee_decl ir_m (mcs_name c) with
  | None => false
  | Some d =>
      let '(d_rattrs, d_pattrs) := dc_param_attrs d in
      match dc_type d with
      | TYPE_Function ret_ty arg_tys false =>
          let arg_dtys := List.map (typ_to_dtyp tenv) arg_tys in
          dtyp_eqb (typ_to_dtyp tenv ret_ty) (DTYPE_Base (DTYPE_I (mcs_ret_width c))) &&
          rv_supported_arg_width (mcs_ret_width c) &&
          cconv_eqb (anns_cconv (dc_annotations d)) CC_Ccc &&
          forallb decl_ann_supported (dc_annotations d) &&
          forallb (fun a => negb (is_unmodeled_fn_attr a))
                  (dc_attrs d ++ ann_fun_attributes (dc_annotations d)) &&
          forallb (fun a => negb (is_unmodeled_param_attr a)) d_rattrs &&
          forallb (forallb (fun a => negb (is_unmodeled_param_attr a))) d_pattrs &&
          check_callee_ret_ext (mcs_ret_width c) d_rattrs (mcs_ret_ext c) &&
          check_callee_args_list arch arg_dtys d_pattrs (mcs_args c)
      | _ => false
      end
  end.

Definition check_mc_callee_contracts
  (tenv : list (ident * typ)) (ir_m : CFG.mcfg typ) (arch : elf_arch) (cs : list mc_callee_spec)
  : bool :=
  forallb (check_one_callee_contract tenv ir_m arch) cs.

Fixpoint find_unique_decl_diag_in_list {A : Type}
  (proj : A -> declaration typ) (cname : string)
  (xs : list A) (found : option (declaration typ))
  : string + option (declaration typ) :=
  match xs with
  | [] => inr found
  | x :: rest =>
      let d := proj x in
      if cert_fn_matches_raw_id cname (dc_name d) then
        match found with
        | None => find_unique_decl_diag_in_list proj cname rest (Some d)
        | Some _ =>
            inl (diag "mc-call-contract"
              ("duplicate IR declaration/definition for callee '" ++ cname ++ "'"))
        end
      else find_unique_decl_diag_in_list proj cname rest found
  end.

Definition find_unique_callee_decl_diag (ir_m : CFG.mcfg typ) (cname : string)
  : string + declaration typ :=
  match find_unique_decl_diag_in_list (fun d => d) cname (m_declarations ir_m) None with
  | inl err => inl err
  | inr found1 =>
      match find_unique_decl_diag_in_list df_prototype cname (m_definitions ir_m) found1 with
      | inl err => inl err
      | inr (Some d) => inr d
      | inr None =>
          inl (diag "mc-call-contract"
            ("missing IR declaration/definition for callee '" ++ cname ++ "'"))
      end
  end.

Local Lemma find_unique_decl_diag_in_list_sound {A : Type} :
  forall (proj : A -> declaration typ) cname xs found res,
    find_unique_decl_diag_in_list proj cname xs found = inr res ->
    find_unique_decl_in_list proj cname xs found = Some res.
Proof.
  intros proj cname xs; induction xs as [| x rest IH];
    intros found res H; cbn [find_unique_decl_diag_in_list find_unique_decl_in_list] in *.
  - inversion H; reflexivity.
  - destruct (cert_fn_matches_raw_id cname (dc_name (proj x)));
      [destruct found; [discriminate H | exact (IH _ _ H)] | exact (IH _ _ H)].
Qed.

Local Lemma find_unique_callee_decl_diag_sound :
  forall ir_m cname d,
    find_unique_callee_decl_diag ir_m cname = inr d ->
    find_unique_callee_decl ir_m cname = Some d.
Proof.
  intros ir_m cname d H; unfold find_unique_callee_decl_diag, find_unique_callee_decl in *.
  destruct (find_unique_decl_diag_in_list (fun d0 => d0) cname (m_declarations ir_m) None) as [| f1] eqn:E1;
    [discriminate H |].
  rewrite (find_unique_decl_diag_in_list_sound _ _ _ _ _ E1).
  destruct (find_unique_decl_diag_in_list df_prototype cname (m_definitions ir_m) f1) as [| [d0 |]] eqn:E2;
    [discriminate H | | discriminate H].
  rewrite (find_unique_decl_diag_in_list_sound _ _ _ _ _ E2); inversion H; reflexivity.
Qed.

Definition check_callee_ret_ext_diag
  (cname : string) (w : positive) (rattrs : list param_attr) (ext : rv_arg_ext) : string + unit :=
  if check_callee_ret_ext w rattrs ext then inr tt
  else
    inl (diag "mc-call-contract"
      ("callee '" ++ cname ++ "' return extension mismatches IR return attributes for width i" ++
       diag_pos_dec w)).

Definition check_callee_arg_contract_diag
  (cname : string) (idx : nat) (arch : elf_arch)
  (dt : dtyp) (pattrs : list param_attr) (sp : rv_arg_spec) : string + unit :=
  if negb (rv_valid_arg_spec sp) then
    inl (diag "mc-call-contract"
      ("callee '" ++ cname ++ "' argument #" ++ diag_nat_dec idx ++
       " has invalid arg spec (width i" ++ diag_pos_dec (ras_width sp) ++ ")"))
  else if negb (dtyp_eqb dt (DTYPE_Base (DTYPE_I (ras_width sp)))) then
    inl (diag "mc-call-contract"
      ("callee '" ++ cname ++ "' argument #" ++ diag_nat_dec idx ++
       " IR type mismatches declared width i" ++ diag_pos_dec (ras_width sp)))
  else if check_callee_arg_contract arch dt pattrs sp then inr tt
  else
    inl (diag "mc-call-contract"
      ("callee '" ++ cname ++ "' argument #" ++ diag_nat_dec idx ++
       " extension/attribute contract mismatch")).

Fixpoint check_callee_args_list_diag
  (cname : string) (idx : nat) (arch : elf_arch)
  (arg_dtys : list dtyp) (pattrs : list (list param_attr)) (specs : list rv_arg_spec)
  {struct specs} : string + unit :=
  match arg_dtys, pattrs, specs with
  | [], [], [] => inr tt
  | dt :: rd, pa :: rp, sp :: rs =>
      match check_callee_arg_contract_diag cname idx arch dt pa sp with
      | inl err => inl err
      | inr tt => check_callee_args_list_diag cname (S idx) arch rd rp rs
      end
  | _, _, _ =>
      inl (diag "mc-call-contract"
        ("callee '" ++ cname ++ "' argument count mismatch (IR=" ++
         diag_nat_dec (List.length arg_dtys) ++ ", attrs=" ++
         diag_nat_dec (List.length pattrs) ++ ", cert=" ++
         diag_nat_dec (List.length specs) ++ ")"))
  end.

Local Lemma check_callee_args_list_diag_sound :
  forall cname idx arch arg_dtys pattrs specs,
    check_callee_args_list_diag cname idx arch arg_dtys pattrs specs = inr tt ->
    check_callee_args_list arch arg_dtys pattrs specs = true.
Proof.
  intros cname idx arch arg_dtys pattrs specs; revert idx arg_dtys pattrs.
  induction specs as [| sp rs IH];
    intros idx [| dt rd] [| pa rp] H;
    cbn [check_callee_args_list_diag check_callee_args_list] in *;
    try discriminate H; [reflexivity |].
  unfold check_callee_arg_contract_diag in H.
  destruct (rv_valid_arg_spec sp); cbn [negb] in H; [| discriminate H].
  destruct (dtyp_eqb dt (DTYPE_Base (DTYPE_I (ras_width sp)))); cbn [negb] in H; [| discriminate H].
  destruct (check_callee_arg_contract arch dt pa sp) eqn:Eac; [| discriminate H].
  rewrite (IH (S idx) rd rp H), Bool.andb_true_r.
  reflexivity.
Qed.

Definition check_one_callee_contract_diag
  (tenv : list (ident * typ)) (ir_m : CFG.mcfg typ) (arch : elf_arch) (c : mc_callee_spec)
  : string + unit :=
  let cn := mcs_name c in
  match find_unique_callee_decl_diag ir_m cn with
  | inl err => inl err
  | inr d =>
      let '(d_rattrs, d_pattrs) := dc_param_attrs d in
      match dc_type d with
      | TYPE_Function ret_ty arg_tys false =>
          let arg_dtys := List.map (typ_to_dtyp tenv) arg_tys in
          if negb (dtyp_eqb (typ_to_dtyp tenv ret_ty) (DTYPE_Base (DTYPE_I (mcs_ret_width c)))) then
            inl (diag "mc-call-contract"
              ("callee '" ++ cn ++ "' IR return type mismatches cert width i" ++ diag_pos_dec (mcs_ret_width c)))
          else if negb (rv_supported_arg_width (mcs_ret_width c)) then
            inl (diag "mc-call-contract"
              ("callee '" ++ cn ++ "' unsupported return width i" ++ diag_pos_dec (mcs_ret_width c)))
          else if negb (cconv_eqb (anns_cconv (dc_annotations d)) CC_Ccc) then
            inl (diag "mc-call-contract"
              ("callee '" ++ cn ++ "' has unsupported calling convention"))
          else if negb (forallb decl_ann_supported (dc_annotations d)) then
            inl (diag "mc-call-contract"
              ("callee '" ++ cn ++ "' has unsupported declaration annotation"))
          else if negb (forallb (fun a => negb (is_unmodeled_fn_attr a))
                                (dc_attrs d ++ ann_fun_attributes (dc_annotations d))) then
            inl (diag "mc-call-contract"
              ("callee '" ++ cn ++ "' has unmodeled function attribute"))
          else if negb (forallb (fun a => negb (is_unmodeled_param_attr a)) d_rattrs) then
            inl (diag "mc-call-contract"
              ("callee '" ++ cn ++ "' has unmodeled return attribute"))
          else if negb (forallb (forallb (fun a => negb (is_unmodeled_param_attr a))) d_pattrs) then
            inl (diag "mc-call-contract"
              ("callee '" ++ cn ++ "' has unmodeled parameter attribute"))
          else
            match check_callee_ret_ext_diag cn (mcs_ret_width c) d_rattrs (mcs_ret_ext c) with
            | inl err => inl err
            | inr tt => check_callee_args_list_diag cn 0%nat arch arg_dtys d_pattrs (mcs_args c)
            end
      | TYPE_Function _ _ true =>
          inl (diag "mc-call-contract" ("varargs callee '" ++ cn ++ "' is not supported"))
      | _ =>
          inl (diag "mc-call-contract" ("callee '" ++ cn ++ "' does not have function type"))
      end
  end.

Local Lemma check_one_callee_contract_diag_sound :
  forall tenv ir_m arch c,
    check_one_callee_contract_diag tenv ir_m arch c = inr tt ->
    check_one_callee_contract tenv ir_m arch c = true.
Proof.
  intros tenv ir_m arch c H; unfold check_one_callee_contract_diag, check_one_callee_contract in *.
  destruct (find_unique_callee_decl_diag ir_m (mcs_name c)) as [| d] eqn:Efd; [discriminate H |].
  rewrite (find_unique_callee_decl_diag_sound _ _ _ Efd).
  destruct (dc_param_attrs d) as [d_rattrs d_pattrs].
  destruct (dc_type d); try discriminate H.
  match goal with b : bool |- _ => destruct b; [discriminate H |] end.
  match goal with
  | |- context [dtyp_eqb (typ_to_dtyp tenv ?r) (DTYPE_Base (DTYPE_I (mcs_ret_width c)))] =>
      destruct (dtyp_eqb (typ_to_dtyp tenv r) (DTYPE_Base (DTYPE_I (mcs_ret_width c))))
  end; cbn [negb] in H; [| discriminate H].
  destruct (rv_supported_arg_width (mcs_ret_width c)); cbn [negb] in H; [| discriminate H].
  destruct (cconv_eqb (anns_cconv (dc_annotations d)) CC_Ccc); cbn [negb] in H; [| discriminate H].
  destruct (forallb decl_ann_supported (dc_annotations d)); cbn [negb] in H; [| discriminate H].
  destruct (forallb (fun a => negb (is_unmodeled_fn_attr a))
                    (dc_attrs d ++ ann_fun_attributes (dc_annotations d)));
    cbn [negb] in H; [| discriminate H].
  destruct (forallb (fun a => negb (is_unmodeled_param_attr a)) d_rattrs);
    cbn [negb] in H; [| discriminate H].
  destruct (forallb (forallb (fun a => negb (is_unmodeled_param_attr a))) d_pattrs);
    cbn [negb] in H; [| discriminate H].
  unfold check_callee_ret_ext_diag in H.
  destruct (check_callee_ret_ext (mcs_ret_width c) d_rattrs (mcs_ret_ext c)); [| discriminate H].
  cbn [andb]; exact (check_callee_args_list_diag_sound _ _ _ _ _ _ H).
Qed.

Fixpoint check_mc_callee_contracts_diag
  (tenv : list (ident * typ)) (ir_m : CFG.mcfg typ) (arch : elf_arch) (cs : list mc_callee_spec)
  : string + unit :=
  match cs with
  | [] => inr tt
  | c :: rest =>
      match check_one_callee_contract_diag tenv ir_m arch c with
      | inl err => inl err
      | inr tt => check_mc_callee_contracts_diag tenv ir_m arch rest
      end
  end.

Lemma check_mc_callee_contracts_diag_sound :
  forall tenv ir_m arch cs,
    check_mc_callee_contracts_diag tenv ir_m arch cs = inr tt ->
    check_mc_callee_contracts tenv ir_m arch cs = true.
Proof.
  intros tenv ir_m arch cs; unfold check_mc_callee_contracts; induction cs as [| c rest IH]; intro H;
    cbn [check_mc_callee_contracts_diag forallb] in *; [reflexivity |].
  destruct (check_one_callee_contract_diag tenv ir_m arch c) as [| []] eqn:Ec; [discriminate H |].
  rewrite (check_one_callee_contract_diag_sound _ _ _ _ Ec), (IH H); reflexivity.
Qed.

(** Call-site attribute safety predicates ensuring [apply_attrs] and [check_call_return]
    reduce cleanly on integer values. *)

Definition pattrs_no_value_poison (pas : list param_attr) : bool :=
  negb (existsb attr_is_nonnull pas) &&
  is_none_b (find_option attr_align pas) &&
  is_none_b (find_option attr_range pas) &&
  is_none_b (find_option attr_nofpclass pas) &&
  is_none_b (find_option attr_dereferenceable pas).

Definition fattrs_call_ok (fas : list fn_attr) : bool :=
  negb (existsb fn_attr_is_noreturn fas).

Lemma pattrs_no_value_poison_value_attrs {Pa : Params} :
  forall pas (v : @dvalue Pa),
    pattrs_no_value_poison pas = true ->
    (forall p, v <> DVALUE_Base (DVALUE_Pointer p)) ->
    value_attrs_poison pas v = v.
Proof.
  intros pas v Hp Hnp.
  unfold pattrs_no_value_poison in Hp; rewrite !andb_true_iff in Hp.
  destruct Hp as ((((Hnn & Hal) & Hrg) & Hnf) & _).
  apply negb_true_iff in Hnn.
  unfold value_attrs_poison, value_attr_nonnull, value_attr_align, value_attr_range, value_attr_nofpclass.
  rewrite Hnn.
  destruct (find_option attr_align pas); [discriminate Hal |].
  destruct (find_option attr_range pas); [discriminate Hrg |].
  destruct (find_option attr_nofpclass pas); [discriminate Hnf |].
  cbn [option_map value_metadata_range].
  destruct v as [[p | | | | | | | ] | |]; try reflexivity; exfalso; exact (Hnp p eq_refl).
Qed.

Lemma pattrs_no_value_poison_deref {Pa : Params} {E : Type -> Type}
  `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{MemoryE -< E} :
  forall pas (v : @dvalue Pa) msg,
    (forall p, v <> DVALUE_Base (DVALUE_Pointer p)) ->
    assert_attrs_dereferenceable (E := E) pas v msg = Ret tt.
Proof.
  intros pas v msg Hnp; unfold assert_attrs_dereferenceable.
  destruct (find_option attr_dereferenceable pas) as [[orn n] |]; [| reflexivity].
  destruct v as [[p | | | | | | | ] | |]; try reflexivity; exfalso; exact (Hnp p eq_refl).
Qed.

(** Shared ABI return extension relation between source [bit_int w] and 64-bit register. *)

Definition rv_abi_ret_matches
  (w : positive) (ext : rv_arg_ext) (v_ret : @Integers.bit_int w) (a0 : @Integers.bit_int 64%positive)
  : Prop :=
  rv_trunc_ret_val w a0 = v_ret /\
  (Pos.eqb w 64%positive = false ->
   match ext with
   | RAE_SignExt => a0 = @Integers.repr 64%positive (@Integers.signed w v_ret)
   | RAE_ZeroExt => a0 = @Integers.repr 64%positive (@Integers.unsigned w v_ret)
   | RAE_None => True
   end).

(** *** 2.1 RISC-V Call-Aware Oracle & Operational Semantics *)

Definition rv_call_oracle : Type :=
  string -> rv_regfile -> mc_stack_mem -> option (rv_regfile * mc_stack_mem).

Definition wf_rv_call_oracle (callees : list mc_callee_spec) (O : rv_call_oracle) : Prop :=
  forall c rf_call mstk_call,
    In c callees ->
    mc_valid_sp0 (rv_read_reg 2%N rf_call) ->
    exists rf_ret (v_ret : @Integers.bit_int (mcs_ret_width c)),
      O (mc_strip_leading_at (mcs_name c)) rf_call mstk_call = Some (rf_ret, mstk_call) /\
      rv_callee_saved_preserved rf_call rf_ret /\
      rv_abi_ret_matches (mcs_ret_width c) (mcs_ret_ext c) v_ret (rv_read_reg 10%N rf_ret).

Definition mc_valid_sp0_depth (d : nat) (sp0 : @Integers.bit_int 64%positive) : Prop :=
  (Z.of_nat d * mc_frame_cap <= @Integers.unsigned 64%positive sp0)%Z /\
  (@Integers.unsigned 64%positive sp0 mod 16 = 0)%Z.

Lemma mc_valid_sp0_depth_step :
  forall sp0 sp_off,
    mc_valid_sp0_depth 2%nat sp0 ->
    mc_sp_aligned16 sp_off = true ->
    mc_valid_sp0 (@Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off)).
Proof.
  intros sp0 sp_off [Hlo Hmod] Hsp.
  destruct (mc_sp_aligned16_bounds _ Hsp) as [Hrng Hhi_off].
  assert (Hmod_off : (sp_off mod 16 = 0)%Z).
  { unfold mc_sp_aligned16 in Hsp; apply andb_true_iff in Hsp as [_ Hm]; apply Z.eqb_eq in Hm; exact Hm. }
  simpl Z.of_nat in Hlo; unfold mc_frame_cap in Hlo, Hrng.
  pose proof (@Integers.unsigned_range 64%positive sp0) as Hrsp0.
  assert (Hre_off : @Integers.unsigned 64%positive (@Integers.repr 64%positive sp_off) =
                    if Z.eqb sp_off 0%Z then 0%Z else (@Integers.modulus 64%positive + sp_off)%Z).
  { change (@Integers.modulus 64%positive) with 18446744073709551616%Z in *.
    destruct (Z.eqb sp_off 0%Z) eqn:Ez.
    - apply Z.eqb_eq in Ez; subst sp_off; rewrite (@Integers.unsigned_repr 64%positive 0); [reflexivity |];
        change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia.
    - apply Z.eqb_neq in Ez.
      rewrite (@Integers.unsigned_repr_eq 64%positive sp_off).
      change (@Integers.modulus 64%positive) with 18446744073709551616%Z.
      rewrite <- (Z.mod_add sp_off 1 18446744073709551616) by lia.
      rewrite Z.mod_small by lia; lia. }
  assert (Hval : @Integers.unsigned 64%positive (@Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off)) =
                 (@Integers.unsigned 64%positive sp0 + sp_off)%Z).
  { unfold Integers.add; rewrite (@Integers.unsigned_repr_eq 64%positive), Hre_off.
    change (@Integers.modulus 64%positive) with 18446744073709551616%Z in *.
    destruct (Z.eqb sp_off 0%Z) eqn:Ez.
    - apply Z.eqb_eq in Ez; subst sp_off; rewrite Z.add_0_r; apply Z.mod_small; lia.
    - apply Z.eqb_neq in Ez.
      replace (@Integers.unsigned 64%positive sp0 + (18446744073709551616 + sp_off))%Z
        with (1 * 18446744073709551616 + (@Integers.unsigned 64%positive sp0 + sp_off))%Z by lia.
      rewrite Z.add_comm, Z.mod_add by lia; apply Z.mod_small; lia. }
  unfold mc_valid_sp0; rewrite Hval; unfold mc_frame_cap.
  split; [lia |].
  rewrite Z.add_mod by lia; rewrite Hmod, Hmod_off; reflexivity.
Qed.

Fixpoint rv_exec_with_calls
  (fuel : nat) (insts : list decoded_rv_call_inst) (O : rv_call_oracle)
  (pc : N) (sp0 : @Integers.bit_int 64%positive) (rf : rv_regfile) (mstk : mc_stack_mem)
  {struct fuel} : option (list (string * rv_regfile * @Integers.bit_int 64%positive) * rv_regfile * mc_stack_mem) :=
  match fuel with
  | O => None
  | S fuel' =>
      match lookup_rv_call_inst insts pc with
      | None => None
      | Some d =>
          match drci_inst d with
          | RCI_Core RV_Ret => Some ([], rf, mstk)
          | RCI_Core i =>
              match rv_exec_one_nonret (mk_decoded_rv (drci_off d) (drci_len d) i) sp0 pc rf mstk with
              | None => None
              | Some (pc1, rf1, mstk1) => rv_exec_with_calls fuel' insts O pc1 sp0 rf1 mstk1
              end
          | RCI_Call cname =>
              if mc_sp_aligned16 (mc_addr_to_off sp0 (rv_read_reg 2%N rf)) then
                let next_pc := (pc + drci_len d)%N in
                let rf_link := rv_write_reg 1%N (@Integers.repr 64%positive (Z.of_N next_pc)) rf in
                match O cname rf_link mstk with
                | None => None
                | Some (rf_ret, mstk_ret) =>
                    match rv_exec_with_calls fuel' insts O next_pc sp0 rf_ret mstk_ret with
                    | None => None
                    | Some (tr, rf_end, mstk_end) =>
                        Some ((cname, rf_link, rv_read_reg 10%N rf_ret) :: tr, rf_end, mstk_end)
                    end
                end
              else None
          end
      end
  end.

(** *** 2.2 AArch64 Call-Aware Oracle & Operational Semantics *)

Definition a64_call_oracle : Type :=
  string -> a64_regfile -> @Integers.bit_int 64%positive -> a64_flags -> mc_stack_mem ->
  option (a64_regfile * @Integers.bit_int 64%positive * a64_flags * mc_stack_mem).

Definition wf_a64_call_oracle (callees : list mc_callee_spec) (O : a64_call_oracle) : Prop :=
  forall c rf_call sp_call fl_call mstk_call,
    In c callees ->
    mc_valid_sp0 sp_call ->
    exists rf_ret fl_ret (v_ret : @Integers.bit_int (mcs_ret_width c)),
      O (mc_strip_leading_at (mcs_name c)) rf_call sp_call fl_call mstk_call =
        Some (rf_ret, sp_call, fl_ret, mstk_call) /\
      a64_callee_saved_preserved rf_call rf_ret /\
      rv_abi_ret_matches (mcs_ret_width c) (mcs_ret_ext c) v_ret (a64_read_reg 0%N rf_ret).

Fixpoint a64_exec_with_calls
  (fuel : nat) (insts : list decoded_a64_call_inst) (O : a64_call_oracle)
  (pc : N) (sp0 : @Integers.bit_int 64%positive)
  (rf : a64_regfile) (sp : @Integers.bit_int 64%positive) (fl : a64_flags) (mstk : mc_stack_mem)
  {struct fuel}
  : option (list (string * a64_regfile * @Integers.bit_int 64%positive) *
            a64_regfile * @Integers.bit_int 64%positive * a64_flags * mc_stack_mem) :=
  match fuel with
  | O => None
  | S fuel' =>
      match lookup_a64_call_inst insts pc with
      | None => None
      | Some d =>
          match daci_inst d with
          | ACI_Core A64_Ret => Some ([], rf, sp, fl, mstk)
          | ACI_Core i =>
              match a64_exec_one_nonret (mk_decoded_a64_inst (daci_off d) i) sp0 pc rf sp fl mstk with
              | None => None
              | Some (pc1, rf1, sp1, fl1, mstk1) =>
                  a64_exec_with_calls fuel' insts O pc1 sp0 rf1 sp1 fl1 mstk1
              end
          | ACI_Call cname =>
              if mc_sp_aligned16 (mc_addr_to_off sp0 sp) then
                let next_pc := (pc + 4%N)%N in
                let rf_link := a64_write_reg 30%N (@Integers.repr 64%positive (Z.of_N next_pc)) rf in
                match O cname rf_link sp fl mstk with
                | None => None
                | Some (rf_ret, sp_ret, fl_ret, mstk_ret) =>
                    match a64_exec_with_calls fuel' insts O next_pc sp0 rf_ret sp_ret fl_ret mstk_ret with
                    | None => None
                    | Some (tr, rf_end, sp_end, fl_end, mstk_end) =>
                        Some ((cname, rf_link, a64_read_reg 0%N rf_ret) :: tr, rf_end, sp_end, fl_end, mstk_end)
                    end
                end
              else None
          end
      end
  end.

(** *** 2.3 Call-Trace IR Operational Stepping & Trace Matching *)

Definition mc_call_event {Pa : Params} : Type :=
  string * list (@dvalue Pa) * @dvalue Pa.

Section IRCallStep.
  Context {Pa : Params}.

  Definition wf_callee_genv (callees : list mc_callee_spec) (genv : raw_id -> @dvalue Pa) : Prop :=
    forall c1 c2,
      In c1 callees -> In c2 callees ->
      genv (Name (mc_strip_leading_at (mcs_name c1))) =
      genv (Name (mc_strip_leading_at (mcs_name c2))) ->
      mc_strip_leading_at (mcs_name c1) = mc_strip_leading_at (mcs_name c2).

  Inductive cfg_call_steps_to_ret {R : Type} (genv : raw_id -> @dvalue Pa)
    : draw_strat -> rmap (@dvalue Pa) -> @CFGtop Pa R ->
      list (@mc_call_event Pa) -> draw_strat -> rmap (@dvalue Pa) -> R -> Prop :=
  | CCSR_Ret sigma env (t : @CFGtop Pa R) (r : R) :
      observe t = RetF r ->
      cfg_call_steps_to_ret genv sigma env t [] sigma env r
  | CCSR_Tau sigma env (t t' : @CFGtop Pa R) tr sigma' env' r :
      observe t = TauF t' ->
      cfg_call_steps_to_ret genv sigma env t' tr sigma' env' r ->
      cfg_call_steps_to_ret genv sigma env t tr sigma' env' r
  | CCSR_LocalRead sigma env (t : @CFGtop Pa R) id dv (k : @dvalue Pa -> @CFGtop Pa R) tr sigma' env' r :
      observe t = VisF (@subevent LocalE CFGEtop _ (@dvalue Pa) (LocalRead id)) k ->
      RM.find id env = Some dv ->
      cfg_call_steps_to_ret genv sigma env (k dv) tr sigma' env' r ->
      cfg_call_steps_to_ret genv sigma env t tr sigma' env' r
  | CCSR_LocalWrite sigma env (t : @CFGtop Pa R) id dv (k : unit -> @CFGtop Pa R) tr sigma' env' r :
      observe t = VisF (@subevent LocalE CFGEtop _ unit (LocalWrite id dv)) k ->
      cfg_call_steps_to_ret genv sigma (RM.add id dv env) (k tt) tr sigma' env' r ->
      cfg_call_steps_to_ret genv sigma env t tr sigma' env' r
  | CCSR_Draw sigma env (t : @CFGtop Pa R) dt (k : @dvalue Pa -> @CFGtop Pa R) tr sigma1 sigma' env' r :
      observe t = VisF (@subevent DrawE CFGEtop _ (@dvalue Pa) (Draw dt)) k ->
      (forall n d, sigma1 n d = shift_draw_strat sigma n d) ->
      cfg_call_steps_to_ret genv sigma1 env (k (sigma 0%nat dt)) tr sigma' env' r ->
      cfg_call_steps_to_ret genv sigma env t tr sigma' env' r
  | CCSR_PureIntrinsic sigma env (t : @CFGtop Pa R) dt fname args va op w rv
      (k : exc + @dvalue Pa -> @CFGtop Pa R) tr sigma' env' r :
      observe t = VisF (@subevent IntrinsicE CFGEtop _ (exc + @dvalue Pa) (Intrinsic dt fname args va)) k ->
      parse_pure_int_intrinsic fname = Some (op, w) ->
      pure_int_intrinsic_fn op w args = raise_ret rv ->
      cfg_call_steps_to_ret genv sigma env (k rv) tr sigma' env' r ->
      cfg_call_steps_to_ret genv sigma env t tr sigma' env' r
  | CCSR_GlobalRead sigma env (t : @CFGtop Pa R) id (k : @dvalue Pa -> @CFGtop Pa R) tr sigma' env' r :
      observe t = VisF (@subevent GlobalE CFGEtop _ (@dvalue Pa) (GlobalRead id)) k ->
      cfg_call_steps_to_ret genv sigma env (k (genv id)) tr sigma' env' r ->
      cfg_call_steps_to_ret genv sigma env t tr sigma' env' r
  | CCSR_Call sigma env (t : @CFGtop Pa R) dt cc cname fv vs dv_ret
      (k : exc + @dvalue Pa -> @CFGtop Pa R) tr sigma' env' r :
      observe t = VisF (@subevent CallE CFGEtop _ (exc + @dvalue Pa) (Call dt cc fv vs)) k ->
      fv = genv (Name cname) ->
      cfg_call_steps_to_ret genv sigma env (k (inr dv_ret)) tr sigma' env' r ->
      cfg_call_steps_to_ret genv sigma env t ((cname, vs, dv_ret) :: tr) sigma' env' r.

  Inductive cfg_call_steps_to_ub {R : Type} (genv : raw_id -> @dvalue Pa)
    : draw_strat -> rmap (@dvalue Pa) -> @CFGtop Pa R -> list (@mc_call_event Pa) -> Prop :=
  | CCSU_UB sigma env (t : @CFGtop Pa R) (k : void -> @CFGtop Pa R) :
      observe t = VisF (@subevent UBE CFGEtop _ void (ThrowUB tt)) k ->
      cfg_call_steps_to_ub genv sigma env t []
  | CCSU_Tau sigma env (t t' : @CFGtop Pa R) tr :
      observe t = TauF t' ->
      cfg_call_steps_to_ub genv sigma env t' tr ->
      cfg_call_steps_to_ub genv sigma env t tr
  | CCSU_LocalRead sigma env (t : @CFGtop Pa R) id dv (k : @dvalue Pa -> @CFGtop Pa R) tr :
      observe t = VisF (@subevent LocalE CFGEtop _ (@dvalue Pa) (LocalRead id)) k ->
      RM.find id env = Some dv ->
      cfg_call_steps_to_ub genv sigma env (k dv) tr ->
      cfg_call_steps_to_ub genv sigma env t tr
  | CCSU_LocalWrite sigma env (t : @CFGtop Pa R) id dv (k : unit -> @CFGtop Pa R) tr :
      observe t = VisF (@subevent LocalE CFGEtop _ unit (LocalWrite id dv)) k ->
      cfg_call_steps_to_ub genv sigma (RM.add id dv env) (k tt) tr ->
      cfg_call_steps_to_ub genv sigma env t tr
  | CCSU_Draw sigma env (t : @CFGtop Pa R) dt (k : @dvalue Pa -> @CFGtop Pa R) tr sigma1 :
      observe t = VisF (@subevent DrawE CFGEtop _ (@dvalue Pa) (Draw dt)) k ->
      (forall n d, sigma1 n d = shift_draw_strat sigma n d) ->
      cfg_call_steps_to_ub genv sigma1 env (k (sigma 0%nat dt)) tr ->
      cfg_call_steps_to_ub genv sigma env t tr
  | CCSU_PureIntrinsic sigma env (t : @CFGtop Pa R) dt fname args va op w rv
      (k : exc + @dvalue Pa -> @CFGtop Pa R) tr :
      observe t = VisF (@subevent IntrinsicE CFGEtop _ (exc + @dvalue Pa) (Intrinsic dt fname args va)) k ->
      parse_pure_int_intrinsic fname = Some (op, w) ->
      pure_int_intrinsic_fn op w args = raise_ret rv ->
      cfg_call_steps_to_ub genv sigma env (k rv) tr ->
      cfg_call_steps_to_ub genv sigma env t tr
  | CCSU_GlobalRead sigma env (t : @CFGtop Pa R) id (k : @dvalue Pa -> @CFGtop Pa R) tr :
      observe t = VisF (@subevent GlobalE CFGEtop _ (@dvalue Pa) (GlobalRead id)) k ->
      cfg_call_steps_to_ub genv sigma env (k (genv id)) tr ->
      cfg_call_steps_to_ub genv sigma env t tr
  | CCSU_Call sigma env (t : @CFGtop Pa R) dt cc cname fv vs dv_ret
      (k : exc + @dvalue Pa -> @CFGtop Pa R) tr :
      observe t = VisF (@subevent CallE CFGEtop _ (exc + @dvalue Pa) (Call dt cc fv vs)) k ->
      fv = genv (Name cname) ->
      cfg_call_steps_to_ub genv sigma env (k (inr dv_ret)) tr ->
      cfg_call_steps_to_ub genv sigma env t ((cname, vs, dv_ret) :: tr).

  Lemma cfg_call_steps_to_ret_obs {R : Type} (genv : raw_id -> @dvalue Pa) :
    forall sigma env (t1 t2 : @CFGtop Pa R) tr sigma' env' r,
      observe t1 = observe t2 ->
      cfg_call_steps_to_ret genv sigma env t1 tr sigma' env' r ->
      cfg_call_steps_to_ret genv sigma env t2 tr sigma' env' r.
  Proof.
    intros sigma env t1 t2 tr sigma' env' r Ho H.
    inversion H; subst;
      [apply CCSR_Ret | eapply CCSR_Tau | eapply CCSR_LocalRead | eapply CCSR_LocalWrite
      | eapply CCSR_Draw | eapply CCSR_PureIntrinsic | eapply CCSR_GlobalRead | eapply CCSR_Call];
      repeat (eassumption || (rewrite <- Ho; eassumption) || reflexivity).
  Qed.

  Lemma cfg_call_steps_to_ub_obs {R : Type} (genv : raw_id -> @dvalue Pa) :
    forall sigma env (t1 t2 : @CFGtop Pa R) tr,
      observe t1 = observe t2 ->
      cfg_call_steps_to_ub genv sigma env t1 tr ->
      cfg_call_steps_to_ub genv sigma env t2 tr.
  Proof.
    intros sigma env t1 t2 tr Ho H.
    inversion H; subst;
      [eapply CCSU_UB | eapply CCSU_Tau | eapply CCSU_LocalRead | eapply CCSU_LocalWrite
      | eapply CCSU_Draw | eapply CCSU_PureIntrinsic | eapply CCSU_GlobalRead | eapply CCSU_Call];
      repeat (eassumption || (rewrite <- Ho; eassumption) || reflexivity).
  Qed.

  Lemma cfg_call_steps_to_ret_bind {R S : Type} (genv : raw_id -> @dvalue Pa) :
    forall s0 env0 (t : @CFGtop Pa R) tr1 s1 env1 x (k : R -> @CFGtop Pa S) tr2 s2 env2 y,
      cfg_call_steps_to_ret genv s0 env0 t tr1 s1 env1 x ->
      cfg_call_steps_to_ret genv s1 env1 (k x) tr2 s2 env2 y ->
      cfg_call_steps_to_ret genv s0 env0 (ITree.bind t k) (tr1 ++ tr2) s2 env2 y.
  Proof.
    intros s0 env0 t tr1 s1 env1 x k tr2 s2 env2 y H1 H2.
    induction H1 as
      [ s env t r Ho
      | s env t t' tr s' env' r Ho _ IH
      | s env t id dv ke tr s' env' r Ho Hf _ IH
      | s env t id dv ke tr s' env' r Ho _ IH
      | s env t dt ke tr s_sh s' env' r Ho Hsh _ IH
      | s env t dt fn args va op w rv ke tr s' env' r Ho Ep Efn _ IH
      | s env t id ke tr s' env' r Ho _ IH
      | s env t dt cc cn fv vs dvr ke tr s' env' r Ho Hfv _ IH ];
      cbn [app].
    - eapply cfg_call_steps_to_ret_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
    - eapply CCSR_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CCSR_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
    - eapply CCSR_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CCSR_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact (IH H2)].
    - eapply CCSR_PureIntrinsic; [rewrite observe_bind, Ho; reflexivity | exact Ep | exact Efn | exact (IH H2)].
    - eapply CCSR_GlobalRead; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CCSR_Call; [rewrite observe_bind, Ho; reflexivity | exact Hfv | exact (IH H2)].
  Qed.

  Lemma cfg_call_steps_to_ub_bind_l {R S : Type} (genv : raw_id -> @dvalue Pa) :
    forall s0 env0 (t : @CFGtop Pa R) tr (k : R -> @CFGtop Pa S),
      cfg_call_steps_to_ub genv s0 env0 t tr ->
      cfg_call_steps_to_ub genv s0 env0 (ITree.bind t k) tr.
  Proof.
    intros s0 env0 t tr k H.
    induction H as
      [ s env t ke Ho
      | s env t t' tr Ho _ IH
      | s env t id dv ke tr Ho Hf _ IH
      | s env t id dv ke tr Ho _ IH
      | s env t dt ke tr s_sh Ho Hsh _ IH
      | s env t dt fn args va op w rv ke tr Ho Ep Efn _ IH
      | s env t id ke tr Ho _ IH
      | s env t dt cc cn fv vs dvr ke tr Ho Hfv _ IH ].
    - eapply CCSU_UB; rewrite observe_bind, Ho; reflexivity.
    - eapply CCSU_Tau; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply CCSU_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact IH].
    - eapply CCSU_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply CCSU_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact IH].
    - eapply CCSU_PureIntrinsic; [rewrite observe_bind, Ho; reflexivity | exact Ep | exact Efn | exact IH].
    - eapply CCSU_GlobalRead; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply CCSU_Call; [rewrite observe_bind, Ho; reflexivity | exact Hfv | exact IH].
  Qed.

  Lemma cfg_call_steps_to_ub_bind_r {R S : Type} (genv : raw_id -> @dvalue Pa) :
    forall s0 env0 (t : @CFGtop Pa R) tr1 s1 env1 x (k : R -> @CFGtop Pa S) tr2,
      cfg_call_steps_to_ret genv s0 env0 t tr1 s1 env1 x ->
      cfg_call_steps_to_ub genv s1 env1 (k x) tr2 ->
      cfg_call_steps_to_ub genv s0 env0 (ITree.bind t k) (tr1 ++ tr2).
  Proof.
    intros s0 env0 t tr1 s1 env1 x k tr2 H1 H2.
    induction H1 as
      [ s env t r Ho
      | s env t t' tr s' env' r Ho _ IH
      | s env t id dv ke tr s' env' r Ho Hf _ IH
      | s env t id dv ke tr s' env' r Ho _ IH
      | s env t dt ke tr s_sh s' env' r Ho Hsh _ IH
      | s env t dt fn args va op w rv ke tr s' env' r Ho Ep Efn _ IH
      | s env t id ke tr s' env' r Ho _ IH
      | s env t dt cc cn fv vs dvr ke tr s' env' r Ho Hfv _ IH ];
      cbn [app].
    - eapply cfg_call_steps_to_ub_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
    - eapply CCSU_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CCSU_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
    - eapply CCSU_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CCSU_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact (IH H2)].
    - eapply CCSU_PureIntrinsic; [rewrite observe_bind, Ho; reflexivity | exact Ep | exact Efn | exact (IH H2)].
    - eapply CCSU_GlobalRead; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CCSU_Call; [rewrite observe_bind, Ho; reflexivity | exact Hfv | exact (IH H2)].
  Qed.

  Lemma cfg_steps_to_call_ret {R : Type} (genv : raw_id -> @dvalue Pa) :
    forall s0 env0 (t : @CFGtop Pa R) s1 env1 r,
      cfg_steps_to_ret s0 env0 t s1 env1 r ->
      cfg_call_steps_to_ret genv s0 env0 t [] s1 env1 r.
  Proof.
    intros s0 env0 t s1 env1 r H.
    induction H;
      [eapply CCSR_Ret | eapply CCSR_Tau | eapply CCSR_LocalRead | eapply CCSR_LocalWrite
      | eapply CCSR_Draw | eapply CCSR_PureIntrinsic]; eassumption.
  Qed.

  Lemma cfg_steps_to_call_ub {R : Type} (genv : raw_id -> @dvalue Pa) :
    forall s0 env0 (t : @CFGtop Pa R),
      cfg_steps_to_ub s0 env0 t ->
      cfg_call_steps_to_ub genv s0 env0 t [].
  Proof.
    intros s0 env0 t H.
    induction H;
      [eapply CCSU_UB | eapply CCSU_Tau | eapply CCSU_LocalRead | eapply CCSU_LocalWrite
      | eapply CCSU_Draw | eapply CCSU_PureIntrinsic]; eassumption.
  Qed.

  Lemma pure_cfg_steps_to_call_ret {R : Type} (genv : raw_id -> @dvalue Pa) :
    forall sigma env0 (t : @CFGtop Pa R) env1 r,
      pure_cfg_steps env0 t env1 r ->
      cfg_call_steps_to_ret genv sigma env0 t [] sigma env1 r.
  Proof.
    intros sigma env0 t env1 r H.
    exact (cfg_steps_to_call_ret genv _ _ _ _ _ _ (pure_cfg_to_cfg_ret sigma _ _ _ _ H)).
  Qed.

  (** Match an IR call event against an RV64 / AArch64 machine call event via ABI specs. *)

  Definition rv_call_event_matches
    (callees : list mc_callee_spec)
    (ev_mc : string * rv_regfile * @Integers.bit_int 64%positive)
    (ev_ir : @mc_call_event Pa) : Prop :=
    let '(cn_mc, rf_call, a0_ret) := ev_mc in
    let '(cn_ir, vs_ir, dv_ret) := ev_ir in
    cn_ir = cn_mc /\
    exists c,
      In c callees /\
      mc_strip_leading_at (mcs_name c) = cn_mc /\
      rv_rf_matches_args (build_param_env (List.map ras_name (mcs_args c)) vs_ir) (mcs_args c) rf_call /\
      List.length vs_ir = List.length (mcs_args c) /\
      dv_ret = DVALUE_Base (@DVALUE_I Pa (mcs_ret_width c) (rv_trunc_ret_val (mcs_ret_width c) a0_ret)).

  Definition a64_call_event_matches
    (callees : list mc_callee_spec)
    (ev_mc : string * a64_regfile * @Integers.bit_int 64%positive)
    (ev_ir : @mc_call_event Pa) : Prop :=
    let '(cn_mc, rf_call, x0_ret) := ev_mc in
    let '(cn_ir, vs_ir, dv_ret) := ev_ir in
    cn_ir = cn_mc /\
    exists c,
      In c callees /\
      mc_strip_leading_at (mcs_name c) = cn_mc /\
      a64_rf_matches_args (build_param_env (List.map ras_name (mcs_args c)) vs_ir) (mcs_args c) rf_call /\
      List.length vs_ir = List.length (mcs_args c) /\
      dv_ret = DVALUE_Base (@DVALUE_I Pa (mcs_ret_width c) (rv_trunc_ret_val (mcs_ret_width c) x0_ret)).

  Inductive prefix_matches {A B : Type} (R : B -> A -> Prop) : list A -> list B -> Prop :=
  | PM_Nil bs : prefix_matches R [] bs
  | PM_Cons a b ra rb : R b a -> prefix_matches R ra rb -> prefix_matches R (a :: ra) (b :: rb).

End IRCallStep.

(** ** 3. Width-Tagged Call Variables & Acyclic Call-Tree Summarizers *)

Definition find_callee_spec (callees : list mc_callee_spec) (cname : string)
  : option mc_callee_spec :=
  List.find (fun c => String.eqb (mc_strip_leading_at (mcs_name c)) cname) callees.

Lemma find_callee_spec_in : forall callees cname c,
  find_callee_spec callees cname = Some c ->
  In c callees /\ mc_strip_leading_at (mcs_name c) = cname.
Proof.
  intros callees cname c Hf; unfold find_callee_spec in Hf.
  apply find_some in Hf as [Hin Heq]; apply String.eqb_eq in Heq; split; assumption.
Qed.

Definition mc_call_ret_var (k : nat) (w : positive) : string :=
  ("!call_" ++ show_Z_dec (Z.of_nat k) ++ "_" ++ show_Z_dec (Z.pos w))%string.

Definition mc_call_hi_var (k : nat) : string :=
  ("!call_hi_" ++ show_Z_dec (Z.of_nat k))%string.

Lemma mc_call_ret_var_bang : forall k w, mc_starts_with_bang (mc_call_ret_var k w) = true.
Proof. intros k w; reflexivity. Qed.

Lemma mc_call_hi_var_bang : forall k, mc_starts_with_bang (mc_call_hi_var k) = true.
Proof. intro k; reflexivity. Qed.

Definition mc_call_hi_mask (w : positive) : N :=
  (N.shiftl 1%N 64%N - N.shiftl 1%N (N.pos w))%N.

Definition mc_combine_hi_expr (w : positive) (e_lo e_hi64 : cert_expr) : cert_expr :=
  CE_BinOp CB_Or 64%positive no_binop_flags
    (CE_Cast CCK_ZExt w 64%positive no_cast_flags e_lo)
    (CE_BinOp CB_And 64%positive no_binop_flags e_hi64 (CE_BvConst 64%positive (mc_call_hi_mask w))).

Lemma mc_combine_hi_expr_wf : forall allowed w e_lo e_hi64,
  (w < 64)%positive ->
  wf_sym_expr allowed w e_lo ->
  wf_sym_expr allowed 64%positive e_hi64 ->
  wf_sym_expr allowed 64%positive (mc_combine_hi_expr w e_lo e_hi64).
Proof.
  intros allowed w e_lo e_hi64 Hlt Hlo Hhi; unfold mc_combine_hi_expr.
  apply a64_wf_sym_binop.
  - apply wf_sym_cast; [apply Pos.ltb_lt; exact Hlt | exact Hlo].
  - apply a64_wf_sym_binop; [exact Hhi | apply wf_sym_bv_const].
Qed.

Lemma mc_combine_hi_expr_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle w e_lo e_hi64
         (rk : @Integers.bit_int 64%positive) (vlo : @Integers.bit_int w),
    (w < 64)%positive ->
    eval_closed_cert_expr penv foracle e_lo = raise_ret (DVALUE_Base (@DVALUE_I Pa w vlo)) ->
    eval_closed_cert_expr penv foracle e_hi64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive rk)) ->
    vlo = @Integers.repr w (@Integers.unsigned 64%positive rk) ->
    eval_closed_cert_expr penv foracle (mc_combine_hi_expr w e_lo e_hi64) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive rk)).
Proof.
  intros penv foracle w e_lo e_hi64 rk vlo Hlt Hlo Hhi Htr; unfold mc_combine_hi_expr.
  assert (Hltb : (w <? 64)%positive = true) by (apply Pos.ltb_lt; exact Hlt).
  assert (Hz : eval_closed_cert_expr penv foracle
                 (CE_Cast CCK_ZExt w 64%positive no_cast_flags e_lo) =
               raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.repr 64%positive (@Integers.unsigned w vlo)))))
    by (apply eval_ce_zext; assumption).
  assert (Ha : eval_closed_cert_expr penv foracle
                 (CE_BinOp CB_And 64%positive no_binop_flags e_hi64 (CE_BvConst 64%positive (mc_call_hi_mask w))) =
               raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
                 (@Integers.and 64%positive rk (@Integers.repr 64%positive (Z.of_N (mc_call_hi_mask w))))))).
  { rewrite eval_ce_binop, Hhi, eval_ce_const; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
  rewrite eval_ce_binop, Hz, Ha; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  cbn - [Integers.or Integers.and Integers.repr Integers.unsigned mc_call_hi_mask].
  replace (Integers.repr (Z.of_N match PosDef.Pos.sub_mask 18446744073709551616 (Pos.iter xO 1%positive w) with
                                 | PosDef.Pos.IsPos p => N.pos p | _ => 0%N end))
    with (@Integers.repr 64%positive (Z.of_N (mc_call_hi_mask w))) by reflexivity.
  rewrite (or_low_hi_mask_eq w rk vlo (mc_call_hi_mask w) Hlt eq_refl Htr).
  reflexivity.
Qed.

Definition mc_post_call_ret_expr (k : nat) (w : positive) (ext : rv_arg_ext)
  : cert_expr * option string :=
  let rv := mc_call_ret_var k w in
  if Pos.eqb w 64%positive then (CE_Var rv 64%positive, None)
  else
    match ext with
    | RAE_SignExt => (CE_Cast CCK_SExt w 64%positive no_cast_flags (CE_Var rv w), None)
    | RAE_ZeroExt => (CE_Cast CCK_ZExt w 64%positive no_cast_flags (CE_Var rv w), None)
    | RAE_None =>
        let hn := mc_call_hi_var k in
        (mc_combine_hi_expr w (CE_Var rv w) (CE_Var hn 64%positive), Some hn)
    end.

Lemma mc_post_call_ret_expr_wf : forall allowed k w ext e_out opt_hi,
  rv_supported_arg_width w = true ->
  In (mc_call_ret_var k w, w) allowed ->
  mc_post_call_ret_expr k w ext = (e_out, opt_hi) ->
  (match opt_hi with None => True | Some hn => In (hn, 64%positive) allowed end) ->
  wf_sym_expr allowed 64%positive e_out.
Proof.
  intros allowed k w ext e_out opt_hi Hw Hin Hpc Hhi.
  assert (Hvar_wf : forall nm wn, In (nm, wn) allowed -> starts_with_dollar nm = false -> wf_sym_expr allowed wn (CE_Var nm wn)).
  { intros nm wn Hnm Hnd; unfold wf_sym_expr; cbn; rewrite Hnd.
    assert (Hvpin : var_pair_in (nm, wn) allowed = true).
    { clear -Hnm; induction allowed as [| [x wx] rest IH]; cbn in *; [contradiction Hnm |].
      destruct Hnm as [Heq | Hr]; [inversion Heq; subst; unfold var_pair_eqb; rewrite String.eqb_refl, Pos.eqb_refl; reflexivity |].
      rewrite (IH Hr), orb_true_r; reflexivity. }
    rewrite Hvpin; repeat split; reflexivity. }
  unfold mc_post_call_ret_expr in Hpc.
  destruct (Pos.eqb w 64%positive) eqn:Ew64.
  - apply Pos.eqb_eq in Ew64; subst w; inversion Hpc; subst; clear Hpc.
    exact (Hvar_wf _ _ Hin ltac:(unfold mc_call_ret_var; cbn; reflexivity)).
  - pose proof (rv_supported_arg_width_lt64 _ Hw Ew64) as Hltb.
    assert (Hlt : (w < 64)%positive) by (apply Pos.ltb_lt; exact Hltb).
    assert (Hvr : wf_sym_expr allowed w (CE_Var (mc_call_ret_var k w) w))
      by exact (Hvar_wf _ _ Hin ltac:(unfold mc_call_ret_var; cbn; reflexivity)).
    destruct ext; inversion Hpc; subst; clear Hpc.
    + apply mc_combine_hi_expr_wf; [exact Hlt | exact Hvr |].
      exact (Hvar_wf _ _ Hhi ltac:(unfold mc_call_hi_var; cbn; reflexivity)).
    + apply wf_sym_cast; assumption.
    + apply wf_sym_cast; assumption.
Qed.

Lemma mc_post_call_ret_expr_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle k w ext e_out opt_hi
         (v_ret : @Integers.bit_int w) (a0 : @Integers.bit_int 64%positive),
    rv_supported_arg_width w = true ->
    mc_post_call_ret_expr k w ext = (e_out, opt_hi) ->
    rv_abi_ret_matches w ext v_ret a0 ->
    penv (mc_call_ret_var k w) = Some (DVALUE_Base (@DVALUE_I Pa w v_ret)) ->
    (match opt_hi with
     | None => True
     | Some hn => penv hn = Some (DVALUE_Base (@DVALUE_I Pa 64%positive a0))
     end) ->
    eval_closed_cert_expr penv foracle e_out =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive a0)).
Proof.
  intros penv foracle k w ext e_out opt_hi v_ret a0 Hw Hpc Habi Hrv Hhi.
  destruct Habi as [Htr Hext]; unfold rv_trunc_ret_val in Htr.
  unfold mc_post_call_ret_expr in Hpc.
  destruct (Pos.eqb w 64%positive) eqn:Ew64.
  - apply Pos.eqb_eq in Ew64; subst w; inversion Hpc; subst; clear Hpc.
    rewrite (@Integers.repr_unsigned 64%positive) in Hrv.
    unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hrv;
      cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
  - pose proof (rv_supported_arg_width_lt64 _ Hw Ew64) as Hltb.
    assert (Hlt : (w < 64)%positive) by (apply Pos.ltb_lt; exact Hltb).
    assert (Hev_r : eval_closed_cert_expr penv foracle (CE_Var (mc_call_ret_var k w) w) =
                    raise_ret (DVALUE_Base (@DVALUE_I Pa w v_ret))).
    { unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hrv; cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity. }
    pose proof (Hext eq_refl) as Hext_f.
    destruct ext; inversion Hpc; subst; clear Hpc.
    + eapply mc_combine_hi_expr_sound; [exact Hlt | exact Hev_r | | reflexivity].
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hhi; cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    + rewrite Hext_f; apply eval_ce_sext; assumption.
    + rewrite Hext_f; apply eval_ce_zext; assumption.
Qed.

(** *** 3.1 Symbolic Call Trees & Variable Collectors *)

Inductive ir_call_tree : Type :=
| ICT_Ret (ret_w : positive) (ret_e : cert_expr)
| ICT_UB
| ICT_Branch (cond : cert_expr) (dt df : ir_call_tree)
| ICT_Call (callee : string) (arg_es : list (bool * positive * cert_expr))
           (ret_w : positive) (ret_var : string) (cont : ir_call_tree).

Inductive mc_call_tree : Type :=
| MCT_Ret (ret_e : cert_expr)
| MCT_Branch (cond : cert_expr) (dt df : mc_call_tree)
| MCT_Call (callee : string) (arg_es64 : list cert_expr)
           (ret_w : positive) (ret_ext : rv_arg_ext)
           (ret_var : string) (ret_hi_var : option string) (cont : mc_call_tree).

Fixpoint collect_ir_call_vars_acc
  (t : ir_call_tree) (acc : list (string * positive)) : list (string * positive) :=
  match t with
  | ICT_Ret _ _ | ICT_UB => acc
  | ICT_Branch _ dt df =>
      collect_ir_call_vars_acc df (collect_ir_call_vars_acc dt acc)
  | ICT_Call _ _ rw rv cont =>
      collect_ir_call_vars_acc cont ((rv, rw) :: acc)
  end.

Definition collect_ir_call_vars (t : ir_call_tree) : list (string * positive) :=
  collect_ir_call_vars_acc t [].

Lemma collect_ir_call_vars_acc_shift : forall t acc,
  collect_ir_call_vars_acc t acc = collect_ir_call_vars t ++ acc.
Proof.
  unfold collect_ir_call_vars; induction t as [| | ? dt IHdt df IHdf | ? ? rw rv cont IH];
    intro acc; cbn [collect_ir_call_vars_acc]; try reflexivity.
  - rewrite IHdf, IHdt, (IHdf (collect_ir_call_vars_acc dt [])), app_assoc; reflexivity.
  - rewrite IH, (IH [(rv, rw)]), <- app_assoc; reflexivity.
Qed.

Fixpoint collect_mc_call_vars_acc
  (t : mc_call_tree) (acc : list (string * positive)) : list (string * positive) :=
  match t with
  | MCT_Ret _ => acc
  | MCT_Branch _ dt df =>
      collect_mc_call_vars_acc df (collect_mc_call_vars_acc dt acc)
  | MCT_Call _ _ rw _ rv opt_hi cont =>
      let acc1 := match opt_hi with
                  | None => (rv, rw) :: acc
                  | Some hn => (rv, rw) :: (hn, 64%positive) :: acc
                  end in
      collect_mc_call_vars_acc cont acc1
  end.

Definition collect_mc_call_vars (t : mc_call_tree) : list (string * positive) :=
  collect_mc_call_vars_acc t [].

Lemma collect_mc_call_vars_acc_shift : forall t acc,
  collect_mc_call_vars_acc t acc = collect_mc_call_vars t ++ acc.
Proof.
  unfold collect_mc_call_vars; induction t as [| ? dt IHdt df IHdf | ? ? rw ? rv opt_hi cont IH];
    intro acc; cbn [collect_mc_call_vars_acc]; try reflexivity.
  - rewrite IHdf, IHdt, (IHdf (collect_mc_call_vars_acc dt [])), app_assoc; reflexivity.
  - destruct opt_hi as [hn |];
      [rewrite (IH ((rv, rw) :: (hn, 64%positive) :: acc)), (IH [(rv, rw); (hn, 64%positive)])
      | rewrite (IH ((rv, rw) :: acc)), (IH [(rv, rw)])];
      rewrite <- app_assoc; reflexivity.
Qed.

Definition sym_expr_freeze_free (allowed : list (string * positive)) (w : positive) (e : cert_expr) : Prop :=
  wf_sym_expr allowed w e /\ expr_has_freeze e = false.

Fixpoint ir_call_tree_wf (allowed : list (string * positive)) (ret_w : positive) (t : ir_call_tree) {struct t} : Prop :=
  match t with
  | ICT_Ret rw ret_e => rw = ret_w /\ sym_expr_freeze_free allowed ret_w ret_e
  | ICT_UB => True
  | ICT_Branch cond dt df =>
      sym_expr_freeze_free allowed 1%positive cond /\
      ir_call_tree_wf allowed ret_w dt /\
      ir_call_tree_wf allowed ret_w df
  | ICT_Call _ arg_es rw rv cont =>
      Forall (fun '(_, w, e) => sym_expr_freeze_free allowed w e) arg_es /\
      is_supported_bit_width rw = true /\
      ir_call_tree_wf ((rv, rw) :: allowed) ret_w cont
  end.

Fixpoint mc_call_tree_wf (allowed : list (string * positive)) (ret_w : positive) (t : mc_call_tree) {struct t} : Prop :=
  match t with
  | MCT_Ret ret_e => wf_sym_expr allowed ret_w ret_e
  | MCT_Branch cond dt df =>
      wf_sym_expr allowed 1%positive cond /\
      mc_call_tree_wf allowed ret_w dt /\
      mc_call_tree_wf allowed ret_w df
  | MCT_Call _ arg_es64 rw _ rv opt_hi cont =>
      Forall (wf_sym_expr allowed 64%positive) arg_es64 /\
      rv_supported_arg_width rw = true /\
      let ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end in
      mc_call_tree_wf ((rv, rw) :: ext ++ allowed) ret_w cont
  end.

(** *** 3.2 Acyclic IR Call-Tree Reifier *)

Fixpoint reify_ir_call_args
  (cname : string) (arg_idx : nat) (lmap : rmap (positive * cert_expr))
  (specs : list rv_arg_spec)
  (args : list (texp dtyp * list param_attr))
  {struct specs} : string + list (bool * positive * cert_expr) :=
  match specs, args with
  | [], [] => inr []
  | sp :: srest, ((aty, ae), pas) :: arest =>
      let w := ras_width sp in
      if negb (dtyp_eqb aty (DTYPE_Base (DTYPE_I w))) then
        inl (diag "mc-call-ir"
          ("argument #" ++ diag_nat_dec arg_idx ++ " type mismatch in call to '" ++ cname ++
           "' (expected i" ++ diag_pos_dec w ++ ")"))
      else if negb (pattrs_no_value_poison pas) then
        inl (diag "mc-call-ir"
          ("argument #" ++ diag_nat_dec arg_idx ++ " has unsupported attribute in call to '" ++ cname ++ "'"))
      else
        match reify_pure_exp lmap (Some aty) ae with
        | None =>
            inl (diag "mc-call-ir"
              ("unsupported non-pure expression in argument #" ++ diag_nat_dec arg_idx ++
               " calling '" ++ cname ++ "'"))
        | Some (_, ce) =>
            if negb (ub_free_expr ce) then
              inl (diag "mc-call-ir"
                ("non-UB-free expression in argument #" ++ diag_nat_dec arg_idx ++
                 " calling '" ++ cname ++ "'"))
            else if expr_has_freeze ce then
              inl (diag "mc-call-ir"
                ("freeze expression not allowed in argument #" ++ diag_nat_dec arg_idx ++
                 " calling '" ++ cname ++ "'"))
            else
              match reify_ir_call_args cname (S arg_idx) lmap srest arest with
              | inl err => inl err
              | inr rest =>
                  let need_def := negb (existsb attr_is_noundef pas) in
                  inr ((need_def, w, ce) :: rest)
              end
        end
  | _, _ =>
      inl (diag "mc-call-ir"
        ("argument count mismatch in call to '" ++ cname ++ "' (at argument #" ++
         diag_nat_dec arg_idx ++ ")"))
  end.

Fixpoint reify_ir_code_calls
  (cur_bid : block_id) (callees : list mc_callee_spec) (c : code dtyp)
  (cid : nat) (lmap : rmap (positive * cert_expr))
  (k_end : nat -> rmap (positive * cert_expr) -> string + ir_call_tree)
  {struct c} : string + ir_call_tree :=
  let loc (_ : unit) : string :=
    (" in IR block '" ++ cert_raw_id_bare cur_bid ++ "'")%string
  in
  match c with
  | [] => k_end cid lmap
  | (IVoid _, INSTR_Comment _, _) :: rest =>
      reify_ir_code_calls cur_bid callees rest cid lmap k_end
  | (IVoid _, _, _) :: _ =>
      inl (diag "mc-call-ir" ("unsupported void instruction" ++ loc tt))
  | (IId id, INSTR_Op op, _) :: rest =>
      match reify_pure_exp lmap None op with
      | None =>
          inl (diag "mc-call-ir"
            ("unsupported non-pure expression for %" ++ cert_raw_id_bare id ++ loc tt))
      | Some (w, ce) =>
          if negb (ub_free_expr ce) then
            inl (diag "mc-call-ir"
              ("non-UB-free expression for %" ++ cert_raw_id_bare id ++ loc tt))
          else if expr_has_freeze ce then
            inl (diag "mc-call-ir"
              ("freeze expression not allowed for %" ++ cert_raw_id_bare id ++ loc tt))
          else
            reify_ir_code_calls cur_bid callees rest cid (RM.add id (w, ce) lmap) k_end
      end
  | (IId id, (INSTR_Call (dt_ret, fn_e) call_args anns obs as ins), md) :: rest =>
      match match_pure_int_intrinsic_call ins with
      | Some (PIICA_Binop op w a0 a1) =>
          if negb (match metadata_range md with None => true | Some _ => false end) then
            inl (diag "mc-call-ir"
              ("range metadata not supported on integer intrinsic for %" ++ cert_raw_id_bare id ++ loc tt))
          else
            match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a0,
                  reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a1 with
            | Some (_, ca), Some (_, cb) =>
                if negb (ub_free_expr ca && ub_free_expr cb) then
                  inl (diag "mc-call-ir"
                    ("non-UB-free operand in integer intrinsic for %" ++ cert_raw_id_bare id ++ loc tt))
                else if expr_has_freeze ca || expr_has_freeze cb then
                  inl (diag "mc-call-ir"
                    ("freeze operand not allowed in integer intrinsic for %" ++ cert_raw_id_bare id ++ loc tt))
                else
                  let ce := lower_pure_int_intrinsic_binop op w ca cb in
                  reify_ir_code_calls cur_bid callees rest cid (RM.add id (w, ce) lmap) k_end
            | _, _ =>
                inl (diag "mc-call-ir"
                  ("unsupported operand in binary integer intrinsic for %" ++ cert_raw_id_bare id ++ loc tt))
            end
      | Some (PIICA_Abs w a0 flag) =>
          if negb (match metadata_range md with None => true | Some _ => false end) then
            inl (diag "mc-call-ir"
              ("range metadata not supported on abs intrinsic for %" ++ cert_raw_id_bare id ++ loc tt))
          else
            match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a0 with
            | Some (_, ca) =>
                if negb (ub_free_expr ca) then
                  inl (diag "mc-call-ir"
                    ("non-UB-free operand in abs intrinsic for %" ++ cert_raw_id_bare id ++ loc tt))
                else if expr_has_freeze ca then
                  inl (diag "mc-call-ir"
                    ("freeze operand not allowed in abs intrinsic for %" ++ cert_raw_id_bare id ++ loc tt))
                else
                  let ce := lower_pure_int_intrinsic_abs w ca flag in
                  reify_ir_code_calls cur_bid callees rest cid (RM.add id (w, ce) lmap) k_end
            | None =>
                inl (diag "mc-call-ir"
                  ("unsupported operand in abs intrinsic for %" ++ cert_raw_id_bare id ++ loc tt))
            end
      | None =>
          match dt_ret, fn_e, obs with
          | DTYPE_Base (DTYPE_I rw), EXP_Ident (ID_Global (Name cname)), [] =>
              if negb (match @intrinsic_exp dtyp fn_e with None => true | Some _ => false end) then
                inl (diag "mc-call-ir"
                  ("unsupported LLVM intrinsic call @" ++ cname ++ loc tt))
              else if negb (cconv_eqb (anns_cconv anns) CC_Ccc) then
                inl (diag "mc-call-ir"
                  ("non-C calling convention on call to @" ++ cname ++ loc tt))
              else if negb (match metadata_range md with None => true | Some _ => false end) then
                inl (diag "mc-call-ir"
                  ("range metadata not supported on call to @" ++ cname ++ loc tt))
              else if negb (fattrs_call_ok (ann_fun_attributes anns)) then
                inl (diag "mc-call-ir"
                  ("unsupported function attributes on call to @" ++ cname ++ loc tt))
              else if negb (pattrs_no_value_poison (ann_ret_attributes anns)) then
                inl (diag "mc-call-ir"
                  ("unsupported return attributes on call to @" ++ cname ++ loc tt))
              else if negb (is_supported_bit_width rw) then
                inl (diag "mc-call-ir"
                  ("unsupported return width i" ++ diag_pos_dec rw ++ " on call to @" ++ cname ++ loc tt))
              else
                match find_callee_spec callees cname with
                | None =>
                    inl (diag "mc-call-ir"
                      ("missing callee specification for @" ++ cname ++ loc tt))
                | Some sp =>
                    if Pos.eqb rw (mcs_ret_width sp) then
                      match reify_ir_call_args cname 0%nat lmap (mcs_args sp) call_args with
                      | inl err => inl err
                      | inr arg_es =>
                          let rv := mc_call_ret_var cid rw in
                          let lmap' := RM.add id (rw, CE_Var rv rw) lmap in
                          match reify_ir_code_calls cur_bid callees rest (S cid) lmap' k_end with
                          | inl err => inl err
                          | inr cont => inr (ICT_Call cname arg_es rw rv cont)
                          end
                      end
                    else
                      inl (diag "mc-call-ir"
                        ("call to @" ++ cname ++ " returns i" ++ diag_pos_dec rw ++
                         ", expected i" ++ diag_pos_dec (mcs_ret_width sp) ++ loc tt))
                end
          | _, _, _ :: _ =>
              inl (diag "mc-call-ir"
                ("operand bundles not supported in call for %" ++ cert_raw_id_bare id ++ loc tt))
          | _, EXP_Ident (ID_Global (Name cname)), [] =>
              inl (diag "mc-call-ir"
                ("non-integer return type on call to @" ++ cname ++ loc tt))
          | _, _, [] =>
              inl (diag "mc-call-ir"
                ("indirect or non-named call for %" ++ cert_raw_id_bare id ++ loc tt))
          end
      end
  | (IId id, _, _) :: _ =>
      inl (diag "mc-call-ir"
        ("unsupported non-pure instruction for %" ++ cert_raw_id_bare id ++ loc tt))
  end.

Fixpoint reify_ir_call_at
  (fuel : nat) (callees : list mc_callee_spec) (bmap : rmap (block dtyp))
  (ret_w : positive) (visited : list block_id)
  (is_entry : bool) (bid_from cur_bid : block_id)
  (cid : nat) (lmap : rmap (positive * cert_expr))
  {struct fuel} : string + ir_call_tree :=
  let loc (_ : unit) : string :=
    ("block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')")%string
  in
  if raw_id_in_list cur_bid visited then
    inl (diag "mc-call-ir" ("CFG loop/cycle detected at " ++ loc tt))
  else
    match fuel with
    | O => inl (diag "mc-call-ir" ("CFG fuel exhausted at " ++ loc tt))
    | S fuel' =>
        match RM.find cur_bid bmap with
        | None => inl (diag "mc-call-ir" ("missing CFG " ++ loc tt))
        | Some b =>
            let visited' := cur_bid :: visited in
            let lmap_phis : string + rmap (positive * cert_expr) :=
              if is_entry then
                match blk_phis b with
                | [] => inr lmap
                | _ :: _ => inl (diag "mc-call-ir" ("entry " ++ loc tt ++ " must not contain phi nodes"))
                end
              else
                match reify_pure_phis bid_from lmap (blk_phis b) with
                | None => inl (diag "mc-call-ir" ("unsupported phi instruction in " ++ loc tt))
                | Some pevals =>
                    if negb (pevals_ub_free pevals) then
                      inl (diag "mc-call-ir" ("non-UB-free phi expression in " ++ loc tt))
                    else if negb (forallb (fun '(_, _, ce) => negb (expr_has_freeze ce)) pevals) then
                      inl (diag "mc-call-ir" ("freeze expression not allowed in phi of " ++ loc tt))
                    else inr (apply_reified_phis lmap pevals)
                end in
            match lmap_phis with
            | inl err => inl err
            | inr lmap1 =>
                reify_ir_code_calls cur_bid callees (blk_code b) cid lmap1
                  (fun cid' lmap2 =>
                     let '(_, term) := fst (blk_term b) in
                     match term with
                     | TERM_Unreachable => inr ICT_UB
                     | TERM_Ret (DTYPE_Base (DTYPE_I rw), op) =>
                         if Pos.eqb rw ret_w then
                           match reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I rw))) op with
                           | Some (_, ret_e) =>
                               if negb (ub_free_expr ret_e) then
                                 inl (diag "mc-call-ir" ("non-UB-free return expression in " ++ loc tt))
                               else if expr_has_freeze ret_e then
                                 inl (diag "mc-call-ir" ("freeze expression not allowed in return of " ++ loc tt))
                               else inr (ICT_Ret rw ret_e)
                           | None => inl (diag "mc-call-ir" ("unsupported return operand in " ++ loc tt))
                           end
                         else
                           inl (diag "mc-call-ir"
                             ("return width i" ++ diag_pos_dec rw ++ " mismatches expected i" ++
                              diag_pos_dec ret_w ++ " in " ++ loc tt))
                     | TERM_Br_1 next_bid =>
                         reify_ir_call_at fuel' callees bmap ret_w visited' false cur_bid next_bid cid' lmap2
                     | TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2 =>
                         match reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
                         | Some (_, cond_e) =>
                             if negb (ub_free_expr cond_e) then
                               inl (diag "mc-call-ir" ("non-UB-free branch condition in " ++ loc tt))
                             else if expr_has_freeze cond_e then
                               inl (diag "mc-call-ir" ("freeze expression not allowed in branch condition of " ++ loc tt))
                             else
                               match reify_ir_call_at fuel' callees bmap ret_w visited' false cur_bid br1 cid' lmap2 with
                               | inl err => inl err
                               | inr dt =>
                                   match reify_ir_call_at fuel' callees bmap ret_w visited' false cur_bid br2 cid' lmap2 with
                                   | inl err => inl err
                                   | inr df => inr (ICT_Branch cond_e dt df)
                                   end
                               end
                         | None => inl (diag "mc-call-ir" ("unsupported branch condition in " ++ loc tt))
                         end
                     | _ => inl (diag "mc-call-ir" ("unsupported terminator in " ++ loc tt))
                     end)
            end
        end
    end.

Fixpoint arg_specs_uses_from (base : nat) (specs : list rv_arg_spec) : list (nat * dtyp) :=
  match specs with
  | [] => []
  | sp :: rest => (base, DTYPE_Base (DTYPE_I (ras_width sp))) :: arg_specs_uses_from (S base) rest
  end.

Lemma arg_specs_uses_from_in : forall base specs idx dt,
  In (idx, dt) (arg_specs_uses_from base specs) ->
  exists k sp, idx = (base + k)%nat /\ nth_error specs k = Some sp /\ dt = DTYPE_Base (DTYPE_I (ras_width sp)).
Proof.
  intros base specs; revert base; induction specs as [| sp rest IH]; intros base idx dt Hin;
    cbn [arg_specs_uses_from] in Hin; [contradiction Hin |].
  destruct Hin as [Heq | Htl].
  - inversion Heq; subst idx dt; exists 0%nat, sp; split; [lia | split; reflexivity].
  - destruct (IH (S base) idx dt Htl) as (k & sp0 & Hidx & Hnth & Hdt).
    exists (S k), sp0; split; [lia | split; [exact Hnth | exact Hdt]].
Qed.

Definition reify_ir_call_tree
  (ir_cfg : CFG.cfg dtyp) (arg_specs : list rv_arg_spec) (callees : list mc_callee_spec) (ret_w : positive)
  : string + ir_call_tree :=
  let ir_pnames := List.map cert_reg_name (args ir_cfg) in
  let lmap_init := init_param_lmap (args ir_cfg) ir_pnames (arg_specs_uses_from 0%nat arg_specs) in
  let bmap := ocfg_map (blks ir_cfg) in
  let fuel := S (List.length (blks ir_cfg) + 1) in
  reify_ir_call_at fuel callees bmap ret_w [] true (init ir_cfg) (init ir_cfg) 0%nat lmap_init.

Lemma sym_expr_freeze_free_wf_intro : forall allowed w e,
  wt_cert_expr [] e = true ->
  cert_expr_bit_width e = w ->
  is_let_free_expr e = true ->
  incl (collect_free_vars [] e) allowed ->
  expr_has_freeze e = false ->
  sym_expr_freeze_free allowed w e.
Proof.
  intros allowed w e Hwt Hbw Hlf Hfv Hnf.
  repeat split; try assumption; exact (incl_vars_subset_b _ _ Hfv).
Qed.

Lemma wf_sym_expr_mono : forall a1 a2 w e,
  incl a1 a2 -> wf_sym_expr a1 w e -> wf_sym_expr a2 w e.
Proof.
  intros a1 a2 w e Hinc (Hwt & Hbw & Hlf & Hsub); repeat split; try assumption.
  apply incl_vars_subset_b; eapply incl_tran; [exact (vars_subset_b_incl _ _ Hsub) | exact Hinc].
Qed.

Lemma sym_expr_freeze_free_mono : forall a1 a2 w e,
  incl a1 a2 ->
  sym_expr_freeze_free a1 w e ->
  sym_expr_freeze_free a2 w e.
Proof.
  intros a1 a2 w e Hinc [Hw Hfr]; split; [exact (wf_sym_expr_mono _ _ _ _ Hinc Hw) | exact Hfr].
Qed.

Lemma ir_call_tree_wf_mono : forall a1 a2 ret_w t,
  incl a1 a2 ->
  ir_call_tree_wf a1 ret_w t ->
  ir_call_tree_wf a2 ret_w t.
Proof.
  intros a1 a2 ret_w t; revert a1 a2;
    induction t as [rw ret_e | | cond dt IHt df IHf | cn aes rw rv cont IH];
    intros a1 a2 Hinc Hwf; cbn [ir_call_tree_wf] in *; try exact I.
  - destruct Hwf as [-> Hsf]; split; [reflexivity | exact (sym_expr_freeze_free_mono _ _ _ _ Hinc Hsf)].
  - destruct Hwf as (Hc & Ht & Hf); split;
      [exact (sym_expr_freeze_free_mono _ _ _ _ Hinc Hc)
      | split; [exact (IHt _ _ Hinc Ht) | exact (IHf _ _ Hinc Hf)]].
  - destruct Hwf as (Ha & Hrw & Hc); split; [| split; [exact Hrw |]].
    + rewrite Forall_forall in Ha |- *; intros [[nd w] e] Hin; exact (sym_expr_freeze_free_mono _ _ _ _ Hinc (Ha _ Hin)).
    + eapply IH; [| exact Hc].
      intros x [-> | Hx]; [left; reflexivity | right; exact (Hinc _ Hx)].
Qed.

Lemma wf_pure_lmap_mono : forall a1 a2 lmap,
  incl a1 a2 -> wf_pure_lmap a1 lmap -> wf_pure_lmap a2 lmap.
Proof.
  intros a1 a2 lmap Hinc Hl r w ce Hf.
  destruct (Hl r w ce Hf) as (Hwt & Hbw & Hlf & Hfv); repeat split; try assumption.
  eapply incl_tran; [exact Hfv | exact Hinc].
Qed.

Lemma reify_ir_call_args_wf : forall cname arg_idx allowed lmap specs args aes,
  wf_pure_lmap allowed lmap ->
  reify_ir_call_args cname arg_idx lmap specs args = inr aes ->
  Forall (fun '(_, w, e) => sym_expr_freeze_free allowed w e) aes.
Proof.
  intros cname arg_idx allowed lmap specs; revert arg_idx;
    induction specs as [| sp srest IH];
    intros arg_idx [| [[aty ae] pas] arest] aes Hlmap H; cbn [reify_ir_call_args] in H;
    try discriminate H; [inversion H; constructor |].
  destruct (dtyp_eqb aty (DTYPE_Base (DTYPE_I (ras_width sp)))) eqn:Hdt; cbn [negb] in H; [| discriminate H].
  unfold dtyp_eqb in Hdt; destruct (dtyp_eq_dec aty (DTYPE_Base (DTYPE_I (ras_width sp)))); [| discriminate Hdt].
  destruct (pattrs_no_value_poison pas); cbn [negb] in H; [| discriminate H].
  destruct (reify_pure_exp lmap (Some aty) ae) as [[w ce] |] eqn:Ere; [| discriminate H].
  destruct (ub_free_expr ce) eqn:Hub; cbn [negb] in H; [| discriminate H].
  destruct (expr_has_freeze ce) eqn:Hnf; [discriminate H |].
  destruct (reify_ir_call_args cname (S arg_idx) lmap srest arest) as [| rest] eqn:Hr; [discriminate H |].
  inversion H; subst aes; clear H.
  destruct (reify_pure_exp_typing ae allowed lmap (Some aty) w ce Hlmap Ere) as (_ & Hwt & Hbw & Hlf & Hfv).
  pose proof (reify_pure_exp_top_width ae lmap (Some aty) w ce Ere) as Htw; rewrite e in Htw.
  cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst w.
  constructor; [exact (sym_expr_freeze_free_wf_intro _ _ _ Hwt Htw Hlf Hfv Hnf) | exact (IH _ _ _ Hlmap Hr)].
Qed.

Lemma expr_has_freeze_false_collect_keys : forall e,
  expr_has_freeze e = false -> collect_freeze_keys e = [].
Proof.
  intro e; induction e using cert_expr_ind_nested;
    cbn [expr_has_freeze collect_freeze_keys]; intro Hfr;
    try reflexivity; try discriminate Hfr;
    repeat match goal with
    | H1 : (_ || _)%bool = false |- _ => apply orb_false_iff in H1 as [? ?]
    end;
    rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; try reflexivity; assumption.
Qed.

Lemma lower_pure_int_intrinsic_binop_freeze_free : forall op w ca cb,
  expr_has_freeze ca = false ->
  expr_has_freeze cb = false ->
  expr_has_freeze (lower_pure_int_intrinsic_binop op w ca cb) = false.
Proof.
  intros [] w ca cb Ha Hb; cbn [lower_pure_int_intrinsic_binop expr_has_freeze];
    rewrite ?Ha, ?Hb; reflexivity.
Qed.

Lemma lower_pure_int_intrinsic_abs_freeze_free : forall w ca fl,
  expr_has_freeze ca = false ->
  expr_has_freeze (lower_pure_int_intrinsic_abs w ca fl) = false.
Proof.
  intros w ca [] Ha; cbn [lower_pure_int_intrinsic_abs expr_has_freeze];
    rewrite ?Ha; reflexivity.
Qed.

Lemma lower_pure_int_intrinsic_binop_ub_free : forall op w ca cb,
  ub_free_expr ca = true ->
  ub_free_expr cb = true ->
  ub_free_expr (lower_pure_int_intrinsic_binop op w ca cb) = true.
Proof.
  intros [] w ca cb Ha Hb; cbn [lower_pure_int_intrinsic_binop ub_free_expr];
    rewrite ?Ha, ?Hb; reflexivity.
Qed.

Lemma lower_pure_int_intrinsic_abs_ub_free : forall w ca fl,
  ub_free_expr ca = true ->
  ub_free_expr (lower_pure_int_intrinsic_abs w ca fl) = true.
Proof.
  intros w ca [] Ha; cbn [lower_pure_int_intrinsic_abs ub_free_expr];
    rewrite ?Ha; reflexivity.
Qed.

Lemma reify_ir_code_calls_wf :
  forall cur_bid callees c cid allowed lmap ret_w k_end t,
    wf_pure_lmap allowed lmap ->
    (forall cid' allowed' lmap' t',
       incl allowed allowed' ->
       wf_pure_lmap allowed' lmap' ->
       k_end cid' lmap' = inr t' ->
       ir_call_tree_wf allowed' ret_w t') ->
    reify_ir_code_calls cur_bid callees c cid lmap k_end = inr t ->
    ir_call_tree_wf allowed ret_w t.
Proof.
  intros cur_bid callees c; induction c as [| [[iid ins] md] rest IH];
    intros cid allowed lmap ret_w k_end t Hlmap Hk Hrc; cbn [reify_ir_code_calls] in Hrc.
  - exact (Hk cid allowed lmap t (incl_refl _) Hlmap Hrc).
  - destruct iid as [id | vid].
    + destruct ins; try discriminate Hrc.
      * destruct (reify_pure_exp lmap None op) as [[w ce] |] eqn:Ere; [| discriminate Hrc].
        destruct (ub_free_expr ce); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (expr_has_freeze ce); [discriminate Hrc |].
        destruct (reify_pure_exp_typing op allowed lmap None w ce Hlmap Ere) as (_ & Hwt & Hbw & Hlf & Hfv).
        exact (IH cid allowed (RM.add id (w, ce) lmap) ret_w k_end t
                 (wf_pure_lmap_add _ _ _ _ _ Hlmap Hwt Hbw Hlf Hfv)
                 (fun c' a' l' t' Hinc => Hk c' a' l' t' Hinc) Hrc).
      * destruct (match_pure_int_intrinsic_call (INSTR_Call fn args anns obs)) as [pic |] eqn:Epic.
        -- pose proof (match_pure_int_intrinsic_call_inv _ _ Epic) as Hinv.
           destruct pic as [op w a0 a1 | w a0 flag]; destruct fn as [dt_fn fn_e].
           ++ destruct (match metadata_range md with None => true | Some _ => false end); cbn [negb] in Hrc; [| discriminate Hrc].
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a0) as [[wa ca] |] eqn:Ea0; [| discriminate Hrc].
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a1) as [[wb cb] |] eqn:Ea1; [| discriminate Hrc].
              destruct (ub_free_expr ca && ub_free_expr cb); cbn [negb] in Hrc; [| discriminate Hrc].
              destruct (expr_has_freeze ca || expr_has_freeze cb) eqn:Efr; [discriminate Hrc |].
              apply orb_false_iff in Efr as [Hnfa Hnfb].
              destruct (reify_pure_exp_typing a0 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Hlmap Ea0)
                as (_ & Hwt0 & Hbw0 & Hlf0 & Hfv0).
              pose proof (reify_pure_exp_top_width a0 lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Ea0) as Htw0.
              cbn [check_opt_int_width] in Htw0; apply Pos.eqb_eq in Htw0; subst wa; rewrite Htw0 in Ea0.
              destruct (reify_pure_exp_typing a1 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wb cb Hlmap Ea1)
                as (_ & Hwt1 & Hbw1 & Hlf1 & Hfv1).
              pose proof (reify_pure_exp_top_width a1 lmap (Some (DTYPE_Base (DTYPE_I w))) wb cb Ea1) as Htw1.
              cbn [check_opt_int_width] in Htw1; apply Pos.eqb_eq in Htw1; subst wb; rewrite Htw1 in Ea1.
              destruct (lower_pure_int_intrinsic_binop_typing op w ca cb
                          Hwt0 Htw0 Hlf0 (expr_has_freeze_false_collect_keys _ Hnfa)
                          Hwt1 Htw1 Hlf1 (expr_has_freeze_false_collect_keys _ Hnfb))
                as [Hwt [Hbw [Hlf [_ Hfv_sub]]]].
              assert (Hfv : incl (collect_free_vars [] (lower_pure_int_intrinsic_binop op w ca cb)) allowed)
                by (intros x Hx; apply Hfv_sub, in_app_iff in Hx as [Hx | Hx]; [exact (Hfv0 _ Hx) | exact (Hfv1 _ Hx)]).
              exact (IH cid allowed (RM.add id (w, lower_pure_int_intrinsic_binop op w ca cb) lmap) ret_w k_end t
                       (wf_pure_lmap_add _ _ _ _ _ Hlmap Hwt Hbw Hlf Hfv) Hk Hrc).
           ++ destruct (match metadata_range md with None => true | Some _ => false end); cbn [negb] in Hrc; [| discriminate Hrc].
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a0) as [[wa ca] |] eqn:Ea0; [| discriminate Hrc].
              destruct (ub_free_expr ca); cbn [negb] in Hrc; [| discriminate Hrc].
              destruct (expr_has_freeze ca) eqn:Hnfa; [discriminate Hrc |].
              destruct (reify_pure_exp_typing a0 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Hlmap Ea0)
                as (_ & Hwt0 & Hbw0 & Hlf0 & Hfv0).
              pose proof (reify_pure_exp_top_width a0 lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Ea0) as Htw0.
              cbn [check_opt_int_width] in Htw0; apply Pos.eqb_eq in Htw0; subst wa; rewrite Htw0 in Ea0.
              destruct (lower_pure_int_intrinsic_abs_typing w ca flag
                          Hwt0 Htw0 Hlf0 (expr_has_freeze_false_collect_keys _ Hnfa))
                as [Hwt [Hbw [Hlf [_ Hfv_sub]]]].
              assert (Hfv : incl (collect_free_vars [] (lower_pure_int_intrinsic_abs w ca flag)) allowed)
                by (intros x Hx; exact (Hfv0 _ (Hfv_sub _ Hx))).
              exact (IH cid allowed (RM.add id (w, lower_pure_int_intrinsic_abs w ca flag) lmap) ret_w k_end t
                       (wf_pure_lmap_add _ _ _ _ _ Hlmap Hwt Hbw Hlf Hfv) Hk Hrc).
        -- destruct fn as [dt_ret fn_e].
           destruct dt_ret as [bdt | |]; [destruct bdt as [rw | | | | | | | | | |] | |];
             destruct fn_e;
             try match goal with iv : ident |- _ => destruct iv as [[cname | | ] | ?] end;
             destruct obs; try discriminate Hrc.
           destruct (match @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname))) with None => true | Some _ => false end); cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (cconv_eqb (anns_cconv anns) CC_Ccc); cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (match metadata_range md with None => true | Some _ => false end); cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (fattrs_call_ok (ann_fun_attributes anns)); cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (pattrs_no_value_poison (ann_ret_attributes anns)); cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (is_supported_bit_width rw) eqn:Hsup; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (find_callee_spec callees cname) as [sp |]; [| discriminate Hrc].
           destruct (Pos.eqb rw (mcs_ret_width sp)); [| discriminate Hrc].
           destruct (reify_ir_call_args cname 0%nat lmap (mcs_args sp) args) as [| aes] eqn:Eaes; [discriminate Hrc |].
           destruct (reify_ir_code_calls cur_bid callees rest (S cid)
                       (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap) k_end)
             as [| cont] eqn:Ect; [discriminate Hrc |].
           inversion Hrc; subst t; cbn [ir_call_tree_wf]; repeat split; try assumption.
           ++ exact (reify_ir_call_args_wf cname 0%nat allowed lmap _ _ _ Hlmap Eaes).
           ++ eapply IH; [| | exact Ect].
              ** apply wf_pure_lmap_add.
                 --- exact (wf_pure_lmap_mono allowed ((mc_call_ret_var cid rw, rw) :: allowed) lmap
                              (fun x Hx => or_intror Hx) Hlmap).
                 --- reflexivity.
                 --- reflexivity.
                 --- reflexivity.
                 --- intros [x wx] [Hx | []]; inversion Hx; subst; left; reflexivity.
              ** intros c' a' l' t' Hinc Hl' Hk'; exact (Hk c' a' l' t' (fun x Hx => Hinc x (or_intror Hx)) Hl' Hk').
    + destruct ins; try discriminate Hrc; exact (IH cid allowed lmap ret_w k_end t Hlmap Hk Hrc).
Qed.

Lemma reify_ir_call_at_wf :
  forall fuel callees bmap ret_w visited is_entry bid_from cur_bid cid allowed lmap t,
    is_supported_bit_width ret_w = true ->
    wf_pure_lmap allowed lmap ->
    reify_ir_call_at fuel callees bmap ret_w visited is_entry bid_from cur_bid cid lmap = inr t ->
    ir_call_tree_wf allowed ret_w t.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros callees bmap ret_w visited is_entry bid_from cur_bid cid allowed lmap t Hrw Hlmap H;
    cbn [reify_ir_call_at] in H;
    destruct (raw_id_in_list cur_bid visited); try discriminate H.
  destruct (RM.find cur_bid bmap) as [b |]; [| discriminate H].
  match type of H with
  | match ?x with inl _ => _ | inr _ => _ end = _ => destruct x as [| lmap1] eqn:El1
  end; [discriminate H |].
  assert (Hlmap1 : wf_pure_lmap allowed lmap1).
  { destruct is_entry.
    - destruct (blk_phis b); inversion El1; subst; exact Hlmap.
    - destruct (reify_pure_phis bid_from lmap (blk_phis b)) as [pevals |] eqn:Erp; [| discriminate El1].
      destruct (pevals_ub_free pevals); cbn [negb] in El1; [| discriminate El1].
      destruct (forallb (fun '(_, _, ce) => negb (expr_has_freeze ce)) pevals); cbn [negb] in El1;
        inversion El1; subst.
      exact (apply_reified_phis_wf _ _ _ Hlmap (reify_pure_phis_typing _ _ _ _ _ Hlmap Erp)). }
  eapply reify_ir_code_calls_wf; [exact Hlmap1 | | exact H].
  intros cid' allowed' lmap2 t' _ Hlmap2 Hterm.
  destruct (blk_term b) as [[tid term] tmd]; cbn [fst] in Hterm.
  destruct term; try discriminate Hterm.
  - destruct v as [[[rw | | | | | | | | | |] | |] op]; try discriminate Hterm.
    destruct (Pos.eqb rw ret_w) eqn:Erw; [apply Pos.eqb_eq in Erw; subst rw | discriminate Hterm].
    destruct (reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I ret_w))) op) as [[w0 ret_e] |] eqn:Ere; [| discriminate Hterm].
    destruct (ub_free_expr ret_e); cbn [negb] in Hterm; [| discriminate Hterm].
    destruct (expr_has_freeze ret_e) eqn:Hnf; [discriminate Hterm |].
    inversion Hterm; subst t'; cbn [ir_call_tree_wf]; split; [reflexivity |].
    destruct (reify_pure_exp_typing op allowed' lmap2 (Some (DTYPE_Base (DTYPE_I ret_w))) w0 ret_e Hlmap2 Ere)
      as (_ & Hwt & Hbw & Hlf & Hfv).
    pose proof (reify_pure_exp_top_width op lmap2 (Some (DTYPE_Base (DTYPE_I ret_w))) w0 ret_e Ere) as Htw.
    cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst w0.
    exact (sym_expr_freeze_free_wf_intro _ _ _ Hwt Htw Hlf Hfv Hnf).
  - match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] e_cond] end; try discriminate Hterm.
    destruct rw; try discriminate Hterm.
    destruct (reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) e_cond) as [[w0 cond_e] |] eqn:Erc; [| discriminate Hterm].
    destruct (ub_free_expr cond_e); cbn [negb] in Hterm; [| discriminate Hterm].
    destruct (expr_has_freeze cond_e) eqn:Hnf; [discriminate Hterm |].
    destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' lmap2)
      as [| dt] eqn:Hdt; [discriminate Hterm |].
    destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' lmap2)
      as [| df] eqn:Hdf; [discriminate Hterm |].
    inversion Hterm; subst t'; cbn [ir_call_tree_wf]; split; [| split].
    + destruct (reify_pure_exp_typing e_cond allowed' lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) w0 cond_e Hlmap2 Erc)
        as (_ & Hwt & Hbw & Hlf & Hfv).
      pose proof (reify_pure_exp_top_width e_cond lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) w0 cond_e Erc) as Htw.
      cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst w0.
      exact (sym_expr_freeze_free_wf_intro _ _ _ Hwt Htw Hlf Hfv Hnf).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ Hrw Hlmap2 Hdt).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ Hrw Hlmap2 Hdf).
  - exact (IH _ _ _ _ _ _ _ _ _ _ _ Hrw Hlmap2 Hterm).
  - inversion Hterm; exact I.
Qed.

Lemma reify_ir_call_tree_wf :
  forall ir_cfg arg_specs callees ret_w allowed t_ir,
    is_supported_bit_width ret_w = true ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (arg_specs_uses_from 0%nat arg_specs) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed) ->
    reify_ir_call_tree ir_cfg arg_specs callees ret_w = inr t_ir ->
    ir_call_tree_wf allowed ret_w t_ir.
Proof.
  intros ir_cfg arg_specs callees ret_w allowed t_ir Hrw Hpu H.
  eapply reify_ir_call_at_wf;
    [exact Hrw
    | exact (init_param_lmap_typing (arg_specs_uses_from 0%nat arg_specs) (args ir_cfg) (List.map cert_reg_name (args ir_cfg)) allowed Hpu)
    | exact H].
Qed.

(** *** 3.3 Acyclic RV64 Call-Tree Summarizer *)

Definition rv_post_call_vrf (call_idx : nat) (c : mc_callee_spec) (vrf : rv_val_regs) : rv_val_regs :=
  let '(ret_e64, _) := mc_post_call_ret_expr call_idx (mcs_ret_width c) (mcs_ret_ext c) in
  fun r =>
    if N.eqb r 0%N then MSV_Expr (CE_BvConst 64%positive 0%N)
    else if N.eqb r 2%N then vrf 2%N
    else if N.eqb r 10%N then MSV_Expr ret_e64
    else if rv_is_callee_saved r then vrf r
    else MSV_Undef.

Fixpoint rv_sym_read_call_args_from
  (pc : N) (cname : string) (idx : N) (n : nat) (vrf : rv_val_regs) {struct n}
  : string + list cert_expr :=
  match n with
  | O => inr []
  | S n' =>
      match rv_val_read idx vrf with
      | MSV_Expr e64 =>
          match rv_sym_read_call_args_from pc cname (N.succ idx) n' vrf with
          | inl err => inl err
          | inr rest => inr (e64 :: rest)
          end
      | other =>
          inl (diag "mc-call-mc"
            ("RV64 call to '" ++ cname ++ "' at pc " ++ diag_N_hex pc ++
             ": arg register a" ++ diag_N_dec (idx - 10%N) ++ " holds " ++
             mcc_sym_val_kind other ++ " instead of scalar expr"))
      end
  end.

Lemma lookup_rv_call_inst_eq_key : forall insts pc,
  lookup_rv_call_inst insts pc = lookup_by_key drci_off insts pc.
Proof.
  induction insts as [| d rest IH]; intro pc; [reflexivity |].
  cbn [lookup_rv_call_inst lookup_by_key]; destruct (N.eqb (drci_off d) pc); [reflexivity | exact (IH pc)].
Qed.

Lemma pt_of_list_first_lookup_rv_call : forall insts pc,
  pt_get (N.succ_pos pc) (pt_of_list_first drci_off insts) = lookup_rv_call_inst insts pc.
Proof.
  intros insts pc; rewrite lookup_rv_call_inst_eq_key; exact (pt_of_list_first_get drci_off insts pc).
Qed.

Fixpoint summarize_rv64_call_at
  (fuel : nat) (im : pos_trie decoded_rv_call_inst) (callees : list mc_callee_spec)
  (visited : pos_trie unit) (pc : N) (cid : nat) (sp_off : Z)
  (vrf : rv_val_regs) (astk : mc_sym_stack) (ret_w : positive)
  {struct fuel} : string + mc_call_tree :=
  if pt_has_n pc visited then
    inl (diag "mc-call-mc" ("RV64 loop/cycle detected at pc " ++ diag_N_hex pc))
  else
    match fuel with
    | O => inl (diag "mc-call-mc" ("RV64 call summarizer out of fuel at pc " ++ diag_N_hex pc))
    | S fuel' =>
        match pt_get (N.succ_pos pc) im with
        | None => inl (diag "mc-call-mc" ("missing decoded RV64 instruction at pc " ++ diag_N_hex pc))
        | Some dec =>
            let visited' := pt_add_n pc visited in
            match drci_inst dec with
            | RCI_Core i =>
                let cdec := mk_decoded_rv (drci_off dec) (drci_len dec) i in
                match rv_sym_step_one cdec pc sp_off vrf astk ret_w with
                | None =>
                    inl (diag "mc-call-mc"
                      ("unsupported/failed RV64 symbolic step at pc " ++ diag_N_hex pc ++
                       " (sp-off=" ++ diag_Z_dec sp_off ++ ")"))
                | Some (RSSR_Next next_pc sp_off' vrf' astk') =>
                    summarize_rv64_call_at fuel' im callees visited'
                      next_pc cid sp_off' vrf' astk' ret_w
                | Some (RSSR_Branch cond tgt_pc next_pc) =>
                    match summarize_rv64_call_at fuel' im callees visited'
                            tgt_pc cid sp_off vrf astk ret_w with
                    | inl err => inl err
                    | inr dt =>
                        match summarize_rv64_call_at fuel' im callees visited'
                                next_pc cid sp_off vrf astk ret_w with
                        | inl err => inl err
                        | inr df => inr (MCT_Branch cond dt df)
                        end
                    end
                | Some (RSSR_Ret ret_e) => inr (MCT_Ret ret_e)
                end
            | RCI_Call cname =>
                if negb (mc_sp_aligned16 sp_off) then
                  inl (diag "mc-call-mc"
                    ("unaligned stack pointer (sp-off=" ++ diag_Z_dec sp_off ++
                     ") at RV64 call to '" ++ cname ++ "' at pc " ++ diag_N_hex pc))
                else
                  match find_callee_spec callees cname with
                  | None =>
                      inl (diag "mc-call-mc"
                        ("missing callee spec for '" ++ cname ++ "' at RV64 pc " ++ diag_N_hex pc))
                  | Some c =>
                      match rv_sym_read_call_args_from pc cname 10%N (List.length (mcs_args c)) vrf with
                      | inl err => inl err
                      | inr arg_es64 =>
                          let rw := mcs_ret_width c in
                          let rext := mcs_ret_ext c in
                          let rv := mc_call_ret_var cid rw in
                          let '(_, opt_hi) := mc_post_call_ret_expr cid rw rext in
                          let vrf' := rv_post_call_vrf cid c vrf in
                          let next_pc := (pc + drci_len dec)%N in
                          match summarize_rv64_call_at fuel' im callees visited'
                                  next_pc (S cid) sp_off vrf' astk ret_w with
                          | inl err => inl err
                          | inr cont =>
                              inr (MCT_Call cname arg_es64 rw rext rv opt_hi cont)
                          end
                      end
                  end
            end
        end
    end.

Definition summarize_rv64_call_tree
  (insts : list decoded_rv_call_inst) (callees : list mc_callee_spec)
  (arg_specs : list rv_arg_spec) (ret_w : positive) : string + mc_call_tree :=
  let fuel := S (2 * elf_length_tr insts) in
  summarize_rv64_call_at fuel (pt_of_list_first drci_off insts) callees PT_Empty 0%N 0%nat 0%Z
    (rv_build_init_val_regs 10%N arg_specs) [] ret_w.

(** *** 3.4 Acyclic AArch64 Call-Tree Summarizer *)

Definition a64_post_call_vrf (call_idx : nat) (c : mc_callee_spec) (vrf : a64_val_regs) : a64_val_regs :=
  let '(ret_e64, _) := mc_post_call_ret_expr call_idx (mcs_ret_width c) (mcs_ret_ext c) in
  fun r =>
    if N.leb 31%N r then MSV_Expr (CE_BvConst 64%positive 0%N)
    else if N.eqb r 0%N then MSV_Expr ret_e64
    else if (N.leb 19%N r && N.leb r 29%N) then vrf r
    else MSV_Undef.

Fixpoint a64_sym_read_call_args_from
  (pc : N) (cname : string) (idx : N) (n : nat) (vrf : a64_val_regs) {struct n}
  : string + list cert_expr :=
  match n with
  | O => inr []
  | S n' =>
      match a64_val_read idx vrf with
      | MSV_Expr e64 =>
          match a64_sym_read_call_args_from pc cname (N.succ idx) n' vrf with
          | inl err => inl err
          | inr rest => inr (e64 :: rest)
          end
      | other =>
          inl (diag "mc-call-mc"
            ("AArch64 call to '" ++ cname ++ "' at pc " ++ diag_N_hex pc ++
             ": arg register x" ++ diag_N_dec idx ++ " holds " ++
             mcc_sym_val_kind other ++ " instead of scalar expr"))
      end
  end.

Lemma lookup_a64_call_inst_eq_key : forall insts pc,
  lookup_a64_call_inst insts pc = lookup_by_key daci_off insts pc.
Proof.
  induction insts as [| d rest IH]; intro pc; [reflexivity |].
  cbn [lookup_a64_call_inst lookup_by_key]; destruct (N.eqb (daci_off d) pc); [reflexivity | exact (IH pc)].
Qed.

Lemma pt_of_list_first_lookup_a64_call : forall insts pc,
  pt_get (N.succ_pos pc) (pt_of_list_first daci_off insts) = lookup_a64_call_inst insts pc.
Proof.
  intros insts pc; rewrite lookup_a64_call_inst_eq_key; exact (pt_of_list_first_get daci_off insts pc).
Qed.

Fixpoint summarize_a64_call_at
  (fuel : nat) (im : pos_trie decoded_a64_call_inst) (callees : list mc_callee_spec)
  (visited : pos_trie unit) (pc : N) (cid : nat) (sp_off : Z)
  (vrf : a64_val_regs) (astk : mc_sym_stack) (sfl : a64_sym_flags) (fl_def : bool)
  (ret_w : positive)
  {struct fuel} : string + mc_call_tree :=
  if pt_has_n pc visited then
    inl (diag "mc-call-mc" ("AArch64 loop/cycle detected at pc " ++ diag_N_hex pc))
  else
    match fuel with
    | O => inl (diag "mc-call-mc" ("AArch64 call summarizer out of fuel at pc " ++ diag_N_hex pc))
    | S fuel' =>
        match pt_get (N.succ_pos pc) im with
        | None => inl (diag "mc-call-mc" ("missing decoded AArch64 instruction at pc " ++ diag_N_hex pc))
        | Some dec =>
            let visited' := pt_add_n pc visited in
            match daci_inst dec with
            | ACI_Core i =>
                let cdec := mk_decoded_a64_inst (daci_off dec) i in
                match a64_sym_step_one cdec pc sp_off vrf astk sfl fl_def ret_w with
                | None =>
                    inl (diag "mc-call-mc"
                      ("unsupported/failed AArch64 symbolic step at pc " ++ diag_N_hex pc ++
                       " (sp-off=" ++ diag_Z_dec sp_off ++ ")"))
                | Some (ASSR_Next next_pc sp_off' vrf' astk' sfl' fl_def') =>
                    summarize_a64_call_at fuel' im callees visited'
                      next_pc cid sp_off' vrf' astk' sfl' fl_def' ret_w
                | Some (ASSR_Branch cond tgt_pc next_pc fl_def') =>
                    match summarize_a64_call_at fuel' im callees visited'
                            tgt_pc cid sp_off vrf astk sfl fl_def' ret_w with
                    | inl err => inl err
                    | inr dt =>
                        match summarize_a64_call_at fuel' im callees visited'
                                next_pc cid sp_off vrf astk sfl fl_def' ret_w with
                        | inl err => inl err
                        | inr df => inr (MCT_Branch cond dt df)
                        end
                    end
                | Some (ASSR_Ret ret_e) => inr (MCT_Ret ret_e)
                end
            | ACI_Call cname =>
                if negb (mc_sp_aligned16 sp_off) then
                  inl (diag "mc-call-mc"
                    ("unaligned stack pointer (sp-off=" ++ diag_Z_dec sp_off ++
                     ") at AArch64 call to '" ++ cname ++ "' at pc " ++ diag_N_hex pc))
                else
                  match find_callee_spec callees cname with
                  | None =>
                      inl (diag "mc-call-mc"
                        ("missing callee spec for '" ++ cname ++ "' at AArch64 pc " ++ diag_N_hex pc))
                  | Some c =>
                      match a64_sym_read_call_args_from pc cname 0%N (List.length (mcs_args c)) vrf with
                      | inl err => inl err
                      | inr arg_es64 =>
                          let rw := mcs_ret_width c in
                          let rext := mcs_ret_ext c in
                          let rv := mc_call_ret_var cid rw in
                          let '(_, opt_hi) := mc_post_call_ret_expr cid rw rext in
                          let vrf' := a64_post_call_vrf cid c vrf in
                          let next_pc := (pc + 4%N)%N in
                          match summarize_a64_call_at fuel' im callees visited'
                                  next_pc (S cid) sp_off vrf' astk sfl false ret_w with
                          | inl err => inl err
                          | inr cont =>
                              inr (MCT_Call cname arg_es64 rw rext rv opt_hi cont)
                          end
                      end
                  end
            end
        end
    end.

Definition summarize_a64_call_tree
  (insts : list decoded_a64_call_inst) (callees : list mc_callee_spec)
  (arg_specs : list rv_arg_spec) (ret_w : positive) : string + mc_call_tree :=
  let fuel := S (2 * elf_length_tr insts) in
  summarize_a64_call_at fuel (pt_of_list_first daci_off insts) callees PT_Empty 0%N 0%nat 0%Z
    (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w.

(** *** 3.5 Well-Formedness of RV64 & AArch64 Call-Tree Summarizers *)

Lemma mc_sym_stack_wf_mono : forall a1 a2 sp_off astk,
  incl a1 a2 -> mc_sym_stack_wf a1 sp_off astk -> mc_sym_stack_wf a2 sp_off astk.
Proof.
  intros a1 a2 sp_off astk Hinc H; unfold mc_sym_stack_wf in *; rewrite Forall_forall in *.
  intros [[o s] v] Hin; pose proof (H (o, s, v) Hin) as [H1 H2]; cbn in H1, H2 |- *.
  split; [exact H1 | destruct v; try exact H2; exact (wf_sym_expr_mono _ _ _ _ Hinc H2)].
Qed.

Lemma rv_val_regs_wf_mono : forall a1 a2 vrf,
  incl a1 a2 -> rv_val_regs_wf a1 vrf -> rv_val_regs_wf a2 vrf.
Proof.
  intros a1 a2 vrf Hinc H r; pose proof (H r) as Hr; destruct (rv_val_read r vrf); try exact Hr.
  exact (wf_sym_expr_mono _ _ _ _ Hinc Hr).
Qed.

Lemma wf_a64_val_regs_mono : forall a1 a2 vrf,
  incl a1 a2 -> wf_a64_val_regs a1 vrf -> wf_a64_val_regs a2 vrf.
Proof.
  intros a1 a2 vrf Hinc H r; pose proof (H r) as Hr; destruct (a64_val_read r vrf); try exact Hr.
  exact (wf_sym_expr_mono _ _ _ _ Hinc Hr).
Qed.

Lemma wf_sym_flags_mono : forall a1 a2 sfl,
  incl a1 a2 -> wf_sym_flags a1 sfl -> wf_sym_flags a2 sfl.
Proof.
  intros a1 a2 sfl Hinc (Hn & Hz & Hc & Hv & Hiz); unfold wf_sym_flags in *;
    split; [| split; [| split; [| split]]];
    eapply wf_sym_expr_mono; try exact Hinc; assumption.
Qed.

Lemma rv_sym_read_call_args_from_wf : forall pc cname allowed idx n vrf es,
  rv_val_regs_wf allowed vrf ->
  rv_sym_read_call_args_from pc cname idx n vrf = inr es ->
  Forall (wf_sym_expr allowed 64%positive) es.
Proof.
  intros pc cname allowed idx n; revert idx; induction n as [| n' IH];
    intros idx vrf es Hwf H; cbn [rv_sym_read_call_args_from] in H;
    [inversion H; constructor |].
  destruct (rv_val_read idx vrf) as [| e64 | |] eqn:Er; try discriminate H.
  destruct (rv_sym_read_call_args_from pc cname (N.succ idx) n' vrf) as [| rest] eqn:Hr; [discriminate H |].
  inversion H; subst es; constructor;
    [pose proof (Hwf idx) as Hi; rewrite Er in Hi; exact Hi | exact (IH _ _ _ Hwf Hr)].
Qed.

Lemma a64_sym_read_call_args_from_wf : forall pc cname allowed idx n vrf es,
  wf_a64_val_regs allowed vrf ->
  a64_sym_read_call_args_from pc cname idx n vrf = inr es ->
  Forall (wf_sym_expr allowed 64%positive) es.
Proof.
  intros pc cname allowed idx n; revert idx; induction n as [| n' IH];
    intros idx vrf es Hwf H; cbn [a64_sym_read_call_args_from] in H;
    [inversion H; constructor |].
  destruct (a64_val_read idx vrf) as [| e64 | |] eqn:Er; try discriminate H.
  destruct (a64_sym_read_call_args_from pc cname (N.succ idx) n' vrf) as [| rest] eqn:Hr; [discriminate H |].
  inversion H; subst es; constructor;
    [pose proof (Hwf idx) as Hi; rewrite Er in Hi; exact Hi | exact (IH _ _ _ Hwf Hr)].
Qed.

Lemma rv_post_call_vrf_wf : forall allowed cid c vrf,
  rv_val_regs_wf allowed vrf ->
  rv_supported_arg_width (mcs_ret_width c) = true ->
  let '(e_ret64, opt_hi) := mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c) in
  let ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end in
  let allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed in
  rv_val_regs_wf allowed' (rv_post_call_vrf cid c vrf).
Proof.
  intros allowed cid c vrf Hwf Hrw; unfold rv_post_call_vrf.
  destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
  set (ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end).
  set (allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed).
  assert (Hinc : incl allowed allowed') by (intros x Hx; right; apply in_or_app; right; exact Hx).
  assert (Hret_wf : wf_sym_expr allowed' 64%positive ret_e64).
  { eapply mc_post_call_ret_expr_wf; [exact Hrw | left; reflexivity | exact Epc |].
    destruct opt_hi as [hn |]; [right; left; reflexivity | exact I]. }
  intro r; unfold rv_val_read.
  destruct (N.eqb r 0%N) eqn:E0; [apply wf_sym_bv_const |].
  destruct (N.eqb r 2%N) eqn:E2.
  - pose proof (Hwf 2%N) as H2; unfold rv_val_read in H2; cbn [N.eqb] in H2.
    destruct (vrf 2%N); try exact H2; exact (wf_sym_expr_mono _ _ _ _ Hinc H2).
  - destruct (N.eqb r 10%N); [exact Hret_wf |].
    destruct (rv_is_callee_saved r); [| exact I].
    pose proof (Hwf r) as Hr; unfold rv_val_read in Hr; rewrite E0 in Hr.
    destruct (vrf r); try exact Hr; exact (wf_sym_expr_mono _ _ _ _ Hinc Hr).
Qed.

Lemma a64_post_call_vrf_wf : forall allowed cid c vrf,
  wf_a64_val_regs allowed vrf ->
  rv_supported_arg_width (mcs_ret_width c) = true ->
  let '(e_ret64, opt_hi) := mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c) in
  let ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end in
  let allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed in
  wf_a64_val_regs allowed' (a64_post_call_vrf cid c vrf).
Proof.
  intros allowed cid c vrf Hwf Hrw; unfold a64_post_call_vrf.
  destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
  set (ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end).
  set (allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed).
  assert (Hinc : incl allowed allowed') by (intros x Hx; right; apply in_or_app; right; exact Hx).
  assert (Hret_wf : wf_sym_expr allowed' 64%positive ret_e64).
  { eapply mc_post_call_ret_expr_wf; [exact Hrw | left; reflexivity | exact Epc |].
    destruct opt_hi as [hn |]; [right; left; reflexivity | exact I]. }
  intro r; unfold a64_val_read.
  destruct (N.leb 31%N r) eqn:E31; [apply wf_sym_bv_const |].
  destruct (N.eqb r 0%N); [exact Hret_wf |].
  destruct (N.leb 19%N r && N.leb r 29%N); [| exact I].
  pose proof (Hwf r) as Hr; unfold a64_val_read in Hr; rewrite E31 in Hr.
  destruct (vrf r); try exact Hr; exact (wf_sym_expr_mono _ _ _ _ Hinc Hr).
Qed.

Lemma summarize_rv64_call_at_wfsym :
  forall insts im
    (Him : forall pc, pt_get (N.succ_pos pc) im = lookup_rv_call_inst insts pc)
    fuel callees visited pc cid sp_off vrf astk ret_w allowed t,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true) ->
    forallb rv_call_inst_no_word_mulh insts = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_wf allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    summarize_rv64_call_at fuel im callees visited pc cid sp_off vrf astk ret_w = inr t ->
    mc_call_tree_wf allowed ret_w t.
Proof.
  intros insts im Him fuel; induction fuel as [| fuel' IH];
    intros callees visited pc cid sp_off vrf astk ret_w allowed t
           Hrw Hcws Hmul Hrng Hsp2 Hvrf Hastk Hsum;
    cbn [summarize_rv64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Hlk; [| discriminate Hsum].
  rewrite Him in Hlk.
  assert (Hin_dec : In dec insts).
  { clear -Hlk; induction insts as [| d rest IHi]; cbn in Hlk; [discriminate |].
    destruct (N.eqb (drci_off d) pc); [inversion Hlk; left; reflexivity | right; exact (IHi Hlk)]. }
  destruct (drci_inst dec) as [i | cname] eqn:Edi.
  - assert (Hdec_nmul : inst_no_word_mulh (mk_decoded_rv (drci_off dec) (drci_len dec) i) = true).
    { rewrite forallb_forall in Hmul; pose proof (Hmul dec Hin_dec) as Hm;
        unfold rv_call_inst_no_word_mulh in Hm; rewrite Edi in Hm; exact Hm. }
    destruct (rv_sym_step_one (mk_decoded_rv (drci_off dec) (drci_len dec) i) pc sp_off vrf astk ret_w)
      as [res |] eqn:Est; [| discriminate Hsum].
    pose proof (rv_sym_step_one_wf allowed (mk_decoded_rv (drci_off dec) (drci_len dec) i)
                  pc sp_off vrf astk ret_w res Hrw Hdec_nmul Hrng Hsp2 Hvrf Hastk Est) as Hwf_step.
    destruct res as [npc sp' vrf' astk' | cond tpc npc | ret_e].
    + destruct Hwf_step as (Hrng' & Hsp2' & Hvrf' & Hastk').
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hcws Hmul Hrng' Hsp2' Hvrf' Hastk' Hsum).
    + destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk ret_w)
        as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk ret_w)
        as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t; cbn [mc_call_tree_wf]; split; [exact Hwf_step | split;
        [exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hcws Hmul Hrng Hsp2 Hvrf Hastk Hdt)
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hcws Hmul Hrng Hsp2 Hvrf Hastk Hdf)]].
    + inversion Hsum; subst t; exact Hwf_step.
  - destruct (mc_sp_aligned16 sp_off) eqn:Esp_al; cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |] eqn:Efc; [| discriminate Hsum].
    destruct (rv_sym_read_call_args_from pc cname 10%N (List.length (mcs_args c)) vrf) as [| aes] eqn:Eargs;
      [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited)
                (pc + drci_len dec)%N (S cid) sp_off (rv_post_call_vrf cid c vrf) astk ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t; clear Hsum.
    pose proof (find_callee_spec_in _ _ _ Efc) as [Hc_in _].
    pose proof (Hcws c Hc_in) as Hcrw.
    set (ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end).
    set (allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed).
    assert (Hinc : incl allowed allowed') by (intros x Hx; right; apply in_or_app; right; exact Hx).
    assert (Hvrf' : rv_val_regs_wf allowed' (rv_post_call_vrf cid c vrf)).
    { pose proof (rv_post_call_vrf_wf allowed cid c vrf Hvrf Hcrw) as Hpv.
      rewrite Epc in Hpv; exact Hpv. }
    assert (Hsp2' : rv_val_read 2%N (rv_post_call_vrf cid c vrf) = MSV_StackPtr sp_off).
    { unfold rv_val_read, rv_post_call_vrf; rewrite Epc; cbn [N.eqb].
      unfold rv_val_read in Hsp2; cbn [N.eqb] in Hsp2; exact Hsp2. }
    assert (Hastk' : mc_sym_stack_wf allowed' sp_off astk)
      by exact (mc_sym_stack_wf_mono _ _ _ _ Hinc Hastk).
    cbn [mc_call_tree_wf]; split; [| split].
    + exact (rv_sym_read_call_args_from_wf _ _ _ _ _ _ _ Hvrf Eargs).
    + exact Hcrw.
    + exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hcws Hmul Hrng Hsp2' Hvrf' Hastk' Ect).
Qed.

Lemma summarize_a64_call_at_wfsym :
  forall insts im
    (Him : forall pc, pt_get (N.succ_pos pc) im = lookup_a64_call_inst insts pc)
    fuel callees visited pc cid sp_off vrf astk sfl fl_def ret_w allowed t,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true) ->
    forallb a64_call_inst_valid insts = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    summarize_a64_call_at fuel im callees visited pc cid sp_off vrf astk sfl fl_def ret_w = inr t ->
    mc_call_tree_wf allowed ret_w t.
Proof.
  intros insts im Him fuel; induction fuel as [| fuel' IH];
    intros callees visited pc cid sp_off vrf astk sfl fl_def ret_w allowed t
           Hrw Hcws Hval Hrng Hvrf Hastk Hfl Hsum;
    cbn [summarize_a64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Hlk; [| discriminate Hsum].
  rewrite Him in Hlk.
  assert (Hin_dec : In dec insts).
  { clear -Hlk; induction insts as [| d rest IHi]; cbn in Hlk; [discriminate |].
    destruct (N.eqb (daci_off d) pc); [inversion Hlk; left; reflexivity | right; exact (IHi Hlk)]. }
  destruct (daci_inst dec) as [i | cname] eqn:Edi.
  - destruct (a64_sym_step_one (mk_decoded_a64_inst (daci_off dec) i) pc sp_off vrf astk sfl fl_def ret_w)
      as [res |] eqn:Est; [| discriminate Hsum].
    pose proof (a64_sym_step_one_wf allowed (mk_decoded_a64_inst (daci_off dec) i)
                  pc sp_off vrf astk sfl fl_def ret_w res Hrw Hrng Hvrf Hastk Hfl Est) as Hwf_step.
    destruct res as [npc sp' vrf' astk' sfl' fl_def' | cond tpc npc fl_def' | ret_e].
    + destruct Hwf_step as (Hrng' & Hvrf' & Hastk' & Hfl').
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hcws Hval Hrng' Hvrf' Hastk' Hfl' Hsum).
    + destruct Hwf_step as [Hcw Himp].
      destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk sfl fl_def' ret_w)
        as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk sfl fl_def' ret_w)
        as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t; cbn [mc_call_tree_wf]; split; [exact Hcw | split;
        [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hcws Hval Hrng Hvrf Hastk (fun h => Hfl (Himp h)) Hdt)
        | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hcws Hval Hrng Hvrf Hastk (fun h => Hfl (Himp h)) Hdf)]].
    + inversion Hsum; subst t; exact Hwf_step.
  - destruct (mc_sp_aligned16 sp_off) eqn:Esp_al; cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |] eqn:Efc; [| discriminate Hsum].
    destruct (a64_sym_read_call_args_from pc cname 0%N (List.length (mcs_args c)) vrf) as [| aes] eqn:Eargs;
      [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited)
                (pc + 4%N)%N (S cid) sp_off (a64_post_call_vrf cid c vrf) astk sfl false ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t; clear Hsum.
    pose proof (find_callee_spec_in _ _ _ Efc) as [Hc_in _].
    pose proof (Hcws c Hc_in) as Hcrw.
    set (ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end).
    set (allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed).
    assert (Hinc : incl allowed allowed') by (intros x Hx; right; apply in_or_app; right; exact Hx).
    assert (Hvrf' : wf_a64_val_regs allowed' (a64_post_call_vrf cid c vrf)).
    { pose proof (a64_post_call_vrf_wf allowed cid c vrf Hvrf Hcrw) as Hpv.
      rewrite Epc in Hpv; exact Hpv. }
    assert (Hastk' : mc_sym_stack_wf allowed' sp_off astk)
      by exact (mc_sym_stack_wf_mono _ _ _ _ Hinc Hastk).
    cbn [mc_call_tree_wf]; split; [| split].
    + exact (a64_sym_read_call_args_from_wf _ _ _ _ _ _ _ Hvrf Eargs).
    + exact Hcrw.
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hcws Hval Hrng Hvrf' Hastk' (fun C : false = true => ltac:(discriminate C)) Ect).
Qed.


(** ** 4. Obligation Collection, Validators & DIMACS CNF Emitters *)

Definition build_rv_call_arg_expr (w : positive) (ext : rv_arg_ext) (e_ir : cert_expr) : cert_expr :=
  if Pos.eqb w 64%positive then e_ir
  else
    match ext with
    | RAE_ZeroExt => CE_Cast CCK_ZExt w 64%positive no_cast_flags e_ir
    | RAE_SignExt | RAE_None => CE_Cast CCK_SExt w 64%positive no_cast_flags e_ir
    end.

Definition build_call_arg_cmp
  (cname : string) (arg_idx : nat) (arch : elf_arch) (path : list (bool * cert_expr))
  (sp : rv_arg_spec) (w : positive) (e_ir e_mc64 : cert_expr) : string + mc_loop_obl :=
  match arch with
  | EA_Riscv64 =>
      inr (MLO_Refine false path 64%positive
             (build_rv_call_arg_expr w (ras_ext sp) e_ir) e_mc64)
  | EA_AArch64 =>
      if Pos.eqb w 64%positive then
        match ras_ext sp with
        | RAE_None => inr (MLO_Refine false path 64%positive e_ir e_mc64)
        | _ =>
            inl (diag "mc-call-obl"
              ("unsupported extension on 64-bit AArch64 arg #" ++ diag_nat_dec arg_idx ++
               " calling '" ++ cname ++ "'"))
        end
      else
        match ras_ext sp with
        | RAE_None =>
            let e_trunc := CE_Cast CCK_Trunc 64%positive w no_cast_flags e_mc64 in
            inr (MLO_Refine false path w e_ir e_trunc)
        | RAE_SignExt =>
            let src32 :=
              if Pos.eqb w 32%positive then e_ir
              else CE_Cast CCK_SExt w 32%positive no_cast_flags e_ir in
            let tgt32 := CE_Cast CCK_Trunc 64%positive 32%positive no_cast_flags e_mc64 in
            inr (MLO_Refine false path 32%positive src32 tgt32)
        | RAE_ZeroExt =>
            let src32 :=
              if Pos.eqb w 32%positive then e_ir
              else CE_Cast CCK_ZExt w 32%positive no_cast_flags e_ir in
            let tgt32 := CE_Cast CCK_Trunc 64%positive 32%positive no_cast_flags e_mc64 in
            inr (MLO_Refine false path 32%positive src32 tgt32)
        end
  end.

Fixpoint build_call_arg_obls_acc
  (cname : string) (arg_idx : nat) (arch : elf_arch) (path : list (bool * cert_expr))
  (specs : list rv_arg_spec)
  (ir_args : list (bool * positive * cert_expr))
  (mc_args64 : list cert_expr)
  (acc : list mc_loop_obl)
  {struct specs} : string + list mc_loop_obl :=
  match specs, ir_args, mc_args64 with
  | [], [], [] => inr acc
  | sp :: srest, (need_def, w, e_ir) :: irest, e_mc64 :: mrest =>
      if Pos.eqb w (ras_width sp) then
        match build_call_arg_cmp cname arg_idx arch path sp w e_ir e_mc64 with
        | inl err => inl err
        | inr cmp_o =>
            let acc1 := if need_def then MLO_Defined false path w e_ir :: cmp_o :: acc else cmp_o :: acc in
            build_call_arg_obls_acc cname (S arg_idx) arch path srest irest mrest acc1
        end
      else
        inl (diag "mc-call-obl"
          ("argument #" ++ diag_nat_dec arg_idx ++ " width mismatch calling '" ++ cname ++
           "': IR has i" ++ diag_pos_dec w ++ ", spec expects i" ++ diag_pos_dec (ras_width sp)))
  | _, _, _ =>
      inl (diag "mc-call-obl"
        ("argument count mismatch calling '" ++ cname ++ "' at argument #" ++
         diag_nat_dec arg_idx))
  end.

Definition build_call_arg_obls_from
  (cname : string) (arg_idx : nat) (arch : elf_arch) (path : list (bool * cert_expr))
  (specs : list rv_arg_spec)
  (ir_args : list (bool * positive * cert_expr))
  (mc_args64 : list cert_expr) : string + list mc_loop_obl :=
  build_call_arg_obls_acc cname arg_idx arch path specs ir_args mc_args64 [].

Definition build_call_arg_obls
  (cname : string) (arch : elf_arch) (path : list (bool * cert_expr))
  (specs : list rv_arg_spec)
  (ir_args : list (bool * positive * cert_expr))
  (mc_args64 : list cert_expr) : string + list mc_loop_obl :=
  build_call_arg_obls_from cname 0%nat arch path specs ir_args mc_args64.

Lemma build_call_arg_obls_acc_shift : forall cname arg_idx arch path specs ir_args mc_args64 acc,
  build_call_arg_obls_acc cname arg_idx arch path specs ir_args mc_args64 acc =
  mcc_sum_map (fun xs => xs ++ acc) (build_call_arg_obls_from cname arg_idx arch path specs ir_args mc_args64).
Proof.
  unfold build_call_arg_obls_from.
  intros cname arg_idx arch path specs; revert arg_idx;
    induction specs as [| sp srest IH];
    intros arg_idx [| [[need_def w] e_ir] irest] [| e_mc64 mrest] acc;
    cbn [build_call_arg_obls_acc mcc_sum_map]; try reflexivity.
  destruct (Pos.eqb w (ras_width sp)); [| reflexivity].
  destruct (build_call_arg_cmp cname arg_idx arch path sp w e_ir e_mc64) as [| cmp_o]; [reflexivity |].
  destruct need_def.
  - rewrite IH, (IH (S arg_idx) _ _ [MLO_Defined false path w e_ir; cmp_o]).
    destruct (build_call_arg_obls_acc cname (S arg_idx) arch path srest irest mrest []) as [| xs];
      [reflexivity | cbn [mcc_sum_map]; rewrite <- app_assoc; reflexivity].
  - rewrite IH, (IH (S arg_idx) _ _ [cmp_o]).
    destruct (build_call_arg_obls_acc cname (S arg_idx) arch path srest irest mrest []) as [| xs];
      [reflexivity | cbn [mcc_sum_map]; rewrite <- app_assoc; reflexivity].
Qed.

Lemma build_call_arg_obls_from_cons :
  forall cname arg_idx arch path sp sr nd w e ir m mr,
    build_call_arg_obls_from cname arg_idx arch path (sp :: sr) ((nd, w, e) :: ir) (m :: mr) =
    if Pos.eqb w (ras_width sp) then
      match build_call_arg_cmp cname arg_idx arch path sp w e m with
      | inl err => inl err
      | inr cmp_o =>
          mcc_sum_map
            (fun rest => rest ++ (if nd then [MLO_Defined false path w e; cmp_o] else [cmp_o]))
            (build_call_arg_obls_from cname (S arg_idx) arch path sr ir mr)
      end
    else
      inl (diag "mc-call-obl"
        ("argument #" ++ diag_nat_dec arg_idx ++ " width mismatch calling '" ++ cname ++
         "': IR has i" ++ diag_pos_dec w ++ ", spec expects i" ++ diag_pos_dec (ras_width sp))).
Proof.
  intros cname arg_idx arch path sp sr nd w e ir m mr; unfold build_call_arg_obls_from;
    cbn [build_call_arg_obls_acc].
  destruct (Pos.eqb w (ras_width sp)); [| reflexivity].
  destruct (build_call_arg_cmp cname arg_idx arch path sp w e m) as [| cmp_o]; [reflexivity |].
  apply build_call_arg_obls_acc_shift.
Qed.

Fixpoint collect_call_obls_ret_acc
  (ret_w rw : positive) (e_ir : cert_expr)
  (p : list (bool * cert_expr)) (m : mc_call_tree) (a : list mc_loop_obl)
  {struct m} : string + list mc_loop_obl :=
  match m with
  | MCT_Ret e_mc =>
      if Pos.eqb rw ret_w then inr (MLO_Refine false p ret_w e_ir e_mc :: a)
      else
        inl (diag "mc-call-obl"
          ("IR return width i" ++ diag_pos_dec rw ++
           " does not match declared ret-width i" ++ diag_pos_dec ret_w))
  | MCT_Branch c mt mf =>
      match collect_call_obls_ret_acc ret_w rw e_ir ((true, c) :: p) mt a with
      | inl err => inl err
      | inr a1 => collect_call_obls_ret_acc ret_w rw e_ir ((false, c) :: p) mf a1
      end
  | MCT_Call cn_m _ _ _ _ _ _ =>
      match p with
      | [] =>
          inl (diag "mc-call-obl"
            ("control-flow mismatch: IR returned while MC called '" ++ cn_m ++ "' unconditionally"))
      | _ :: _ => inr (imposs_obl false p ++ a)
      end
  end.

Lemma collect_call_obls_ret_acc_shift : forall ret_w rw e_ir p m a,
  collect_call_obls_ret_acc ret_w rw e_ir p m a =
  mcc_sum_map (fun xs => xs ++ a) (collect_call_obls_ret_acc ret_w rw e_ir p m []).
Proof.
  intros ret_w rw e_ir p m; revert p;
    induction m as [e_mc | cm mt IHmt mf IHmf | cn_m am rw_m rm rv_m oh_m cm];
    intros p a; cbn [collect_call_obls_ret_acc mcc_sum_map].
  - destruct (Pos.eqb rw ret_w); reflexivity.
  - rewrite IHmt at 1;
      destruct (collect_call_obls_ret_acc ret_w rw e_ir ((true, cm) :: p) mt []) as [| o1];
      cbn [mcc_sum_map]; [reflexivity |].
    rewrite IHmf at 1; rewrite (IHmf _ o1);
      destruct (collect_call_obls_ret_acc ret_w rw e_ir ((false, cm) :: p) mf []) as [| o2];
      cbn [mcc_sum_map]; [reflexivity | rewrite <- app_assoc; reflexivity].
  - destruct p; [reflexivity | cbn [mcc_sum_map]; rewrite app_nil_r; reflexivity].
Qed.

Fixpoint collect_call_obls_acc
  (arch : elf_arch) (callees : list mc_callee_spec) (ret_w : positive)
  (path : list (bool * cert_expr)) (t_ir : ir_call_tree) (t_mc : mc_call_tree)
  (acc : list mc_loop_obl)
  {struct t_ir} : string + list mc_loop_obl :=
  match t_ir with
  | ICT_UB => inr acc
  | ICT_Branch c dt df =>
      match collect_call_obls_acc arch callees ret_w ((true, c) :: path) dt t_mc acc with
      | inl err => inl err
      | inr a1 => collect_call_obls_acc arch callees ret_w ((false, c) :: path) df t_mc a1
      end
  | ICT_Ret rw e_ir => collect_call_obls_ret_acc ret_w rw e_ir path t_mc acc
  | ICT_Call cn_ir args_ir rw_ir rv_ir c_ir =>
      (fix go_call (p : list (bool * cert_expr)) (m : mc_call_tree) (a : list mc_loop_obl) {struct m}
          : string + list mc_loop_obl :=
        match m with
        | MCT_Branch c mt mf =>
            match go_call ((true, c) :: p) mt a with
            | inl err => inl err
            | inr a1 => go_call ((false, c) :: p) mf a1
            end
        | MCT_Ret _ =>
            match p with
            | [] =>
                inl (diag "mc-call-obl"
                  ("control-flow mismatch: IR called '" ++ cn_ir ++ "' while MC returned unconditionally"))
            | _ :: _ => inr (imposs_obl false p ++ a)
            end
        | MCT_Call cn_mc args_mc rw_mc _ rv_mc _ c_mc =>
            if String.eqb cn_ir cn_mc && Pos.eqb rw_ir rw_mc && String.eqb rv_ir rv_mc then
              match find_callee_spec callees cn_ir with
              | None => inl (diag "mc-call-obl" ("missing callee spec for '" ++ cn_ir ++ "'"))
              | Some sp =>
                  if Pos.eqb rw_ir (mcs_ret_width sp) then
                    match build_call_arg_obls_acc cn_ir 0%nat arch p (mcs_args sp) args_ir args_mc a with
                    | inl err => inl err
                    | inr a1 => collect_call_obls_acc arch callees ret_w p c_ir c_mc a1
                    end
                  else
                    inl (diag "mc-call-obl"
                      ("callee '" ++ cn_ir ++ "' return width i" ++ diag_pos_dec rw_ir ++
                       " mismatches spec i" ++ diag_pos_dec (mcs_ret_width sp)))
              end
            else
              match p with
              | [] =>
                  inl (diag "mc-call-obl"
                    ("unconditional call mismatch: IR called '" ++ cn_ir ++ "' (i" ++
                     diag_pos_dec rw_ir ++ ", " ++ rv_ir ++ ") while MC called '" ++
                     cn_mc ++ "' (i" ++ diag_pos_dec rw_mc ++ ", " ++ rv_mc ++ ")"))
              | _ :: _ => inr (imposs_obl false p ++ a)
              end
        end) path t_mc acc
  end.

Lemma collect_call_obls_acc_ict_call_ret :
  forall arch callees ret_w p cn_ir args_ir rw_ir rv_ir c_ir e_mc acc,
    collect_call_obls_acc arch callees ret_w p (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) (MCT_Ret e_mc) acc =
    match p with
    | [] =>
        inl (diag "mc-call-obl"
          ("control-flow mismatch: IR called '" ++ cn_ir ++ "' while MC returned unconditionally"))
    | _ :: _ => inr (imposs_obl false p ++ acc)
    end.
Proof. reflexivity. Qed.

Lemma collect_call_obls_acc_ict_call_branch :
  forall arch callees ret_w p cn_ir args_ir rw_ir rv_ir c_ir c mt mf acc,
    collect_call_obls_acc arch callees ret_w p (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) (MCT_Branch c mt mf) acc =
    match collect_call_obls_acc arch callees ret_w ((true, c) :: p) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mt acc with
    | inl err => inl err
    | inr a1 => collect_call_obls_acc arch callees ret_w ((false, c) :: p) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mf a1
    end.
Proof. reflexivity. Qed.

Lemma collect_call_obls_acc_ict_call_call :
  forall arch callees ret_w p cn_ir args_ir rw_ir rv_ir c_ir cn_mc args_mc rw_mc rm_mc rv_mc oh_mc c_mc acc,
    collect_call_obls_acc arch callees ret_w p (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir)
      (MCT_Call cn_mc args_mc rw_mc rm_mc rv_mc oh_mc c_mc) acc =
    (if String.eqb cn_ir cn_mc && Pos.eqb rw_ir rw_mc && String.eqb rv_ir rv_mc then
       match find_callee_spec callees cn_ir with
       | None => inl (diag "mc-call-obl" ("missing callee spec for '" ++ cn_ir ++ "'"))
       | Some sp =>
           if Pos.eqb rw_ir (mcs_ret_width sp) then
             match build_call_arg_obls_acc cn_ir 0%nat arch p (mcs_args sp) args_ir args_mc acc with
             | inl err => inl err
             | inr a1 => collect_call_obls_acc arch callees ret_w p c_ir c_mc a1
             end
           else
             inl (diag "mc-call-obl"
               ("callee '" ++ cn_ir ++ "' return width i" ++ diag_pos_dec rw_ir ++
                " mismatches spec i" ++ diag_pos_dec (mcs_ret_width sp)))
       end
     else
       match p with
       | [] =>
           inl (diag "mc-call-obl"
             ("unconditional call mismatch: IR called '" ++ cn_ir ++ "' (i" ++
              diag_pos_dec rw_ir ++ ", " ++ rv_ir ++ ") while MC called '" ++
              cn_mc ++ "' (i" ++ diag_pos_dec rw_mc ++ ", " ++ rv_mc ++ ")"))
       | _ :: _ => inr (imposs_obl false p ++ acc)
       end).
Proof. reflexivity. Qed.

Definition collect_call_obls
  (arch : elf_arch) (callees : list mc_callee_spec) (ret_w : positive)
  (path : list (bool * cert_expr)) (t_ir : ir_call_tree) (t_mc : mc_call_tree)
  : string + list mc_loop_obl :=
  collect_call_obls_acc arch callees ret_w path t_ir t_mc [].

Lemma collect_call_obls_acc_shift : forall arch callees ret_w path t_ir t_mc acc,
  collect_call_obls_acc arch callees ret_w path t_ir t_mc acc =
  mcc_sum_map (fun xs => xs ++ acc) (collect_call_obls arch callees ret_w path t_ir t_mc).
Proof.
  unfold collect_call_obls.
  intros arch callees ret_w path t_ir; revert path;
    induction t_ir as [rw e_ir | | c dt IHt df IHf | cn_ir args_ir rw_ir rv_ir c_ir IHc];
    intros path t_mc acc.
  - cbn [collect_call_obls_acc]; exact (collect_call_obls_ret_acc_shift ret_w rw e_ir path t_mc acc).
  - cbn [collect_call_obls_acc mcc_sum_map]; reflexivity.
  - cbn [collect_call_obls_acc].
    rewrite IHt at 1;
      destruct (collect_call_obls_acc arch callees ret_w ((true, c) :: path) dt t_mc []) as [| o1];
      cbn [mcc_sum_map]; [reflexivity |].
    rewrite IHf at 1; rewrite (IHf ((false, c) :: path) t_mc o1);
      destruct (collect_call_obls_acc arch callees ret_w ((false, c) :: path) df t_mc []) as [| o2];
      cbn [mcc_sum_map]; [reflexivity | rewrite <- app_assoc; reflexivity].
  - induction t_mc as [e_mc | cm mt IHmt mf IHmf | cn_mc args_mc rw_mc rm_mc rv_mc oh_mc c_mc] in path, acc |- *.
    + rewrite !collect_call_obls_acc_ict_call_ret; destruct path; [reflexivity | cbn [mcc_sum_map]; rewrite app_nil_r; reflexivity].
    + rewrite !collect_call_obls_acc_ict_call_branch.
      rewrite IHmt at 1;
        destruct (collect_call_obls_acc arch callees ret_w ((true, cm) :: path) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mt []) as [| o1];
        cbn [mcc_sum_map]; [reflexivity |].
      rewrite IHmf at 1; rewrite (IHmf _ o1);
        destruct (collect_call_obls_acc arch callees ret_w ((false, cm) :: path) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mf []) as [| o2];
        cbn [mcc_sum_map]; [reflexivity | rewrite <- app_assoc; reflexivity].
    + rewrite !collect_call_obls_acc_ict_call_call.
      destruct (String.eqb cn_ir cn_mc && Pos.eqb rw_ir rw_mc && String.eqb rv_ir rv_mc);
        [| destruct path; [reflexivity | cbn [mcc_sum_map]; rewrite app_nil_r; reflexivity]].
      destruct (find_callee_spec callees cn_ir) as [sp |]; [| reflexivity].
      destruct (Pos.eqb rw_ir (mcs_ret_width sp)); [| reflexivity].
      rewrite !build_call_arg_obls_acc_shift.
      destruct (build_call_arg_obls_from cn_ir 0%nat arch path (mcs_args sp) args_ir args_mc) as [| ao];
        cbn [mcc_sum_map]; [reflexivity | rewrite app_nil_r].
      rewrite IHc, (IHc path c_mc ao);
        destruct (collect_call_obls_acc arch callees ret_w path c_ir c_mc []) as [| co];
        cbn [mcc_sum_map]; [reflexivity | rewrite <- app_assoc; reflexivity].
Qed.

Fixpoint dedup_typed_vars_acc
  (vs acc : list (string * positive)) : list (string * positive) :=
  match vs with
  | [] => acc
  | (nm, w) :: rest =>
      if existsb (fun '(x, _) => String.eqb nm x) acc then dedup_typed_vars_acc rest acc
      else dedup_typed_vars_acc rest ((nm, w) :: acc)
  end.

Definition dedup_typed_vars (vs : list (string * positive)) : list (string * positive) :=
  dedup_typed_vars_acc vs [].

Lemma dedup_typed_vars_acc_nodup : forall vs acc,
  NoDup (List.map fst acc) ->
  NoDup (List.map fst (dedup_typed_vars_acc vs acc)).
Proof.
  induction vs as [| [nm w] rest IH]; intros acc Hnd;
    cbn [dedup_typed_vars_acc]; [exact Hnd |].
  destruct (existsb (fun '(x, _) => String.eqb nm x) acc) eqn:Eex; [exact (IH _ Hnd) |].
  apply IH; cbn [List.map]; constructor; [| exact Hnd].
  intro Hin; apply in_map_iff in Hin as [[x wx] [Heq Hina]]; cbn in Heq; subst x.
  assert (Htru : existsb (fun '(x, _) => String.eqb nm x) acc = true)
    by (apply existsb_exists; exists (nm, wx); split; [exact Hina | apply String.eqb_refl]).
  congruence.
Qed.

Lemma dedup_typed_vars_nodup : forall vs,
  NoDup (List.map fst (dedup_typed_vars vs)).
Proof. intro vs; apply dedup_typed_vars_acc_nodup; constructor. Qed.

Lemma dedup_typed_vars_acc_sub : forall vs acc nm w,
  In (nm, w) (dedup_typed_vars_acc vs acc) -> In (nm, w) vs \/ In (nm, w) acc.
Proof.
  induction vs as [| [a wa] rest IH]; intros acc nm w Hin;
    cbn [dedup_typed_vars_acc] in Hin; [right; exact Hin |].
  destruct (existsb (fun '(x, _) => String.eqb a x) acc).
  - destruct (IH _ _ _ Hin) as [Hr | Ha]; [left; right; exact Hr | right; exact Ha].
  - destruct (IH _ _ _ Hin) as [Hr | Ha].
    + left; right; exact Hr.
    + destruct Ha as [Heq | Ha]; [left; left; exact Heq | right; exact Ha].
Qed.

Lemma dedup_typed_vars_sub : forall vs nm w,
  In (nm, w) (dedup_typed_vars vs) -> In (nm, w) vs.
Proof.
  intros vs nm w Hin; destruct (dedup_typed_vars_acc_sub vs [] nm w Hin) as [H | H];
    [exact H | contradiction H].
Qed.

Definition vars_width_consistent (raw all_vars : list (string * positive)) : bool :=
  forallb (fun '(nm, w) =>
    existsb (fun '(nm', w') => String.eqb nm nm' && Pos.eqb w w') all_vars) raw.

Lemma vars_width_consistent_in : forall raw all_vars nm w,
  vars_width_consistent raw all_vars = true ->
  In (nm, w) raw ->
  In (nm, w) all_vars.
Proof.
  intros raw all_vars nm w Hc Hin; unfold vars_width_consistent in Hc.
  rewrite forallb_forall in Hc; pose proof (Hc (nm, w) Hin) as Hex.
  apply existsb_exists in Hex as [[nm' w'] [Hin' Heq]].
  apply andb_true_iff in Heq as [Hn Hw]; apply String.eqb_eq in Hn; apply Pos.eqb_eq in Hw; subst nm' w'; exact Hin'.
Qed.

Record mc_call_bundle : Type := mk_mc_call_bundle {
  mccb_t_ir : ir_call_tree;
  mccb_t_mc : mc_call_tree;
  mccb_call_vars : list (string * positive);
  mccb_all_vars : list (string * positive);
  mccb_ctx : ub_ctx;
  mccb_obls : list mc_loop_obl;
}.

Definition build_mc_call_bundle_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_call_inst) (arg_specs : list rv_arg_spec)
  (ret_w : positive) (callees : list mc_callee_spec) : string + mc_call_bundle :=
  if negb (rv_supported_arg_width ret_w) then
    inl (diag "mc-call-spec" ("unsupported RV64 call return width i" ++ diag_pos_dec ret_w))
  else if negb (forallb rv_call_inst_no_word_mulh insts) then
    inl (diag "mc-call-mc" "unsupported RV64 mulhw instruction in call function")
  else if negb (Nat.leb (List.length arg_specs) 8) || negb (forallb rv_valid_arg_spec arg_specs) then
    inl (diag "mc-call-spec" "invalid RV64 argument specs for call function")
  else if negb (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) then
    inl (diag "mc-call-spec" "internal bang-prefixed parameter variable in IR/MC context")
  else if negb (forallb (fun c => rv_supported_arg_width (mcs_ret_width c) &&
                                   Nat.leb (List.length (mcs_args c)) 8 &&
                                   forallb rv_valid_arg_spec (mcs_args c) &&
                                   mc_no_dup_strings (List.map ras_name (mcs_args c))) callees) then
    inl (diag "mc-call-spec" "unsupported callee return width, arg count, arg width, or duplicate arg name")
  else
    match reify_ir_call_tree ir_cfg arg_specs callees ret_w with
    | inl err => inl err
    | inr t_ir =>
        match summarize_rv64_call_tree insts callees arg_specs ret_w with
        | inl err => inl err
        | inr t_mc =>
            match collect_call_obls EA_Riscv64 callees ret_w [] t_ir t_mc with
            | inl err => inl err
            | inr obls =>
                let raw_cvars := collect_ir_call_vars_acc t_ir (collect_mc_call_vars_acc t_mc []) in
                let call_vars := dedup_typed_vars raw_cvars in
                let all_vars := dedup_typed_vars_acc allowed0 call_vars in
                let call_ctx := List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars in
                let all_ctx := mc_init_ctx ++ call_ctx in
                if negb (vars_width_consistent allowed0 all_vars && vars_width_consistent raw_cvars all_vars) then
                  inl (diag "mc-call-obl" "inconsistent variable widths across RV64 call tree branches")
                else if negb (forallb (obl_wf_exprs all_vars) obls) then
                  inl (diag "mc-call-obl" "ill-typed or ill-scoped RV64 call obligation")
                else inr (mk_mc_call_bundle t_ir t_mc call_vars all_vars all_ctx obls)
            end
        end
    end.

Definition build_mc_call_bundle_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_call_inst) (arg_specs : list rv_arg_spec)
  (ret_w : positive) (callees : list mc_callee_spec) : string + mc_call_bundle :=
  if negb (rv_supported_arg_width ret_w) then
    inl (diag "mc-call-spec" ("unsupported AArch64 call return width i" ++ diag_pos_dec ret_w))
  else if negb (forallb a64_call_inst_valid insts) then
    inl (diag "mc-call-mc" "unsupported AArch64 instruction in call function")
  else if negb (Nat.leb (List.length arg_specs) 8) || negb (forallb a64_valid_arg_spec arg_specs) then
    inl (diag "mc-call-spec" "invalid AArch64 argument specs for call function")
  else if negb (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) then
    inl (diag "mc-call-spec" "internal bang-prefixed parameter variable in IR/MC context")
  else if negb (forallb (fun c => rv_supported_arg_width (mcs_ret_width c) &&
                                   Nat.leb (List.length (mcs_args c)) 8 &&
                                   forallb rv_valid_arg_spec (mcs_args c) &&
                                   mc_no_dup_strings (List.map ras_name (mcs_args c))) callees) then
    inl (diag "mc-call-spec" "unsupported callee return width, arg count, arg width, or duplicate arg name")
  else
    match reify_ir_call_tree ir_cfg arg_specs callees ret_w with
    | inl err => inl err
    | inr t_ir =>
        match summarize_a64_call_tree insts callees arg_specs ret_w with
        | inl err => inl err
        | inr t_mc =>
            match collect_call_obls EA_AArch64 callees ret_w [] t_ir t_mc with
            | inl err => inl err
            | inr obls =>
                let raw_cvars := collect_ir_call_vars_acc t_ir (collect_mc_call_vars_acc t_mc []) in
                let call_vars := dedup_typed_vars raw_cvars in
                let all_vars := dedup_typed_vars_acc allowed0 call_vars in
                let call_ctx := List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars in
                let all_ctx := mc_init_ctx ++ call_ctx in
                if negb (vars_width_consistent allowed0 all_vars && vars_width_consistent raw_cvars all_vars) then
                  inl (diag "mc-call-obl" "inconsistent variable widths across AArch64 call tree branches")
                else if negb (forallb (obl_wf_exprs all_vars) obls) then
                  inl (diag "mc-call-obl" "ill-typed or ill-scoped AArch64 call obligation")
                else inr (mk_mc_call_bundle t_ir t_mc call_vars all_vars all_ctx obls)
            end
        end
    end.

Definition validate_mc_call_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_call_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (callees : list mc_callee_spec) (opt_pf : option (list lrat_step)) : string + unit :=
  match build_mc_call_bundle_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees with
  | inl err => inl err
  | inr b => check_mc_loop_obls "mc-call" (mccb_ctx b) (mccb_all_vars b) None (mccb_obls b) opt_pf
  end.

Definition validate_mc_call_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_call_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (callees : list mc_callee_spec) (opt_pf : option (list lrat_step)) : string + unit :=
  match build_mc_call_bundle_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees with
  | inl err => inl err
  | inr b => check_mc_loop_obls "mc-call" (mccb_ctx b) (mccb_all_vars b) None (mccb_obls b) opt_pf
  end.

Definition emit_mc_call_cnf_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_call_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (callees : list mc_callee_spec) : string + option (positive * cnf) :=
  match build_mc_call_bundle_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees with
  | inl err => inl err
  | inr b => emit_mc_loop_cnf "mc-call" (mccb_ctx b) (mccb_all_vars b) None (mccb_obls b)
  end.

Definition emit_mc_call_cnf_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_call_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (callees : list mc_callee_spec) : string + option (positive * cnf) :=
  match build_mc_call_bundle_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees with
  | inl err => inl err
  | inr b => emit_mc_loop_cnf "mc-call" (mccb_ctx b) (mccb_all_vars b) None (mccb_obls b)
  end.

(** ** 5. End-to-End Soundness & Caller/Callee Composition Proofs *)

Section CallSoundness.

  Definition rv_call_sound_spec {Pa : Params}
    (ir_cfg : CFG.cfg dtyp) (insts : list decoded_rv_call_inst) (ret_w : positive)
    (callees : list mc_callee_spec) (vs : list (@dvalue Pa))
    (rf0 : rv_regfile) (mstk0 : mc_stack_mem) : Prop :=
    forall genv (O : rv_call_oracle),
      wf_callee_genv callees genv ->
      wf_rv_call_oracle callees O ->
      let rv_fuel := S (2 * List.length insts) in
      exists tr_mc rf_end mstk_end,
        rv_exec_with_calls rv_fuel insts O 0%N (rv_read_reg 2%N rf0) rf0 mstk0 =
          Some (tr_mc, rf_end, mstk_end) /\
        rv_callee_saved_preserved rf0 rf_end /\
        rf_end 1%N = rf0 1%N /\
        ((exists sigma_ir tr_ir_pre,
            wf_draw_strat sigma_ir /\
            prefix_matches (rv_call_event_matches callees) tr_ir_pre tr_mc /\
            cfg_call_steps_to_ub genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
              (denote_cfg ir_cfg None) tr_ir_pre) \/
         (exists sigma_ir tr_ir sigma_ir' env_out dv_ir,
            wf_draw_strat sigma_ir /\
            Forall2 (rv_call_event_matches callees) tr_mc tr_ir /\
            cfg_call_steps_to_ret genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
              (denote_cfg ir_cfg None) tr_ir sigma_ir' env_out dv_ir /\
            dvalue_refines dv_ir
              (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))))).

  Definition a64_call_sound_spec {Pa : Params}
    (ir_cfg : CFG.cfg dtyp) (insts : list decoded_a64_call_inst) (ret_w : positive)
    (callees : list mc_callee_spec) (vs : list (@dvalue Pa))
    (rf0 : a64_regfile) (sp0 : @Integers.bit_int 64%positive)
    (fl0 : a64_flags) (mstk0 : mc_stack_mem) : Prop :=
    forall genv (O : a64_call_oracle),
      wf_callee_genv callees genv ->
      wf_a64_call_oracle callees O ->
      let a64_fuel := S (2 * List.length insts) in
      exists tr_mc rf_end fl_end mstk_end,
        a64_exec_with_calls a64_fuel insts O 0%N sp0 rf0 sp0 fl0 mstk0 =
          Some (tr_mc, rf_end, sp0, fl_end, mstk_end) /\
        a64_callee_saved_preserved rf0 rf_end /\
        ((exists sigma_ir tr_ir_pre,
            wf_draw_strat sigma_ir /\
            prefix_matches (a64_call_event_matches callees) tr_ir_pre tr_mc /\
            cfg_call_steps_to_ub genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
              (denote_cfg ir_cfg None) tr_ir_pre) \/
         (exists sigma_ir tr_ir sigma_ir' env_out dv_ir,
            wf_draw_strat sigma_ir /\
            Forall2 (a64_call_event_matches callees) tr_mc tr_ir /\
            cfg_call_steps_to_ret genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
              (denote_cfg ir_cfg None) tr_ir sigma_ir' env_out dv_ir /\
            dvalue_refines dv_ir
              (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))).

End CallSoundness.

(** Shared fresh-variable disjointness & path-execution helpers *)

Lemma collect_ir_call_vars_sub_app : forall dt df nm w,
  In (nm, w) (collect_ir_call_vars dt) \/ In (nm, w) (collect_ir_call_vars df) ->
  In (nm, w) (collect_ir_call_vars dt ++ collect_ir_call_vars df).
Proof. intros dt df nm w [H | H]; apply in_app_iff; [left | right]; exact H. Qed.

Lemma mcc_eval_cert_expr_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e,
    is_let_free_expr e = true ->
    (forall nm w, In (nm, w) (collect_free_vars [] e) -> penv1 nm = penv2 nm) ->
    eval_cert_expr penv1 [] foracle e = eval_cert_expr penv2 [] foracle e.
Proof.
  intros penv1 penv2 foracle e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf Hag; cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in *.
  - reflexivity.
  - reflexivity.
  - rewrite (Hag nm w ltac:(left; reflexivity)); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl Hlfl (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHr Hlfr (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror Hx)))); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl Hlfl (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHr Hlfr (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror Hx)))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as [[Hlfc Hlft] Hlff].
    rewrite (IHc Hlfc (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHt Hlft (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hx)))))),
            (IHf Hlff (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hx)))))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - discriminate Hlf.
Qed.

Lemma rv_val_regs_agrees_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle allowed rf0 sp0 vrf rf,
    rv_val_regs_wf allowed vrf ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    rv_val_regs_agrees penv1 foracle rf0 sp0 vrf rf ->
    rv_val_regs_agrees penv2 foracle rf0 sp0 vrf rf.
Proof.
  intros penv1 penv2 foracle allowed rf0 sp0 vrf rf Hwf Hag Hrg r.
  pose proof (Hrg r) as Hr; pose proof (Hwf r) as Hwr.
  destruct (rv_val_read r vrf) as [| e | |]; try exact Hr.
  destruct Hwr as (_ & _ & Hlf & Hsub).
  cbn [mc_sym_val_agrees] in *; unfold eval_closed_cert_expr in *.
  erewrite mcc_eval_cert_expr_penv_agree; [exact Hr | exact Hlf |].
  intros nm w Hn; symmetry; exact (Hag nm w (vars_subset_b_incl _ _ Hsub _ Hn)).
Qed.

Lemma mc_sym_stack_agrees_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle allowed rf0 sp0 sp_off astk mstk,
    mc_sym_stack_wf allowed sp_off astk ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    mc_sym_stack_agrees penv1 foracle rf0 sp0 astk mstk ->
    mc_sym_stack_agrees penv2 foracle rf0 sp0 astk mstk.
Proof.
  intros penv1 penv2 foracle allowed rf0 sp0 sp_off astk mstk Hwf Hag Hst.
  unfold mc_sym_stack_wf, mc_sym_stack_agrees in *.
  rewrite Forall_forall in *.
  intros [[o sz] v] Hin; pose proof (Hwf (o, sz, v) Hin) as [_ Hwv];
    pose proof (Hst (o, sz, v) Hin) as Hst_v; cbn in Hwv, Hst_v |- *.
  destruct v as [| e | |]; try exact Hst_v.
  destruct Hwv as (_ & _ & Hlf & Hsub); cbn [mc_sym_val_agrees] in *; unfold eval_closed_cert_expr in *.
  erewrite mcc_eval_cert_expr_penv_agree; [exact Hst_v | exact Hlf |].
  intros nm w Hn; symmetry; exact (Hag nm w (vars_subset_b_incl _ _ Hsub _ Hn)).
Qed.

Lemma a64_val_regs_agrees_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle allowed rf0 sp0 vrf rf,
    wf_a64_val_regs allowed vrf ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    a64_val_regs_agrees penv1 foracle rf0 sp0 vrf rf ->
    a64_val_regs_agrees penv2 foracle rf0 sp0 vrf rf.
Proof.
  intros penv1 penv2 foracle allowed rf0 sp0 vrf rf Hwf Hag Hrg r.
  pose proof (Hrg r) as Hr; pose proof (Hwf r) as Hwr.
  destruct (a64_val_read r vrf) as [| e | |]; try exact Hr.
  destruct Hwr as (_ & _ & Hlf & Hsub).
  cbn [mc_sym_val_agrees] in *; unfold eval_closed_cert_expr in *.
  erewrite mcc_eval_cert_expr_penv_agree; [exact Hr | exact Hlf |].
  intros nm w Hn; symmetry; exact (Hag nm w (vars_subset_b_incl _ _ Hsub _ Hn)).
Qed.

Lemma sym_flags_agree_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle allowed sfl fl,
    wf_sym_flags allowed sfl ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    sym_flags_agree penv1 foracle sfl fl ->
    sym_flags_agree penv2 foracle sfl fl.
Proof.
  intros penv1 penv2 foracle allowed [n z c v isz] [fn fz fc fv]
         ((_ & _ & Hln & Hsn) & (_ & _ & Hlz & Hsz) & (_ & _ & Hlc & Hsc) & (_ & _ & Hlv & Hsv) & (_ & _ & Hli & Hsi))
         Hag (Hn & Hz & Hc & Hv & Hi).
  unfold sym_flags_agree, eval_closed_cert_expr in *; cbn in *.
  repeat split.
  - erewrite mcc_eval_cert_expr_penv_agree; [exact Hn | exact Hln | intros x wx Hx; symmetry; exact (Hag x wx (vars_subset_b_incl _ _ Hsn _ Hx))].
  - erewrite mcc_eval_cert_expr_penv_agree; [exact Hz | exact Hlz | intros x wx Hx; symmetry; exact (Hag x wx (vars_subset_b_incl _ _ Hsz _ Hx))].
  - erewrite mcc_eval_cert_expr_penv_agree; [exact Hc | exact Hlc | intros x wx Hx; symmetry; exact (Hag x wx (vars_subset_b_incl _ _ Hsc _ Hx))].
  - erewrite mcc_eval_cert_expr_penv_agree; [exact Hv | exact Hlv | intros x wx Hx; symmetry; exact (Hag x wx (vars_subset_b_incl _ _ Hsv _ Hx))].
  - erewrite mcc_eval_cert_expr_penv_agree; [exact Hi | exact Hli | intros x wx Hx; symmetry; exact (Hag x wx (vars_subset_b_incl _ _ Hsi _ Hx))].
Qed.

(** Concrete-path execution witness along an [mc_call_tree] *)

Inductive mc_tree_path_ok {Pa : Params} (penv : param_env Pa) (ret_w : positive)
  : list (bool * cert_expr) -> mc_call_tree ->
    list (string * list (@Integers.bit_int 64%positive) * @Integers.bit_int 64%positive) ->
    @Integers.bit_int ret_w -> Prop :=
| MTPO_Ret path ret_e (v_ret : @Integers.bit_int ret_w) :
    eval_closed_cert_expr penv dummy_freeze_oracle ret_e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w v_ret)) ->
    mc_tree_path_ok penv ret_w path (MCT_Ret ret_e) [] v_ret
| MTPO_Branch path cond dt df (b : bool) tr_vals v_ret :
    eval_closed_cert_expr penv dummy_freeze_oracle cond =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
        (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    mc_tree_path_ok penv ret_w ((b, cond) :: path) (if b then dt else df) tr_vals v_ret ->
    mc_tree_path_ok penv ret_w path (MCT_Branch cond dt df) tr_vals v_ret
| MTPO_Call path cname aes rw rext rv opt_hi cont
            (arg_vals : list (@Integers.bit_int 64%positive))
            (a0_ret : @Integers.bit_int 64%positive)
            (v_call : @Integers.bit_int rw)
            tr_vals v_ret :
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv dummy_freeze_oracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))) aes arg_vals ->
    penv rv = Some (DVALUE_Base (@DVALUE_I Pa rw v_call)) ->
    v_call = rv_trunc_ret_val rw a0_ret ->
    mc_tree_path_ok penv ret_w path cont tr_vals v_ret ->
    mc_tree_path_ok penv ret_w path (MCT_Call cname aes rw rext rv opt_hi cont)
      ((cname, arg_vals, a0_ret) :: tr_vals) v_ret.

