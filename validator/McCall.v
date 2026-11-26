(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Direct Call Summaries & Caller/Callee Composition ([CertValidator.McCall])

    Implements Milestone M3c of Phase 8.3a for direct non-recursive acyclic calls
    on [RV64IM+RVC] and [AArch64]:
    1. Call-site decoders ([decode_rv64_bytes_with_calls], [decode_a64_bytes_with_calls])
       binding [ET_REL] call relocations ([R_RISCV_CALL_PLT] / [R_RISCV_CALL] /
       [R_RISCV_JAL] / [R_AARCH64_CALL26]) and [ET_EXEC]/[ET_DYN] resolved PC-relative
       target addresses to unique callee symbols.
    2. Callee prototype/ABI contract checks ([check_mc_callee_contracts]) and
       call-trace operational semantics ([rv_exec_with_calls], [a64_exec_with_calls],
       [cfg_call_steps_to_ret], [cfg_call_steps_to_ub]).
    3. Acyclic symbolic call-tree summarizers ([reify_ir_call_tree],
       [summarize_rv64_call_tree], [summarize_a64_call_tree]) using fresh
       width-tagged call result variables ([!call_<k>_<w>], [!call_hi_<k>]).
    4. Path-flattened call & return obligation generation reusing
       [McLoop.check_mc_loop_obls] and [McLoop.emit_mc_loop_cnf].
    5. End-to-end call-validator soundness ([validate_mc_call_rv64_sound],
       [validate_mc_call_a64_sound]) and caller/callee composition theorems
       ([compose_rv64_caller_callee_sound], [compose_a64_caller_callee_sound]). *)

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
  Rv64Sem
  A64CoreSem
  McFormat
  Diag
  McLoop.

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

(** *** 5.1 Call Variable Disjointness & Incremental Context Invariance *)

Lemma string_append_eq_prefix : forall p s1 s2,
  (p ++ s1 = p ++ s2 -> s1 = s2)%string.
Proof.
  induction p as [| c rp IH]; intros s1 s2 H; cbn in H; [exact H |].
  inversion H; apply IH; assumption.
Qed.

Lemma mc_call_hi_var_inj : forall k1 k2,
  mc_call_hi_var k1 = mc_call_hi_var k2 -> k1 = k2.
Proof.
  intros k1 k2 Heq; unfold mc_call_hi_var in Heq.
  apply string_append_eq_prefix in Heq.
  apply show_Z_dec_pos_inj in Heq; lia.
Qed.

Lemma decimal_uint_no_underscore : forall d,
  ~ In "_"%char (list_ascii_of_string (DecimalString.NilEmpty.string_of_uint d)).
Proof.
  induction d; cbn [DecimalString.NilEmpty.string_of_uint list_ascii_of_string In];
    intro H; try exact H; (destruct H as [Hc | Hr]; [discriminate Hc | exact (IHd Hr)]).
Qed.

Lemma show_Z_dec_pos_no_underscore : forall n : Z,
  (0 <= n)%Z ->
  ~ In "_"%char (list_ascii_of_string (show_Z_dec n)).
Proof.
  intros n Hn Hin; unfold show_Z_dec in Hin.
  destruct n as [| p | p]; [| | lia]; cbn in Hin.
  - destruct Hin as [H | H]; [discriminate H | contradiction H].
  - exact (decimal_uint_no_underscore (Pos.to_uint p) Hin).
Qed.

Fixpoint take_before_underscore (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => if Ascii.eqb c "_"%char then EmptyString else String c (take_before_underscore rest)
  end.

Lemma take_before_underscore_app : forall a b,
  ~ In "_"%char (list_ascii_of_string a) ->
  take_before_underscore (a ++ "_" ++ b)%string = a.
Proof.
  induction a as [| c ra IH]; intros b Hnin.
  - cbn; reflexivity.
  - change ((String c ra ++ "_" ++ b)%string) with (String c (ra ++ "_" ++ b)%string).
    cbn [take_before_underscore]; destruct (Ascii.eqb c "_"%char) eqn:Ec.
    + apply Ascii.eqb_eq in Ec; subst c; exfalso; apply Hnin; left; reflexivity.
    + f_equal; apply IH; intro H; apply Hnin; right; exact H.
Qed.

Lemma mc_call_ret_var_k_inj : forall k1 k2 w1 w2,
  mc_call_ret_var k1 w1 = mc_call_ret_var k2 w2 -> k1 = k2.
Proof.
  intros k1 k2 w1 w2 Heq; unfold mc_call_ret_var in Heq.
  apply string_append_eq_prefix in Heq.
  apply (f_equal take_before_underscore) in Heq.
  rewrite !take_before_underscore_app in Heq
    by (apply show_Z_dec_pos_no_underscore; lia).
  apply show_Z_dec_pos_inj in Heq; lia.
Qed.

Lemma mc_call_ret_hi_disjoint : forall k1 w1 k2,
  mc_call_ret_var k1 w1 <> mc_call_hi_var k2.
Proof.
  intros k1 w1 k2 Heq; unfold mc_call_ret_var, mc_call_hi_var in Heq.
  change ("!call_hi_" ++ show_Z_dec (Z.of_nat k2))%string
    with ("!call_" ++ ("hi_" ++ show_Z_dec (Z.of_nat k2)))%string in Heq.
  apply string_append_eq_prefix in Heq.
  unfold show_Z_dec in Heq; destruct (Z.of_nat k1) as [| p1 |] eqn:Ez; try lia.
  - cbn in Heq; discriminate Heq.
  - cbn in Heq; destruct (Pos.to_uint p1); cbn in Heq; discriminate Heq.
Qed.

(** An environment invariant indexed by [cid]: all [!call_*] and [!call_hi_*]
    variables appearing inside expressions valid at step [cid] are not overwritten
    by binding calls at [cid' >= cid]. *)

Definition allowed_ge_cid_fresh (cid : nat) (allowed : list (string * positive)) : Prop :=
  (forall k w, In (mc_call_ret_var k w, w) allowed -> (k < cid)%nat) /\
  (forall k w, In (mc_call_ret_var k w, w) allowed -> False -> False) /\
  (forall nm w, In (nm, w) allowed ->
     forall k' w', (cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').

Lemma allowed0_fresh_all : forall (allowed0 : list (string * positive)),
  (forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false) ->
  forall cid nm w, In (nm, w) allowed0 ->
    forall k' w', (cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k'.
Proof.
  intros allowed0 Hnb cid nm w Hin k' w' _.
  pose proof (Hnb nm w Hin) as Hf; split; intro Heq; subst nm; discriminate Hf.
Qed.

(** *** 5.2 Concrete Path Execution Witnesses for RV64 & AArch64 *)

Lemma rv_sym_read_call_args_from_sound {Pa : Params} :
  forall pc cname (penv : param_env Pa) foracle rf0 sp0 vrf rf idx n aes,
    rv_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    rv_sym_read_call_args_from pc cname idx n vrf = inr aes ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv foracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)))
      aes
      (List.map (fun k => rv_read_reg (idx + N.of_nat k) rf) (seq 0 n)).
Proof.
  intros pc cname penv foracle rf0 sp0 vrf rf idx n; revert idx;
    induction n as [| n' IH]; intros idx aes Hag Hrd;
    cbn [rv_sym_read_call_args_from seq List.map] in *;
    [inversion Hrd; constructor |].
  destruct (rv_val_read idx vrf) as [| e64 | |] eqn:Er; try discriminate Hrd.
  destruct (rv_sym_read_call_args_from pc cname (N.succ idx) n' vrf) as [| rest] eqn:Hr; [discriminate Hrd |].
  inversion Hrd; subst aes; clear Hrd.
  constructor.
  - pose proof (Hag idx) as Hi; rewrite Er in Hi; cbn [mc_sym_val_agrees] in Hi.
    rewrite N.add_0_r; exact Hi.
  - rewrite <- seq_shift, !map_map.
    replace (List.map (fun x => rv_read_reg (idx + N.of_nat (S x)) rf) (seq 0 n'))
      with (List.map (fun k => rv_read_reg (N.succ idx + N.of_nat k) rf) (seq 0 n'))
      by (apply map_ext; intro k; f_equal; lia).
    exact (IH (N.succ idx) rest Hag Hr).
Qed.

Lemma a64_sym_read_call_args_from_sound {Pa : Params} :
  forall pc cname (penv : param_env Pa) foracle rf0 sp0 vrf rf idx n aes,
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    a64_sym_read_call_args_from pc cname idx n vrf = inr aes ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv foracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)))
      aes
      (List.map (fun k => a64_read_reg (idx + N.of_nat k) rf) (seq 0 n)).
Proof.
  intros pc cname penv foracle rf0 sp0 vrf rf idx n; revert idx;
    induction n as [| n' IH]; intros idx aes Hag Hrd;
    cbn [a64_sym_read_call_args_from seq List.map] in *;
    [inversion Hrd; constructor |].
  destruct (a64_val_read idx vrf) as [| e64 | |] eqn:Er; try discriminate Hrd.
  destruct (a64_sym_read_call_args_from pc cname (N.succ idx) n' vrf) as [| rest] eqn:Hr; [discriminate Hrd |].
  inversion Hrd; subst aes; clear Hrd.
  constructor.
  - pose proof (Hag idx) as Hi; rewrite Er in Hi; cbn [mc_sym_val_agrees] in Hi.
    rewrite N.add_0_r; exact Hi.
  - rewrite <- seq_shift, !map_map.
    replace (List.map (fun x => a64_read_reg (idx + N.of_nat (S x)) rf) (seq 0 n'))
      with (List.map (fun k => a64_read_reg (N.succ idx + N.of_nat k) rf) (seq 0 n'))
      by (apply map_ext; intro k; f_equal; lia).
    exact (IH (N.succ idx) rest Hag Hr).
Qed.

Lemma eval_let_binds_ext {Pa : Params}
  (f1 f2 : let_val_env Pa -> cert_expr -> EOU (@dvalue Pa))
  (xs : list (string * cert_expr)) :
  Forall (fun p => forall lenv, f1 lenv (snd p) = f2 lenv (snd p)) xs ->
  forall lenv,
    eval_let_binds f1 lenv xs = eval_let_binds f2 lenv xs.
Proof.
  intros Hfa; induction Hfa as [| [nm be] rest Hhead _ IH]; intros lenv; cbn in *; [reflexivity |].
  rewrite Hhead; destruct (f2 lenv be); cbn; try reflexivity; apply IH.
Qed.

Lemma eval_cert_expr_extensional {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e lenv,
    (forall nm, penv1 nm = penv2 nm) ->
    eval_cert_expr penv1 lenv foracle e = eval_cert_expr penv2 lenv foracle e.
Proof.
  intros penv1 penv2 foracle e lenv Heq; revert lenv.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intro lenv; cbn [eval_cert_expr]; try reflexivity.
  - destruct (lookup_let_val lenv nm); [reflexivity | rewrite Heq; reflexivity].
  - rewrite IHl, IHr; reflexivity.
  - rewrite IHl, IHr; reflexivity.
  - rewrite IHo; reflexivity.
  - rewrite IHc, IHt, IHf; reflexivity.
  - rewrite IHo; reflexivity.
  - rewrite (@eval_let_binds_ext Pa
               (fun ce x => eval_cert_expr penv1 ce foracle x)
               (fun ce x => eval_cert_expr penv2 ce foracle x) bs IHbs lenv).
    destruct (eval_let_binds (fun ce x => eval_cert_expr penv2 ce foracle x) lenv bs);
      cbn; [| | | apply IHb]; reflexivity.
Qed.

Lemma mc_tree_path_ok_extensional {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) ret_w path t tr v,
    (forall nm, penv1 nm = penv2 nm) ->
    mc_tree_path_ok penv1 ret_w path t tr v ->
    mc_tree_path_ok penv2 ret_w path t tr v.
Proof.
  intros penv1 penv2 ret_w path t tr v Heq H.
  assert (Hce : forall e, eval_closed_cert_expr penv1 dummy_freeze_oracle e =
                          eval_closed_cert_expr penv2 dummy_freeze_oracle e)
    by (intro e; apply eval_cert_expr_extensional; exact Heq).
  induction H.
  - apply MTPO_Ret; rewrite <- Hce; exact H.
  - eapply MTPO_Branch; [rewrite <- Hce; exact H | exact IHmc_tree_path_ok].
  - eapply MTPO_Call; [| rewrite <- Heq; exact H0 | exact H1 | exact IHmc_tree_path_ok].
    clear -H Hce; induction H; [constructor | constructor; [rewrite <- Hce; exact H | exact IHForall2]].
Qed.

Lemma mc_tree_path_ok_app_r {Pa : Params} :
  forall (penv : param_env Pa) ret_w p1 p2 t tr_vals v_ret,
    mc_tree_path_ok penv ret_w p1 t tr_vals v_ret ->
    mc_tree_path_ok penv ret_w (p1 ++ p2) t tr_vals v_ret.
Proof.
  intros penv ret_w p1 p2 t tr_vals v_ret H; induction H.
  - apply MTPO_Ret; exact H.
  - eapply MTPO_Branch; [exact H | exact IHmc_tree_path_ok].
  - eapply MTPO_Call; eassumption.
Qed.

Definition binds_disjoint_from {Pa : Params}
  (allowed : list (string * positive)) (binds : list (string * @dvalue Pa)) : Prop :=
  forall nm w, In (nm, w) allowed -> ~ In nm (List.map fst binds).

Lemma binds_disjoint_app {Pa : Params} :
  forall allowed (b1 b2 : list (string * @dvalue Pa)),
    binds_disjoint_from allowed b1 ->
    binds_disjoint_from allowed b2 ->
    binds_disjoint_from allowed (b1 ++ b2).
Proof.
  intros allowed b1 b2 H1 H2 nm w Hin Hina; rewrite List.map_app in Hina;
    apply in_app_iff in Hina as [H | H]; [exact (H1 nm w Hin H) | exact (H2 nm w Hin H)].
Qed.

Lemma overlay_penv_app {Pa : Params} :
  forall (b1 b2 : list (string * @dvalue Pa)) (base : param_env Pa) nm,
    overlay_penv (b1 ++ b2) base nm = overlay_penv b1 (overlay_penv b2 base) nm.
Proof.
  induction b1 as [| [x dv] rest IH]; intros b2 base nm; cbn; [reflexivity |].
  destruct (String.eqb nm x); [reflexivity | exact (IH b2 base nm)].
Qed.

Lemma overlay_penv_disjoint_allowed {Pa : Params} :
  forall (binds : list (string * @dvalue Pa)) (base : param_env Pa) allowed,
    binds_disjoint_from allowed binds ->
    forall nm w, In (nm, w) allowed -> overlay_penv binds base nm = base nm.
Proof.
  intros binds base allowed Hdisj nm w Hin; apply overlay_penv_not_in; exact (Hdisj nm w Hin).
Qed.

Lemma summarize_rv64_call_at_exec {Pa : Params} :
  forall insts im
    (Him : forall pc, pt_get (N.succ_pos pc) im = lookup_rv_call_inst insts pc)
    fuel callees visited pc cid sp_off vrf astk ret_w allowed t_mc
    (O : rv_call_oracle) (penv0 : param_env Pa) rf0 rf mstk,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true) ->
    forallb rv_call_inst_no_word_mulh insts = true ->
    wf_rv_call_oracle callees O ->
    mc_valid_sp0_depth 2%nat (rv_read_reg 2%N rf0) ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_wf allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (forall nm w, In (nm, w) allowed ->
       forall k' w', (cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k') ->
    rv_val_regs_agrees penv0 dummy_freeze_oracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    mc_sym_stack_agrees penv0 dummy_freeze_oracle (fun r => rv_read_reg r rf0) (rv_read_reg 2%N rf0) astk mstk ->
    summarize_rv64_call_at fuel im callees visited pc cid sp_off vrf astk ret_w = inr t_mc ->
    exists tr_mc new_binds rf_end mstk_end,
      NoDup (List.map fst new_binds) /\
      binds_disjoint_from allowed new_binds /\
      (forall nm, In nm (List.map fst new_binds) ->
         exists k, (cid <= k)%nat /\
           ((exists w, nm = mc_call_ret_var k w) \/ nm = mc_call_hi_var k)) /\
      (forall nm dv, In (nm, dv) new_binds ->
         exists w, In (nm, w) (collect_mc_call_vars t_mc) /\
           exists v : @Integers.bit_int w, dv = DVALUE_Base (@DVALUE_I Pa w v)) /\
      rv_exec_with_calls fuel insts O pc (rv_read_reg 2%N rf0) rf mstk = Some (tr_mc, rf_end, mstk_end) /\
      rv_callee_saved_preserved rf0 rf_end /\
      rf_end 1%N = rf0 1%N /\
      forall extra_binds : list (string * @dvalue Pa),
        binds_disjoint_from allowed extra_binds ->
        (forall nm, In nm (List.map fst new_binds) -> ~ In nm (List.map fst extra_binds)) ->
        mc_tree_path_ok (overlay_penv (new_binds ++ extra_binds) penv0) ret_w [] t_mc
          (List.map (fun '(cn, rf_c, a0_r) =>
             let n := match find_callee_spec callees cn with
                      | Some sp => List.length (mcs_args sp)
                      | None => 0%nat end in
             (cn, List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_c) (seq 0 n), a0_r)) tr_mc)
          (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)).
Proof.
  intros insts im Him fuel; induction fuel as [| fuel' IH];
    intros callees visited pc cid sp_off vrf astk ret_w allowed t_mc
           O penv0 rf0 rf mstk Hrw Hcws Hmul HO Hsp0 Hrng Hsp2 Hvrf Hastk Hfresh Hag_rf Hag_stk Hsum;
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
    assert (Hsp0_1 : mc_valid_sp0 (rv_read_reg 2%N rf0))
      by (destruct Hsp0 as [H0 H1]; split; [unfold mc_frame_cap in *; lia | exact H1]).
    destruct (rv_sym_step_one (mk_decoded_rv (drci_off dec) (drci_len dec) i) pc sp_off vrf astk ret_w)
      as [res |] eqn:Est; [| discriminate Hsum].
    pose proof (rv_sym_step_one_wf allowed (mk_decoded_rv (drci_off dec) (drci_len dec) i)
                  pc sp_off vrf astk ret_w res Hrw Hdec_nmul Hrng Hsp2 Hvrf Hastk Est) as Hwf_step.
    pose proof (rv_sym_step_one_sound (mk_decoded_rv (drci_off dec) (drci_len dec) i)
                  pc sp_off vrf astk ret_w res penv0 dummy_freeze_oracle rf0 rf mstk
                  Hrw Hdec_nmul Hsp0_1 Hrng Hsp2 Hag_rf Hag_stk Est) as Hsd_step.
    destruct res as [npc sp' vrf' astk' | cond tpc npc | ret_e].
    + destruct Hwf_step as (Hrng' & Hsp2' & Hvrf' & Hastk').
      destruct Hsd_step as (rf' & mstk' & Hexec1 & _ & _ & Hag_rf' & Hag_stk').
      destruct (IH callees (pt_add_n pc visited) npc cid sp' vrf' astk' ret_w allowed t_mc
                   O penv0 rf0 rf' mstk' Hrw Hcws Hmul HO Hsp0 Hrng' Hsp2' Hvrf' Hastk' Hfresh
                   Hag_rf' Hag_stk' Hsum)
        as (tr_mc & nb & rf_end & mstk_end & Hnd & Hdisj & Hkge & Hcv & Hexec & Hpres & Hra & Hpath).
      exists tr_mc, nb, rf_end, mstk_end; repeat split; try assumption.
      cbn [rv_exec_with_calls]; rewrite Hlk, Edi.
      destruct i; cbn [rv_exec_one_nonret] in Hexec1; try discriminate Hexec1;
        rewrite ?Hexec1; exact Hexec.
    + destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk ret_w)
        as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk ret_w)
        as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t_mc; clear Hsum.
      destruct Hwf_step as (Hwt_c & Hbw_c & Hlf_c & Hsub_c).
      destruct Hsd_step as [b [Hevc Hexec1]].
      assert (Hnext_p : summarize_rv64_call_at fuel' im callees (pt_add_n pc visited)
                          (if b then tpc else npc) cid sp_off vrf astk ret_w = inr (if b then dt else df))
        by (destruct b; [exact Hdt | exact Hdf]).
      destruct (IH callees (pt_add_n pc visited) (if b then tpc else npc) cid sp_off vrf astk ret_w
                   allowed (if b then dt else df) O penv0 rf0 rf mstk
                   Hrw Hcws Hmul HO Hsp0 Hrng Hsp2 Hvrf Hastk Hfresh Hag_rf Hag_stk Hnext_p)
        as (tr_mc & nb & rf_end & mstk_end & Hnd & Hdisj & Hkge & Hcv & Hexec & Hpres & Hra & Hpath).
      exists tr_mc, nb, rf_end, mstk_end; repeat split; try assumption.
      * intros nm dv Hinn; destruct (Hcv nm dv Hinn) as (w & Hcm & Hv).
        exists w; split; [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_app_iff; destruct b; [right | left]; exact Hcm | exact Hv].
      * cbn [rv_exec_with_calls]; rewrite Hlk, Edi.
        destruct i; cbn [rv_exec_one_nonret] in Hexec1; try discriminate Hexec1;
          rewrite Hexec1; exact Hexec.
      * intros extra Hdx Hnx; specialize (Hpath extra Hdx Hnx).
        eapply MTPO_Branch.
        -- unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hevc | exact Hlf_c |].
           intros nm w Hnm; pose proof (vars_subset_b_incl _ _ Hsub_c _ Hnm) as Hal.
           apply (overlay_penv_disjoint_allowed (nb ++ extra) penv0 allowed (binds_disjoint_app _ _ _ Hdisj Hdx) nm w Hal).
        -- exact (mc_tree_path_ok_app_r _ _ [] [(b, cond)] _ _ _ Hpath).
    + inversion Hsum; subst t_mc; clear Hsum.
      destruct Hsd_step as (Edri & Hpres & Hra & Hevr).
      destruct Hwf_step as (_ & _ & Hlf_r & Hsub_r).
      exists [], [], rf, mstk.
      split; [constructor | split; [| split; [| split; [| split; [| split; [exact Hpres | split; [exact Hra |]]]]]]].
      * intros nm w _ H; contradiction H.
      * intros nm H; contradiction H.
      * intros nm dv H; contradiction H.
      * cbn [dri_inst] in Edri; cbn [rv_exec_with_calls]; rewrite Hlk, Edi, Edri; reflexivity.
      * intros extra Hdx _; apply MTPO_Ret.
        unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hevr | exact Hlf_r |].
        intros nm w Hnm; pose proof (vars_subset_b_incl _ _ Hsub_r _ Hnm) as Hal.
        cbn [app]; exact (overlay_penv_disjoint_allowed extra penv0 allowed Hdx nm w Hal).
  - destruct (mc_sp_aligned16 sp_off) eqn:Esp_al; cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |] eqn:Efc; [| discriminate Hsum].
    destruct (rv_sym_read_call_args_from pc cname 10%N (List.length (mcs_args c)) vrf) as [| aes] eqn:Eargs;
      [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited)
                (pc + drci_len dec)%N (S cid) sp_off (rv_post_call_vrf cid c vrf) astk ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t_mc; clear Hsum.
    pose proof (find_callee_spec_in _ _ _ Efc) as [Hc_in Hc_nm].
    pose proof (Hcws c Hc_in) as Hcrw.
    pose proof (Hag_rf 2%N) as Hag2; rewrite Hsp2 in Hag2; cbn [mc_sym_val_agrees] in Hag2.
    destruct Hag2 as [_ Hrf2_eq].
    assert (Hsp_eq_off : mc_addr_to_off (rv_read_reg 2%N rf0) (rv_read_reg 2%N rf) = sp_off).
    { rewrite Hrf2_eq; refine (mc_addr_to_off_add (rv_read_reg 2%N rf0) sp_off _ Hrng).
      destruct Hsp0 as [Hlo_sp _]; simpl Z.of_nat in Hlo_sp; unfold mc_frame_cap in *; lia. }
    assert (Hsp_call_valid : mc_valid_sp0 (rv_read_reg 2%N rf)).
    { rewrite Hrf2_eq; exact (mc_valid_sp0_depth_step _ _ Hsp0 Esp_al). }
    set (next_pc := (pc + drci_len dec)%N).
    set (rf_link := rv_write_reg 1%N (@Integers.repr 64%positive (Z.of_N next_pc)) rf).
    assert (Hrf_link2 : rv_read_reg 2%N rf_link = rv_read_reg 2%N rf)
      by (unfold rv_read_reg, rf_link, rv_write_reg; cbn [N.eqb]; reflexivity).
    assert (Hsp_call_valid_l : mc_valid_sp0 (rv_read_reg 2%N rf_link))
      by (rewrite Hrf_link2; exact Hsp_call_valid).
    destruct (HO c rf_link mstk Hc_in Hsp_call_valid_l) as (rf_ret & v_ret & HO_eq & Hpres_c & Habi_c).
    rewrite Hc_nm in HO_eq.
    set (step_binds :=
      (mc_call_ret_var cid (mcs_ret_width c), DVALUE_Base (@DVALUE_I Pa (mcs_ret_width c) v_ret)) ::
      match opt_hi with
      | None => []
      | Some hn => [(hn, DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg 10%N rf_ret)))]
      end).
    set (penv1 := overlay_penv step_binds penv0).
    set (ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end).
    set (allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed).
    assert (Hinc : incl allowed allowed') by (intros x Hx; right; apply in_or_app; right; exact Hx).
    assert (Hopt_hi_nm : forall hn, opt_hi = Some hn -> hn = mc_call_hi_var cid).
    { intros hn Hhn; unfold mc_post_call_ret_expr in Epc.
      destruct (Pos.eqb (mcs_ret_width c) 64%positive); [inversion Epc; rewrite Hhn in *; discriminate |].
      destruct (mcs_ret_ext c); inversion Epc; subst; try discriminate; congruence. }
    assert (Hnd_step : NoDup (List.map fst step_binds)).
    { unfold step_binds; destruct opt_hi as [hn |] eqn:Ehi; cbn [List.map].
      - constructor; [| constructor; [intro H; contradiction H | constructor]].
        intro Hin; destruct Hin as [Heq | []]; pose proof (Hopt_hi_nm hn eq_refl) as ->.
        cbn [fst] in Heq; exfalso; apply (mc_call_ret_hi_disjoint cid (mcs_ret_width c) cid); symmetry; exact Heq.
      - constructor; [intro H; contradiction H | constructor]. }
    assert (Hdisj_step : binds_disjoint_from allowed step_binds).
    { intros nm w Hin Hina; unfold step_binds in Hina; destruct opt_hi as [hn |]; cbn [List.map fst] in Hina.
      - destruct Hina as [Heq | [Heq | []]].
        + exfalso; apply (proj1 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq.
        + pose proof (Hopt_hi_nm hn eq_refl) as ->.
          exfalso; apply (proj2 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq.
      - destruct Hina as [Heq | []].
        exfalso; apply (proj1 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq. }
    assert (Hp1_al : forall nm w, In (nm, w) allowed -> penv1 nm = penv0 nm)
      by (intros nm w Hin; unfold penv1; exact (overlay_penv_disjoint_allowed step_binds penv0 allowed Hdisj_step nm w Hin)).
    assert (Hvrf' : rv_val_regs_wf allowed' (rv_post_call_vrf cid c vrf)).
    { pose proof (rv_post_call_vrf_wf allowed cid c vrf Hvrf Hcrw) as Hpv; rewrite Epc in Hpv; exact Hpv. }
    assert (Hsp2' : rv_val_read 2%N (rv_post_call_vrf cid c vrf) = MSV_StackPtr sp_off).
    { unfold rv_val_read, rv_post_call_vrf; rewrite Epc; cbn [N.eqb]; unfold rv_val_read in Hsp2; exact Hsp2. }
    assert (Hastk' : mc_sym_stack_wf allowed' sp_off astk)
      by (exact (mc_sym_stack_wf_mono _ _ _ _ Hinc Hastk)).
    assert (Hfresh' : forall nm w, In (nm, w) allowed' ->
      forall k' w', (S cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').
    { intros nm w Hin k' w' Hge; destruct Hin as [Heq | Hin].
      - inversion Heq; subst nm w; split;
          [intro H; apply mc_call_ret_var_k_inj in H; lia | apply mc_call_ret_hi_disjoint].
      - apply in_app_iff in Hin as [Hext | Hal].
        + unfold ext in Hext; destruct opt_hi as [hn |]; [| contradiction Hext].
          destruct Hext as [Heq | []]; inversion Heq; subst nm w; pose proof (Hopt_hi_nm hn eq_refl) as ->.
          split; [intro H; symmetry in H; apply (mc_call_ret_hi_disjoint _ _ _ H)
                 | intro H; apply mc_call_hi_var_inj in H; lia].
        + exact (Hfresh nm w Hal k' w' ltac:(lia)). }
    assert (Hag_rf_ret : rv_val_regs_agrees penv1 dummy_freeze_oracle rf0 (rv_read_reg 2%N rf0)
                           (rv_post_call_vrf cid c vrf) rf_ret).
    { intro r; unfold rv_val_read, rv_post_call_vrf; rewrite Epc.
      destruct (N.eqb r 0%N) eqn:Er0.
      - apply N.eqb_eq in Er0; subst r; unfold rv_read_reg; cbn [N.eqb mc_sym_val_agrees].
        rewrite eval_ce_const, repr_zero_N; reflexivity.
      - destruct (N.eqb r 2%N) eqn:Er2.
        + apply N.eqb_eq in Er2; subst r; pose proof (Hag_rf 2%N) as H2; unfold rv_val_read in H2, Hsp2; cbn [N.eqb] in H2, Hsp2.
          rewrite Hsp2 in H2 |- *; cbn [mc_sym_val_agrees] in H2 |- *.
          assert (Hrf_eq2 : rf_ret 2%N = rf_link 2%N) by (apply Hpres_c; reflexivity).
          unfold rv_read_reg in *; cbn [N.eqb] in *; rewrite Hrf_eq2, Hrf_link2; exact H2.
        + destruct (N.eqb r 10%N) eqn:Er10.
          * apply N.eqb_eq in Er10; subst r; cbn [mc_sym_val_agrees].
            unfold rv_read_reg; cbn [N.eqb].
            eapply mc_post_call_ret_expr_sound; [exact Hcrw | exact Epc | exact Habi_c | |].
            -- unfold penv1; apply overlay_penv_lookup_in; [exact Hnd_step | left; reflexivity].
            -- destruct opt_hi as [hn |] eqn:Ehi; [| exact I].
               unfold penv1; apply overlay_penv_lookup_in; [exact Hnd_step | right; left; reflexivity].
          * destruct (rv_is_callee_saved r) eqn:Ecs; [| exact I].
            pose proof (Hag_rf r) as Hr; unfold rv_val_read in Hr; rewrite Er0 in Hr.
            assert (Hr_ne1 : r <> 1%N) by (intro C; subst r; discriminate Ecs).
            assert (Hrf_eqr : rv_read_reg r rf_ret = rv_read_reg r rf).
            { unfold rv_read_reg; rewrite Er0; rewrite (Hpres_c r Ecs).
              unfold rf_link, rv_write_reg; cbn [N.eqb]; destruct (N.eqb r 1%N) eqn:E1;
                [apply N.eqb_eq in E1; contradiction | reflexivity]. }
            rewrite Hrf_eqr.
            destruct (vrf r) as [| e | |] eqn:Evr; try exact Hr.
            pose proof (Hvrf r) as Hwr; unfold rv_val_read in Hwr; rewrite Er0, Evr in Hwr.
            destruct Hwr as (_ & _ & Hlf_e & Hsub_e); cbn [mc_sym_val_agrees] in Hr |- *.
            unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hr | exact Hlf_e |].
            intros nm0 w0 Hnm0; exact (Hp1_al nm0 w0 (vars_subset_b_incl _ _ Hsub_e _ Hnm0)). }
    assert (Hag_stk1 : mc_sym_stack_agrees penv1 dummy_freeze_oracle (fun r => rv_read_reg r rf0) (rv_read_reg 2%N rf0) astk mstk)
      by (eapply (mc_sym_stack_agrees_penv_agree penv0 penv1); [exact Hastk | intros nm w H; symmetry; exact (Hp1_al nm w H) | exact Hag_stk]).
    destruct (IH callees (pt_add_n pc visited) next_pc (S cid) sp_off
                 (rv_post_call_vrf cid c vrf) astk ret_w allowed' cont
                 O penv1 rf0 rf_ret mstk Hrw Hcws Hmul HO Hsp0 Hrng Hsp2' Hvrf' Hastk' Hfresh' Hag_rf_ret Hag_stk1 Ect)
      as (tr_r & nb_r & rf_end & mstk_end & Hnd_r & Hdisj_r & Hkge_r & Hcv_r & Hexec_r & Hpres_r & Hra_r & Hpath_r).
    exists ((cname, rf_link, rv_read_reg 10%N rf_ret) :: tr_r), (step_binds ++ nb_r), rf_end, mstk_end.
    assert (Hdisj_sr : forall nm, In nm (List.map fst step_binds) -> ~ In nm (List.map fst nb_r)).
    { intros nm Hst Hin_r; destruct (Hkge_r nm Hin_r) as [k' [Hk' Hnm']].
      assert (Hex : exists w', In (nm, w') allowed').
      { unfold step_binds in Hst; destruct opt_hi as [hn |] eqn:Ehi; cbn [List.map fst] in Hst.
        - destruct Hst as [<- | [<- | []]].
          + exists (mcs_ret_width c); left; reflexivity.
          + exists 64%positive; right; left; reflexivity.
        - destruct Hst as [<- | []]; exists (mcs_ret_width c); left; reflexivity. }
      destruct Hex as [w' Hw'].
      destruct Hnm' as [[w'' Heq] | Heq];
        [pose proof (Hfresh' nm w' Hw' k' w'' Hk') as [Hne _]; exact (Hne Heq)
        | pose proof (Hfresh' nm w' Hw' k' 1%positive Hk') as [_ Hne]; exact (Hne Heq)]. }
    repeat split.
    + rewrite List.map_app; apply NoDup_app_intro; assumption.
    + apply binds_disjoint_app; [exact Hdisj_step |].
      intros nm w Hin; exact (Hdisj_r nm w (Hinc _ Hin)).
    + intros nm Hin; rewrite List.map_app in Hin; apply in_app_iff in Hin as [Hst | Hr].
      * unfold step_binds in Hst; destruct opt_hi as [hn |]; cbn [List.map fst] in Hst.
        -- destruct Hst as [<- | [<- | []]].
           ++ exists cid; split; [lia | left; exists (mcs_ret_width c); reflexivity].
           ++ pose proof (Hopt_hi_nm hn eq_refl) as ->; exists cid; split; [lia | right; reflexivity].
        -- destruct Hst as [<- | []]; exists cid; split; [lia | left; exists (mcs_ret_width c); reflexivity].
      * destruct (Hkge_r nm Hr) as [k [Hk Hnm]]; exists k; split; [lia | exact Hnm].
    + intros nm dv Hin; apply in_app_iff in Hin as [Hst | Hr].
      * unfold step_binds in Hst; destruct opt_hi as [hn |] eqn:Ehi.
        -- destruct Hst as [Heq | [Heq | []]]; inversion Heq; subst nm dv.
           ++ exists (mcs_ret_width c); split;
                [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; left; reflexivity
                | exists v_ret; reflexivity].
           ++ exists 64%positive; split;
                [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; right; left; reflexivity
                | exists (rv_read_reg 10%N rf_ret); reflexivity].
        -- destruct Hst as [Heq | []]; inversion Heq; subst nm dv.
           exists (mcs_ret_width c); split;
             [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; left; reflexivity
             | exists v_ret; reflexivity].
      * destruct (Hcv_r nm dv Hr) as (w & Hcm & Hv); exists w; split;
          [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; left; exact Hcm
          | exact Hv].
    + cbn [rv_exec_with_calls]; rewrite Hlk, Edi, Hsp_eq_off, Esp_al.
      fold next_pc rf_link; rewrite HO_eq; cbn [fst snd]; rewrite Hexec_r; reflexivity.
    + exact Hpres_r.
    + exact Hra_r.
    + intros extra Hdx Hnx.
      cbn [List.map] in *.
      assert (Hfc : find_callee_spec callees cname = Some c) by exact Efc.
      rewrite Hfc.
      assert (Hargs_eval : Forall2 (fun e64 v64 =>
        eval_closed_cert_expr (overlay_penv ((step_binds ++ nb_r) ++ extra) penv0) dummy_freeze_oracle e64 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)))
        aes
        (List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_link) (seq 0 (List.length (mcs_args c))))).
      { assert (Hrf_arg_eq : List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_link) (seq 0 (List.length (mcs_args c))) =
                             List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf) (seq 0 (List.length (mcs_args c)))).
        { apply map_ext; intro j; unfold rf_link, rv_read_reg, rv_write_reg; cbn [N.eqb].
          destruct (N.eqb (10%N + N.of_nat j) 0%N) eqn:E0; [reflexivity |].
          destruct (N.eqb (10%N + N.of_nat j) 1%N) eqn:E1; [apply N.eqb_eq in E1; lia | reflexivity]. }
        rewrite Hrf_arg_eq.
        pose proof (rv_sym_read_call_args_from_sound pc cname penv0 dummy_freeze_oracle rf0 (rv_read_reg 2%N rf0) vrf rf 10%N
                      (List.length (mcs_args c)) aes Hag_rf Eargs) as Hs_args.
        pose proof (rv_sym_read_call_args_from_wf pc cname allowed 10%N (List.length (mcs_args c)) vrf aes Hvrf Eargs) as Hwf_args.
        assert (Hfa_ev : forall e64 v64,
          wf_sym_expr allowed 64%positive e64 ->
          eval_closed_cert_expr penv0 dummy_freeze_oracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
          eval_closed_cert_expr (overlay_penv ((step_binds ++ nb_r) ++ extra) penv0) dummy_freeze_oracle e64 =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))).
        { intros e64 v64 (_ & _ & Hlf & Hsub) Hev; unfold eval_closed_cert_expr in *.
          assert (Hdisj_all : binds_disjoint_from allowed ((step_binds ++ nb_r) ++ extra))
            by (apply binds_disjoint_app; [apply binds_disjoint_app; [exact Hdisj_step | intros x wx Hx; exact (Hdisj_r x wx (Hinc _ Hx))] | exact Hdx]).
          erewrite mcc_eval_cert_expr_penv_agree; [exact Hev | exact Hlf |].
          intros nm w Hnm; exact (overlay_penv_disjoint_allowed _ penv0 allowed Hdisj_all nm w (vars_subset_b_incl _ _ Hsub _ Hnm)). }
        clear -Hwf_args Hs_args Hfa_ev; induction Hs_args; [constructor |].
        inversion Hwf_args as [| ? ? Hw0 Hwr]; subst; constructor; [exact (Hfa_ev _ _ Hw0 H) | exact (IHHs_args Hwr)]. }
      eapply MTPO_Call; [exact Hargs_eval | | symmetry; exact (proj1 Habi_c) |].
      * unfold penv1; rewrite <- app_assoc, overlay_penv_app;
          unfold step_binds; cbn [overlay_penv]; rewrite String.eqb_refl; reflexivity.
      * assert (Hdx_r : binds_disjoint_from allowed' extra).
        { intros nm w Hin Hina; destruct Hin as [Heq | Hin].
          - inversion Heq; subst nm w; apply (Hnx (mc_call_ret_var cid (mcs_ret_width c)));
              [rewrite List.map_app; apply in_or_app; left; left; reflexivity | exact Hina].
          - apply in_app_iff in Hin as [Hext | Hal].
            + unfold ext in Hext; destruct opt_hi as [hn |]; [| contradiction Hext].
              destruct Hext as [Heq | []]; inversion Heq; subst nm w; apply (Hnx hn);
                [rewrite List.map_app; apply in_or_app; left; right; left; reflexivity | exact Hina].
            + exact (Hdx nm w Hal Hina). }
        assert (Hnx_r : forall nm, In nm (List.map fst nb_r) -> ~ In nm (List.map fst extra)).
        { intros nm Hin; apply Hnx; rewrite List.map_app; apply in_or_app; right; exact Hin. }
        specialize (Hpath_r extra Hdx_r Hnx_r).
        assert (Henv_eq : forall nm,
          overlay_penv (nb_r ++ extra) penv1 nm =
          overlay_penv ((step_binds ++ nb_r) ++ extra) penv0 nm).
        { intro nm; unfold penv1; rewrite <- app_assoc; repeat rewrite overlay_penv_app.
          destruct (in_dec string_dec nm (List.map fst nb_r)) as [Hin_r | Hnin_r].
          - rewrite (overlay_penv_not_in step_binds _ nm).
            + clear -Hin_r; induction nb_r as [| [x dv] rest IHnb]; cbn in *; [contradiction |].
              destruct (String.eqb nm x) eqn:Ex; [reflexivity |].
              apply IHnb; destruct Hin_r as [-> | Hr]; [rewrite String.eqb_refl in Ex; discriminate Ex | exact Hr].
            + intro Hs; exact (Hdisj_sr nm Hs Hin_r).
          - rewrite !overlay_penv_not_in by exact Hnin_r.
            destruct (in_dec string_dec nm (List.map fst step_binds)) as [Hin_s | Hnin_s].
            + rewrite (overlay_penv_not_in extra _ nm) by (apply Hnx; rewrite List.map_app; apply in_or_app; left; exact Hin_s).
              clear -Hin_s; induction step_binds as [| [x dv] rest IHst]; cbn in *;
                [exfalso; exact Hin_s |].
              destruct (String.eqb nm x) eqn:Ex; [reflexivity |].
              apply IHst; destruct Hin_s as [<- | Hs]; [rewrite String.eqb_refl in Ex; discriminate Ex | exact Hs].
            + rewrite (overlay_penv_not_in step_binds _ nm Hnin_s).
              rewrite overlay_penv_app, (overlay_penv_not_in nb_r _ nm Hnin_r).
              clear -Hnin_s; induction extra as [| [x dv] rest IHe]; cbn [overlay_penv];
                [exact (overlay_penv_not_in step_binds penv0 nm Hnin_s)
                | destruct (String.eqb nm x); [reflexivity | exact IHe]]. }
        exact (mc_tree_path_ok_extensional _ _ _ _ _ _ _ Henv_eq Hpath_r).
Qed.



(** *** 5.3 AArch64 Call-Tree Execution Witness *)

Lemma summarize_a64_call_at_exec {Pa : Params} :
  forall insts im
    (Him : forall pc, pt_get (N.succ_pos pc) im = lookup_a64_call_inst insts pc)
    fuel callees visited pc cid sp_off vrf astk sfl fl_def ret_w allowed t_mc
    (O : a64_call_oracle) (penv0 : param_env Pa) rf0 sp0 rf sp fl mstk,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees ->
       rv_supported_arg_width (mcs_ret_width c) = true /\
       (List.length (mcs_args c) <= 8)%nat) ->
    forallb a64_call_inst_valid insts = true ->
    wf_a64_call_oracle callees O ->
    mc_valid_sp0_depth 2%nat sp0 ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    (forall nm w, In (nm, w) allowed ->
       forall k' w', (cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k') ->
    a64_val_regs_agrees penv0 dummy_freeze_oracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv0 dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv0 dummy_freeze_oracle sfl fl) ->
    summarize_a64_call_at fuel im callees visited pc cid sp_off vrf astk sfl fl_def ret_w = inr t_mc ->
    exists tr_mc new_binds rf_end fl_end mstk_end,
      NoDup (List.map fst new_binds) /\
      binds_disjoint_from allowed new_binds /\
      (forall nm, In nm (List.map fst new_binds) ->
         exists k, (cid <= k)%nat /\ ((exists w, nm = mc_call_ret_var k w) \/ nm = mc_call_hi_var k)) /\
      (forall nm dv, In (nm, dv) new_binds ->
         exists w, In (nm, w) (collect_mc_call_vars t_mc) /\
                   exists v : @Integers.bit_int w, dv = DVALUE_Base (@DVALUE_I Pa w v)) /\
      a64_exec_with_calls fuel insts O pc sp0 rf sp fl mstk =
        Some (tr_mc, rf_end, sp0, fl_end, mstk_end) /\
      a64_callee_saved_preserved rf0 rf_end /\
      forall extra_binds,
        binds_disjoint_from allowed extra_binds ->
        (forall nm, In nm (List.map fst new_binds) -> ~ In nm (List.map fst extra_binds)) ->
        mc_tree_path_ok (overlay_penv (new_binds ++ extra_binds) penv0) ret_w [] t_mc
          (List.map (fun '(cn, rf_c, a0_r) =>
            let n := match find_callee_spec callees cn with
                     | Some spc => List.length (mcs_args spc)
                     | None => 0%nat
                     end in
            (cn, List.map (fun j => a64_read_reg (N.of_nat j) rf_c) (seq 0 n), a0_r)) tr_mc)
          (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)).
Proof.
  intros insts im Him fuel; induction fuel as [| fuel' IH];
    intros callees visited pc cid sp_off vrf astk sfl fl_def ret_w allowed t_mc
           O penv0 rf0 sp0 rf sp fl mstk
           Hrw Hcws Hval HO Hsp0 Hrng Hsp Hvrf Hastk Hflwf Hfresh Hag_rf Hag_stk Hfl Hsum;
    cbn [summarize_a64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Hlk; [| discriminate Hsum].
  rewrite Him in Hlk.
  assert (Hin_dec : In dec insts).
  { clear -Hlk; induction insts as [| d rest IHi]; cbn in Hlk; [discriminate |].
    destruct (N.eqb (daci_off d) pc); [inversion Hlk; left; reflexivity | right; exact (IHi Hlk)]. }
  assert (Hsp0_1 : mc_valid_sp0 sp0)
    by (destruct Hsp0 as [H0 H1]; split; [unfold mc_frame_cap in *; lia | exact H1]).
  destruct (daci_inst dec) as [i | cname] eqn:Edi.
  - assert (Hdec_val : a64_inst_valid (mk_decoded_a64_inst (daci_off dec) i) = true).
    { rewrite forallb_forall in Hval; pose proof (Hval dec Hin_dec) as Hv;
        unfold a64_call_inst_valid in Hv; rewrite Edi in Hv; exact Hv. }
    destruct (a64_sym_step_one (mk_decoded_a64_inst (daci_off dec) i) pc sp_off vrf astk sfl fl_def ret_w)
      as [res |] eqn:Est; [| discriminate Hsum].
    pose proof (a64_sym_step_one_wf allowed (mk_decoded_a64_inst (daci_off dec) i)
                  pc sp_off vrf astk sfl fl_def ret_w res Hrw Hrng Hvrf Hastk Hflwf Est) as Hwf_step.
    pose proof (a64_sym_step_one_sound (mk_decoded_a64_inst (daci_off dec) i)
                  pc sp_off vrf astk sfl fl_def ret_w res penv0 dummy_freeze_oracle rf0 sp0 rf sp fl mstk
                  Hrw Hdec_val Hsp0_1 Hrng Hsp Hag_rf Hag_stk Hfl Est) as Hsd_step.
    destruct res as [npc sp_off' vrf' astk' sfl' fl_def' | cond tpc npc fl_def' | ret_e].
    + destruct Hwf_step as (Hrng' & Hvrf' & Hastk' & Hflwf').
      destruct Hsd_step as (rf' & sp' & fl' & mstk' & Hexec1 & _ & Hsp' & Hag_rf' & Hag_stk' & Hfl').
      destruct (IH callees (pt_add_n pc visited) npc cid sp_off' vrf' astk' sfl' fl_def' ret_w
                   allowed t_mc O penv0 rf0 sp0 rf' sp' fl' mstk'
                   Hrw Hcws Hval HO Hsp0 Hrng' Hsp' Hvrf' Hastk' Hflwf' Hfresh Hag_rf' Hag_stk' Hfl' Hsum)
        as (tr_mc & nb & rf_end & fl_end & mstk_end & Hnd & Hdisj & Hkge & Hcv & Hexec & Hpres & Hpath).
      exists tr_mc, nb, rf_end, fl_end, mstk_end; split; [exact Hnd | split; [exact Hdisj | split; [exact Hkge | split; [exact Hcv | split; [| split; [exact Hpres | exact Hpath]]]]]].
      cbn [a64_exec_with_calls]; rewrite Hlk, Edi.
      destruct i; cbn [a64_exec_one_nonret] in Hexec1; try discriminate Hexec1;
        rewrite Hexec1; exact Hexec.
    + destruct Hwf_step as [Hcw Himp].
      destruct Hcw as (_ & _ & Hlf_c & Hsub_c).
      destruct Hsd_step as (b & Hevc & Hexec1 & _).
      destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk sfl fl_def' ret_w)
        as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk sfl fl_def' ret_w)
        as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t_mc; clear Hsum.
      assert (Hnext_p : summarize_a64_call_at fuel' im callees (pt_add_n pc visited)
                          (if b then tpc else npc) cid sp_off vrf astk sfl fl_def' ret_w =
                        inr (if b then dt else df))
        by (destruct b; [exact Hdt | exact Hdf]).
      destruct (IH callees (pt_add_n pc visited) (if b then tpc else npc) cid sp_off vrf astk sfl fl_def' ret_w
                   allowed (if b then dt else df) O penv0 rf0 sp0 rf sp fl mstk
                   Hrw Hcws Hval HO Hsp0 Hrng Hsp Hvrf Hastk (fun h => Hflwf (Himp h)) Hfresh Hag_rf Hag_stk (fun h => Hfl (Himp h)) Hnext_p)
        as (tr_mc & nb & rf_end & fl_end & mstk_end & Hnd & Hdisj & Hkge & Hcv & Hexec & Hpres & Hpath).
      exists tr_mc, nb, rf_end, fl_end, mstk_end; repeat split; try assumption.
      * intros nm dv Hinn; destruct (Hcv nm dv Hinn) as (w & Hcm & Hv).
        exists w; split; [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_app_iff; destruct b; [right | left]; exact Hcm | exact Hv].
      * cbn [a64_exec_with_calls]; rewrite Hlk, Edi.
        destruct i; cbn [a64_exec_one_nonret] in Hexec1; try discriminate Hexec1;
          rewrite Hexec1; exact Hexec.
      * intros extra Hdx Hnx; specialize (Hpath extra Hdx Hnx).
        eapply MTPO_Branch.
        -- unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hevc | exact Hlf_c |].
           intros nm w Hnm; pose proof (vars_subset_b_incl _ _ Hsub_c _ Hnm) as Hal.
           apply (overlay_penv_disjoint_allowed (nb ++ extra) penv0 allowed (binds_disjoint_app _ _ _ Hdisj Hdx) nm w Hal).
        -- exact (mc_tree_path_ok_app_r _ _ [] [(b, cond)] _ _ _ Hpath).
    + inversion Hsum; subst t_mc; clear Hsum.
      destruct Hsd_step as (Edai & Esp_eq & Hpres & Hevr).
      destruct Hwf_step as (_ & _ & Hlf_r & Hsub_r).
      exists [], [], rf, fl, mstk.
      split; [constructor | split; [| split; [| split; [| split; [| split; [exact Hpres |]]]]]].
      * intros nm w _ H; contradiction H.
      * intros nm H; contradiction H.
      * intros nm dv H; contradiction H.
      * cbn [dai_inst] in Edai; cbn [a64_exec_with_calls]; rewrite Hlk, Edi, Edai, Esp_eq; reflexivity.
      * intros extra Hdx _; apply MTPO_Ret.
        unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hevr | exact Hlf_r |].
        intros nm w Hnm; pose proof (vars_subset_b_incl _ _ Hsub_r _ Hnm) as Hal.
        cbn [app]; exact (overlay_penv_disjoint_allowed extra penv0 allowed Hdx nm w Hal).
  - destruct (mc_sp_aligned16 sp_off) eqn:Esp_al; cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |] eqn:Efc; [| discriminate Hsum].
    destruct (a64_sym_read_call_args_from pc cname 0%N (List.length (mcs_args c)) vrf) as [| aes] eqn:Eargs;
      [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited)
                (pc + 4%N)%N (S cid) sp_off (a64_post_call_vrf cid c vrf) astk sfl false ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t_mc; clear Hsum.
    pose proof (find_callee_spec_in _ _ _ Efc) as [Hc_in Hc_nm].
    destruct (Hcws c Hc_in) as [Hcrw Hclen].
    assert (Hsp_eq_off : mc_addr_to_off sp0 sp = sp_off).
    { rewrite Hsp; refine (mc_addr_to_off_add sp0 sp_off _ Hrng).
      destruct Hsp0 as [Hlo_sp _]; simpl Z.of_nat in Hlo_sp; unfold mc_frame_cap in *; lia. }
    assert (Hsp_call_valid : mc_valid_sp0 sp)
      by (rewrite Hsp; exact (mc_valid_sp0_depth_step sp0 sp_off Hsp0 Esp_al)).
    set (next_pc := (pc + 4%N)%N).
    set (rf_link := a64_write_reg 30%N (@Integers.repr 64%positive (Z.of_N next_pc)) rf).
    destruct (HO c rf_link sp fl mstk Hc_in Hsp_call_valid)
      as (rf_ret & fl_ret & v_ret & HO_eq & Hpres_c & Habi_c).
    rewrite Hc_nm in HO_eq.
    set (step_binds :=
      (mc_call_ret_var cid (mcs_ret_width c), DVALUE_Base (@DVALUE_I Pa (mcs_ret_width c) v_ret)) ::
      match opt_hi with
      | None => []
      | Some hn => [(hn, DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg 0%N rf_ret)))]
      end).
    set (penv1 := overlay_penv step_binds penv0).
    set (ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end).
    set (allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed).
    assert (Hinc : incl allowed allowed') by (intros x Hx; right; apply in_or_app; right; exact Hx).
    assert (Hopt_hi_nm : forall hn, opt_hi = Some hn -> hn = mc_call_hi_var cid).
    { intros hn Hhn; unfold mc_post_call_ret_expr in Epc.
      destruct (Pos.eqb (mcs_ret_width c) 64%positive); [inversion Epc; rewrite Hhn in *; discriminate |].
      destruct (mcs_ret_ext c); inversion Epc; subst; try discriminate; congruence. }
    assert (Hnd_step : NoDup (List.map fst step_binds)).
    { unfold step_binds; destruct opt_hi as [hn |] eqn:Ehi; cbn [List.map].
      - constructor; [| constructor; [intro H; contradiction H | constructor]].
        intro Hin; destruct Hin as [Heq | []]; pose proof (Hopt_hi_nm hn eq_refl) as ->.
        cbn [fst] in Heq; exfalso; apply (mc_call_ret_hi_disjoint cid (mcs_ret_width c) cid); symmetry; exact Heq.
      - constructor; [intro H; contradiction H | constructor]. }
    assert (Hdisj_step : binds_disjoint_from allowed step_binds).
    { intros nm w Hin Hina; unfold step_binds in Hina; destruct opt_hi as [hn |]; cbn [List.map fst] in Hina.
      - destruct Hina as [Heq | [Heq | []]].
        + exfalso; apply (proj1 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq.
        + pose proof (Hopt_hi_nm hn eq_refl) as ->.
          exfalso; apply (proj2 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq.
      - destruct Hina as [Heq | []].
        exfalso; apply (proj1 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq. }
    assert (Hp1_al : forall nm w, In (nm, w) allowed -> penv1 nm = penv0 nm)
      by (intros nm w Hin; unfold penv1; exact (overlay_penv_disjoint_allowed step_binds penv0 allowed Hdisj_step nm w Hin)).
    assert (Hvrf' : wf_a64_val_regs allowed' (a64_post_call_vrf cid c vrf)).
    { pose proof (a64_post_call_vrf_wf allowed cid c vrf Hvrf Hcrw) as Hpv; rewrite Epc in Hpv; exact Hpv. }
    assert (Hastk' : mc_sym_stack_wf allowed' sp_off astk)
      by (exact (mc_sym_stack_wf_mono _ _ _ _ Hinc Hastk)).
    assert (Hfresh' : forall nm w, In (nm, w) allowed' ->
      forall k' w', (S cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').
    { intros nm w Hin k' w' Hge; destruct Hin as [Heq | Hin].
      - inversion Heq; subst nm w; split;
          [intro H; apply mc_call_ret_var_k_inj in H; lia | apply mc_call_ret_hi_disjoint].
      - apply in_app_iff in Hin as [Hext | Hal].
        + unfold ext in Hext; destruct opt_hi as [hn |]; [| contradiction Hext].
          destruct Hext as [Heq | []]; inversion Heq; subst nm w; pose proof (Hopt_hi_nm hn eq_refl) as ->.
          split; [intro H; symmetry in H; apply (mc_call_ret_hi_disjoint _ _ _ H)
                 | intro H; apply mc_call_hi_var_inj in H; lia].
        + exact (Hfresh nm w Hal k' w' ltac:(lia)). }
    assert (Hag_rf_ret : a64_val_regs_agrees penv1 dummy_freeze_oracle rf0 sp0
                           (a64_post_call_vrf cid c vrf) rf_ret).
    { intro r; unfold a64_val_read, a64_post_call_vrf; rewrite Epc.
      destruct (N.leb 31%N r) eqn:E31.
      - unfold a64_read_reg; rewrite E31; cbn [mc_sym_val_agrees].
        rewrite eval_ce_const, repr_zero_N; reflexivity.
      - destruct (N.eqb r 0%N) eqn:Er0.
        + apply N.eqb_eq in Er0; subst r; cbn [mc_sym_val_agrees].
          unfold a64_read_reg; cbn [N.leb].
          eapply mc_post_call_ret_expr_sound; [exact Hcrw | exact Epc | exact Habi_c | |].
          * unfold penv1; apply overlay_penv_lookup_in; [exact Hnd_step | left; reflexivity].
          * destruct opt_hi as [hn |] eqn:Ehi; [| exact I].
            unfold penv1; apply overlay_penv_lookup_in; [exact Hnd_step | right; left; reflexivity].
        + destruct (N.leb 19%N r && N.leb r 29%N) eqn:E19; [| exact I].
          apply andb_true_iff in E19 as [H19 H29].
          assert (Hcs : a64_is_callee_saved r = true).
          { unfold a64_is_callee_saved; rewrite H19; apply N.leb_le in H29; apply N.leb_le; lia. }
          assert (Hr_ne30 : r <> 30%N) by (apply N.leb_le in H29; lia).
          pose proof (Hag_rf r) as Hr; unfold a64_val_read in Hr; rewrite E31 in Hr.
          assert (Hrf_eqr : a64_read_reg r rf_ret = a64_read_reg r rf).
          { unfold a64_read_reg; rewrite E31; rewrite (Hpres_c r Hcs).
            unfold rf_link, a64_write_reg; change (N.leb 31%N 30%N) with false; cbn [N.eqb]; destruct (N.eqb r 30%N) eqn:E30;
              [apply N.eqb_eq in E30; contradiction | reflexivity]. }
          rewrite Hrf_eqr.
          destruct (vrf r) as [| e | |] eqn:Evr; try exact Hr.
          pose proof (Hvrf r) as Hwr; unfold a64_val_read in Hwr; rewrite E31, Evr in Hwr.
          destruct Hwr as (_ & _ & Hlf_e & Hsub_e); cbn [mc_sym_val_agrees] in Hr |- *.
          unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hr | exact Hlf_e |].
          intros nm0 w0 Hnm0; exact (Hp1_al nm0 w0 (vars_subset_b_incl _ _ Hsub_e _ Hnm0)). }
    assert (Hag_stk1 : mc_sym_stack_agrees penv1 dummy_freeze_oracle (fun r => a64_read_reg r rf0) sp0 astk mstk)
      by (eapply (mc_sym_stack_agrees_penv_agree penv0 penv1); [exact Hastk | intros nm w H; symmetry; exact (Hp1_al nm w H) | exact Hag_stk]).
    destruct (IH callees (pt_add_n pc visited) next_pc (S cid) sp_off
                 (a64_post_call_vrf cid c vrf) astk sfl false ret_w allowed' cont
                 O penv1 rf0 sp0 rf_ret sp fl_ret mstk
                 Hrw Hcws Hval HO Hsp0 Hrng Hsp Hvrf' Hastk' (fun C : false = true => ltac:(discriminate C))
                 Hfresh' Hag_rf_ret Hag_stk1 (fun C : false = true => ltac:(discriminate C)) Ect)
      as (tr_r & nb_r & rf_end & fl_end & mstk_end & Hnd_r & Hdisj_r & Hkge_r & Hcv_r & Hexec_r & Hpres_r & Hpath_r).
    exists ((cname, rf_link, a64_read_reg 0%N rf_ret) :: tr_r), (step_binds ++ nb_r), rf_end, fl_end, mstk_end.
    assert (Hdisj_sr : forall nm, In nm (List.map fst step_binds) -> ~ In nm (List.map fst nb_r)).
    { intros nm Hst Hin_r; destruct (Hkge_r nm Hin_r) as [k' [Hk' Hnm']].
      assert (Hex : exists w', In (nm, w') allowed').
      { unfold step_binds in Hst; destruct opt_hi as [hn |] eqn:Ehi; cbn [List.map fst] in Hst.
        - destruct Hst as [<- | [<- | []]].
          + exists (mcs_ret_width c); left; reflexivity.
          + exists 64%positive; right; left; reflexivity.
        - destruct Hst as [<- | []]; exists (mcs_ret_width c); left; reflexivity. }
      destruct Hex as [w' Hw'].
      destruct Hnm' as [[w'' Heq] | Heq];
        [pose proof (Hfresh' nm w' Hw' k' w'' Hk') as [Hne _]; exact (Hne Heq)
        | pose proof (Hfresh' nm w' Hw' k' 1%positive Hk') as [_ Hne]; exact (Hne Heq)]. }
    repeat split.
    + rewrite List.map_app; apply NoDup_app_intro; assumption.
    + apply binds_disjoint_app; [exact Hdisj_step |].
      intros nm w Hin; exact (Hdisj_r nm w (Hinc _ Hin)).
    + intros nm Hin; rewrite List.map_app in Hin; apply in_app_iff in Hin as [Hst | Hr].
      * unfold step_binds in Hst; destruct opt_hi as [hn |]; cbn [List.map fst] in Hst.
        -- destruct Hst as [<- | [<- | []]].
           ++ exists cid; split; [lia | left; exists (mcs_ret_width c); reflexivity].
           ++ pose proof (Hopt_hi_nm hn eq_refl) as ->; exists cid; split; [lia | right; reflexivity].
        -- destruct Hst as [<- | []]; exists cid; split; [lia | left; exists (mcs_ret_width c); reflexivity].
      * destruct (Hkge_r nm Hr) as [k [Hk Hnm]]; exists k; split; [lia | exact Hnm].
    + intros nm dv Hin; apply in_app_iff in Hin as [Hst | Hr].
      * unfold step_binds in Hst; destruct opt_hi as [hn |] eqn:Ehi.
        -- destruct Hst as [Heq | [Heq | []]]; inversion Heq; subst nm dv.
           ++ exists (mcs_ret_width c); split;
                [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; left; reflexivity
                | exists v_ret; reflexivity].
           ++ exists 64%positive; split;
                [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; right; left; reflexivity
                | exists (a64_read_reg 0%N rf_ret); reflexivity].
        -- destruct Hst as [Heq | []]; inversion Heq; subst nm dv.
           exists (mcs_ret_width c); split;
             [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; left; reflexivity
             | exists v_ret; reflexivity].
      * destruct (Hcv_r nm dv Hr) as (w & Hcm & Hv); exists w; split;
          [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; left; exact Hcm
          | exact Hv].
    + cbn [a64_exec_with_calls]; rewrite Hlk, Edi, Hsp_eq_off, Esp_al.
      fold next_pc rf_link; rewrite HO_eq; cbn [fst snd]; rewrite Hexec_r; reflexivity.
    + exact Hpres_r.
    + intros extra Hdx Hnx.
      cbn [List.map] in *.
      assert (Hfc : find_callee_spec callees cname = Some c) by exact Efc.
      rewrite Hfc.
      assert (Hargs_eval : Forall2 (fun e64 v64 =>
        eval_closed_cert_expr (overlay_penv ((step_binds ++ nb_r) ++ extra) penv0) dummy_freeze_oracle e64 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)))
        aes
        (List.map (fun j => a64_read_reg (N.of_nat j) rf_link) (seq 0 (List.length (mcs_args c))))).
      { assert (Hrf_arg_eq : List.map (fun j => a64_read_reg (N.of_nat j) rf_link) (seq 0 (List.length (mcs_args c))) =
                             List.map (fun j => a64_read_reg (N.of_nat j) rf) (seq 0 (List.length (mcs_args c)))).
        { apply map_ext_in; intros j Hj; apply in_seq in Hj as [_ Hj].
          unfold rf_link, a64_read_reg, a64_write_reg; change (N.leb 31%N 30%N) with false.
          destruct (N.leb 31%N (N.of_nat j)) eqn:E31; [reflexivity |].
          destruct (N.eqb (N.of_nat j) 30%N) eqn:E30; [apply N.eqb_eq in E30; lia | reflexivity]. }
        rewrite Hrf_arg_eq.
        pose proof (a64_sym_read_call_args_from_sound pc cname penv0 dummy_freeze_oracle rf0 sp0 vrf rf 0%N
                      (List.length (mcs_args c)) aes Hag_rf Eargs) as Hs_args.
        replace (List.map (fun k => a64_read_reg (0%N + N.of_nat k) rf) (seq 0 (List.length (mcs_args c))))
          with (List.map (fun k => a64_read_reg (N.of_nat k) rf) (seq 0 (List.length (mcs_args c)))) in Hs_args
          by (apply map_ext; intro k; reflexivity).
        pose proof (a64_sym_read_call_args_from_wf pc cname allowed 0%N (List.length (mcs_args c)) vrf aes Hvrf Eargs) as Hwf_args.
        assert (Hfa_ev : forall e64 v64,
          wf_sym_expr allowed 64%positive e64 ->
          eval_closed_cert_expr penv0 dummy_freeze_oracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
          eval_closed_cert_expr (overlay_penv ((step_binds ++ nb_r) ++ extra) penv0) dummy_freeze_oracle e64 =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))).
        { intros e64 v64 (_ & _ & Hlf_a & Hsub_a) Hev; unfold eval_closed_cert_expr in *.
          assert (Hdisj_all : binds_disjoint_from allowed ((step_binds ++ nb_r) ++ extra))
            by (apply binds_disjoint_app; [apply binds_disjoint_app; [exact Hdisj_step | intros x wx Hx; exact (Hdisj_r x wx (Hinc _ Hx))] | exact Hdx]).
          erewrite mcc_eval_cert_expr_penv_agree; [exact Hev | exact Hlf_a |].
          intros nm w Hnm; exact (overlay_penv_disjoint_allowed _ penv0 allowed Hdisj_all nm w (vars_subset_b_incl _ _ Hsub_a _ Hnm)). }
        clear -Hwf_args Hs_args Hfa_ev; induction Hs_args; [constructor |].
        inversion Hwf_args as [| ? ? Hw0 Hwr]; subst; constructor; [exact (Hfa_ev _ _ Hw0 H) | exact (IHHs_args Hwr)]. }
      eapply MTPO_Call; [exact Hargs_eval | | symmetry; exact (proj1 Habi_c) |].
      * unfold penv1; rewrite <- app_assoc, overlay_penv_app;
          unfold step_binds; cbn [overlay_penv]; rewrite String.eqb_refl; reflexivity.
      * assert (Hdx_r : binds_disjoint_from allowed' extra).
        { intros nm w Hin Hina; destruct Hin as [Heq | Hin].
          - inversion Heq; subst nm w; apply (Hnx (mc_call_ret_var cid (mcs_ret_width c)));
              [rewrite List.map_app; apply in_or_app; left; left; reflexivity | exact Hina].
          - apply in_app_iff in Hin as [Hext | Hal].
            + unfold ext in Hext; destruct opt_hi as [hn |]; [| contradiction Hext].
              destruct Hext as [Heq | []]; inversion Heq; subst nm w; apply (Hnx hn);
                [rewrite List.map_app; apply in_or_app; left; right; left; reflexivity | exact Hina].
            + exact (Hdx nm w Hal Hina). }
        assert (Hnx_r : forall nm, In nm (List.map fst nb_r) -> ~ In nm (List.map fst extra)).
        { intros nm Hin; apply Hnx; rewrite List.map_app; apply in_or_app; right; exact Hin. }
        specialize (Hpath_r extra Hdx_r Hnx_r).
        assert (Henv_eq : forall nm,
          overlay_penv (nb_r ++ extra) penv1 nm =
          overlay_penv ((step_binds ++ nb_r) ++ extra) penv0 nm).
        { intro nm; unfold penv1; rewrite <- app_assoc; repeat rewrite overlay_penv_app.
          destruct (in_dec string_dec nm (List.map fst nb_r)) as [Hin_r | Hnin_r].
          - rewrite (overlay_penv_not_in step_binds _ nm).
            + clear -Hin_r; induction nb_r as [| [x dv] rest IHnb]; cbn in *; [contradiction |].
              destruct (String.eqb nm x) eqn:Ex; [reflexivity |].
              apply IHnb; destruct Hin_r as [-> | Hr]; [rewrite String.eqb_refl in Ex; discriminate Ex | exact Hr].
            + intro Hs; exact (Hdisj_sr nm Hs Hin_r).
          - rewrite !overlay_penv_not_in by exact Hnin_r.
            destruct (in_dec string_dec nm (List.map fst step_binds)) as [Hin_s | Hnin_s].
            + rewrite (overlay_penv_not_in extra _ nm) by (apply Hnx; rewrite List.map_app; apply in_or_app; left; exact Hin_s).
              clear -Hin_s; induction step_binds as [| [x dv] rest IHst]; cbn in *;
                [exfalso; exact Hin_s |].
              destruct (String.eqb nm x) eqn:Ex; [reflexivity |].
              apply IHst; destruct Hin_s as [<- | Hs]; [rewrite String.eqb_refl in Ex; discriminate Ex | exact Hs].
            + rewrite (overlay_penv_not_in step_binds _ nm Hnin_s).
              rewrite overlay_penv_app, (overlay_penv_not_in nb_r _ nm Hnin_r).
              clear -Hnin_s; induction extra as [| [x dv] rest IHe]; cbn [overlay_penv];
                [exact (overlay_penv_not_in step_binds penv0 nm Hnin_s)
                | destruct (String.eqb nm x); [reflexivity | exact IHe]]. }
        exact (mc_tree_path_ok_extensional _ _ _ _ _ _ _ Henv_eq Hpath_r).
Qed.

(** *** 5.4 IR Call-Tree Execution, Argument Obligation Checking & Lockstep Soundness *)

Lemma eou_raise_ub_cfg_call_ub {Pa : Params} {R S : Type} (genv : raw_id -> @dvalue Pa) :
  forall sigma env msg (k : R -> @CFGtop Pa S),
    cfg_call_steps_to_ub genv sigma env (ITree.bind (EOU_to_itree (E := CFGEtop) (@raise_ub R msg)) k) [].
Proof.
  intros sigma env msg k; cbn [EOU_to_itree]; apply cfg_call_steps_to_ub_bind_l.
  eapply CCSU_UB; unfold raiseUB, trigger_cast', ITree.trigger; rewrite observe_bind; reflexivity.
Qed.

Lemma apply_attrs_scalar_step {Pa : Params} (genv : raw_id -> @dvalue Pa) :
  forall sigma env pas msg w (dv : @dvalue Pa),
    pattrs_no_value_poison pas = true ->
    wf_scalar_dvalue w dv ->
    (existsb attr_is_noundef pas = true /\ dv = DVALUE_Base DVALUE_Poison ->
     cfg_call_steps_to_ub genv sigma env (apply_attrs pas msg dv) []) /\
    ((existsb attr_is_noundef pas = false \/ dvalue_well_defined dv = true) ->
     pure_cfg_steps env (apply_attrs pas msg dv) env dv).
Proof.
  intros sigma env pas msg w dv Hnp Hsc.
  assert (Hnp_ptr : forall p, dv <> DVALUE_Base (DVALUE_Pointer p))
    by (intros p Heq; destruct Hsc as [H1 | [? H1]]; rewrite H1 in Heq; discriminate Heq).
  split.
  - intros [Hn Hd]; subst dv.
    unfold apply_attrs, apply_value_attrs; rewrite (pattrs_no_value_poison_value_attrs pas _ Hnp Hnp_ptr).
    rewrite Hn; cbn [dvalue_well_defined negb andb].
    apply cfg_call_steps_to_ub_bind_l; apply cfg_call_steps_to_ub_bind_l; cbn [EOU_to_itree].
    unfold trigger, ITree.trigger; eapply CCSU_UB; cbn; reflexivity.
  - intros Hnn.
    unfold apply_attrs, apply_value_attrs; rewrite (pattrs_no_value_poison_value_attrs pas dv Hnp Hnp_ptr).
    assert (Hb : existsb attr_is_noundef pas && negb (dvalue_well_defined dv) = false)
      by (destruct Hnn as [-> | ->]; [reflexivity | apply andb_false_r]).
    rewrite Hb; cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
    eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity |].
    rewrite (pattrs_no_value_poison_deref pas dv msg Hnp_ptr).
    eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | apply PCS_Ret; reflexivity].
Qed.

Lemma eval_reified_pure_exp_no_ub {Pa : Params} :
  forall allowed (penv : param_env Pa) lmap env o top w ce,
    wf_pure_lmap allowed lmap ->
    wf_param_env_for allowed penv ->
    lmap_matches_env penv lmap env ->
    reify_pure_exp lmap top o = Some (w, ce) ->
    ub_free_expr ce = true ->
    expr_has_freeze ce = false ->
    exists dv,
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv /\
      pure_mcfg_steps env (denote_exp top o) env dv.
Proof.
  intros allowed penv lmap env o top w ce Hlmap Hpenv Henv Hre Hub Hnf.
  destruct (reify_pure_exp_typing o allowed lmap top w ce Hlmap Hre) as (_ & Hwt & Hbw & Hlf & Hfv).
  destruct (ub_free_expr_eval_ret ce [] penv [] dummy_freeze_oracle Hub Hwt wf_let_val_env_nil
              (fun nm w0 Hin => Hpenv nm w0 (Hfv _ Hin)))
    as [dv0 [Hev0 _]].
  destruct (eval_reified_pure_exp o penv lmap env top w ce Henv Hre)
    as [[_ [msg Hub_e]] | (dv & Hev & Hsc & Hst)];
    [unfold eval_closed_cert_expr in *; congruence | exists dv; repeat split; assumption].
Qed.

Lemma denote_call_args_step {Pa : Params} (genv : raw_id -> @dvalue Pa) :
  forall cname arg_idx allowed (penv : param_env Pa) lmap env specs args aes msg,
    wf_pure_lmap allowed lmap ->
    wf_param_env_for allowed penv ->
    lmap_matches_env penv lmap env ->
    reify_ir_call_args cname arg_idx lmap specs args = inr aes ->
    (forall sigma, cfg_call_steps_to_ub genv sigma env (denote_call_args args msg) []) \/
    exists dvs,
      pure_cfg_steps env (denote_call_args args msg) env dvs /\
      Forall2 (fun '(need_def, w, ce) dv =>
        eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
        wf_scalar_dvalue w dv /\
        (need_def = false -> dvalue_well_defined dv = true)) aes dvs.
Proof.
  intros cname arg_idx allowed penv lmap env specs; revert arg_idx;
    induction specs as [| sp srest IH];
    intros arg_idx [| [[aty ae] pas] arest] aes msg Hlmap Hpenv Henv Hra;
    cbn [reify_ir_call_args] in Hra; try discriminate Hra.
  - inversion Hra; subst aes; right; exists []; split; [apply PCS_Ret; reflexivity | constructor].
  - destruct (dtyp_eqb aty (DTYPE_Base (DTYPE_I (ras_width sp)))) eqn:Hdt; cbn [negb] in Hra; [| discriminate Hra].
    destruct (pattrs_no_value_poison pas) eqn:Hnp; cbn [negb] in Hra; [| discriminate Hra].
    destruct (reify_pure_exp lmap (Some aty) ae) as [[w0 ce] |] eqn:Ere; [| discriminate Hra].
    destruct (ub_free_expr ce) eqn:Hub; cbn [negb] in Hra; [| discriminate Hra].
    destruct (expr_has_freeze ce) eqn:Hnf; [discriminate Hra |].
    destruct (reify_ir_call_args cname (S arg_idx) lmap srest arest) as [| rest] eqn:Hrr; [discriminate Hra |].
    inversion Hra; subst aes; clear Hra.
    pose proof (reify_pure_exp_top_width ae lmap (Some aty) w0 ce Ere) as Htw.
    unfold dtyp_eqb in Hdt; destruct (dtyp_eq_dec aty (DTYPE_Base (DTYPE_I (ras_width sp))));
      [| discriminate Hdt].
    subst aty; cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst w0.
    destruct (eval_reified_pure_exp_no_ub allowed penv lmap env ae (Some (DTYPE_Base (DTYPE_I (ras_width sp))))
                (ras_width sp) ce Hlmap Hpenv Henv Ere Hub Hnf)
      as (dv & Hev & Hsc & Hst).
    assert (Hsc_step : cfg_steps_to_ret default_draw_strat env (denote_exp' (Some (DTYPE_Base (DTYPE_I (ras_width sp)))) ae)
                         default_draw_strat env dv)
      by (apply mcfg_to_cfg_steps_ret; exact (pure_mcfg_to_mcfg_ret _ _ _ _ _ Hst)).
    cbn [denote_call_args map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    destruct (existsb attr_is_noundef pas) eqn:Enu; destruct Hsc as [-> | [iv ->]].
    + left; intro sigma.
      apply cfg_call_steps_to_ub_bind_l; change [] with ([] ++ @nil (@mc_call_event Pa)).
      eapply cfg_call_steps_to_ub_bind_r;
        [apply pure_cfg_steps_to_call_ret; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) |].
      destruct (apply_attrs_scalar_step genv sigma env pas msg (ras_width sp) (DVALUE_Base DVALUE_Poison) Hnp (or_introl eq_refl)) as [Hub_a _].
      exact (Hub_a (conj Enu eq_refl)).
    + destruct (apply_attrs_scalar_step genv default_draw_strat env pas msg (ras_width sp)
                  (DVALUE_Base (@DVALUE_I Pa (ras_width sp) iv)) Hnp (or_intror (ex_intro _ iv eq_refl)))
        as [_ Hret_a].
      destruct (IH (S arg_idx) arest rest msg Hlmap Hpenv Henv Hrr) as [Hub_r | (dvs_r & Hst_r & Hfa_r)].
      * left; intro sigma.
        change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ub_bind_r.
        -- change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind;
             [apply pure_cfg_steps_to_call_ret; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst)
             | apply pure_cfg_steps_to_call_ret; exact (Hret_a (or_intror eq_refl))].
        -- apply cfg_call_steps_to_ub_bind_l; exact (Hub_r sigma).
      * right; exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) iv) :: dvs_r); split.
        -- eapply pure_cfg_steps_bind;
             [eapply pure_cfg_steps_bind;
                [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) | exact (Hret_a (or_intror eq_refl))] |].
           eapply pure_cfg_steps_bind; [exact Hst_r | apply PCS_Ret; reflexivity].
        -- constructor; [| exact Hfa_r].
           split; [exact Hev | split; [right; exists iv; reflexivity | intro; reflexivity]].
    + destruct (apply_attrs_scalar_step genv default_draw_strat env pas msg (ras_width sp)
                  (DVALUE_Base DVALUE_Poison) Hnp (or_introl eq_refl)) as [_ Hret_a].
      destruct (IH (S arg_idx) arest rest msg Hlmap Hpenv Henv Hrr) as [Hub_r | (dvs_r & Hst_r & Hfa_r)].
      * left; intro sigma.
        change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ub_bind_r.
        -- change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind;
             [apply pure_cfg_steps_to_call_ret; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst)
             | apply pure_cfg_steps_to_call_ret; exact (Hret_a (or_introl Enu))].
        -- apply cfg_call_steps_to_ub_bind_l; exact (Hub_r sigma).
      * right; exists (DVALUE_Base DVALUE_Poison :: dvs_r); split.
        -- eapply pure_cfg_steps_bind;
             [eapply pure_cfg_steps_bind;
                [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) | exact (Hret_a (or_introl Enu))] |].
           eapply pure_cfg_steps_bind; [exact Hst_r | apply PCS_Ret; reflexivity].
        -- constructor; [| exact Hfa_r].
           split; [exact Hev | split; [left; reflexivity | intro C; discriminate C]].
    + destruct (apply_attrs_scalar_step genv default_draw_strat env pas msg (ras_width sp)
                  (DVALUE_Base (@DVALUE_I Pa (ras_width sp) iv)) Hnp (or_intror (ex_intro _ iv eq_refl)))
        as [_ Hret_a].
      destruct (IH (S arg_idx) arest rest msg Hlmap Hpenv Henv Hrr) as [Hub_r | (dvs_r & Hst_r & Hfa_r)].
      * left; intro sigma.
        change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ub_bind_r.
        -- change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind;
             [apply pure_cfg_steps_to_call_ret; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst)
             | apply pure_cfg_steps_to_call_ret; exact (Hret_a (or_intror eq_refl))].
        -- apply cfg_call_steps_to_ub_bind_l; exact (Hub_r sigma).
      * right; exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) iv) :: dvs_r); split.
        -- eapply pure_cfg_steps_bind;
             [eapply pure_cfg_steps_bind;
                [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) | exact (Hret_a (or_intror eq_refl))] |].
           eapply pure_cfg_steps_bind; [exact Hst_r | apply PCS_Ret; reflexivity].
        -- constructor; [| exact Hfa_r].
           split; [exact Hev | split; [right; exists iv; reflexivity | intro; reflexivity]].
Qed.

Lemma check_call_return_int_step {Pa : Params} (genv : raw_id -> @dvalue Pa) :
  forall sigma env fattrs ret_attrs loc args rw (v_ret : @Integers.bit_int rw),
    fattrs_call_ok fattrs = true ->
    pattrs_no_value_poison ret_attrs = true ->
    cfg_call_steps_to_ret genv sigma env
      (check_call_return (E := CFGEtop) fattrs ret_attrs None loc args
         (inr (DVALUE_Base (@DVALUE_I Pa rw v_ret))))
      [] sigma env (inr (DVALUE_Base (@DVALUE_I Pa rw v_ret))).
Proof.
  intros sigma env fattrs ret_attrs loc args rw v_ret Hfa Hra.
  unfold check_call_return, check_call_result.
  unfold fattrs_call_ok in Hfa; apply negb_true_iff in Hfa; rewrite Hfa.
  cbn [dvalue_well_defined negb andb].
  rewrite !andb_false_r.
  cbn [EOU_to_itree value_metadata_range ExtLib.Structures.Monad.ret Monad_itree].
  change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind; [apply CCSR_Ret; reflexivity |].
  destruct (apply_attrs_scalar_step genv sigma env ret_attrs (loc ++ " return value violates noundef.")%string
              rw (DVALUE_Base (@DVALUE_I Pa rw v_ret)) Hra (or_intror (ex_intro _ v_ret eq_refl)))
    as [_ Hret].
  change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind;
    [apply pure_cfg_steps_to_call_ret; exact (Hret (or_intror eq_refl)) | apply CCSR_Ret; reflexivity].
Qed.

Lemma build_call_arg_obls_from_length :
  forall cname arg_idx arch path specs ir_args mc_args64 obls,
    build_call_arg_obls_from cname arg_idx arch path specs ir_args mc_args64 = inr obls ->
    List.length ir_args = List.length specs /\
    List.length mc_args64 = List.length specs.
Proof.
  intros cname arg_idx arch path specs; revert arg_idx;
    induction specs as [| sp sr IH];
    intros arg_idx [| [[nd w] e] ir] [| m mr] obls Hbao;
    try (cbn [build_call_arg_obls_from build_call_arg_obls_acc] in Hbao; discriminate Hbao);
    [split; reflexivity |].
  rewrite build_call_arg_obls_from_cons in Hbao.
  destruct (Pos.eqb w (ras_width sp)); [| discriminate].
  destruct (build_call_arg_cmp cname arg_idx arch path sp w e m); [discriminate |].
  destruct (build_call_arg_obls_from cname (S arg_idx) arch path sr ir mr) as [| rest] eqn:Er;
    cbn [mcc_sum_map] in Hbao; [discriminate |].
  destruct (IH _ _ _ _ Er) as [H1 H2]; cbn; split; f_equal; assumption.
Qed.

Lemma build_call_arg_obls_length :
  forall cname arch path specs ir_args mc_args64 obls,
    build_call_arg_obls cname arch path specs ir_args mc_args64 = inr obls ->
    List.length ir_args = List.length specs /\
    List.length mc_args64 = List.length specs.
Proof.
  intros cname; exact (build_call_arg_obls_from_length cname 0%nat).
Qed.

Lemma rv_supported_arg_width_lt32 : forall w,
  rv_supported_arg_width w = true ->
  (w =? 64)%positive = false ->
  (w =? 32)%positive = false ->
  (w <? 32)%positive = true.
Proof.
  intros w Hs E64 E32; unfold rv_supported_arg_width in Hs.
  do 8 (destruct w as [w | w |]; try discriminate Hs; try discriminate E64; try discriminate E32; try reflexivity).
Qed.

Lemma rv_supported_to_is_supported : forall w,
  rv_supported_arg_width w = true -> is_supported_bit_width w = true.
Proof.
  intro w; unfold rv_supported_arg_width, is_supported_bit_width.
  do 8 (destruct w as [w | w |]; try discriminate; try reflexivity).
Qed.

Lemma build_call_arg_obls_rv64_matches {Pa : Params} :
  forall cname (penv : param_env Pa) (path : list (bool * cert_expr)) specs ir_args mc_args64 obls arg_vals vs_ir rf,
    (forall (b : bool) c, In (b, c) path ->
       eval_closed_cert_expr penv dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv dummy_freeze_oracle None false) obls ->
    build_call_arg_obls cname EA_Riscv64 path specs ir_args mc_args64 = inr obls ->
    Forall rv_valid_arg_spec specs ->
    NoDup (List.map ras_name specs) ->
    Forall2 (fun '(need_def, w, ce) dv =>
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv /\
      (need_def = false -> dvalue_well_defined dv = true)) ir_args vs_ir ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv dummy_freeze_oracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))) mc_args64 arg_vals ->
    arg_vals = List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf) (seq 0 (List.length specs)) ->
    rv_rf_matches_args (build_param_env (List.map ras_name specs) vs_ir) specs rf /\
    List.length vs_ir = List.length specs.
Proof.
  intros cname penv path specs ir_args mc_args64 obls arg_vals vs_ir rf
         Hpath Hobls Hbao Hvs Hnd Hfir Hfmc Harg_eq.
  assert (Hlen : List.length vs_ir = List.length specs)
    by (destruct (build_call_arg_obls_length _ _ _ _ _ _ _ Hbao) as [Hl1 _];
        pose proof (Forall2_length Hfir); congruence).
  split; [| exact Hlen].
  assert (Hitem : forall k sp v_mc,
    nth_error specs k = Some sp ->
    nth_error arg_vals k = Some v_mc ->
    exists v : @Integers.bit_int (ras_width sp),
      nth_error vs_ir k = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      v_mc =
        (if Pos.eqb (ras_width sp) 64%positive then
           @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
         else
           match ras_ext sp with
           | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
           | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
           end)).
  { clear Hnd Hlen Harg_eq.
    unfold build_call_arg_obls in Hbao; revert Hbao; generalize 0%nat as arg_idx.
    revert ir_args mc_args64 obls arg_vals vs_ir Hobls Hvs Hfir Hfmc.
    induction specs as [| sp0 srest IH]; intros ir_args mc_args64 ob0 avs vs0 Hob0 Hvs0 Hfi0 Hfm0 arg_idx Hb0 k sp v_mc Hsp0_n Hav_n;
      try (destruct k; discriminate Hsp0_n);
      destruct ir_args as [| [[nd0 w0] e0] irest]; destruct mc_args64 as [| m0 mrest];
      try (cbn [build_call_arg_obls_from build_call_arg_obls_acc] in Hb0; discriminate Hb0).
    rewrite build_call_arg_obls_from_cons in Hb0; cbn [build_call_arg_cmp] in Hb0.
    destruct (Pos.eqb w0 (ras_width sp0)) eqn:Epw; [apply Pos.eqb_eq in Epw; subst w0 | discriminate Hb0].
    destruct (build_call_arg_obls_from cname (S arg_idx) EA_Riscv64 path srest irest mrest) as [| rest_o] eqn:Erest;
      cbn [mcc_sum_map] in Hb0; [discriminate Hb0 |].
    inversion Hb0; subst ob0; clear Hb0.
    destruct avs as [| vm0 av_r]; [inversion Hfm0 |].
    destruct vs0 as [| dv0 vs_r]; [inversion Hfi0 |].
    inversion Hvs0 as [| ? ? Hsp0_v Hvs_r]; subst.
    inversion Hfi0 as [| ? ? ? ? Hp0 Hfi_r]; subst; destruct Hp0 as [Hev0 [Hsc0 Hnd0]].
    inversion Hfm0 as [| ? ? ? ? Hm0 Hfm_r]; subst.
    rewrite Forall_app in Hob0; destruct Hob0 as [Hrest_o Hhead0].
    assert (Hc0 : mc_obl_holds penv dummy_freeze_oracle None false
                    (MLO_Refine false path 64%positive (build_rv_call_arg_expr (ras_width sp0) (ras_ext sp0) e0) m0)).
    { destruct nd0; [inversion Hhead0 as [| ? ? _ Htl]; inversion Htl; assumption | inversion Hhead0; assumption]. }
    destruct k as [| k']; cbn in Hsp0_n, Hav_n.
    - inversion Hsp0_n; subst sp0; inversion Hav_n; subst vm0; clear Hsp0_n Hav_n.
      assert (Hwd0 : dvalue_well_defined dv0 = true).
      { destruct nd0; [| exact (Hnd0 eq_refl)].
        inversion Hhead0 as [| ? ? Hd _]; subst.
        pose proof (Hd eq_refl ltac:(discriminate) Hpath) as [v Hv1].
        unfold eval_closed_cert_expr in *; rewrite Hev0 in Hv1; inversion Hv1; reflexivity. }
      destruct Hsc0 as [Hbad | [iv ->]]; [rewrite Hbad in Hwd0; discriminate Hwd0 |].
      pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href.
      unfold refine_eou_dvalue, dvalue_refines, build_rv_call_arg_expr in Href.
      exists iv; split; [reflexivity |].
      destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
      + apply Pos.eqb_eq in Ew64; generalize iv Hev0 Href; rewrite Ew64; intros iv64 Hev64 Href64.
        rewrite Hev64, Hm0 in Href64; cbn in Href64.
        destruct Href64 as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; symmetry in Heq; subst; rewrite (@Integers.repr_unsigned 64%positive); reflexivity].
      + assert (Hltb : (ras_width sp <? 64)%positive = true).
        { apply Pos.ltb_lt; unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _].
          apply rv_supported_arg_width_lt64 in Ew64; [apply Pos.ltb_lt; exact Ew64 | exact Hsup]. }
        destruct (ras_ext sp).
        * erewrite eval_ce_sext in Href by (first [exact Hltb | exact Hev0]).
          rewrite Hm0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
        * erewrite eval_ce_sext in Href by (first [exact Hltb | exact Hev0]).
          rewrite Hm0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
        * erewrite eval_ce_zext in Href by (first [exact Hltb | exact Hev0]).
          rewrite Hm0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
    - exact (IH irest mrest rest_o av_r vs_r Hrest_o Hvs_r Hfi_r Hfm_r (S arg_idx) Erest k' sp v_mc Hsp0_n Hav_n). }
  intros k sp Hkl Hsp_n.
  assert (Hnth_av : nth_error arg_vals k = Some (rv_read_reg (10%N + N.of_nat k) rf)).
  { rewrite Harg_eq, nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hkl as Hltb_k; rewrite Hltb_k; cbn [option_map Nat.add]; reflexivity. }
  destruct (Hitem k sp _ Hsp_n Hnth_av) as (v & Hvs_n & Hvmc).
  exists v; split; [| rewrite <- Hvmc; reflexivity].
  destruct (build_param_env_nth (List.map ras_name specs) vs_ir k (ras_name sp) Hnd) as [dv [Hdv Hbp]].
  - rewrite List.length_map; symmetry; exact Hlen.
  - erewrite nth_error_map, Hsp_n; reflexivity.
  - rewrite Hvs_n in Hdv; inversion Hdv; subst dv; exact Hbp.
Qed.

Lemma build_call_arg_obls_a64_matches {Pa : Params} :
  forall cname (penv : param_env Pa) (path : list (bool * cert_expr)) specs ir_args mc_args64 obls arg_vals vs_ir rf,
    (forall (b : bool) c, In (b, c) path ->
       eval_closed_cert_expr penv dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv dummy_freeze_oracle None false) obls ->
    build_call_arg_obls cname EA_AArch64 path specs ir_args mc_args64 = inr obls ->
    Forall rv_valid_arg_spec specs ->
    NoDup (List.map ras_name specs) ->
    Forall2 (fun '(need_def, w, ce) dv =>
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv /\
      (need_def = false -> dvalue_well_defined dv = true)) ir_args vs_ir ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv dummy_freeze_oracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))) mc_args64 arg_vals ->
    arg_vals = List.map (fun j => a64_read_reg (N.of_nat j) rf) (seq 0 (List.length specs)) ->
    a64_rf_matches_args (build_param_env (List.map ras_name specs) vs_ir) specs rf /\
    List.length vs_ir = List.length specs.
Proof.
  intros cname penv path specs ir_args mc_args64 obls arg_vals vs_ir rf
         Hpath Hobls Hbao Hvs Hnd Hfir Hfmc Harg_eq.
  assert (Hlen : List.length vs_ir = List.length specs)
    by (destruct (build_call_arg_obls_length _ _ _ _ _ _ _ Hbao) as [Hl1 _];
        pose proof (Forall2_length Hfir); congruence).
  split; [| exact Hlen].
  assert (Hitem : forall k sp v_mc,
    nth_error specs k = Some sp ->
    nth_error arg_vals k = Some v_mc ->
    exists v : @Integers.bit_int (ras_width sp),
      nth_error vs_ir k = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
      | true, RAE_None =>
          v_mc = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
      | false, RAE_None =>
          @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive v_mc) = v
      | false, RAE_SignExt =>
          @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
          @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
      | false, RAE_ZeroExt =>
          @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
          @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
      | _, _ => False
      end).
  { clear Hnd Hlen Harg_eq.
    unfold build_call_arg_obls in Hbao; revert Hbao; generalize 0%nat as arg_idx.
    revert ir_args mc_args64 obls arg_vals vs_ir Hobls Hvs Hfir Hfmc.
    induction specs as [| sp0 srest IH]; intros ir_args mc_args64 ob0 avs vs0 Hob0 Hvs0 Hfi0 Hfm0 arg_idx Hb0 k sp v_mc Hsp0_n Hav_n;
      try (destruct k; discriminate Hsp0_n);
      destruct ir_args as [| [[nd0 w0] e0] irest]; destruct mc_args64 as [| m0 mrest];
      try (cbn [build_call_arg_obls_from build_call_arg_obls_acc] in Hb0; discriminate Hb0).
    rewrite build_call_arg_obls_from_cons in Hb0; cbn [build_call_arg_cmp] in Hb0.
    destruct (Pos.eqb w0 (ras_width sp0)) eqn:Epw; [apply Pos.eqb_eq in Epw; subst w0 | discriminate Hb0].
    match type of Hb0 with
    | context [match ?x with inl _ => _ | inr _ => _ end] => destruct x as [| cmp0] eqn:Ecmp0; [discriminate Hb0 |]
    end.
    destruct (build_call_arg_obls_from cname (S arg_idx) EA_AArch64 path srest irest mrest) as [| rest_o] eqn:Erest;
      cbn [mcc_sum_map] in Hb0; [discriminate Hb0 |].
    inversion Hb0; subst ob0; clear Hb0.
    destruct avs as [| vm0 av_r]; [inversion Hfm0 |].
    destruct vs0 as [| dv0 vs_r]; [inversion Hfi0 |].
    inversion Hvs0 as [| ? ? Hsp0_v Hvs_r]; subst.
    inversion Hfi0 as [| ? ? ? ? Hp0 Hfi_r]; subst; destruct Hp0 as [Hev0 [Hsc0 Hnd0]].
    inversion Hfm0 as [| ? ? ? ? Hm0 Hfm_r]; subst.
    rewrite Forall_app in Hob0; destruct Hob0 as [Hrest_o Hhead0].
    assert (Hcmp0 : Forall (mc_obl_holds penv dummy_freeze_oracle None false) [cmp0])
      by (destruct nd0; [inversion Hhead0; assumption | exact Hhead0]).
    destruct k as [| k']; cbn in Hsp0_n, Hav_n.
    - inversion Hsp0_n; subst sp0; inversion Hav_n; subst vm0; clear Hsp0_n Hav_n.
      assert (Hwd0 : dvalue_well_defined dv0 = true).
      { destruct nd0; [| exact (Hnd0 eq_refl)].
        inversion Hhead0 as [| ? ? Hd _]; subst.
        pose proof (Hd eq_refl ltac:(discriminate) Hpath) as [v Hv1].
        unfold eval_closed_cert_expr in *; rewrite Hev0 in Hv1; inversion Hv1; reflexivity. }
      destruct Hsc0 as [Hbad | [iv ->]]; [rewrite Hbad in Hwd0; discriminate Hwd0 |].
      exists iv; split; [reflexivity |].
      destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
      + destruct (ras_ext sp); inversion Ecmp0; subst cmp0; clear Ecmp0.
        inversion Hcmp0 as [| ? ? Hc0 _]; subst.
        pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href.
        unfold refine_eou_dvalue, dvalue_refines in Href.
        apply Pos.eqb_eq in Ew64; generalize iv Hev0 Href; rewrite Ew64; intros iv64 Hev64 Href64; rewrite Hev64, Hm0 in Href64.
        cbn in Href64; destruct Href64 as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; symmetry in Heq; subst].
        rewrite (@Integers.repr_unsigned 64%positive); reflexivity.
      + assert (Hltb : (ras_width sp <? 64)%positive = true).
        { apply Pos.ltb_lt; unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _].
          apply rv_supported_arg_width_lt64 in Ew64; [apply Pos.ltb_lt; exact Ew64 | exact Hsup]. }
        destruct (ras_ext sp) eqn:Eext; inversion Ecmp0; subst cmp0; clear Ecmp0;
          inversion Hcmp0 as [| ? ? Hc0 _]; subst;
          pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href;
          unfold refine_eou_dvalue, dvalue_refines in Href.
        * erewrite eval_ce_trunc in Href by (first [exact Hltb | exact Hm0]).
          rewrite Hev0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
        * erewrite eval_ce_trunc in Href by (first [reflexivity | exact Hm0]).
          destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
          -- apply Pos.eqb_eq in Ew32; generalize iv Href Hev0; rewrite Ew32; intros iv' Href' Hev0'.
             rewrite Hev0' in Href'; cbn in Href'; destruct Href' as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; subst iv'].
             rewrite (@Integers.repr_signed 32%positive); reflexivity.
          -- assert (Hlt32 : (ras_width sp <? 32)%positive = true)
               by (unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _];
                   exact (rv_supported_arg_width_lt32 _ Hsup Ew64 Ew32)).
             erewrite eval_ce_sext in Href by (first [exact Hlt32 | exact Hev0]).
             cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
        * erewrite eval_ce_trunc in Href by (first [reflexivity | exact Hm0]).
          destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
          -- apply Pos.eqb_eq in Ew32; generalize iv Href Hev0; rewrite Ew32; intros iv' Href' Hev0'.
             rewrite Hev0' in Href'; cbn in Href'; destruct Href' as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; subst iv'].
             rewrite (@Integers.repr_unsigned 32%positive); reflexivity.
          -- assert (Hlt32 : (ras_width sp <? 32)%positive = true)
               by (unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _];
                   exact (rv_supported_arg_width_lt32 _ Hsup Ew64 Ew32)).
             erewrite eval_ce_zext in Href by (first [exact Hlt32 | exact Hev0]).
             cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
    - exact (IH irest mrest rest_o av_r vs_r Hrest_o Hvs_r Hfi_r Hfm_r (S arg_idx) Erest k' sp v_mc Hsp0_n Hav_n). }
  intros k sp Hkl Hsp_n.
  assert (Hnth_av : nth_error arg_vals k = Some (a64_read_reg (N.of_nat k) rf)).
  { rewrite Harg_eq, nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hkl as Hltb_k; rewrite Hltb_k; cbn [option_map Nat.add]; reflexivity. }
  destruct (Hitem k sp _ Hsp_n Hnth_av) as (v & Hvs_n & Hvmc).
  exists v; split; [| exact Hvmc].
  destruct (build_param_env_nth (List.map ras_name specs) vs_ir k (ras_name sp) Hnd) as [dv [Hdv Hbp]].
  - rewrite List.length_map; symmetry; exact Hlen.
  - erewrite nth_error_map, Hsp_n; reflexivity.
  - rewrite Hvs_n in Hdv; inversion Hdv; subst dv; exact Hbp.
Qed.

Section IrTreeDenote.
  Context {Pa : Params}.

  Fixpoint ir_tree_denotes
    (genv : raw_id -> @dvalue Pa) (penv : param_env Pa) (ret_w : positive)
    (env : rmap (@dvalue Pa)) (it_prog : @CFGtop Pa (@dvalue Pa)) (t : ir_call_tree)
    {struct t} : Prop :=
    match t with
    | ICT_UB =>
        forall sigma, cfg_call_steps_to_ub genv sigma env it_prog []
    | ICT_Ret rw ret_e =>
        rw = ret_w /\
        exists env_out dv_ir,
          eval_closed_cert_expr penv dummy_freeze_oracle ret_e = raise_ret dv_ir /\
          wf_scalar_dvalue ret_w dv_ir /\
          forall sigma, cfg_call_steps_to_ret genv sigma env it_prog [] sigma env_out dv_ir
    | ICT_Branch cond dt df =>
        (eval_closed_cert_expr penv dummy_freeze_oracle cond = raise_ret (DVALUE_Base DVALUE_Poison) /\
         forall sigma, cfg_call_steps_to_ub genv sigma env it_prog []) \/
        (exists b : bool,
           eval_closed_cert_expr penv dummy_freeze_oracle cond =
             raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
           ir_tree_denotes genv penv ret_w env it_prog (if b then dt else df))
    | ICT_Call cname arg_es rw rv cont =>
        (forall sigma, cfg_call_steps_to_ub genv sigma env it_prog []) \/
        exists dvs,
          Forall2 (fun '(nd, w, ce) dv =>
            eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
            wf_scalar_dvalue w dv /\
            (nd = false -> dvalue_well_defined dv = true)) arg_es dvs /\
          forall (v_ret : @Integers.bit_int rw),
            penv rv = Some (DVALUE_Base (@DVALUE_I Pa rw v_ret)) ->
            let dv_ret := DVALUE_Base (@DVALUE_I Pa rw v_ret) in
            exists env1 t1,
              (forall sigma tr_r s' env' r,
                 cfg_call_steps_to_ret genv sigma env1 t1 tr_r s' env' r ->
                 cfg_call_steps_to_ret genv sigma env it_prog ((cname, dvs, dv_ret) :: tr_r) s' env' r) /\
              (forall sigma tr_r,
                 cfg_call_steps_to_ub genv sigma env1 t1 tr_r ->
                 cfg_call_steps_to_ub genv sigma env it_prog ((cname, dvs, dv_ret) :: tr_r)) /\
              ir_tree_denotes genv penv ret_w env1 t1 cont
    end.

  Lemma ir_tree_denotes_prepend_tau_pure :
    forall genv penv ret_w t env0 env1 t0 t1,
      (forall sigma tr s' env' r,
         cfg_call_steps_to_ret genv sigma env1 t1 tr s' env' r ->
         cfg_call_steps_to_ret genv sigma env0 t0 tr s' env' r) ->
      (forall sigma tr,
         cfg_call_steps_to_ub genv sigma env1 t1 tr ->
         cfg_call_steps_to_ub genv sigma env0 t0 tr) ->
      ir_tree_denotes genv penv ret_w env1 t1 t ->
      ir_tree_denotes genv penv ret_w env0 t0 t.
  Proof.
    intros genv penv ret_w t; induction t as [rw ret_e | | cond dt IHt df IHf | cname aes rw rv cont IH];
      intros env0 env1 t0 t1 Hret Hub Hd; cbn [ir_tree_denotes] in *.
    - destruct Hd as [-> (env_out & dv & Hev & Hsc & Hst)]; split; [reflexivity |].
      exists env_out, dv; repeat split; try assumption; intro sigma; exact (Hret _ _ _ _ _ (Hst sigma)).
    - intro sigma; exact (Hub sigma [] (Hd sigma)).
    - destruct Hd as [[Hp Hubc] | [b [Hev Hb]]].
      + left; split; [exact Hp | intro sigma; exact (Hub sigma [] (Hubc sigma))].
      + right; exists b; split; [exact Hev |].
        destruct b; [exact (IHt _ _ _ _ Hret Hub Hb) | exact (IHf _ _ _ _ Hret Hub Hb)].
    - destruct Hd as [Hubc | (dvs & Hfa & Hk)].
      + left; intro sigma; exact (Hub sigma [] (Hubc sigma)).
      + right; exists dvs; split; [exact Hfa |].
        intros v_ret Hrv; destruct (Hk v_ret Hrv) as (env2 & t2 & Hret2 & Hub2 & Hd2).
        exists env2, t2; repeat split; try assumption.
        * intros sigma tr_r s' env' r Hs; exact (Hret _ _ _ _ _ (Hret2 _ _ _ _ _ Hs)).
        * intros sigma tr_r Hs; exact (Hub _ _ (Hub2 _ _ Hs)).
  Qed.

  Lemma pure_cfg_steps_prepend_bind {R S : Type} :
    forall genv env0 env1 (p : @CFGtop Pa R) (k : R -> @CFGtop Pa S) x,
      pure_cfg_steps env0 p env1 x ->
      (forall sigma tr s' env' r,
         cfg_call_steps_to_ret genv sigma env1 (k x) tr s' env' r ->
         cfg_call_steps_to_ret genv sigma env0 (ITree.bind p k) tr s' env' r) /\
      (forall sigma tr,
         cfg_call_steps_to_ub genv sigma env1 (k x) tr ->
         cfg_call_steps_to_ub genv sigma env0 (ITree.bind p k) tr).
  Proof.
    intros genv env0 env1 p k x Hp; split.
    - intros sigma tr s' env' r Hs; change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_bind;
        [exact (pure_cfg_steps_to_call_ret genv sigma _ _ _ _ Hp) | exact Hs].
    - intros sigma tr Hs; change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_bind_r;
        [exact (pure_cfg_steps_to_call_ret genv sigma _ _ _ _ Hp) | exact Hs].
  Qed.

  Inductive cfg_bind_ctxt : Type -> Type -> Type :=
  | CBC_Id {A : Type} : cfg_bind_ctxt A A
  | CBC_Bind {A B C : Type} : (A -> @CFGtop Pa B) -> cfg_bind_ctxt B C -> cfg_bind_ctxt A C.

  Fixpoint apply_cfg_ctxt {A B : Type} (ctx : cfg_bind_ctxt A B) (t : @CFGtop Pa A) : @CFGtop Pa B :=
    match ctx in cfg_bind_ctxt X Y return @CFGtop Pa X -> @CFGtop Pa Y with
    | @CBC_Id _ => fun t0 => t0
    | @CBC_Bind _ _ _ k rest => fun t0 => apply_cfg_ctxt rest (ITree.bind t0 k)
    end t.

  Lemma apply_cfg_ctxt_obs :
    forall A B (ctx : cfg_bind_ctxt A B) (t1 t2 : @CFGtop Pa A),
      observe t1 = observe t2 ->
      observe (apply_cfg_ctxt ctx t1) = observe (apply_cfg_ctxt ctx t2).
  Proof.
    intros A B ctx; induction ctx as [A | A B C k rest IH]; intros t1 t2 Hobs; cbn [apply_cfg_ctxt].
    - exact Hobs.
    - apply IH; rewrite !observe_bind, Hobs; reflexivity.
  Qed.

  Lemma apply_cfg_ctxt_tau :
    forall A B (ctx : cfg_bind_ctxt A B) (p p' : @CFGtop Pa A),
      observe p = TauF p' ->
      observe (apply_cfg_ctxt ctx p) = TauF (apply_cfg_ctxt ctx p').
  Proof.
    intros A B ctx; induction ctx as [A | A B C k rest IH]; intros p p' H; cbn [apply_cfg_ctxt];
      [exact H | apply IH; rewrite observe_bind, H; reflexivity].
  Qed.

  Lemma apply_cfg_ctxt_vis :
    forall A B X (ctx : cfg_bind_ctxt A B) (p : @CFGtop Pa A) (e : CFGEtop X) (k : X -> @CFGtop Pa A),
      observe p = VisF e k ->
      observe (apply_cfg_ctxt ctx p) = VisF e (fun a => apply_cfg_ctxt ctx (k a)).
  Proof.
    intros A B X ctx; revert X; induction ctx as [A | A B C k0 rest IH]; intros X p e k H; cbn [apply_cfg_ctxt];
      [exact H | apply IH; rewrite observe_bind, H; reflexivity].
  Qed.

  Lemma cfg_call_steps_to_ret_ctxt_bind {R S T : Type} (genv : raw_id -> @dvalue Pa) :
    forall (ctx : cfg_bind_ctxt S T) s0 env0 (p : @CFGtop Pa R) tr0 s1 env1 x
           (k : R -> @CFGtop Pa S) tr1 s2 env2 z,
      cfg_call_steps_to_ret genv s0 env0 p tr0 s1 env1 x ->
      cfg_call_steps_to_ret genv s1 env1 (apply_cfg_ctxt ctx (k x)) tr1 s2 env2 z ->
      cfg_call_steps_to_ret genv s0 env0 (apply_cfg_ctxt ctx (ITree.bind p k)) (tr0 ++ tr1) s2 env2 z.
  Proof.
    intros ctx s0 env0 p tr0 s1 env1 x k tr1 s2 env2 z Hp; revert tr1 s2 env2 z;
      induction Hp; intros tr1 s2' env2' z Hcont; cbn [app] in *.
    - eapply cfg_call_steps_to_ret_obs;
        [symmetry; apply apply_cfg_ctxt_obs; rewrite observe_bind, H; reflexivity | exact Hcont].
    - eapply CCSR_Tau;
        [apply apply_cfg_ctxt_tau; rewrite observe_bind, H; reflexivity | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_LocalRead;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_LocalWrite;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_Draw;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_PureIntrinsic;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact H1 | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_GlobalRead;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_Call;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ _ _ _ Hcont)].
  Qed.

  Lemma cfg_call_steps_to_ub_ctxt_bind_r {R S T : Type} (genv : raw_id -> @dvalue Pa) :
    forall (ctx : cfg_bind_ctxt S T) s0 env0 (p : @CFGtop Pa R) tr0 s1 env1 x
           (k : R -> @CFGtop Pa S) tr1,
      cfg_call_steps_to_ret genv s0 env0 p tr0 s1 env1 x ->
      cfg_call_steps_to_ub genv s1 env1 (apply_cfg_ctxt ctx (k x)) tr1 ->
      cfg_call_steps_to_ub genv s0 env0 (apply_cfg_ctxt ctx (ITree.bind p k)) (tr0 ++ tr1).
  Proof.
    intros ctx s0 env0 p tr0 s1 env1 x k tr1 Hp; revert tr1;
      induction Hp; intros tr1 Hcont; cbn [app] in *.
    - eapply cfg_call_steps_to_ub_obs;
        [symmetry; apply apply_cfg_ctxt_obs; rewrite observe_bind, H; reflexivity | exact Hcont].
    - eapply CCSU_Tau;
        [apply apply_cfg_ctxt_tau; rewrite observe_bind, H; reflexivity | exact (IHHp _ Hcont)].
    - eapply CCSU_LocalRead;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ Hcont)].
    - eapply CCSU_LocalWrite;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact (IHHp _ Hcont)].
    - eapply CCSU_Draw;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ Hcont)].
    - eapply CCSU_PureIntrinsic;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact H1 | exact (IHHp _ Hcont)].
    - eapply CCSU_GlobalRead;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact (IHHp _ Hcont)].
    - eapply CCSU_Call;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ Hcont)].
  Qed.

  Lemma cfg_call_steps_to_ub_ctxt {R T : Type} (genv : raw_id -> @dvalue Pa) :
    forall (ctx : cfg_bind_ctxt R T) s0 env0 (p : @CFGtop Pa R) tr,
      cfg_call_steps_to_ub genv s0 env0 p tr ->
      cfg_call_steps_to_ub genv s0 env0 (apply_cfg_ctxt ctx p) tr.
  Proof.
    intros ctx s0 env0 p tr Hub; induction Hub.
    - eapply CCSU_UB; apply apply_cfg_ctxt_vis; exact H.
    - eapply CCSU_Tau; [apply apply_cfg_ctxt_tau; exact H | exact IHHub].
    - eapply CCSU_LocalRead; [apply apply_cfg_ctxt_vis; exact H | exact H0 | exact IHHub].
    - eapply CCSU_LocalWrite; [apply apply_cfg_ctxt_vis; exact H | exact IHHub].
    - eapply CCSU_Draw; [apply apply_cfg_ctxt_vis; exact H | exact H0 | exact IHHub].
    - eapply CCSU_PureIntrinsic; [apply apply_cfg_ctxt_vis; exact H | exact H0 | exact H1 | exact IHHub].
    - eapply CCSU_GlobalRead; [apply apply_cfg_ctxt_vis; exact H | exact IHHub].
    - eapply CCSU_Call; [apply apply_cfg_ctxt_vis; exact H | exact H0 | exact IHHub].
  Qed.

End IrTreeDenote.

Lemma reify_ir_code_calls_exec {Pa : Params} :
  forall cur_bid (genv : raw_id -> @dvalue Pa) (penv : param_env Pa)
         callees c cid allowed lmap env ret_w k_end t
         (ctx : cfg_bind_ctxt unit (@dvalue Pa)),
    wf_pure_lmap allowed lmap ->
    wf_param_env_for allowed penv ->
    lmap_matches_env penv lmap env ->
    (forall cid' allowed' lmap' env' t',
       incl allowed allowed' ->
       wf_pure_lmap allowed' lmap' ->
       wf_param_env_for allowed' penv ->
       lmap_matches_env penv lmap' env' ->
       k_end cid' lmap' = inr t' ->
       ir_tree_denotes genv penv ret_w env' (apply_cfg_ctxt ctx (Ret tt)) t') ->
    reify_ir_code_calls cur_bid callees c cid lmap k_end = inr t ->
    ir_tree_denotes genv penv ret_w env (apply_cfg_ctxt ctx (denote_code c None)) t.
Proof.
  intros cur_bid genv penv callees c; induction c as [| [[iid ins] md] rest IH];
    intros cid allowed lmap env ret_w k_end t ctx Hlmap Hpenv Henv Hk Hrc;
    cbn [reify_ir_code_calls] in Hrc.
  - eapply ir_tree_denotes_prepend_tau_pure with (env1 := env) (t1 := apply_cfg_ctxt ctx (Ret tt)).
    + intros sigma tr s' env' r Hs; unfold denote_code; cbn; eapply cfg_call_steps_to_ret_obs;
        [symmetry; apply apply_cfg_ctxt_obs; reflexivity | exact Hs].
    + intros sigma tr Hs; unfold denote_code; cbn; eapply cfg_call_steps_to_ub_obs;
        [symmetry; apply apply_cfg_ctxt_obs; reflexivity | exact Hs].
    + exact (Hk cid allowed lmap env t (incl_refl _) Hlmap Hpenv Henv Hrc).
  - destruct iid as [id | vid].
    + destruct ins; try discriminate Hrc.
      * destruct (reify_pure_exp lmap None op) as [[w ce] |] eqn:Ere; [| discriminate Hrc].
        destruct (ub_free_expr ce) eqn:Hub; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (expr_has_freeze ce) eqn:Hnf; [discriminate Hrc |].
        destruct (reify_pure_exp_typing op allowed lmap None w ce Hlmap Ere) as (_ & Hwt & Hbw & Hlf & Hfv).
        destruct (eval_reified_pure_exp_no_ub allowed penv lmap env op None w ce Hlmap Hpenv Henv Ere Hub Hnf)
          as (dv & Hev & Hsc & Hst).
        pose proof (lmap_matches_env_add penv lmap env id w ce dv Henv Hev Hsc) as Henv1.
        pose proof (wf_pure_lmap_add allowed lmap id w ce Hlmap Hwt Hbw Hlf Hfv) as Hlmap1.
        specialize (IH cid allowed (RM.add id (w, ce) lmap) (RM.add id dv env) ret_w k_end t ctx
                      Hlmap1 Hpenv Henv1 Hk Hrc).
        assert (Hpref : pure_cfg_steps env (denote_instr (IId id, INSTR_Op op, md) None) (RM.add id dv env) tt).
        { cbn [denote_instr]; unfold denote_exp'.
          eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) |].
          eapply pure_cfg_steps_bind; [apply pure_cfg_steps_lwrite | apply PCS_Ret; reflexivity]. }
        eapply ir_tree_denotes_prepend_tau_pure with (env1 := RM.add id dv env)
          (t1 := apply_cfg_ctxt ctx (denote_code rest None)); [| | exact IH].
        -- intros sigma tr s' env' r Hs; unfold denote_code; cbn [loop_monad].
           change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind;
             [apply pure_cfg_steps_to_call_ret; exact Hpref | exact Hs].
        -- intros sigma tr Hs; unfold denote_code; cbn [loop_monad].
           change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r;
             [apply pure_cfg_steps_to_call_ret; exact Hpref | exact Hs].
      * destruct (match_pure_int_intrinsic_call (INSTR_Call fn args anns obs)) as [pic |] eqn:Epic.
        -- pose proof (match_pure_int_intrinsic_call_inv _ _ Epic) as Hinv.
           destruct pic as [op w a0 a1 | w a0 flag]; destruct fn as [dt_fn fn_e].
           ++ destruct (match metadata_range md with None => true | Some _ => false end) eqn:Emr; cbn [negb] in Hrc; [| discriminate Hrc].
              assert (Hmr_none : metadata_range md = None) by (destruct (metadata_range md); [discriminate | reflexivity]).
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a0) as [[wa ca] |] eqn:Ea0; [| discriminate Hrc].
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a1) as [[wb cb] |] eqn:Ea1; [| discriminate Hrc].
              destruct (ub_free_expr ca && ub_free_expr cb) eqn:Eub; cbn [negb] in Hrc; [| discriminate Hrc].
              destruct (expr_has_freeze ca || expr_has_freeze cb) eqn:Efr; [discriminate Hrc |].
              apply andb_true_iff in Eub as [Huba Hubb].
              apply orb_false_iff in Efr as [Hnfa Hnfb].
              destruct (reify_pure_exp_typing a0 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Hlmap Ea0)
                as (_ & Hwt0 & Hbw0 & Hlf0 & Hfv0).
              pose proof (reify_pure_exp_top_width a0 lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Ea0) as Htw0.
              cbn [check_opt_int_width] in Htw0; apply Pos.eqb_eq in Htw0; subst wa; rewrite Htw0 in Ea0.
              destruct (reify_pure_exp_typing a1 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wb cb Hlmap Ea1)
                as (_ & Hwt1 & Hbw1 & Hlf1 & Hfv1).
              pose proof (reify_pure_exp_top_width a1 lmap (Some (DTYPE_Base (DTYPE_I w))) wb cb Ea1) as Htw1.
              cbn [check_opt_int_width] in Htw1; apply Pos.eqb_eq in Htw1; subst wb; rewrite Htw1 in Ea1.
              destruct (eval_reified_pure_exp_no_ub allowed penv lmap env a0 (Some (DTYPE_Base (DTYPE_I w))) w ca Hlmap Hpenv Henv Ea0 Huba Hnfa)
                as (dv0 & Hev0 & Hsc0 & Hst0).
              destruct (eval_reified_pure_exp_no_ub allowed penv lmap env a1 (Some (DTYPE_Base (DTYPE_I w))) w cb Hlmap Hpenv Henv Ea1 Hubb Hnfb)
                as (dv1 & Hev1 & Hsc1 & Hst1).
              destruct fn_e; try contradiction Hinv; destruct id0 as [[fname | | ] | ?]; try contradiction Hinv;
                destruct obs; try contradiction Hinv;
                destruct Hinv as (Hdt & Hpars & Hnop & Hargs & Hfa & Hra).
              destruct (pure_int_intrinsic_binop_eval_helpers op w ca cb penv dummy_freeze_oracle dv0 dv1 Hnop Hsc0 Hsc1 Hev0 Hev1)
                as (dv_out & Hpi & Hev_out & Hsc_out).
              destruct (lower_pure_int_intrinsic_binop_typing op w ca cb
                          Hwt0 Htw0 Hlf0 (expr_has_freeze_false_collect_keys _ Hnfa)
                          Hwt1 Htw1 Hlf1 (expr_has_freeze_false_collect_keys _ Hnfb))
                as (Hwt & Hbw & Hlf & _ & Hfv_sub).
              assert (Hfv : incl (collect_free_vars [] (lower_pure_int_intrinsic_binop op w ca cb)) allowed)
                by (intros x Hx; apply Hfv_sub, in_app_iff in Hx as [Hx | Hx]; [exact (Hfv0 _ Hx) | exact (Hfv1 _ Hx)]).
              pose proof (wf_pure_lmap_add allowed lmap id w (lower_pure_int_intrinsic_binop op w ca cb) Hlmap Hwt Hbw Hlf Hfv) as Hlmap1.
              pose proof (lmap_matches_env_add penv lmap env id w (lower_pure_int_intrinsic_binop op w ca cb) dv_out Henv Hev_out Hsc_out) as Henv1.
              specialize (IH cid allowed (RM.add id (w, lower_pure_int_intrinsic_binop op w ca cb) lmap)
                            (RM.add id dv_out env) ret_w k_end t ctx Hlmap1 Hpenv Henv1 Hk Hrc).
              eapply ir_tree_denotes_prepend_tau_pure with (env1 := RM.add id dv_out env)
                (t1 := apply_cfg_ctxt ctx (denote_code rest None)); [| | exact IH].
               ** intros sigma tr s' env' r Hs; unfold denote_code; cbn [loop_monad].
                  change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind;
                    [apply cfg_steps_to_call_ret;
                     exact (@cfg_steps_pure_int_intrinsic_binop_ret Pa sigma sigma sigma
                              env id dt_fn (EXP_Ident (ID_Global (Name fname))) args anns md fname op w a0 a1 dv0 dv1 dv_out None
                              eq_refl Hpars Hargs Hfa Hra Hmr_none
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst0)
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1)
                              Hpi)
                    | exact Hs].
               ** intros sigma tr Hs; unfold denote_code; cbn [loop_monad].
                  change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r;
                    [apply cfg_steps_to_call_ret;
                     exact (@cfg_steps_pure_int_intrinsic_binop_ret Pa sigma sigma sigma
                              env id dt_fn (EXP_Ident (ID_Global (Name fname))) args anns md fname op w a0 a1 dv0 dv1 dv_out None
                              eq_refl Hpars Hargs Hfa Hra Hmr_none
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst0)
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1)
                              Hpi)
                    | exact Hs].
           ++ destruct (match metadata_range md with None => true | Some _ => false end) eqn:Emr; cbn [negb] in Hrc; [| discriminate Hrc].
              assert (Hmr_none : metadata_range md = None) by (destruct (metadata_range md); [discriminate | reflexivity]).
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a0) as [[wa ca] |] eqn:Ea0; [| discriminate Hrc].
              destruct (ub_free_expr ca) eqn:Huba; cbn [negb] in Hrc; [| discriminate Hrc].
              destruct (expr_has_freeze ca) eqn:Hnfa; [discriminate Hrc |].
              destruct (reify_pure_exp_typing a0 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Hlmap Ea0)
                as (_ & Hwt0 & Hbw0 & Hlf0 & Hfv0).
              pose proof (reify_pure_exp_top_width a0 lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Ea0) as Htw0.
              cbn [check_opt_int_width] in Htw0; apply Pos.eqb_eq in Htw0; subst wa; rewrite Htw0 in Ea0.
              destruct (eval_reified_pure_exp_no_ub allowed penv lmap env a0 (Some (DTYPE_Base (DTYPE_I w))) w ca Hlmap Hpenv Henv Ea0 Huba Hnfa)
                as (dv0 & Hev0 & Hsc0 & Hst0).
              destruct fn_e; try contradiction Hinv; destruct id0 as [[fname | | ] | ?]; try contradiction Hinv;
                destruct obs; try contradiction Hinv;
                destruct Hinv as (Hdt & Hpars & a1 & Hargs & Hbool & Hfa & Hra).
              destruct (pure_int_intrinsic_abs_eval_helper w ca flag penv dummy_freeze_oracle dv0 Hsc0 Hev0)
                as (dv_out & Hpi & Hev_out & Hsc_out).
              destruct (lower_pure_int_intrinsic_abs_typing w ca flag
                          Hwt0 Htw0 Hlf0 (expr_has_freeze_false_collect_keys _ Hnfa))
                as (Hwt & Hbw & Hlf & _ & Hfv_sub).
              assert (Hfv : incl (collect_free_vars [] (lower_pure_int_intrinsic_abs w ca flag)) allowed)
                by (intros x Hx; exact (Hfv0 _ (Hfv_sub _ Hx))).
              pose proof (wf_pure_lmap_add allowed lmap id w (lower_pure_int_intrinsic_abs w ca flag) Hlmap Hwt Hbw Hlf Hfv) as Hlmap1.
              pose proof (lmap_matches_env_add penv lmap env id w (lower_pure_int_intrinsic_abs w ca flag) dv_out Henv Hev_out Hsc_out) as Henv1.
              specialize (IH cid allowed (RM.add id (w, lower_pure_int_intrinsic_abs w ca flag) lmap)
                            (RM.add id dv_out env) ret_w k_end t ctx Hlmap1 Hpenv Henv1 Hk Hrc).
              eapply ir_tree_denotes_prepend_tau_pure with (env1 := RM.add id dv_out env)
                (t1 := apply_cfg_ctxt ctx (denote_code rest None)); [| | exact IH].
               ** intros sigma tr s' env' r Hs; unfold denote_code; cbn [loop_monad].
                  change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind;
                    [apply cfg_steps_to_call_ret;
                     exact (@cfg_steps_pure_int_intrinsic_abs_ret Pa sigma sigma
                              env id dt_fn (EXP_Ident (ID_Global (Name fname))) args anns md fname w a0 a1 flag dv0 dv_out None
                              eq_refl Hpars Hargs Hbool Hfa Hra Hmr_none
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst0)
                              Hpi)
                    | exact Hs].
               ** intros sigma tr Hs; unfold denote_code; cbn [loop_monad].
                  change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r;
                    [apply cfg_steps_to_call_ret;
                     exact (@cfg_steps_pure_int_intrinsic_abs_ret Pa sigma sigma
                              env id dt_fn (EXP_Ident (ID_Global (Name fname))) args anns md fname w a0 a1 flag dv0 dv_out None
                              eq_refl Hpars Hargs Hbool Hfa Hra Hmr_none
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst0)
                              Hpi)
                    | exact Hs].
        -- destruct fn as [dt_ret fn_e].
           destruct dt_ret as [bdt | |]; [destruct bdt as [rw | | | | | | | | | |] | |];
             destruct fn_e;
             try match goal with iv : ident |- _ => destruct iv as [[cname | | ] | ?] end;
             destruct obs; try discriminate Hrc.
           destruct (match @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname))) with None => true | Some _ => false end) eqn:Hintr; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (cconv_eqb (anns_cconv anns) CC_Ccc) eqn:Hcc; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (match metadata_range md with None => true | Some _ => false end) eqn:Hmr_b; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (fattrs_call_ok (ann_fun_attributes anns)) eqn:Hfa; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (pattrs_no_value_poison (ann_ret_attributes anns)) eqn:Hra; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (is_supported_bit_width rw) eqn:Hsup; cbn [negb] in Hrc; [| discriminate Hrc].
           assert (Hintr_none : @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname))) = None)
             by (destruct (@intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname)))); [discriminate | reflexivity]).
           assert (Hmr_none : metadata_range md = None)
             by (destruct (metadata_range md); [discriminate | reflexivity]).
           destruct (find_callee_spec callees cname) as [sp |]; [| discriminate Hrc].
           destruct (Pos.eqb rw (mcs_ret_width sp)); [| discriminate Hrc].
           destruct (reify_ir_call_args cname 0%nat lmap (mcs_args sp) args) as [| aes] eqn:Eaes; [discriminate Hrc |].
           destruct (reify_ir_code_calls cur_bid callees rest (S cid)
                       (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap) k_end)
             as [| cont] eqn:Ect; [discriminate Hrc |].
           inversion Hrc; subst t; clear Hrc;
           cbn [ir_tree_denotes];
             destruct (denote_call_args_step genv cname 0%nat allowed penv lmap env (mcs_args sp) args aes
                         ((set_loc (get_file_info md) ++ location_error_string md) ++ ": Call argument violates noundef.")%string
                         Hlmap Hpenv Henv Eaes) as [Hub_a | (dvs & Hst_a & Hfa_a)];
             [left; intro sigma;
              unfold denote_code; cbn [loop_monad denote_instr];
              eapply cfg_call_steps_to_ub_ctxt with (ctx := CBC_Bind _ ctx);
              apply cfg_call_steps_to_ub_bind_l; exact (Hub_a sigma)
             | right; exists dvs; split; [exact Hfa_a |];
               intros v_ret Hrv_p;
               set (dv_ret := DVALUE_Base (@DVALUE_I Pa rw v_ret));
               assert (Hpenv' : wf_param_env_for ((mc_call_ret_var cid rw, rw) :: allowed) penv) by
                 (intros nm0 w0 [Heq0 | Hal0]; [inversion Heq0; subst nm0 w0; exists dv_ret; split; [exact Hrv_p | right; exists v_ret; reflexivity] | exact (Hpenv nm0 w0 Hal0)]);
               assert (Hlmap' : wf_pure_lmap ((mc_call_ret_var cid rw, rw) :: allowed)
                                  (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap)) by
                 (apply wf_pure_lmap_add;
                   [exact (wf_pure_lmap_mono allowed ((mc_call_ret_var cid rw, rw) :: allowed) lmap (fun x Hx => or_intror Hx) Hlmap)
                   | reflexivity | reflexivity | reflexivity | intros [? ?] [? | []]; inversion H; left; reflexivity]);
               assert (Henv' : lmap_matches_env penv
                                 (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap)
                                 (RM.add id dv_ret env)) by
                 (apply lmap_matches_env_add; [exact Henv | | right; exists v_ret; reflexivity];
                  unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hrv_p;
                  cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity);
               specialize (IH (S cid) ((mc_call_ret_var cid rw, rw) :: allowed)
                             (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap)
                             (RM.add id dv_ret env) ret_w k_end cont ctx
                             Hlmap' Hpenv' Henv'
                             (fun c' a' l' e' t' Hinc => Hk c' a' l' e' t' (fun x Hx => Hinc x (or_intror Hx)))
                             Ect);
               exists (RM.add id dv_ret env), (apply_cfg_ctxt ctx (denote_code rest None));
               assert (Hcall_step : forall sigma,
                 cfg_call_steps_to_ret genv sigma env
                   (denote_instr (IId id, INSTR_Call (DTYPE_Base (DTYPE_I rw), EXP_Ident (ID_Global (Name cname))) args anns [], md) None)
                   [(cname, dvs, dv_ret)] sigma (RM.add id dv_ret env) tt) by
                 (intro sigma; cbn [denote_instr];
                  change [(cname, dvs, dv_ret)] with ([] ++ [(cname, dvs, dv_ret)]);
                  eapply cfg_call_steps_to_ret_bind; [apply pure_cfg_steps_to_call_ret; exact Hst_a |];
                  change [(cname, dvs, dv_ret)] with ([] ++ [(cname, dvs, dv_ret)]);
                  eapply cfg_call_steps_to_ret_bind; [apply cfg_steps_to_call_ret, denote_operand_bundles_nil_cfg_steps |];
                  change [(cname, dvs, dv_ret)] with ([(cname, dvs, dv_ret)] ++ []);
                  eapply cfg_call_steps_to_ret_bind;
                  [rewrite Hintr_none;
                   change [(cname, dvs, dv_ret)] with ([] ++ [(cname, dvs, dv_ret)]);
                   eapply cfg_call_steps_to_ret_bind;
                   [unfold denote_exp', withCall;
                    eapply CCSR_GlobalRead;
                    [rewrite observe_translate; cbn [denote_exp lookup_id];
                     unfold gread, ITree.trigger, subevent; cbn [observe _observe translateF]; reflexivity
                    | apply CCSR_Ret; rewrite observe_translate; reflexivity]
                   | unfold call, ITree.trigger, subevent;
                     eapply CCSR_Call; [reflexivity | reflexivity | apply CCSR_Ret; reflexivity]]
                  | change [] with ([] ++ @nil (@mc_call_event Pa));
                    eapply cfg_call_steps_to_ret_bind;
                    [rewrite Hmr_none; exact (check_call_return_int_step genv sigma env (ann_fun_attributes anns)
                                                 (ann_ret_attributes anns) _ dvs rw v_ret Hfa Hra)
                    | change [] with ([] ++ @nil (@mc_call_event Pa));
                      eapply cfg_call_steps_to_ret_bind; [apply CCSR_Ret; reflexivity |];
                      apply cfg_steps_to_call_ret, cfg_steps_lwrite]]);
               repeat split; [| | exact IH];
               [intros sigma tr_r s' env' r Hs; unfold denote_code; cbn [loop_monad];
                change ((cname, dvs, dv_ret) :: tr_r) with ([(cname, dvs, dv_ret)] ++ tr_r);
                eapply cfg_call_steps_to_ret_ctxt_bind; [exact (Hcall_step sigma) | exact Hs]
               | intros sigma tr_r Hs; unfold denote_code; cbn [loop_monad];
                change ((cname, dvs, dv_ret) :: tr_r) with ([(cname, dvs, dv_ret)] ++ tr_r);
                eapply cfg_call_steps_to_ub_ctxt_bind_r; [exact (Hcall_step sigma) | exact Hs]]].
    + destruct ins; try discriminate Hrc; specialize (IH cid allowed lmap env ret_w k_end t ctx Hlmap Hpenv Henv Hk Hrc).
      eapply ir_tree_denotes_prepend_tau_pure with (env1 := env)
        (t1 := apply_cfg_ctxt ctx (denote_code rest None)); [| | exact IH].
      * intros sigma tr s' env' r Hs; eapply cfg_call_steps_to_ret_obs; [| exact Hs].
        apply apply_cfg_ctxt_obs; unfold denote_code;
          cbn [loop_monad denote_instr ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          rewrite observe_bind; cbn [observe _observe]; reflexivity.
      * intros sigma tr Hs; eapply cfg_call_steps_to_ub_obs; [| exact Hs].
        apply apply_cfg_ctxt_obs; unfold denote_code;
          cbn [loop_monad denote_instr ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          rewrite observe_bind; cbn [observe _observe]; reflexivity.
Qed.

Lemma cfg_call_steps_to_ret_bind_obs {Pa : Params} {R S : Type} (genv : raw_id -> @dvalue Pa) :
  forall s0 env0 (t1 t2 : @CFGtop Pa R) (k : R -> @CFGtop Pa S) tr s1 env1 y,
    observe t1 = observe t2 ->
    cfg_call_steps_to_ret genv s0 env0 (ITree.bind t1 k) tr s1 env1 y ->
    cfg_call_steps_to_ret genv s0 env0 (ITree.bind t2 k) tr s1 env1 y.
Proof.
  intros s0 env0 t1 t2 k tr s1 env1 y Ho H.
  eapply cfg_call_steps_to_ret_obs; [| exact H].
  rewrite !observe_bind, Ho; reflexivity.
Qed.

Lemma cfg_call_steps_to_ub_bind_obs {Pa : Params} {R S : Type} (genv : raw_id -> @dvalue Pa) :
  forall s0 env0 (t1 t2 : @CFGtop Pa R) (k : R -> @CFGtop Pa S) tr,
    observe t1 = observe t2 ->
    cfg_call_steps_to_ub genv s0 env0 (ITree.bind t1 k) tr ->
    cfg_call_steps_to_ub genv s0 env0 (ITree.bind t2 k) tr.
Proof.
  intros s0 env0 t1 t2 k tr Ho H.
  eapply cfg_call_steps_to_ub_obs; [| exact H].
  rewrite !observe_bind, Ho; reflexivity.
Qed.

Lemma reify_ir_call_at_exec {Pa : Params} :
  forall fuel (genv : raw_id -> @dvalue Pa) (penv : param_env Pa)
         callees bmap ret_w visited is_entry bid_from cur_bid cid allowed lmap env t,
    is_supported_bit_width ret_w = true ->
    wf_pure_lmap allowed lmap ->
    wf_param_env_for allowed penv ->
    lmap_matches_env penv lmap env ->
    reify_ir_call_at fuel callees bmap ret_w visited is_entry bid_from cur_bid cid lmap = inr t ->
    ir_tree_denotes genv penv ret_w env (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) t.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros genv penv callees bmap ret_w visited is_entry bid_from cur_bid cid allowed lmap env t
           Hrw Hlmap Hpenv Henv Hrec;
    cbn [reify_ir_call_at] in Hrec;
    destruct (raw_id_in_list cur_bid visited); try discriminate Hrec.
  destruct (RM.find cur_bid bmap) as [b |] eqn:Efind; [| discriminate Hrec].
  match type of Hrec with
  | match ?x with inl _ => _ | inr _ => _ end = _ => destruct x as [| lmap1] eqn:El1
  end; [discriminate Hrec |].
  assert (Hphis :
    wf_pure_lmap allowed lmap1 /\
    exists env1,
      lmap_matches_env penv lmap1 env1 /\
      pure_cfg_steps env (denote_phis bid_from (blk_phis b)) env1 tt).
  { destruct is_entry.
    - destruct (blk_phis b) eqn:Ebp; inversion El1; subst; split; [exact Hlmap |].
      exists env; split; [exact Henv | unfold denote_phis; cbn [map_monad];
        eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | apply PCS_Ret; reflexivity]]].
    - destruct (reify_pure_phis bid_from lmap (blk_phis b)) as [pevals |] eqn:Erp; [| discriminate El1].
      destruct (pevals_ub_free pevals) eqn:Eub; cbn [negb] in El1; [| discriminate El1].
      destruct (forallb (fun '(_, _, ce) => negb (expr_has_freeze ce)) pevals) eqn:Efr; cbn [negb] in El1;
        inversion El1; subst.
      pose proof (reify_pure_phis_typing (blk_phis b) allowed bid_from lmap pevals Hlmap Erp) as Htp_p.
      split; [exact (apply_reified_phis_wf _ _ _ Hlmap Htp_p) |].
      destruct (pure_phis_denote_step (blk_phis b) penv bid_from lmap env pevals Henv Erp)
        as [[_ (ce & msg & Hin_c & Hev_ub)] | [dvs [Hpm Hst_p]]].
      + unfold pevals_ub_free in Eub; rewrite forallb_forall in Eub.
        unfold peval_exprs in Hin_c; apply in_map_iff in Hin_c as [[[id_p w_p] ce_p] [<- Hin_p]].
        pose proof (Eub _ Hin_p) as Hce_ub.
        rewrite Forall_forall in Htp_p; destruct (Htp_p _ Hin_p) as (_ & _ & (Hwt_p & Hlf_p & Hfv_p)).
        destruct (ub_free_expr_eval_ret ce_p [] penv [] dummy_freeze_oracle Hce_ub Hwt_p wf_let_val_env_nil
                    (fun nm w0 Hin0 => Hpenv nm w0 (Hfv_p _ Hin0))) as [dv0 [Hev0 _]].
        unfold eval_closed_cert_expr in *; congruence.
      + exists (apply_phi_env env dvs); split;
          [exact (apply_reified_phis_matches _ _ _ _ _ Henv Hpm) | exact Hst_p]. }
  destruct Hphis as (Hlmap1 & env1 & Henv1 & Hst_phis).
  destruct (blk_term b) as [[tid term] tmd] eqn:Etb.
  set (k_bd := (fun bd : block_id + @dvalue Pa =>
    match bd with
    | inr dv => Ret (inr (inr dv))
    | inl bid_target => Ret (inl (cur_bid, bid_target))
    end) : (block_id + @dvalue Pa) -> @CFGtop Pa ((block_id * block_id) + ((block_id * block_id) + @dvalue Pa))).
  set (k_lr := (fun lr : (block_id * block_id) + ((block_id * block_id) + @dvalue Pa) =>
    match lr with
    | inl j => Tau (@denote_ocfg_map Pa bmap None j)
    | inr r => Ret r
    end) : ((block_id * block_id) + ((block_id * block_id) + @dvalue Pa)) -> @CFGtop Pa ((block_id * block_id) + @dvalue Pa)).
  set (k_outer := (fun r : (block_id * block_id) + @dvalue Pa =>
    match r with
    | inl bid => raise ("Can't find block in denote_cfg " ++ show (snd bid))%string
    | inr uv => ret uv
    end) : ((block_id * block_id) + @dvalue Pa) -> @CFGtop Pa (@dvalue Pa)).
  set (ctx_term := CBC_Bind k_bd (CBC_Bind k_lr (CBC_Bind k_outer CBC_Id))).
  set (ctx_code := CBC_Bind (fun _ : unit => denote_terminator (blk_term b)) ctx_term).
  assert (Hk : forall cid' allowed' lmap' env' t',
    incl allowed allowed' ->
    wf_pure_lmap allowed' lmap' ->
    wf_param_env_for allowed' penv ->
    lmap_matches_env penv lmap' env' ->
    (let '(_, t_k) := fst (blk_term b) in
     match t_k with
     | TERM_Ret (DTYPE_Base (DTYPE_I rw), op) =>
         if Pos.eqb rw ret_w then
           match reify_pure_exp lmap' (Some (DTYPE_Base (DTYPE_I rw))) op with
           | Some (_, ret_e) =>
               if negb (ub_free_expr ret_e) then inl (diag "mc-call-ir" ("non-UB-free return expression in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
               else if expr_has_freeze ret_e then inl (diag "mc-call-ir" ("freeze expression not allowed in return of block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
               else inr (ICT_Ret rw ret_e)
           | None => inl (diag "mc-call-ir" ("unsupported return operand in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
           end
         else inl (diag "mc-call-ir" ("return width i" ++ diag_pos_dec rw ++ " mismatches expected i" ++ diag_pos_dec ret_w ++ " in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
     | TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2 =>
         match reify_pure_exp lmap' (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
         | Some (_, cond_e) =>
             if negb (ub_free_expr cond_e) then inl (diag "mc-call-ir" ("non-UB-free branch condition in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
             else if expr_has_freeze cond_e then inl (diag "mc-call-ir" ("freeze expression not allowed in branch condition of block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
             else
               match reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' lmap' with
               | inl err => inl err
               | inr dt =>
                   match reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' lmap' with
                   | inl err => inl err
                   | inr df => inr (ICT_Branch cond_e dt df)
                   end
               end
         | None => inl (diag "mc-call-ir" ("unsupported branch condition in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
         end
     | TERM_Br_1 next_bid =>
         reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid next_bid cid' lmap'
     | TERM_Unreachable => inr ICT_UB
     | _ => inl (diag "mc-call-ir" ("unsupported terminator in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
     end) = inr t' ->
    ir_tree_denotes genv penv ret_w env' (apply_cfg_ctxt ctx_code (Ret tt)) t').
  { intros cid' allowed' lmap' env' t' _ Hlmap' Hpenv' Henv' Ht'.
    assert (Hlift_t :
      ir_tree_denotes genv penv ret_w env' (apply_cfg_ctxt ctx_term (denote_terminator (blk_term b))) t' ->
      ir_tree_denotes genv penv ret_w env' (apply_cfg_ctxt ctx_code (Ret tt)) t').
    { apply ir_tree_denotes_prepend_tau_pure.
      - intros sigma tr s' env_f r Hs.
        eapply cfg_call_steps_to_ret_obs; [symmetry; apply apply_cfg_ctxt_obs with (ctx := ctx_term); rewrite observe_bind; reflexivity | exact Hs].
      - intros sigma tr Hs.
        eapply cfg_call_steps_to_ub_obs; [symmetry; apply apply_cfg_ctxt_obs with (ctx := ctx_term); rewrite observe_bind; reflexivity | exact Hs]. }
    apply Hlift_t; clear Hlift_t.
    rewrite Etb in Ht'; cbn [fst] in Ht'.
    destruct term; try discriminate Ht'.
    - (* TERM_Ret *)
      match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] op] end; try discriminate Ht'.
      destruct (Pos.eqb rw ret_w) eqn:Erw; [apply Pos.eqb_eq in Erw; subst rw | discriminate Ht'].
      destruct (reify_pure_exp lmap' (Some (DTYPE_Base (DTYPE_I ret_w))) op) as [[wa ret_e] |] eqn:Eop;
        [| discriminate Ht'].
      destruct (ub_free_expr ret_e) eqn:Hub_r; cbn [negb] in Ht'; [| discriminate Ht'].
      destruct (expr_has_freeze ret_e) eqn:Hnf_r; [discriminate Ht' |].
      inversion Ht'; subst t'; clear Ht'.
      destruct (eval_reified_pure_exp_no_ub allowed' penv lmap' env' op
                  (Some (DTYPE_Base (DTYPE_I ret_w))) wa ret_e Hlmap' Hpenv' Henv' Eop Hub_r Hnf_r)
        as (dv_ir & Hev & Hsc & Hst_op).
      pose proof (reify_pure_exp_top_width op lmap' (Some (DTYPE_Base (DTYPE_I ret_w))) wa ret_e Eop) as Htw.
      cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst wa.
      cbn [ir_tree_denotes]; split; [reflexivity |].
      exists env', dv_ir; repeat split; try assumption.
      intro sigma; apply pure_cfg_steps_to_call_ret.
      unfold ctx_term, apply_cfg_ctxt, k_bd, k_lr, k_outer; rewrite Etb; cbn [denote_terminator].
      eapply pure_cfg_steps_bind.
      + eapply pure_cfg_steps_bind.
        -- eapply pure_cfg_steps_bind.
           ++ eapply pure_cfg_steps_bind;
                [unfold denote_exp'; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_op)
                | apply PCS_Ret; reflexivity].
           ++ apply PCS_Ret; reflexivity.
        -- apply PCS_Ret; reflexivity.
      + apply PCS_Ret; reflexivity.
    - (* TERM_Br *)
      match goal with x : texp dtyp |- _ => destruct x as [[[w | | | | | | | | | |] | |] op] end; try discriminate Ht'.
      destruct w; try discriminate Ht'.
      destruct (reify_pure_exp lmap' (Some (DTYPE_Base (DTYPE_I 1%positive))) op) as [[wc cond_e] |] eqn:Eop;
        [| discriminate Ht'].
      destruct (ub_free_expr cond_e) eqn:Hub_c; cbn [negb] in Ht'; [| discriminate Ht'].
      destruct (expr_has_freeze cond_e) eqn:Hnf_c; [discriminate Ht' |].
      destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' lmap')
        as [| dt1] eqn:Edt; [discriminate Ht' |].
      destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' lmap')
        as [| df1] eqn:Edf; [discriminate Ht' |].
      inversion Ht'; subst t'; clear Ht'.
      destruct (eval_reified_pure_exp_no_ub allowed' penv lmap' env' op
                  (Some (DTYPE_Base (DTYPE_I 1%positive))) wc cond_e Hlmap' Hpenv' Henv' Eop Hub_c Hnf_c)
        as (dv_c & Hev & Hsc & Hst_op).
      pose proof (reify_pure_exp_top_width op lmap' (Some (DTYPE_Base (DTYPE_I 1%positive))) wc cond_e Eop) as Htw.
      cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst wc.
      cbn [wf_scalar_dvalue] in Hsc; destruct Hsc as [Hpois | [v1 ->]].
      + subst dv_c; cbn [ir_tree_denotes]; left; split; [exact Hev |].
        intro sigma; unfold ctx_term, apply_cfg_ctxt; rewrite Etb; cbn [denote_terminator].
        apply cfg_call_steps_to_ub_ctxt with (ctx := CBC_Bind k_bd (CBC_Bind k_lr (CBC_Bind k_outer CBC_Id))).
        change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ub_bind_r;
          [apply pure_cfg_steps_to_call_ret, pure_mcfg_to_pure_cfg; exact Hst_op |].
        eapply CCSU_UB; unfold raiseUB, trigger_cast', ITree.trigger; rewrite observe_bind; reflexivity.
      + set (bflag := ((@Integers.unsigned 1%positive v1 =? 1)%Z)).
        assert (Hv1_eq : v1 = if bflag then @Integers.one 1%positive else @Integers.zero 1%positive).
        { unfold bflag; pose proof (@Integers.unsigned_range 1%positive v1) as Hrng.
          change (@Integers.modulus 1%positive) with 2%Z in Hrng.
          destruct ((@Integers.unsigned 1%positive v1 =? 1)%Z) eqn:Eu.
          - apply Z.eqb_eq in Eu.
            rewrite <- (@Integers.repr_unsigned 1%positive v1), Eu.
            unfold Integers.one; reflexivity.
          - apply Z.eqb_neq in Eu.
            assert (Hu0 : @Integers.unsigned 1%positive v1 = 0%Z) by lia.
            rewrite <- (@Integers.repr_unsigned 1%positive v1), Hu0.
            unfold Integers.zero; reflexivity. }
        cbn [ir_tree_denotes]; right; exists bflag; split.
        * rewrite Hev, <- Hv1_eq; reflexivity.
        * set (br := if bflag then br1 else br2).
          assert (Hden_br : ir_tree_denotes genv penv ret_w env' (@denote_cfg_from Pa bmap None (cur_bid, br)) (if bflag then dt1 else df1)).
          { unfold br; destruct bflag.
            - exact (IH genv penv callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' allowed' lmap' env' dt1 Hrw Hlmap' Hpenv' Henv' Edt).
            - exact (IH genv penv callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' allowed' lmap' env' df1 Hrw Hlmap' Hpenv' Henv' Edf). }
          assert (Hjump_step : pure_cfg_steps env' (denote_terminator (blk_term b)) env' (inl br)).
          { rewrite Etb; cbn [denote_terminator].
            eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_op) |].
            cbn iota beta; rewrite bit_int_1_equ_one_eq_unsigned; unfold br; fold bflag; destruct bflag; apply PCS_Ret; reflexivity. }
          eapply ir_tree_denotes_prepend_tau_pure with (env1 := env') (t1 := @denote_cfg_from Pa bmap None (cur_bid, br));
            [| | exact Hden_br].
          -- intros sigma tr s' env_f r Hs.
             unfold ctx_term, apply_cfg_ctxt; change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind with (ctx := CBC_Bind k_lr (CBC_Bind k_outer CBC_Id)); [apply pure_cfg_steps_to_call_ret; exact Hjump_step |].
             unfold apply_cfg_ctxt, k_bd, k_lr, k_outer.
             eapply CCSR_Tau; [rewrite !observe_bind; reflexivity | exact Hs].
          -- intros sigma tr Hs.
             unfold ctx_term, apply_cfg_ctxt; change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r with (ctx := CBC_Bind k_lr (CBC_Bind k_outer CBC_Id)); [apply pure_cfg_steps_to_call_ret; exact Hjump_step |].
             unfold apply_cfg_ctxt, k_bd, k_lr, k_outer.
             eapply CCSU_Tau; [rewrite !observe_bind; reflexivity | exact Hs].
    - (* TERM_Br_1 *)
      match type of Ht' with
      | reify_ir_call_at _ _ _ _ _ _ _ ?nxt _ _ = _ => set (b_nxt := nxt) in *
      end.
      assert (Hden_br : ir_tree_denotes genv penv ret_w env' (@denote_cfg_from Pa bmap None (cur_bid, b_nxt)) t')
        by exact (IH genv penv callees bmap ret_w (cur_bid :: visited) false cur_bid b_nxt cid' allowed' lmap' env' t' Hrw Hlmap' Hpenv' Henv' Ht').
      assert (Hjump_step : pure_cfg_steps env' (denote_terminator (blk_term b)) env' (inl b_nxt))
        by (rewrite Etb; cbn [denote_terminator]; apply PCS_Ret; reflexivity).
      eapply ir_tree_denotes_prepend_tau_pure with (env1 := env') (t1 := @denote_cfg_from Pa bmap None (cur_bid, b_nxt));
        [| | exact Hden_br].
      + intros sigma tr s' env_f r Hs.
        unfold ctx_term, apply_cfg_ctxt; change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind with (ctx := CBC_Bind k_lr (CBC_Bind k_outer CBC_Id)); [apply pure_cfg_steps_to_call_ret; exact Hjump_step |].
        unfold apply_cfg_ctxt, k_bd, k_lr, k_outer.
        eapply CCSR_Tau; [rewrite !observe_bind; reflexivity | exact Hs].
      + intros sigma tr Hs.
        unfold ctx_term, apply_cfg_ctxt; change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r with (ctx := CBC_Bind k_lr (CBC_Bind k_outer CBC_Id)); [apply pure_cfg_steps_to_call_ret; exact Hjump_step |].
        unfold apply_cfg_ctxt, k_bd, k_lr, k_outer.
        eapply CCSU_Tau; [rewrite !observe_bind; reflexivity | exact Hs].
    - (* TERM_Unreachable *)
      inversion Ht'; subst t'; clear Ht'; cbn [ir_tree_denotes].
      intro sigma; unfold ctx_term; rewrite Etb; cbn [denote_terminator].
      apply cfg_call_steps_to_ub_ctxt; eapply CCSU_UB; unfold raiseUB, trigger_cast', ITree.trigger; rewrite observe_bind; reflexivity. }
  rewrite <- Etb in Hrec.
  pose proof (@reify_ir_code_calls_exec Pa cur_bid genv penv callees (blk_code b) cid allowed lmap1 env1 ret_w
                _ t ctx_code Hlmap1 Hpenv Henv1 Hk Hrec) as Hcode.
  eapply ir_tree_denotes_prepend_tau_pure with (env1 := env1) (t1 := apply_cfg_ctxt ctx_code (denote_code (blk_code b) None));
    [| | exact Hcode].
  - intros sigma tr s' env' r Hs.
    unfold ctx_code in Hs.
    change (apply_cfg_ctxt (CBC_Bind (fun _ : unit => denote_terminator (blk_term b)) ctx_term) (denote_code (blk_code b) None))
      with (apply_cfg_ctxt ctx_term (ITree.bind (denote_code (blk_code b) None) (fun _ : unit => denote_terminator (blk_term b)))) in Hs.
    assert (Hblk : cfg_call_steps_to_ret genv sigma env (apply_cfg_ctxt ctx_term (denote_block b bid_from None)) tr s' env' r).
    { unfold denote_block; change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind;
        [apply pure_cfg_steps_to_call_ret; exact Hst_phis | exact Hs]. }
    unfold denote_cfg_from, ctx_term, apply_cfg_ctxt in Hblk |- *.
    eapply cfg_call_steps_to_ret_bind_obs;
      [symmetry; exact (denote_ocfg_map_step_varargs_obs bmap None bid_from cur_bid b Efind) | exact Hblk].
  - intros sigma tr Hs.
    unfold ctx_code in Hs.
    change (apply_cfg_ctxt (CBC_Bind (fun _ : unit => denote_terminator (blk_term b)) ctx_term) (denote_code (blk_code b) None))
      with (apply_cfg_ctxt ctx_term (ITree.bind (denote_code (blk_code b) None) (fun _ : unit => denote_terminator (blk_term b)))) in Hs.
    assert (Hblk : cfg_call_steps_to_ub genv sigma env (apply_cfg_ctxt ctx_term (denote_block b bid_from None)) tr).
    { unfold denote_block; change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r;
        [apply pure_cfg_steps_to_call_ret; exact Hst_phis | exact Hs]. }
    unfold denote_cfg_from, ctx_term, apply_cfg_ctxt in Hblk |- *.
    eapply cfg_call_steps_to_ub_bind_obs;
      [symmetry; exact (denote_ocfg_map_step_varargs_obs bmap None bid_from cur_bid b Efind) | exact Hblk].
Qed.

Lemma reify_ir_call_tree_exec {Pa : Params} :
  forall (genv : raw_id -> @dvalue Pa) (penv : param_env Pa)
         ir_cfg arg_specs callees ret_w allowed arg_dtys vs t_ir,
    is_supported_bit_width ret_w = true ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    (forall idx dt, In (idx, dt) (arg_specs_uses_from 0%nat arg_specs) -> nth_error arg_dtys idx = Some dt) ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (arg_specs_uses_from 0%nat arg_specs) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    wf_param_env_for allowed penv ->
    reify_ir_call_tree ir_cfg arg_specs callees ret_w = inr t_ir ->
    ir_tree_denotes genv penv ret_w (init_cfg_locals (args ir_cfg) vs) (@denote_cfg Pa ir_cfg None) t_ir.
Proof.
  intros genv penv ir_cfg arg_specs callees ret_w allowed arg_dtys vs t_ir
         Hrw Hnda Hnds Hlens Hlenad Hcomp_n Hty Hpu Hpeq Hpenv Hrc.
  assert (Hlen_vs : List.length (args ir_cfg) = List.length vs)
    by (pose proof (Forall2_length Hty); lia).
  set (ir_pnames := List.map cert_reg_name (args ir_cfg)) in *.
  set (lmap_init := init_param_lmap (args ir_cfg) ir_pnames (arg_specs_uses_from 0%nat arg_specs)) in *.
  assert (Hwf_li : wf_pure_lmap allowed lmap_init)
    by exact (init_param_lmap_typing (arg_specs_uses_from 0%nat arg_specs) (args ir_cfg) ir_pnames allowed Hpu).
  assert (Henv_i : lmap_matches_env penv lmap_init (init_cfg_locals (args ir_cfg) vs)).
  { pose proof (init_param_lmap_matches (arg_specs_uses_from 0%nat arg_specs) (args ir_cfg) ir_pnames arg_dtys vs
                  Hnda Hnds Hlen_vs (eq_trans Hlens Hlen_vs) Hty Hcomp_n) as Hbase.
    intros r w ce Hf; destruct (Hbase r w ce Hf) as (dv & Hev & Hsc & Hrm).
    destruct (init_param_lmap_dom (args ir_cfg) ir_pnames (arg_specs_uses_from 0%nat arg_specs) r w ce Hf)
      as [pnm [-> Hinp]].
    exists dv; repeat split; try assumption.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr lookup_let_val] in *; rewrite (Hpeq pnm Hinp); exact Hsc. }
  exact (reify_ir_call_at_exec (S (List.length (blks ir_cfg) + 1)) genv penv callees
           (ocfg_map (blks ir_cfg)) ret_w [] true (init ir_cfg) (init ir_cfg) 0%nat allowed
           lmap_init (init_cfg_locals (args ir_cfg) vs) t_ir Hrw Hwf_li Hpenv Henv_i Hrc).
Qed.

Lemma summarize_rv64_call_tree_wfsym :
  forall insts callees arg_specs ret_w allowed t_mc,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true) ->
    forallb rv_call_inst_no_word_mulh insts = true ->
    forallb rv_valid_arg_spec arg_specs = true ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed) ->
    summarize_rv64_call_tree insts callees arg_specs ret_w = inr t_mc ->
    mc_call_tree_wf allowed ret_w t_mc.
Proof.
  intros insts callees arg_specs ret_w allowed t_mc Hrw Hcws Hmul Hws Hargs_al Hsum.
  unfold summarize_rv64_call_tree in Hsum.
  eapply summarize_rv64_call_at_wfsym;
    [exact (pt_of_list_first_lookup_rv_call insts)
    | exact Hrw | exact Hcws | exact Hmul | | | exact (rv_init_val_regs_wf allowed arg_specs Hargs_al Hws) | | exact Hsum].
  - unfold mc_frame_cap; lia.
  - unfold rv_val_read; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity.
  - constructor.
Qed.

Lemma a64_hi_vars_in_specs :
  forall (specs : list rv_arg_spec) sp,
    In sp specs ->
    ras_width sp <> 64%positive ->
    In (a64_hi_var_name (ras_name sp), 64%positive) (a64_hi_vars specs).
Proof.
  induction specs as [| s rest IH]; intros sp Hin Hw; cbn [In] in Hin;
    unfold a64_hi_vars in *; cbn [flat_map] in *; [contradiction |].
  destruct (Pos.eqb (ras_width s) 64%positive) eqn:E64.
  - destruct Hin as [<- | Hr]; [apply Pos.eqb_eq in E64; contradiction | exact (IH sp Hr Hw)].
  - destruct Hin as [<- | Hr]; [left; reflexivity | right; exact (IH sp Hr Hw)].
Qed.

Lemma summarize_a64_call_tree_wfsym :
  forall insts callees arg_specs ret_w allowed t_mc,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true) ->
    forallb a64_call_inst_valid insts = true ->
    forallb a64_valid_arg_spec arg_specs = true ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed) ->
    (forall nv, In nv (a64_hi_vars arg_specs) -> In nv allowed) ->
    summarize_a64_call_tree insts callees arg_specs ret_w = inr t_mc ->
    mc_call_tree_wf allowed ret_w t_mc.
Proof.
  intros insts callees arg_specs ret_w allowed t_mc Hrw Hcws Hval Hws Hargs_al Hhi_al Hsum.
  unfold summarize_a64_call_tree in Hsum.
  assert (Hall_a64 : forall sp, In sp arg_specs ->
    In (ras_name sp, ras_width sp) allowed /\
    (ras_width sp <> 64%positive -> In (a64_hi_var_name (ras_name sp), 64%positive) allowed)).
  { intros sp Hsp; split; [exact (Hargs_al sp Hsp) | intro Hne; exact (Hhi_al _ (a64_hi_vars_in_specs _ _ Hsp Hne))]. }
  eapply summarize_a64_call_at_wfsym;
    [exact (pt_of_list_first_lookup_a64_call insts)
    | exact Hrw | exact Hcws | exact Hval | | exact (a64_init_val_regs_wf allowed arg_specs Hall_a64 Hws) | | | exact Hsum].
  - unfold mc_frame_cap; lia.
  - constructor.
  - intro C; discriminate C.
Qed.

Lemma mc_tree_path_ok_repath {Pa : Params} (penv : param_env Pa) (ret_w : positive) :
  forall p1 p2 t_mc evs_mc v_mc_ret,
    mc_tree_path_ok penv ret_w p1 t_mc evs_mc v_mc_ret ->
    mc_tree_path_ok penv ret_w p2 t_mc evs_mc v_mc_ret.
Proof.
  intros p1 p2 t_mc evs_mc v_mc_ret H; revert p2;
    induction H; intros p2;
    [eapply MTPO_Ret; eassumption
    | eapply MTPO_Branch; [eassumption | exact (IHmc_tree_path_ok _)]
    | eapply MTPO_Call; [eassumption | eassumption | eassumption | exact (IHmc_tree_path_ok _)]].
Qed.

Lemma build_call_arg_obls_list_matches {Pa : Params} :
  forall cname arch (penv : param_env Pa) (path : list (bool * cert_expr)) specs ir_args mc_args64 obls arg_vals vs_ir,
    (forall (b : bool) c, In (b, c) path ->
       eval_closed_cert_expr penv dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv dummy_freeze_oracle None false) obls ->
    build_call_arg_obls cname arch path specs ir_args mc_args64 = inr obls ->
    Forall rv_valid_arg_spec specs ->
    NoDup (List.map ras_name specs) ->
    Forall2 (fun '(need_def, w, ce) dv =>
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv /\
      (need_def = false -> dvalue_well_defined dv = true)) ir_args vs_ir ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv dummy_freeze_oracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))) mc_args64 arg_vals ->
    List.length vs_ir = List.length specs /\
    List.length arg_vals = List.length specs /\
    (forall k sp v_mc,
       nth_error specs k = Some sp ->
       nth_error arg_vals k = Some v_mc ->
       exists v : @Integers.bit_int (ras_width sp),
         build_param_env (List.map ras_name specs) vs_ir (ras_name sp) =
           Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
         match arch with
         | EA_Riscv64 =>
             v_mc =
               (if Pos.eqb (ras_width sp) 64%positive then
                  @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                else
                  match ras_ext sp with
                  | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                  | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
                  end)
         | EA_AArch64 =>
             match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
             | true, RAE_None =>
                 v_mc = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
             | false, RAE_None =>
                 @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive v_mc) = v
             | false, RAE_SignExt =>
                 @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
                 @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
             | false, RAE_ZeroExt =>
                 @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
                 @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
             | _, _ => False
             end
         end).
Proof.
  intros cname arch penv path specs ir_args mc_args64 obls arg_vals vs_ir
         Hpath Hobls Hbao Hvs Hnd Hfir Hfmc.
  assert (Hlen_av : List.length arg_vals = List.length specs)
    by (destruct (build_call_arg_obls_length _ _ _ _ _ _ _ Hbao) as [_ Hl2];
        pose proof (Forall2_length Hfmc); congruence).
  assert (Hlen_vs : List.length vs_ir = List.length specs)
    by (destruct (build_call_arg_obls_length _ _ _ _ _ _ _ Hbao) as [Hl1 _];
        pose proof (Forall2_length Hfir); congruence).
  repeat split; [exact Hlen_vs | exact Hlen_av |].
  assert (Hitem : forall k sp v_mc,
    nth_error specs k = Some sp ->
    nth_error arg_vals k = Some v_mc ->
    exists v : @Integers.bit_int (ras_width sp),
      nth_error vs_ir k = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      match arch with
      | EA_Riscv64 =>
          v_mc =
            (if Pos.eqb (ras_width sp) 64%positive then
               @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
             else
               match ras_ext sp with
               | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
               | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
               end)
      | EA_AArch64 =>
          match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
          | true, RAE_None =>
              v_mc = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
          | false, RAE_None =>
              @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive v_mc) = v
          | false, RAE_SignExt =>
              @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
              @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
          | false, RAE_ZeroExt =>
              @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
              @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
          | _, _ => False
          end
      end).
  { clear Hnd Hlen_av Hlen_vs.
    unfold build_call_arg_obls in Hbao; revert Hbao; generalize 0%nat as arg_idx.
    revert ir_args mc_args64 obls arg_vals vs_ir Hobls Hvs Hfir Hfmc.
    induction specs as [| sp0 srest IH];
      intros ir_args mc_args64 ob0 avs vs0 Hob0 Hvs0 Hfi0 Hfm0 arg_idx Hb0 k sp v_mc Hsp0_n Hav_n;
      try (destruct k; discriminate Hsp0_n);
      destruct ir_args as [| [[nd0 w0] e0] irest]; destruct mc_args64 as [| m0 mrest];
      try (cbn [build_call_arg_obls_from build_call_arg_obls_acc] in Hb0; discriminate Hb0).
    rewrite build_call_arg_obls_from_cons in Hb0.
    destruct (Pos.eqb w0 (ras_width sp0)) eqn:Epw; [apply Pos.eqb_eq in Epw; subst w0 | discriminate Hb0].
    match type of Hb0 with
    | context [match ?x with inl _ => _ | inr _ => _ end] => destruct x as [| cmp0] eqn:Ecmp0; [discriminate Hb0 |]
    end.
    destruct (build_call_arg_obls_from cname (S arg_idx) arch path srest irest mrest) as [| rest_o] eqn:Erest;
      cbn [mcc_sum_map] in Hb0; [discriminate Hb0 |].
    inversion Hb0; subst ob0; clear Hb0.
    destruct avs as [| vm0 av_r]; [inversion Hfm0 |].
    destruct vs0 as [| dv0 vs_r]; [inversion Hfi0 |].
    inversion Hvs0 as [| ? ? Hsp0_v Hvs_r]; subst.
    inversion Hfi0 as [| ? ? ? ? Hp0 Hfi_r]; subst; destruct Hp0 as [Hev0 [Hsc0 Hnd0]].
    inversion Hfm0 as [| ? ? ? ? Hm0 Hfm_r]; subst.
    rewrite Forall_app in Hob0; destruct Hob0 as [Hrest_o Hhead_o].
    assert (Hdef0 : Forall (mc_obl_holds penv dummy_freeze_oracle None false) (if nd0 then [MLO_Defined false path (ras_width sp0) e0] else [])).
    { destruct nd0; [inversion Hhead_o as [| ? ? Hd _]; constructor; [exact Hd | constructor] | constructor]. }
    assert (Hcmp0 : Forall (mc_obl_holds penv dummy_freeze_oracle None false) [cmp0]).
    { destruct nd0; [inversion Hhead_o as [| ? ? _ Hc]; exact Hc | exact Hhead_o]. }
    destruct k as [| k']; cbn in Hsp0_n, Hav_n.
    - inversion Hsp0_n; subst sp0; inversion Hav_n; subst vm0; clear Hsp0_n Hav_n.
      assert (Hwd0 : dvalue_well_defined dv0 = true).
      { destruct nd0; [| exact (Hnd0 eq_refl)].
        inversion Hdef0 as [| ? ? Hd _]; subst.
        pose proof (Hd eq_refl ltac:(discriminate) Hpath) as [v Hv1].
        unfold eval_closed_cert_expr in *; rewrite Hev0 in Hv1; inversion Hv1; reflexivity. }
      destruct Hsc0 as [Hbad | [iv ->]]; [rewrite Hbad in Hwd0; discriminate Hwd0 |].
      exists iv; split; [reflexivity |].
      destruct arch;
        [inversion Ecmp0; subst cmp0; clear Ecmp0;
         inversion Hcmp0 as [| ? ? Hc0 _]; subst;
         pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href;
         unfold refine_eou_dvalue, dvalue_refines, build_rv_call_arg_expr in Href |].
      + destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; generalize iv Hev0 Href; rewrite Ew64; intros iv64 Hev64 Href64; rewrite Hev64, Hm0 in Href64; cbn in Href64.
          destruct Href64 as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; symmetry in Heq; subst; rewrite (@Integers.repr_unsigned 64%positive); reflexivity].
        * assert (Hltb : (ras_width sp <? 64)%positive = true).
          { apply Pos.ltb_lt; unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _].
            apply rv_supported_arg_width_lt64 in Ew64; [apply Pos.ltb_lt; exact Ew64 | exact Hsup]. }
          destruct (ras_ext sp);
            erewrite ?eval_ce_sext, ?eval_ce_zext in Href by (first [exact Hltb | exact Hev0]);
            rewrite Hm0 in Href; cbn in Href; destruct Href as [Hbad | Heq];
            [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq | discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq | discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
      + unfold build_call_arg_cmp in Ecmp0; destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * destruct (ras_ext sp); inversion Ecmp0; subst cmp0; clear Ecmp0.
          inversion Hcmp0 as [| ? ? Hc0 _]; subst; pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href.
          unfold refine_eou_dvalue, dvalue_refines in Href.
          apply Pos.eqb_eq in Ew64; generalize iv Hev0 Href; rewrite Ew64; intros iv64 Hev64 Href64; rewrite Hev64, Hm0 in Href64.
          cbn in Href64; destruct Href64 as [Hbad | Heq];
            [discriminate Hbad | apply dvalue_i_inj in Heq; symmetry in Heq; subst; rewrite (@Integers.repr_unsigned 64%positive); reflexivity].
        * assert (Hltb : (ras_width sp <? 64)%positive = true).
          { apply Pos.ltb_lt; unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _].
            apply rv_supported_arg_width_lt64 in Ew64; [apply Pos.ltb_lt; exact Ew64 | exact Hsup]. }
          destruct (ras_ext sp); inversion Ecmp0; subst cmp0; clear Ecmp0;
            inversion Hcmp0 as [| ? ? Hc0 _]; subst;
            pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href;
            unfold refine_eou_dvalue, dvalue_refines in Href.
          -- erewrite eval_ce_trunc in Href by (first [exact Hltb | exact Hm0]).
             rewrite Hev0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
          -- erewrite eval_ce_trunc in Href by (first [reflexivity | exact Hm0]).
             destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
             ++ apply Pos.eqb_eq in Ew32; generalize iv Href Hev0; rewrite Ew32; intros iv' Href' Hev0'.
                rewrite Hev0' in Href'; cbn in Href'; destruct Href' as [Hbad | Heq];
                  [discriminate Hbad | apply dvalue_i_inj in Heq; subst iv'; rewrite (@Integers.repr_signed 32%positive); reflexivity].
             ++ assert (Hlt32 : (ras_width sp <? 32)%positive = true)
                  by (unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _];
                      exact (rv_supported_arg_width_lt32 _ Hsup Ew64 Ew32)).
                erewrite eval_ce_sext in Href by (first [exact Hlt32 | exact Hev0]).
                cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
          -- erewrite eval_ce_trunc in Href by (first [reflexivity | exact Hm0]).
             destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
             ++ apply Pos.eqb_eq in Ew32; generalize iv Href Hev0; rewrite Ew32; intros iv' Href' Hev0'.
                rewrite Hev0' in Href'; cbn in Href'; destruct Href' as [Hbad | Heq];
                  [discriminate Hbad | apply dvalue_i_inj in Heq; subst iv'; rewrite (@Integers.repr_unsigned 32%positive); reflexivity].
             ++ assert (Hlt32 : (ras_width sp <? 32)%positive = true)
                  by (unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _];
                      exact (rv_supported_arg_width_lt32 _ Hsup Ew64 Ew32)).
                erewrite eval_ce_zext in Href by (first [exact Hlt32 | exact Hev0]).
                cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
    - exact (IH irest mrest rest_o av_r vs_r Hrest_o Hvs_r Hfi_r Hfm_r (S arg_idx) Erest k' sp v_mc Hsp0_n Hav_n). }
  intros k sp v_mc Hsp_n Hav_n.
  destruct (Hitem k sp v_mc Hsp_n Hav_n) as (v & Hvs_n & Hvmc).
  exists v; split; [| exact Hvmc].
  destruct (build_param_env_nth (List.map ras_name specs) vs_ir k (ras_name sp) Hnd) as [dv [Hdv Hbp]].
  - rewrite List.length_map; symmetry; exact Hlen_vs.
  - erewrite nth_error_map, Hsp_n; reflexivity.
  - rewrite Hvs_n in Hdv; inversion Hdv; subst dv; exact Hbp.
Qed.

Lemma collect_call_obls_mct_branch :
  forall arch callees ret_w p t_ir c mt mf,
    t_ir <> ICT_UB ->
    (forall cond dt df, t_ir <> ICT_Branch cond dt df) ->
    collect_call_obls arch callees ret_w p t_ir (MCT_Branch c mt mf) =
    match collect_call_obls arch callees ret_w ((true, c) :: p) t_ir mt,
          collect_call_obls arch callees ret_w ((false, c) :: p) t_ir mf with
    | inr o1, inr o2 => inr (o2 ++ o1)
    | inl err, _ => inl err
    | _, inl err => inl err
    end.
Proof.
  intros arch callees ret_w p t_ir c mt mf Hub Hbr; unfold collect_call_obls;
    destruct t_ir as [rw e_ir | | cond dt df | cn_ir args_ir rw_ir rv_ir c_ir].
  - cbn [collect_call_obls_acc collect_call_obls_ret_acc].
    destruct (collect_call_obls_ret_acc ret_w rw e_ir ((true, c) :: p) mt []) as [| o1]; [reflexivity |].
    rewrite collect_call_obls_ret_acc_shift.
    destruct (collect_call_obls_ret_acc ret_w rw e_ir ((false, c) :: p) mf []) as [| o2]; reflexivity.
  - exfalso; exact (Hub eq_refl).
  - exfalso; exact (Hbr _ _ _ eq_refl).
  - rewrite collect_call_obls_acc_ict_call_branch.
    destruct (collect_call_obls_acc arch callees ret_w ((true, c) :: p) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mt []) as [| o1];
      [reflexivity |].
    rewrite collect_call_obls_acc_shift; unfold collect_call_obls.
    destruct (collect_call_obls_acc arch callees ret_w ((false, c) :: p) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mf []) as [| o2];
      reflexivity.
Qed.

Lemma collect_call_obls_ict_branch :
  forall arch callees ret_w p cond dt df m,
    collect_call_obls arch callees ret_w p (ICT_Branch cond dt df) m =
    match collect_call_obls arch callees ret_w ((true, cond) :: p) dt m,
          collect_call_obls arch callees ret_w ((false, cond) :: p) df m with
    | inr o1, inr o2 => inr (o2 ++ o1)
    | inl err, _ => inl err
    | _, inl err => inl err
    end.
Proof.
  intros arch callees ret_w p cond dt df m; unfold collect_call_obls;
    cbn [collect_call_obls_acc];
    destruct (collect_call_obls_acc arch callees ret_w ((true, cond) :: p) dt m []) as [| o1];
    [reflexivity |];
    rewrite collect_call_obls_acc_shift; unfold collect_call_obls;
    destruct (collect_call_obls_acc arch callees ret_w ((false, cond) :: p) df m []) as [| o2];
    reflexivity.
Qed.

Lemma ir_mc_call_trees_sound {Pa : Params} :
  forall arch callees ret_w genv (penv : param_env Pa)
         t_ir t_mc (path : list (bool * cert_expr)) obls allowed_ir env_cur it_cur evs_mc (v_mc_ret : @Integers.bit_int ret_w),
    (forall c, In c callees ->
       forallb rv_valid_arg_spec (mcs_args c) = true /\
       NoDup (List.map ras_name (mcs_args c))) ->
    (forall (b : bool) c, In (b, c) path ->
       eval_closed_cert_expr penv dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv dummy_freeze_oracle None false) obls ->
    collect_call_obls arch callees ret_w path t_ir t_mc = inr obls ->
    ir_call_tree_wf allowed_ir ret_w t_ir ->
    ir_tree_denotes genv penv ret_w env_cur it_cur t_ir ->
    mc_tree_path_ok penv ret_w path t_mc evs_mc v_mc_ret ->
    let rel :=
      (fun (ev_m : string * list (@Integers.bit_int 64%positive) * @Integers.bit_int 64%positive)
           (ev_i : @mc_call_event Pa) =>
         let '(cn_m, args_m, ret_m) := ev_m in
         let '(cn_i, vs_i, dv_i) := ev_i in
         cn_i = cn_m /\
         exists c,
           find_callee_spec callees cn_m = Some c /\
           In c callees /\
           mc_strip_leading_at (mcs_name c) = cn_m /\
           List.length args_m = List.length (mcs_args c) /\
           List.length vs_i = List.length (mcs_args c) /\
           (forall k sp v_m,
              nth_error (mcs_args c) k = Some sp ->
              nth_error args_m k = Some v_m ->
              exists v : @Integers.bit_int (ras_width sp),
                build_param_env (List.map ras_name (mcs_args c)) vs_i (ras_name sp) =
                  Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
                match arch with
                | EA_Riscv64 =>
                    v_m =
                      (if Pos.eqb (ras_width sp) 64%positive then
                         @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                       else
                         match ras_ext sp with
                         | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                         | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
                         end)
                | EA_AArch64 =>
                    match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
                    | true, RAE_None =>
                        v_m = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                    | false, RAE_None =>
                        @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive v_m) = v
                    | false, RAE_SignExt =>
                        @Integers.repr 32%positive (@Integers.unsigned 64%positive v_m) =
                        @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
                    | false, RAE_ZeroExt =>
                        @Integers.repr 32%positive (@Integers.unsigned 64%positive v_m) =
                        @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
                    | _, _ => False
                    end
                end) /\
           dv_i = DVALUE_Base (@DVALUE_I Pa (mcs_ret_width c) (rv_trunc_ret_val (mcs_ret_width c) ret_m))) in
    (exists tr_ir_pre,
       prefix_matches rel tr_ir_pre evs_mc /\
       cfg_call_steps_to_ub genv default_draw_strat env_cur it_cur tr_ir_pre) \/
    (exists tr_ir env_out dv_ir,
       Forall2 rel evs_mc tr_ir /\
       cfg_call_steps_to_ret genv default_draw_strat env_cur it_cur tr_ir default_draw_strat env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w v_mc_ret))).
Proof.
  intros arch callees ret_w genv penv t_ir;
    induction t_ir as [rw e_ir | | cond dt IHt df IHf | cn_ir args_ir rw_ir rv_ir c_ir IHc];
    intros t_mc path obls allowed_ir env_cur it_cur evs_mc v_mc_ret
           Hcs Hpath Hobls Hco Hwf_ir Hden Hmt rel.
  - (* ICT_Ret *)
    revert obls Hobls Hco.
    induction Hmt as [p0 ret_e v0 Hev_mc | p0 cond0 mt mf b tr_v v0 Hev_c Hmt_r IHm | p0 cn_m aes rw_m rext rv_m ohi cont avals a0r vc tr_v v0];
      intros obls Hobls Hco.
    + cbn [collect_call_obls collect_call_obls_acc collect_call_obls_ret_acc] in Hco.
      destruct (Pos.eqb rw ret_w) eqn:Erw; [| discriminate Hco].
      apply Pos.eqb_eq in Erw; subst rw.
      inversion Hco; subst obls; clear Hco.
      inversion Hobls as [| ? ? Ho _]; subst.
      destruct Hden as [_ (env_out & dv_ir & Hev_ir & _ & Hst)].
      pose proof (Ho eq_refl ltac:(discriminate) Hpath) as Href.
      cbn [refine_eou_dvalue] in Href; rewrite Hev_ir, Hev_mc in Href.
      right; exists [], env_out, dv_ir; repeat split; [constructor | exact (Hst default_draw_strat) | exact Href].
    + rewrite collect_call_obls_mct_branch in Hco by ltac:(discriminate).
      destruct (collect_call_obls arch callees ret_w ((true, cond0) :: p0) (ICT_Ret rw e_ir) mt) as [| o1] eqn:Eo1;
        [discriminate Hco |].
      destruct (collect_call_obls arch callees ret_w ((false, cond0) :: p0) (ICT_Ret rw e_ir) mf) as [| o2] eqn:Eo2;
        [discriminate Hco |].
      inversion Hco; subst obls; rewrite Forall_app in Hobls; destruct Hobls as [Ho2 Ho1].
      assert (Hpath' : forall b0 c0, In (b0, c0) ((b, cond0) :: p0) ->
        eval_closed_cert_expr penv dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Hev_c | exact (Hpath b0 c0 Hin)]. }
      destruct b; [exact (IHm Hpath' _ Ho1 Eo1) | exact (IHm Hpath' _ Ho2 Eo2)].
    + cbn [collect_call_obls collect_call_obls_acc collect_call_obls_ret_acc] in Hco;
        destruct p0; [discriminate Hco |].
      rewrite app_nil_r in Hco; inversion Hco; subst obls.
      exfalso; exact (imposs_obl_absurd penv dummy_freeze_oracle None false _ (fun C => ltac:(discriminate C)) Hpath Hobls).
  - (* ICT_UB *)
    cbn [ir_tree_denotes] in Hden.
    left; exists []; split; [constructor | exact (Hden default_draw_strat)].
  - (* ICT_Branch *)
    rewrite collect_call_obls_ict_branch in Hco.
    destruct (collect_call_obls arch callees ret_w ((true, cond) :: path) dt t_mc) as [| o1] eqn:Eo1;
      [discriminate Hco |].
    destruct (collect_call_obls arch callees ret_w ((false, cond) :: path) df t_mc) as [| o2] eqn:Eo2;
      [discriminate Hco |].
    inversion Hco; subst obls; rewrite Forall_app in Hobls; destruct Hobls as [Ho2 Ho1].
    cbn [ir_call_tree_wf] in Hwf_ir; destruct Hwf_ir as [_ [Hwf_t Hwf_f]].
    cbn [ir_tree_denotes] in Hden; destruct Hden as [[_ Hub] | [b [Hev Hb]]].
    + left; exists []; split; [constructor | exact (Hub default_draw_strat)].
    + assert (Hpath' : forall b0 c0, In (b0, c0) ((b, cond) :: path) ->
        eval_closed_cert_expr penv dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Hev | exact (Hpath b0 c0 Hin)]. }
      pose proof (mc_tree_path_ok_repath penv ret_w path ((b, cond) :: path) t_mc evs_mc v_mc_ret Hmt) as Hmt'.
      destruct b;
        [exact (IHt t_mc ((true, cond) :: path) o1 allowed_ir env_cur it_cur evs_mc v_mc_ret Hcs Hpath' Ho1 Eo1 Hwf_t Hb Hmt')
        | exact (IHf t_mc ((false, cond) :: path) o2 allowed_ir env_cur it_cur evs_mc v_mc_ret Hcs Hpath' Ho2 Eo2 Hwf_f Hb Hmt')].
  - (* ICT_Call *)
    cbn [ir_call_tree_wf] in Hwf_ir; destruct Hwf_ir as [_ [Hsup_c Hwf_c]].
    revert obls Hobls Hco.
    induction Hmt as [p0 ret_e v0 Hev_mc | p0 cond0 mt mf b tr_v v0 Hev_c Hmt_r IHm
                     | p0 cn_m aes rw_m rext rv_m ohi cont avals a0r vc tr_v v0 Hfa_mc Hrv_m Hvc_eq Hmt_cont _];
      intros obls Hobls Hco.
    + unfold collect_call_obls in Hco; rewrite collect_call_obls_acc_ict_call_ret in Hco;
        destruct p0; [discriminate Hco |].
      rewrite app_nil_r in Hco; inversion Hco; subst obls.
      exfalso; exact (imposs_obl_absurd penv dummy_freeze_oracle None false _ (fun C => ltac:(discriminate C)) Hpath Hobls).
    + rewrite collect_call_obls_mct_branch in Hco by ltac:(discriminate).
      destruct (collect_call_obls arch callees ret_w ((true, cond0) :: p0) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mt)
        as [| o1] eqn:Eo1; [discriminate Hco |].
      destruct (collect_call_obls arch callees ret_w ((false, cond0) :: p0) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mf)
        as [| o2] eqn:Eo2; [discriminate Hco |].
      inversion Hco; subst obls; rewrite Forall_app in Hobls; destruct Hobls as [Ho2 Ho1].
      assert (Hpath' : forall b0 c0, In (b0, c0) ((b, cond0) :: p0) ->
        eval_closed_cert_expr penv dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Hev_c | exact (Hpath b0 c0 Hin)]. }
      destruct b; [exact (IHm Hpath' _ Ho1 Eo1) | exact (IHm Hpath' _ Ho2 Eo2)].
    + unfold collect_call_obls in Hco; rewrite collect_call_obls_acc_ict_call_call in Hco.
      destruct (String.eqb cn_ir cn_m && Pos.eqb rw_ir rw_m && String.eqb rv_ir rv_m) eqn:Em.
      * rewrite !andb_true_iff in Em; destruct Em as [[Ecn Erw] Erv].
        apply String.eqb_eq in Ecn; apply Pos.eqb_eq in Erw; apply String.eqb_eq in Erv; subst cn_m rw_m rv_m.
        destruct (find_callee_spec callees cn_ir) as [sp |] eqn:Efc; [| discriminate Hco].
        destruct (Pos.eqb rw_ir (mcs_ret_width sp)) eqn:Ewrw; [apply Pos.eqb_eq in Ewrw | discriminate Hco].
        unfold build_call_arg_obls in *;
          destruct (build_call_arg_obls_acc cn_ir 0%nat arch p0 (mcs_args sp) args_ir aes []) as [| aobls] eqn:Ebao; [discriminate Hco |].
        rewrite collect_call_obls_acc_shift in Hco; unfold collect_call_obls in Hco.
        destruct (collect_call_obls_acc arch callees ret_w p0 c_ir cont []) as [| cobls] eqn:Eco;
          cbn [mcc_sum_map] in Hco; [discriminate Hco |].
        inversion Hco; subst obls; rewrite Forall_app in Hobls; destruct Hobls as [Hcobls Haobls].
        pose proof (find_callee_spec_in _ _ _ Efc) as [Hin_sp Hstrip].
        destruct (Hcs sp Hin_sp) as [Hvs_sp Hnd_sp].
        assert (Hvs_f : Forall rv_valid_arg_spec (mcs_args sp))
          by (apply Forall_forall; apply forallb_forall; exact Hvs_sp).
        cbn [ir_tree_denotes] in Hden; destruct Hden as [Hub | (dvs & Hfa_ir & Hk)].
        -- left; exists []; split; [constructor | exact (Hub default_draw_strat)].
        -- assert (Herv : penv rv_ir = Some (DVALUE_Base (@DVALUE_I Pa rw_ir vc))) by exact Hrv_m.
           destruct (Hk vc Herv) as (env1 & t1 & Hret1 & Hub1 & Hden1).
           destruct (@build_call_arg_obls_list_matches Pa cn_ir arch penv p0 (mcs_args sp) args_ir aes aobls avals dvs
                       Hpath Haobls Ebao Hvs_f Hnd_sp Hfa_ir Hfa_mc)
             as (Hlen_v & Hlen_a & Hitem).
           assert (Hrel_hd :
             rel (cn_ir, avals, a0r)
                 (cn_ir, dvs, DVALUE_Base (@DVALUE_I Pa rw_ir vc))).
           { unfold rel; split; [reflexivity |].
             exists sp; repeat split; try assumption.
             subst rw_ir vc; reflexivity. }
           destruct (IHc cont p0 cobls ((rv_ir, rw_ir) :: allowed_ir) env1 t1 tr_v v0
                       Hcs Hpath Hcobls Eco Hwf_c Hden1 Hmt_cont)
             as [[tr_pre [Hpm Hub_t]] | (tr_t & env_out & dv_ir & Hfa_t & Hret_t & Href_t)].
           ++ left; exists ((cn_ir, dvs, DVALUE_Base (@DVALUE_I Pa rw_ir vc)) :: tr_pre); split.
              ** constructor; [exact Hrel_hd | exact Hpm].
              ** exact (Hub1 default_draw_strat tr_pre Hub_t).
           ++ right; exists ((cn_ir, dvs, DVALUE_Base (@DVALUE_I Pa rw_ir vc)) :: tr_t), env_out, dv_ir;
                repeat split; [constructor; [exact Hrel_hd | exact Hfa_t] | exact (Hret1 default_draw_strat tr_t default_draw_strat env_out dv_ir Hret_t) | exact Href_t].
      * destruct p0; [discriminate Hco |].
        rewrite app_nil_r in Hco; inversion Hco; subst obls.
        exfalso; exact (imposs_obl_absurd penv dummy_freeze_oracle None false _ (fun C => ltac:(discriminate C)) Hpath Hobls).
Qed.

(** *** 5.5 Ghost Call-Variable Filling & End-to-End Call Validator Soundness *)

Lemma reify_ir_code_calls_vars_bang :
  forall cur_bid callees c cid lmap k_end t,
    (forall cid' lmap' t', k_end cid' lmap' = inr t' ->
       forall nm w, In (nm, w) (collect_ir_call_vars t') -> mc_starts_with_bang nm = true) ->
    reify_ir_code_calls cur_bid callees c cid lmap k_end = inr t ->
    forall nm w, In (nm, w) (collect_ir_call_vars t) -> mc_starts_with_bang nm = true.
Proof.
  intros cur_bid callees c; induction c as [| [[iid ins] md] rest IH];
    intros cid lmap k_end t Hk Hrc nm w Hin; cbn [reify_ir_code_calls] in Hrc.
  - exact (Hk cid lmap t Hrc nm w Hin).
  - destruct iid as [id | vid];
      [| destruct ins; try discriminate Hrc; exact (IH cid lmap k_end t Hk Hrc nm w Hin)].
    destruct ins; try discriminate Hrc.
    + destruct (reify_pure_exp lmap None op) as [[? ?] |]; [| discriminate Hrc].
      destruct (ub_free_expr _); cbn [negb] in Hrc; [| discriminate Hrc].
      destruct (expr_has_freeze _); [discriminate Hrc |].
      exact (IH cid _ k_end t Hk Hrc nm w Hin).
    + destruct fn as [dt_ret fn_e].
      destruct (match_pure_int_intrinsic_call (INSTR_Call (dt_ret, fn_e) args anns obs)) as [[op wi a0 a1 | wi a0 fl] |] eqn:Epic.
      * destruct (match metadata_range md with None => true | Some _ => false end) eqn:Emr; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wi))) a0) as [[? ?] |] eqn:Ea0; [| discriminate Hrc].
        destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wi))) a1) as [[? ?] |] eqn:Ea1; [| discriminate Hrc].
        destruct (ub_free_expr _ && ub_free_expr _) eqn:Euf; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (expr_has_freeze _ || expr_has_freeze _); [discriminate Hrc |].
        exact (IH cid _ k_end t Hk Hrc nm w Hin).
      * destruct (match metadata_range md with None => true | Some _ => false end) eqn:Emr; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wi))) a0) as [[? ?] |] eqn:Ea0; [| discriminate Hrc].
        destruct (ub_free_expr _) eqn:Euf; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (expr_has_freeze _); [discriminate Hrc |].
        exact (IH cid _ k_end t Hk Hrc nm w Hin).
      * destruct dt_ret as [bdt | |]; [destruct bdt as [rw | | | | | | | | | |] | |];
          destruct fn_e;
          try match goal with iv : ident |- _ => destruct iv as [[cname | | ] | ?] end;
          destruct obs; try discriminate Hrc.
        destruct (match @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname))) with None => true | Some _ => false end); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (cconv_eqb (anns_cconv anns) CC_Ccc); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (match metadata_range md with None => true | Some _ => false end); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (fattrs_call_ok (ann_fun_attributes anns)); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (pattrs_no_value_poison (ann_ret_attributes anns)); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (is_supported_bit_width rw); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (find_callee_spec callees cname) as [sp |] eqn:Efc; [| discriminate Hrc].
        destruct (Pos.eqb rw (mcs_ret_width sp)) eqn:Erw; [| discriminate Hrc].
        destruct (reify_ir_call_args cname 0%nat lmap (mcs_args sp) args) as [| aes] eqn:Eaes; [discriminate Hrc |].
        destruct (reify_ir_code_calls cur_bid callees rest (S cid) _ k_end) as [| cont] eqn:Ect; [discriminate Hrc |].
        inversion Hrc; subst t; clear Hrc;
        unfold collect_ir_call_vars in Hin; cbn [collect_ir_call_vars_acc] in Hin;
        rewrite collect_ir_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [Hr | [Heq | []]];
        [exact (IH _ _ _ _ Hk Ect nm w Hr) | inversion Heq; subst; apply mc_call_ret_var_bang].
Qed.

Lemma reify_ir_call_at_vars_bang :
  forall fuel callees bmap ret_w visited is_entry bid_from cur_bid cid lmap t,
    reify_ir_call_at fuel callees bmap ret_w visited is_entry bid_from cur_bid cid lmap = inr t ->
    forall nm w, In (nm, w) (collect_ir_call_vars t) -> mc_starts_with_bang nm = true.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros callees bmap ret_w visited is_entry bid_from cur_bid cid lmap t Hrec;
    cbn [reify_ir_call_at] in Hrec;
    destruct (raw_id_in_list cur_bid visited); try discriminate Hrec.
  destruct (RM.find cur_bid bmap) as [b |]; [| discriminate Hrec].
  match type of Hrec with
  | match ?x with inl _ => _ | inr _ => _ end = _ => destruct x as [| lmap1]; [discriminate Hrec |]
  end.
  eapply reify_ir_code_calls_vars_bang; [| exact Hrec].
  intros cid' lmap' t' Ht' nm w Hin.
  destruct (fst (blk_term b)) as [_ term]; destruct term; try discriminate Ht';
    try (inversion Ht'; subst t'; contradiction Hin).
  - match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] op] end; try discriminate Ht'.
    destruct (Pos.eqb rw ret_w); [| discriminate Ht'].
    destruct (reify_pure_exp lmap' _ op) as [[? ret_e] |]; [| discriminate Ht'].
    destruct (ub_free_expr ret_e); cbn [negb] in Ht'; [| discriminate Ht'].
    destruct (expr_has_freeze ret_e); inversion Ht'; subst t'; contradiction Hin.
  - match goal with x : texp dtyp |- _ => destruct x as [[[w0 | | | | | | | | | |] | |] e_cond] end; try discriminate Ht'.
    destruct w0; try discriminate Ht'.
    destruct (reify_pure_exp lmap' _ e_cond) as [[? cond_e] |]; [| discriminate Ht'].
    destruct (ub_free_expr cond_e); cbn [negb] in Ht'; [| discriminate Ht'].
    destruct (expr_has_freeze cond_e); [discriminate Ht' |].
    destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' lmap') as [| dt1] eqn:Edt; [discriminate Ht' |].
    destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' lmap') as [| df1] eqn:Edf; [discriminate Ht' |].
    inversion Ht'; subst t';
      unfold collect_ir_call_vars in Hin; cbn [collect_ir_call_vars_acc] in Hin;
      rewrite collect_ir_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [Hin | Hin];
      [exact (IH _ _ _ _ _ _ _ _ _ _ Edf nm w Hin) | exact (IH _ _ _ _ _ _ _ _ _ _ Edt nm w Hin)].
  - exact (IH _ _ _ _ _ _ _ _ _ _ Ht' nm w Hin).
Qed.

Lemma summarize_rv64_call_at_vars_bang :
  forall fuel im callees visited pc cid sp_off vrf astk ret_w t,
    summarize_rv64_call_at fuel im callees visited pc cid sp_off vrf astk ret_w = inr t ->
    forall nm w, In (nm, w) (collect_mc_call_vars t) -> mc_starts_with_bang nm = true.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros im callees visited pc cid sp_off vrf astk ret_w t Hsum nm w Hin;
    cbn [summarize_rv64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |]; [| discriminate Hsum].
  destruct (drci_inst dec) as [i | cname].
  - destruct (rv_sym_step_one (mk_decoded_rv (drci_off dec) (drci_len dec) i) pc sp_off vrf astk ret_w)
      as [[npc sp' vrf' astk' | cond tpc npc | ret_e] |] eqn:Est; try discriminate Hsum.
    + exact (IH _ _ _ _ _ _ _ _ _ _ Hsum nm w Hin).
    + destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk ret_w) as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk ret_w) as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t;
        unfold collect_mc_call_vars in Hin; cbn [collect_mc_call_vars_acc] in Hin;
        rewrite collect_mc_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [H | H];
        [exact (IH _ _ _ _ _ _ _ _ _ _ Hdf nm w H) | exact (IH _ _ _ _ _ _ _ _ _ _ Hdt nm w H)].
    + inversion Hsum; subst t; contradiction Hin.
  - destruct (mc_sp_aligned16 sp_off); cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |]; [| discriminate Hsum].
    destruct (rv_sym_read_call_args_from pc cname 10%N (List.length (mcs_args c)) vrf); [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) (pc + drci_len dec)%N (S cid) sp_off (rv_post_call_vrf cid c vrf) astk ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t;
      unfold collect_mc_call_vars in Hin; cbn [collect_mc_call_vars_acc] in Hin;
      rewrite collect_mc_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [Hr | Hh];
      [exact (IH _ _ _ _ _ _ _ _ _ _ Ect nm w Hr) |].
    destruct opt_hi as [hn |] eqn:Eoh.
    + destruct Hh as [Heq | [Heq | []]]; inversion Heq; subst.
      * apply mc_call_ret_var_bang.
      * unfold mc_post_call_ret_expr in Epc; destruct (Pos.eqb _ 64%positive); [discriminate Epc |].
        destruct (mcs_ret_ext c); inversion Epc; apply mc_call_hi_var_bang.
    + destruct Hh as [Heq | []]; inversion Heq; subst; apply mc_call_ret_var_bang.
Qed.

Lemma summarize_a64_call_at_vars_bang :
  forall fuel im callees visited pc cid sp_off vrf astk sfl fl_def ret_w t,
    summarize_a64_call_at fuel im callees visited pc cid sp_off vrf astk sfl fl_def ret_w = inr t ->
    forall nm w, In (nm, w) (collect_mc_call_vars t) -> mc_starts_with_bang nm = true.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros im callees visited pc cid sp_off vrf astk sfl fl_def ret_w t Hsum nm w Hin;
    cbn [summarize_a64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |]; [| discriminate Hsum].
  destruct (daci_inst dec) as [i | cname].
  - destruct (a64_sym_step_one (mk_decoded_a64_inst (daci_off dec) i) pc sp_off vrf astk sfl fl_def ret_w)
      as [[npc sp' vrf' astk' sfl' fl_def' | cond tpc npc fl_def' | ret_e] |] eqn:Est; try discriminate Hsum.
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hsum nm w Hin).
    + destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk sfl fl_def' ret_w) as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk sfl fl_def' ret_w) as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t;
        unfold collect_mc_call_vars in Hin; cbn [collect_mc_call_vars_acc] in Hin;
        rewrite collect_mc_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [H | H];
        [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hdf nm w H) | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hdt nm w H)].
    + inversion Hsum; subst t; contradiction Hin.
  - destruct (mc_sp_aligned16 sp_off); cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |]; [| discriminate Hsum].
    destruct (a64_sym_read_call_args_from pc cname 0%N (List.length (mcs_args c)) vrf); [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) (pc + 4%N)%N (S cid) sp_off (a64_post_call_vrf cid c vrf) astk sfl false ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t;
      unfold collect_mc_call_vars in Hin; cbn [collect_mc_call_vars_acc] in Hin;
      rewrite collect_mc_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [Hr | Hh];
      [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Ect nm w Hr) |].
    destruct opt_hi as [hn |] eqn:Eoh.
    + destruct Hh as [Heq | [Heq | []]]; inversion Heq; subst.
      * apply mc_call_ret_var_bang.
      * unfold mc_post_call_ret_expr in Epc; destruct (Pos.eqb _ 64%positive); [discriminate Epc |].
        destruct (mcs_ret_ext c); inversion Epc; apply mc_call_hi_var_bang.
    + destruct Hh as [Heq | []]; inversion Heq; subst; apply mc_call_ret_var_bang.
Qed.

Section CallGhostFilling.
  Context {Pa : Params}.

  Definition call_extra_binds
    (new_binds : list (string * @dvalue Pa)) (call_vars : list (string * positive))
    : list (string * @dvalue Pa) :=
    List.map
      (fun '(nm, w) => (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
      (List.filter (fun '(nm, _) => negb (existsb (String.eqb nm) (List.map fst new_binds))) call_vars).

  Lemma call_extra_binds_props :
    forall allowed0 mc_vars call_vars all_vars (penv0 : param_env Pa) new_binds,
      (forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false) ->
      (forall nm w, In (nm, w) call_vars -> mc_starts_with_bang nm = true) ->
      NoDup (List.map fst call_vars) ->
      NoDup (List.map fst all_vars) ->
      (forall nm w, In (nm, w) call_vars -> In (nm, w) all_vars) ->
      (forall nm w, In (nm, w) allowed0 -> In (nm, w) all_vars) ->
      (forall nm w, In (nm, w) all_vars -> In (nm, w) allowed0 \/ In (nm, w) call_vars) ->
      (forall nm w, In (nm, w) mc_vars -> In (nm, w) all_vars) ->
      NoDup (List.map fst new_binds) ->
      (forall nm, In nm (List.map fst new_binds) -> mc_starts_with_bang nm = true) ->
      (forall nm dv, In (nm, dv) new_binds ->
         exists w, In (nm, w) mc_vars /\ exists v : @Integers.bit_int w, dv = DVALUE_Base (@DVALUE_I Pa w v)) ->
      wf_param_env_for allowed0 penv0 ->
      (forall penv' : param_env Pa,
         (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
         ub_ctx_holds penv' dummy_freeze_oracle []) ->
      let extra_binds := call_extra_binds new_binds call_vars in
      let penv_full := overlay_penv (new_binds ++ extra_binds) penv0 in
      binds_disjoint_from allowed0 extra_binds /\
      (forall nm, In nm (List.map fst new_binds) -> ~ In nm (List.map fst extra_binds)) /\
      (forall nm, mc_starts_with_bang nm = false -> penv_full nm = penv0 nm) /\
      wf_param_env_for all_vars penv_full /\
      ub_ctx_holds penv_full dummy_freeze_oracle (List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars).
  Proof.
    intros allowed0 mc_vars call_vars all_vars penv0 new_binds
           Hnb_al Hnb_cv Hnd_cv Hnd_av Hcv_av Hal_av Hav_sp Hmv_av Hnd_nb Hnb_nb Hnb_vals Hpenv0 _ extra_binds penv_full.
    assert (Hextra_bang : forall nm, In nm (List.map fst extra_binds) -> mc_starts_with_bang nm = true).
    { intros nm Hin; unfold extra_binds, call_extra_binds in Hin.
      rewrite map_map in Hin; apply in_map_iff in Hin as [[nm0 w0] [Heq Hflt]]; cbn in Heq; subst nm0.
      apply filter_In in Hflt as [Hcv _]; exact (Hnb_cv nm w0 Hcv). }
    assert (Hdisj_eb : binds_disjoint_from allowed0 extra_binds).
    { intros nm w Hal Hin; pose proof (Hnb_al nm w Hal) as Hb0; pose proof (Hextra_bang nm Hin) as Hb1; congruence. }
    assert (Hdisj_nb_eb : forall nm, In nm (List.map fst new_binds) -> ~ In nm (List.map fst extra_binds)).
    { intros nm HinN HinE; unfold extra_binds, call_extra_binds in HinE; rewrite map_map in HinE.
      apply in_map_iff in HinE as [[nm0 w0] [Heq Hflt]]; cbn in Heq; subst nm0.
      apply filter_In in Hflt as [_ Hneg]; apply negb_true_iff in Hneg.
      assert (Hex : existsb (String.eqb nm) (List.map fst new_binds) = true)
        by (apply existsb_exists; exists nm; split; [exact HinN | apply String.eqb_refl]).
      congruence. }
    assert (Hpres_nonbang : forall nm, mc_starts_with_bang nm = false -> penv_full nm = penv0 nm).
    { intros nm Hnb; unfold penv_full; apply overlay_penv_not_in; intro Hin.
      rewrite map_app in Hin; apply in_app_iff in Hin as [Hin | Hin];
        [pose proof (Hnb_nb nm Hin) | pose proof (Hextra_bang nm Hin)]; congruence. }
    assert (Hnd_comb : NoDup (List.map fst (new_binds ++ extra_binds))).
    { rewrite map_app; apply NoDup_app; [exact Hnd_nb | |].
      - unfold extra_binds, call_extra_binds.
        assert (Hmfst : List.map fst (List.map (fun '(nm, w) => (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
                                        (List.filter (fun '(nm, _) => negb (existsb (String.eqb nm) (List.map fst new_binds))) call_vars)) =
                        List.filter (fun nm => negb (existsb (String.eqb nm) (List.map fst new_binds))) (List.map fst call_vars)).
        { clear; induction call_vars as [| [a w] r IH]; cbn; [reflexivity |].
          destruct (negb (existsb (String.eqb a) (List.map fst new_binds))); cbn; [f_equal |]; exact IH. }
        rewrite Hmfst; apply NoDup_filter; exact Hnd_cv.
      - exact Hdisj_nb_eb. }
    assert (Hcv_val : forall nm w, In (nm, w) call_vars ->
      exists v : @Integers.bit_int w, penv_full nm = Some (DVALUE_Base (@DVALUE_I Pa w v))).
    { intros nm w Hcv.
      destruct (in_dec String.string_dec nm (List.map fst new_binds)) as [HinN | HnotN].
      - apply in_map_iff in HinN as [[nm0 dv0] [Heq HinP]]; cbn in Heq; subst nm0.
        destruct (Hnb_vals nm dv0 HinP) as (w' & Hmv' & v' & ->).
        pose proof (Hcv_av nm w Hcv) as Hav1.
        pose proof (Hmv_av nm w' Hmv') as Hav2.
        assert (Hw_eq : w' = w).
        { clear -Hnd_av Hav1 Hav2; induction all_vars as [| [x wx] rest IH]; cbn in *; [contradiction |].
          inversion Hnd_av as [| ? ? Hni Hndr]; subst.
          destruct Hav1 as [H1 | H1], Hav2 as [H2 | H2].
          - inversion H1; inversion H2; congruence.
          - inversion H1; subst; exfalso; apply Hni; apply in_map_iff; exists (nm, w'); split; [reflexivity | exact H2].
          - inversion H2; subst; exfalso; apply Hni; apply in_map_iff; exists (nm, w); split; [reflexivity | exact H1].
          - exact (IH Hndr H1 H2). }
        subst w'; exists v'; unfold penv_full; apply overlay_penv_lookup_in; [exact Hnd_comb |].
        apply in_or_app; left; exact HinP.
      - assert (HinE : In (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))) extra_binds).
        { unfold extra_binds, call_extra_binds; apply in_map_iff; exists (nm, w); split; [reflexivity |].
          apply filter_In; split; [exact Hcv | apply negb_true_iff].
          destruct (existsb (String.eqb nm) (List.map fst new_binds)) eqn:Eex; [| reflexivity].
          exfalso; apply existsb_exists in Eex as [y [Hy Heqy]]; apply String.eqb_eq in Heqy; subst y; contradiction. }
        exists (@Integers.zero w); unfold penv_full; apply overlay_penv_lookup_in; [exact Hnd_comb |].
        apply in_or_app; right; exact HinE. }
    repeat split; try assumption.
    - intros nm w Hav; destruct (Hav_sp nm w Hav) as [Hal | Hcv].
      + rewrite (Hpres_nonbang nm (Hnb_al nm w Hal)); exact (Hpenv0 nm w Hal).
      + destruct (Hcv_val nm w Hcv) as [v Hv]; exists (DVALUE_Base (@DVALUE_I Pa w v)); split; [exact Hv | right; exists v; reflexivity].
    - apply Forall_forall; intros u Hu; apply in_map_iff in Hu as [[nm w] [<- Hcv]].
      destruct (Hcv_val nm w Hcv) as [v Hv]; cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hv in Hdv; inversion Hdv; discriminate.
  Qed.

End CallGhostFilling.

Lemma mc_no_dup_strings_spec : forall xs,
  mc_no_dup_strings xs = true -> NoDup xs.
Proof.
  induction xs as [| x rest IH]; intros H; [constructor |].
  cbn in H; apply andb_true_iff in H as [Hneg Hnd]; apply negb_true_iff in Hneg.
  constructor; [| exact (IH Hnd)].
  intro Hin; unfold mc_str_in_list in Hneg;
    assert (Hex : existsb (String.eqb x) rest = true) by (apply existsb_exists; exists x; split; [exact Hin | apply String.eqb_refl]);
    congruence.
Qed.

Theorem validate_mc_call_rv64_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
         (insts : list decoded_rv_call_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
         (callees : list mc_callee_spec) (opt_pf : option (list lrat_step))
         arg_dtys vs (penv0 : param_env Pa) rf0 mstk0,
    validate_mc_call_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees opt_pf = inr tt ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    cfg_param_dtyp_compatible ir_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx sp,
       nth_error arg_specs idx = Some sp ->
       nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I (ras_width sp))) /\
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some (ras_name sp)) ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (param_idx_uses_cfg ir_cfg) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed0) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv0 nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed0) ->
    mc_valid_sp0_depth 2%nat (rv_read_reg 2%N rf0) ->
    rv_rf_matches_args penv0 arg_specs rf0 ->
    rv_call_sound_spec ir_cfg insts ret_w callees vs rf0 mstk0.
Proof.
  intros ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees opt_pf
         arg_dtys vs penv0 rf0 mstk0
         Hval Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp Hty Hargs_compat Hpu Hpenv_eq Hpenv0 Hctx0 Hargs_al Hsp0 Hm.
  unfold validate_mc_call_rv64, build_mc_call_bundle_rv64 in Hval.
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hval; [| discriminate Hval].
  destruct (forallb rv_call_inst_no_word_mulh insts) eqn:Hmul; cbn [negb] in Hval; [| discriminate Hval].
  destruct (Nat.leb (List.length arg_specs) 8) eqn:Hlen_a; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) eqn:Hnb_al_b;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (forallb (fun c => rv_supported_arg_width (mcs_ret_width c) &&
                              Nat.leb (List.length (mcs_args c)) 8 &&
                              forallb rv_valid_arg_spec (mcs_args c) &&
                              mc_no_dup_strings (List.map ras_name (mcs_args c))) callees) eqn:Hcal_b;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (reify_ir_call_tree ir_cfg arg_specs callees ret_w) as [| t_ir] eqn:Eir; [discriminate Hval |].
  destruct (summarize_rv64_call_tree insts callees arg_specs ret_w) as [| t_mc] eqn:Emc; [discriminate Hval |].
  destruct (collect_call_obls EA_Riscv64 callees ret_w [] t_ir t_mc) as [| obls] eqn:Eco; [discriminate Hval |].
  set (raw_cvars := collect_ir_call_vars_acc t_ir (collect_mc_call_vars_acc t_mc [])) in *.
  set (call_vars := dedup_typed_vars raw_cvars) in *.
  set (all_vars := dedup_typed_vars_acc allowed0 call_vars) in *.
  destruct (vars_width_consistent allowed0 all_vars && vars_width_consistent raw_cvars all_vars) eqn:Evwc;
    cbn [negb] in Hval; [| discriminate Hval].
  apply andb_true_iff in Evwc as [Evwc_al Evwc_cv].
  destruct (forallb (obl_wf_exprs all_vars) obls) eqn:Ewf_o; cbn [negb] in Hval; [| discriminate Hval].
  cbn [mccb_ctx mccb_all_vars mccb_obls] in Hval.
  destruct (check_mc_loop_obls "mc-call" (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars)
              all_vars None obls opt_pf) as [| []] eqn:Hchk; [discriminate Hval |].
  clear Hval.
  assert (Hnb_al : forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false).
  { intros nm w Hin; rewrite forallb_forall in Hnb_al_b; pose proof (Hnb_al_b (nm, w) Hin) as Hn; apply negb_true_iff in Hn; exact Hn. }
  assert (Hcws : forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true).
  { intros c Hc; rewrite forallb_forall in Hcal_b; pose proof (Hcal_b c Hc) as Ht;
      rewrite !andb_true_iff in Ht; exact (proj1 (proj1 (proj1 Ht))). }
  assert (Hcs : forall c, In c callees -> forallb rv_valid_arg_spec (mcs_args c) = true /\ NoDup (List.map ras_name (mcs_args c))).
  { intros c Hc; rewrite forallb_forall in Hcal_b; pose proof (Hcal_b c Hc) as Ht;
      rewrite !andb_true_iff in Ht; destruct Ht as [[[_ _] Hva] Hnd]; split; [exact Hva | apply mc_no_dup_strings_spec; exact Hnd]. }
  assert (Hnb_cv : forall nm w, In (nm, w) call_vars -> mc_starts_with_bang nm = true).
  { intros nm w Hcv; apply dedup_typed_vars_sub in Hcv; unfold raw_cvars in Hcv;
      rewrite collect_ir_call_vars_acc_shift in Hcv; apply in_app_iff in Hcv as [H1 | H2].
    - eapply reify_ir_call_at_vars_bang; [exact Eir | exact H1].
    - eapply summarize_rv64_call_at_vars_bang; [exact Emc | exact H2]. }
  assert (Hcv_av : forall nm w, In (nm, w) call_vars -> In (nm, w) all_vars).
  { intros nm w Hcv; apply dedup_typed_vars_sub in Hcv.
    exact (vars_width_consistent_in _ _ _ _ Evwc_cv Hcv). }
  assert (Hal_av : forall nm w, In (nm, w) allowed0 -> In (nm, w) all_vars)
    by (intros nm w Hal; exact (vars_width_consistent_in _ _ _ _ Evwc_al Hal)).
  assert (Hmv_av : forall nm w, In (nm, w) (collect_mc_call_vars t_mc) -> In (nm, w) all_vars).
  { intros nm w Hmv; eapply vars_width_consistent_in; [exact Evwc_cv |].
    unfold raw_cvars; rewrite collect_ir_call_vars_acc_shift; apply in_or_app; right; exact Hmv. }
  assert (Hav_sp : forall nm w, In (nm, w) all_vars -> In (nm, w) allowed0 \/ In (nm, w) call_vars)
    by (intros nm w Hav; exact (dedup_typed_vars_acc_sub allowed0 call_vars nm w Hav)).
  intros genv O Hgenv HO; cbn [rv_call_sound_spec].
  assert (Hsp2_init : rv_val_read 2%N (rv_build_init_val_regs 10%N arg_specs) = MSV_StackPtr 0%Z)
    by (unfold rv_val_read; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity).
  assert (Hfresh0 : forall nm w, In (nm, w) allowed0 -> forall k' w', (0 <= k')%nat ->
    nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').
  { intros nm w Hal k' w' _; pose proof (Hnb_al nm w Hal) as Hnb; split; intro Heq; subst;
      [rewrite mc_call_ret_var_bang in Hnb | rewrite mc_call_hi_var_bang in Hnb]; discriminate Hnb. }
  unfold summarize_rv64_call_tree in Emc; rewrite elf_length_tr_eq in Emc.
  destruct (summarize_rv64_call_at_exec insts (pt_of_list_first drci_off insts) (pt_of_list_first_lookup_rv_call insts)
              (S (2 * List.length insts)) callees PT_Empty 0%N 0%nat 0%Z
              (rv_build_init_val_regs 10%N arg_specs) [] ret_w allowed0 t_mc O penv0 rf0 rf0 mstk0
              Hrw Hcws Hmul HO Hsp0 ltac:(unfold mc_frame_cap; lia) Hsp2_init
              (rv_init_val_regs_wf allowed0 arg_specs Hargs_al Hws) ltac:(constructor)
              Hfresh0 (rv_init_val_regs_agrees penv0 dummy_freeze_oracle arg_specs rf0 Hws Hm)
              (mc_sym_stack_agrees_empty _ _ _ _ _) Emc)
    as (tr_mc & new_binds & rf_end & mstk_end & Hnd_nb & Hdisj_nb & Hnb_form & Hnb_vals & Hexec & Hcs_mc & Hra_mc & Hmt_gen).
  assert (Hnb_nb : forall nm, In nm (List.map fst new_binds) -> mc_starts_with_bang nm = true).
  { intros nm Hin; destruct (Hnb_form nm Hin) as [k [_ [[w ->] | ->]]];
      [apply mc_call_ret_var_bang | apply mc_call_hi_var_bang]. }
  destruct (call_extra_binds_props allowed0 (collect_mc_call_vars t_mc) call_vars all_vars penv0 new_binds
              Hnb_al Hnb_cv (dedup_typed_vars_nodup _) (dedup_typed_vars_acc_nodup _ _ (dedup_typed_vars_nodup _))
              Hcv_av Hal_av Hav_sp Hmv_av Hnd_nb Hnb_nb Hnb_vals Hpenv0
              (fun _ _ => Forall_nil _))
    as (Hdisj_eb & Hdisj_nb_eb & Hpres_nb & Hwf_full & Hctx_call).
  set (extra_binds := call_extra_binds new_binds call_vars) in *.
  set (penv_full := overlay_penv (new_binds ++ extra_binds) penv0) in *.
  assert (Hctx_all : ub_ctx_holds penv_full dummy_freeze_oracle (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars))
    by (apply Forall_app; split; [exact (Hctx0 penv_full Hpres_nb) | exact Hctx_call]).
  pose proof (check_mc_loop_obls_sound _ _ _ _ _ _ penv_full dummy_freeze_oracle false Hchk Hwf_full Hctx_all) as Hobls_ok.
  assert (Hpenv_ir_eq : forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
    penv_full nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm).
  { intros nm Hin; rewrite (Hpres_nb nm), (Hpenv_eq nm Hin); [reflexivity |].
    apply in_map_iff in Hin as [id [<- _]]; unfold cert_reg_name; reflexivity. }
  assert (Hpu_as : forall idx w pnm,
    In (idx, DTYPE_Base (DTYPE_I w)) (arg_specs_uses_from 0%nat arg_specs) ->
    nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
    In (pnm, w) all_vars).
  { intros idx w pnm Hin Hpnm; apply arg_specs_uses_from_in in Hin as (k & sp & -> & Hnth & Heq_dt).
    inversion Heq_dt; subst w; destruct (Hargs_compat k sp Hnth) as [_ Hp_sp].
    cbn [Nat.add] in Hpnm; rewrite Hpnm in Hp_sp; inversion Hp_sp; subst pnm.
    exact (Hal_av _ _ (Hargs_al sp (nth_error_In _ _ Hnth))). }
  assert (Hcomp_as : forall idx dt,
    In (idx, dt) (arg_specs_uses_from 0%nat arg_specs) -> nth_error arg_dtys idx = Some dt).
  { intros idx dt Hin; apply arg_specs_uses_from_in in Hin as (k & sp & -> & Hnth & ->).
    cbn [Nat.add]; exact (proj1 (Hargs_compat k sp Hnth)). }
  assert (Hwf_ir_t : ir_call_tree_wf all_vars ret_w t_ir)
    by (exact (reify_ir_call_tree_wf ir_cfg arg_specs callees ret_w all_vars t_ir (rv_supported_to_is_supported _ Hrw) Hpu_as Eir)).
  pose proof (reify_ir_call_tree_exec genv penv_full ir_cfg arg_specs callees ret_w all_vars arg_dtys vs t_ir
                (rv_supported_to_is_supported _ Hrw) Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp_as Hty
                Hpu_as Hpenv_ir_eq Hwf_full Eir) as Hden_ir.
  pose proof (Hmt_gen extra_binds Hdisj_eb Hdisj_nb_eb) as Hmt_full.
  destruct (ir_mc_call_trees_sound EA_Riscv64 callees ret_w genv penv_full t_ir t_mc [] obls all_vars
              (init_cfg_locals (args ir_cfg) vs) (@denote_cfg Pa ir_cfg None) _ _
              Hcs (fun _ _ Hin => ltac:(contradiction Hin)) Hobls_ok Eco Hwf_ir_t Hden_ir Hmt_full)
    as [[tr_ir_pre [Hpm_pre Hub_ir]] | (tr_ir & env_out & dv_ir & Hfa_tr & Hret_ir & Href_ir)].
  - exists tr_mc, rf_end, mstk_end; repeat split; try assumption.
    left; exists default_draw_strat, tr_ir_pre;
      split; [exact default_draw_strat_wf | split; [| exact Hub_ir]].
    clear -Hpm_pre; generalize dependent tr_ir_pre; induction tr_mc as [| [[cn_m rf_c] a0_r] r_mc IH];
      intros [| [[cn_i vs_i] dv_i] r_i] Hpm; [constructor | inversion Hpm | constructor |].
    inversion Hpm as [| ? ? ? ? Hhd Htl]; subst; constructor; [| exact (IH _ Htl)].
    destruct Hhd as (Hcn & sp & Efc & Hin_sp & Hstrip & Hlen_a & Hlen_v & Hargs & Hdv).
    rewrite Efc in Hargs, Hlen_a.
    unfold rv_call_event_matches; split; [exact Hcn | exists sp; repeat split; try assumption].
    intros k sp0 Hlt Hsp0.
    assert (Evm : nth_error (List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_c) (seq 0 (List.length (mcs_args sp)))) k =
                  Some (rv_read_reg (10%N + N.of_nat k) rf_c))
      by (rewrite nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
    exact (Hargs k sp0 _ Hsp0 Evm).
  - exists tr_mc, rf_end, mstk_end; repeat split; try assumption.
    right; exists default_draw_strat, tr_ir, default_draw_strat, env_out, dv_ir;
      split; [exact default_draw_strat_wf | split; [| split; [exact Hret_ir | exact Href_ir]]].
    clear -Hfa_tr; generalize dependent tr_ir; induction tr_mc as [| [[cn_m rf_c] a0_r] r_mc IH];
      intros [| [[cn_i vs_i] dv_i] r_i] Hfa; [constructor | inversion Hfa | inversion Hfa |].
    inversion Hfa as [| ? ? ? ? Hhd Htl]; subst; constructor; [| exact (IH _ Htl)].
    destruct Hhd as (Hcn & sp & Efc & Hin_sp & Hstrip & Hlen_a & Hlen_v & Hargs & Hdv).
    rewrite Efc in Hargs, Hlen_a.
    unfold rv_call_event_matches; split; [exact Hcn | exists sp; repeat split; try assumption].
    intros k sp0 Hlt Hsp0.
    assert (Evm : nth_error (List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_c) (seq 0 (List.length (mcs_args sp)))) k =
                  Some (rv_read_reg (10%N + N.of_nat k) rf_c))
      by (rewrite nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
    exact (Hargs k sp0 _ Hsp0 Evm).
Qed.

Theorem validate_mc_call_a64_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
         (insts : list decoded_a64_call_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
         (callees : list mc_callee_spec) (opt_pf : option (list lrat_step))
         arg_dtys vs (penv0 : param_env Pa) rf0 sp0 fl0 mstk0,
    validate_mc_call_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees opt_pf = inr tt ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    cfg_param_dtyp_compatible ir_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx sp,
       nth_error arg_specs idx = Some sp ->
       nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I (ras_width sp))) /\
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some (ras_name sp)) ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (param_idx_uses_cfg ir_cfg) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed0) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv0 nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    (forall sp, In sp arg_specs ->
       penv0 (a64_hi_var_name (ras_name sp)) =
       a64_extend_penv_with_hi (build_param_env (List.map cert_reg_name (args ir_cfg)) vs) arg_specs rf0 (a64_hi_var_name (ras_name sp))) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed0) ->
    (forall nv, In nv (a64_hi_vars arg_specs) -> In nv allowed0) ->
    NoDup (List.map ras_name arg_specs) ->
    (forall sp, In sp arg_specs -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name arg_specs)) ->
    (forall sp, In sp arg_specs -> penv0 (ras_name sp) = build_param_env (List.map cert_reg_name (args ir_cfg)) vs (ras_name sp)) ->
    mc_valid_sp0_depth 2%nat sp0 ->
    a64_rf_matches_args (build_param_env (List.map cert_reg_name (args ir_cfg)) vs) arg_specs rf0 ->
    a64_call_sound_spec ir_cfg insts ret_w callees vs rf0 sp0 fl0 mstk0.
Proof.
  intros ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees opt_pf
         arg_dtys vs penv0 rf0 sp0 fl0 mstk0
         Hval Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp Hty Hargs_compat Hpu Hpenv_eq Hhi_eq Hpenv0 Hctx0 Hargs_al Hhi_al Hnd_sp Hdis_hi Hsp_eq Hsp0 Hm.
  unfold validate_mc_call_a64, build_mc_call_bundle_a64 in Hval.
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hval; [| discriminate Hval].
  destruct (forallb a64_call_inst_valid insts) eqn:Hvalid; cbn [negb] in Hval; [| discriminate Hval].
  destruct (Nat.leb (List.length arg_specs) 8) eqn:Hlen_a; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb a64_valid_arg_spec arg_specs) eqn:Hws; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) eqn:Hnb_al_b;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (forallb (fun c => rv_supported_arg_width (mcs_ret_width c) &&
                              Nat.leb (List.length (mcs_args c)) 8 &&
                              forallb rv_valid_arg_spec (mcs_args c) &&
                              mc_no_dup_strings (List.map ras_name (mcs_args c))) callees) eqn:Hcal_b;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (reify_ir_call_tree ir_cfg arg_specs callees ret_w) as [| t_ir] eqn:Eir; [discriminate Hval |].
  destruct (summarize_a64_call_tree insts callees arg_specs ret_w) as [| t_mc] eqn:Emc; [discriminate Hval |].
  destruct (collect_call_obls EA_AArch64 callees ret_w [] t_ir t_mc) as [| obls] eqn:Eco; [discriminate Hval |].
  set (raw_cvars := collect_ir_call_vars_acc t_ir (collect_mc_call_vars_acc t_mc [])) in *.
  set (call_vars := dedup_typed_vars raw_cvars) in *.
  set (all_vars := dedup_typed_vars_acc allowed0 call_vars) in *.
  destruct (vars_width_consistent allowed0 all_vars && vars_width_consistent raw_cvars all_vars) eqn:Evwc;
    cbn [negb] in Hval; [| discriminate Hval].
  apply andb_true_iff in Evwc as [Evwc_al Evwc_cv].
  destruct (forallb (obl_wf_exprs all_vars) obls) eqn:Ewf_o; cbn [negb] in Hval; [| discriminate Hval].
  cbn [mccb_ctx mccb_all_vars mccb_obls] in Hval.
  destruct (check_mc_loop_obls "mc-call" (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars)
              all_vars None obls opt_pf) as [| []] eqn:Hchk; [discriminate Hval |].
  clear Hval.
  assert (Hnb_al : forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false).
  { intros nm w Hin; rewrite forallb_forall in Hnb_al_b; pose proof (Hnb_al_b (nm, w) Hin) as Hn; apply negb_true_iff in Hn; exact Hn. }
  assert (Hcws : forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true /\ (List.length (mcs_args c) <= 8)%nat).
  { intros c Hc; rewrite forallb_forall in Hcal_b; pose proof (Hcal_b c Hc) as Ht;
      rewrite !andb_true_iff in Ht; destruct Ht as [[[Hrwc Hlc] _] _]; split; [exact Hrwc | apply Nat.leb_le; exact Hlc]. }
  assert (Hcs : forall c, In c callees -> forallb rv_valid_arg_spec (mcs_args c) = true /\ NoDup (List.map ras_name (mcs_args c))).
  { intros c Hc; rewrite forallb_forall in Hcal_b; pose proof (Hcal_b c Hc) as Ht;
      rewrite !andb_true_iff in Ht; destruct Ht as [[[_ _] Hva] Hnd]; split; [exact Hva | apply mc_no_dup_strings_spec; exact Hnd]. }
  assert (Hnb_cv : forall nm w, In (nm, w) call_vars -> mc_starts_with_bang nm = true).
  { intros nm w Hcv; apply dedup_typed_vars_sub in Hcv; unfold raw_cvars in Hcv;
      rewrite collect_ir_call_vars_acc_shift in Hcv; apply in_app_iff in Hcv as [H1 | H2].
    - eapply reify_ir_call_at_vars_bang; [exact Eir | exact H1].
    - eapply summarize_a64_call_at_vars_bang; [exact Emc | exact H2]. }
  assert (Hcv_av : forall nm w, In (nm, w) call_vars -> In (nm, w) all_vars)
    by (intros nm w Hcv; apply dedup_typed_vars_sub in Hcv; exact (vars_width_consistent_in _ _ _ _ Evwc_cv Hcv)).
  assert (Hal_av : forall nm w, In (nm, w) allowed0 -> In (nm, w) all_vars)
    by (intros nm w Hal; exact (vars_width_consistent_in _ _ _ _ Evwc_al Hal)).
  assert (Hmv_av : forall nm w, In (nm, w) (collect_mc_call_vars t_mc) -> In (nm, w) all_vars).
  { intros nm w Hmv; eapply vars_width_consistent_in; [exact Evwc_cv |].
    unfold raw_cvars; rewrite collect_ir_call_vars_acc_shift; apply in_or_app; right; exact Hmv. }
  assert (Hav_sp : forall nm w, In (nm, w) all_vars -> In (nm, w) allowed0 \/ In (nm, w) call_vars)
    by (intros nm w Hav; exact (dedup_typed_vars_acc_sub allowed0 call_vars nm w Hav)).
  intros genv O Hgenv HO; cbn [a64_call_sound_spec].
  assert (Hfresh0 : forall nm w, In (nm, w) allowed0 -> forall k' w', (0 <= k')%nat ->
    nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').
  { intros nm w Hal k' w' _; pose proof (Hnb_al nm w Hal) as Hnb; split; intro Heq; subst;
      [rewrite mc_call_ret_var_bang in Hnb | rewrite mc_call_hi_var_bang in Hnb]; discriminate Hnb. }
  assert (Hag_init : a64_val_regs_agrees penv0 dummy_freeze_oracle rf0 sp0 (a64_build_init_val_regs 0%N arg_specs) rf0).
  { set (penv_ir := build_param_env (List.map cert_reg_name (args ir_cfg)) vs) in *.
    pose proof (a64_init_val_regs_agrees penv_ir dummy_freeze_oracle arg_specs rf0 sp0 Hws Hnd_sp) as Hbase.
    assert (Hbase2 : a64_val_regs_agrees (a64_extend_penv_with_hi penv_ir arg_specs rf0) dummy_freeze_oracle rf0 sp0 (a64_build_init_val_regs 0%N arg_specs) rf0)
      by (apply Hbase; [exact Hdis_hi | exact Hm]).
    intro r; pose proof (Hbase2 r) as Hr; destruct (a64_val_read r (a64_build_init_val_regs 0%N arg_specs)) as [| e_arg | |] eqn:Erd; try exact Hr.
    destruct (a64_build_init_val_regs_vars 0%N arg_specs r e_arg Erd) as [Hlf Hfv].
    cbn [mc_sym_val_agrees] in *; unfold eval_closed_cert_expr in Hr |- *;
      erewrite mcc_eval_cert_expr_penv_agree; [exact Hr | exact Hlf |].
    intros nm w Hin; destruct (Hfv nm w Hin) as [sp [Hsp [[-> ->] | [_ [-> ->]]]]].
    - unfold a64_extend_penv_with_hi; rewrite a64_extend_penv_at_orig;
        [exact (Hsp_eq sp Hsp)
        | intros s Hs Heq; apply (Hdis_hi s Hs); rewrite Heq; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]].
    - exact (Hhi_eq sp Hsp). }
  assert (Hall_a64 : forall sp, In sp arg_specs ->
    In (ras_name sp, ras_width sp) allowed0 /\
    (ras_width sp <> 64%positive -> In (a64_hi_var_name (ras_name sp), 64%positive) allowed0)).
  { intros sp Hsp; split; [exact (Hargs_al sp Hsp) | intro Hne; exact (Hhi_al _ (a64_hi_vars_in_specs _ _ Hsp Hne))]. }
  unfold summarize_a64_call_tree in Emc; rewrite elf_length_tr_eq in Emc.
  destruct (summarize_a64_call_at_exec insts (pt_of_list_first daci_off insts) (pt_of_list_first_lookup_a64_call insts)
              (S (2 * List.length insts)) callees PT_Empty 0%N 0%nat 0%Z
              (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w allowed0 t_mc
              O penv0 rf0 sp0 rf0 sp0 fl0 mstk0
              Hrw Hcws Hvalid HO Hsp0 ltac:(unfold mc_frame_cap; lia) ltac:(symmetry; apply Integers.add_zero)
              (a64_init_val_regs_wf allowed0 arg_specs Hall_a64 Hws)
              ltac:(constructor) (fun C => ltac:(discriminate C))
              Hfresh0 Hag_init (mc_sym_stack_agrees_empty _ _ _ _ _) (fun C => ltac:(discriminate C)) Emc)
    as (tr_mc & new_binds & rf_end & fl_end & mstk_end & Hnd_nb & Hdisj_nb & Hnb_form & Hnb_vals & Hexec & Hcs_mc & Hmt_gen).
  assert (Hnb_nb : forall nm, In nm (List.map fst new_binds) -> mc_starts_with_bang nm = true).
  { intros nm Hin; destruct (Hnb_form nm Hin) as [k [_ [[w ->] | ->]]];
      [apply mc_call_ret_var_bang | apply mc_call_hi_var_bang]. }
  destruct (call_extra_binds_props allowed0 (collect_mc_call_vars t_mc) call_vars all_vars penv0 new_binds
              Hnb_al Hnb_cv (dedup_typed_vars_nodup _) (dedup_typed_vars_acc_nodup _ _ (dedup_typed_vars_nodup _))
              Hcv_av Hal_av Hav_sp Hmv_av Hnd_nb Hnb_nb Hnb_vals Hpenv0
              (fun _ _ => Forall_nil _))
    as (Hdisj_eb & Hdisj_nb_eb & Hpres_nb & Hwf_full & Hctx_call).
  set (extra_binds := call_extra_binds new_binds call_vars) in *.
  set (penv_full := overlay_penv (new_binds ++ extra_binds) penv0) in *.
  assert (Hctx_all : ub_ctx_holds penv_full dummy_freeze_oracle (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars))
    by (apply Forall_app; split; [exact (Hctx0 penv_full Hpres_nb) | exact Hctx_call]).
  pose proof (check_mc_loop_obls_sound _ _ _ _ _ _ penv_full dummy_freeze_oracle false Hchk Hwf_full Hctx_all) as Hobls_ok.
  assert (Hpenv_ir_eq : forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
    penv_full nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm).
  { intros nm Hin; rewrite (Hpres_nb nm), (Hpenv_eq nm Hin); [reflexivity |].
    apply in_map_iff in Hin as [id [<- _]]; unfold cert_reg_name; reflexivity. }
  assert (Hpu_as : forall idx w pnm,
    In (idx, DTYPE_Base (DTYPE_I w)) (arg_specs_uses_from 0%nat arg_specs) ->
    nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
    In (pnm, w) all_vars).
  { intros idx w pnm Hin Hpnm; apply arg_specs_uses_from_in in Hin as (k & sp & -> & Hnth & Heq_dt).
    inversion Heq_dt; subst w; destruct (Hargs_compat k sp Hnth) as [_ Hp_sp].
    cbn [Nat.add] in Hpnm; rewrite Hpnm in Hp_sp; inversion Hp_sp; subst pnm.
    exact (Hal_av _ _ (Hargs_al sp (nth_error_In _ _ Hnth))). }
  assert (Hcomp_as : forall idx dt,
    In (idx, dt) (arg_specs_uses_from 0%nat arg_specs) -> nth_error arg_dtys idx = Some dt).
  { intros idx dt Hin; apply arg_specs_uses_from_in in Hin as (k & sp & -> & Hnth & ->).
    cbn [Nat.add]; exact (proj1 (Hargs_compat k sp Hnth)). }
  assert (Hwf_ir_t : ir_call_tree_wf all_vars ret_w t_ir)
    by (exact (reify_ir_call_tree_wf ir_cfg arg_specs callees ret_w all_vars t_ir (rv_supported_to_is_supported _ Hrw) Hpu_as Eir)).
  pose proof (reify_ir_call_tree_exec genv penv_full ir_cfg arg_specs callees ret_w all_vars arg_dtys vs t_ir
                (rv_supported_to_is_supported _ Hrw) Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp_as Hty
                Hpu_as Hpenv_ir_eq Hwf_full Eir) as Hden_ir.
  pose proof (Hmt_gen extra_binds Hdisj_eb Hdisj_nb_eb) as Hmt_full.
  destruct (ir_mc_call_trees_sound EA_AArch64 callees ret_w genv penv_full t_ir t_mc [] obls all_vars
              (init_cfg_locals (args ir_cfg) vs) (@denote_cfg Pa ir_cfg None) _ _
              Hcs (fun _ _ Hin => ltac:(contradiction Hin)) Hobls_ok Eco Hwf_ir_t Hden_ir Hmt_full)
    as [[tr_ir_pre [Hpm_pre Hub_ir]] | (tr_ir & env_out & dv_ir & Hfa_tr & Hret_ir & Href_ir)].
  - exists tr_mc, rf_end, fl_end, mstk_end; repeat split; try assumption.
    left; exists default_draw_strat, tr_ir_pre;
      split; [exact default_draw_strat_wf | split; [| exact Hub_ir]].
    clear -Hpm_pre; generalize dependent tr_ir_pre; induction tr_mc as [| [[cn_m rf_c] x0_r] r_mc IH];
      intros [| [[cn_i vs_i] dv_i] r_i] Hpm; [constructor | inversion Hpm | constructor |].
    inversion Hpm as [| ? ? ? ? Hhd Htl]; subst; constructor; [| exact (IH _ Htl)].
    destruct Hhd as (Hcn & sp & Efc & Hin_sp & Hstrip & Hlen_a & Hlen_v & Hargs & Hdv).
    rewrite Efc in Hargs, Hlen_a.
    unfold a64_call_event_matches; split; [exact Hcn | exists sp; repeat split; try assumption].
    intros k sp0 Hlt Hsp0.
    assert (Evm : nth_error (List.map (fun j => a64_read_reg (N.of_nat j) rf_c) (seq 0 (List.length (mcs_args sp)))) k =
                  Some (a64_read_reg (N.of_nat k) rf_c))
      by (rewrite nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
    exact (Hargs k sp0 _ Hsp0 Evm).
  - exists tr_mc, rf_end, fl_end, mstk_end; repeat split; try assumption.
    right; exists default_draw_strat, tr_ir, default_draw_strat, env_out, dv_ir;
      split; [exact default_draw_strat_wf | split; [| split; [exact Hret_ir | exact Href_ir]]].
    clear -Hfa_tr; generalize dependent tr_ir; induction tr_mc as [| [[cn_m rf_c] x0_r] r_mc IH];
      intros [| [[cn_i vs_i] dv_i] r_i] Hfa; [constructor | inversion Hfa | inversion Hfa |].
    inversion Hfa as [| ? ? ? ? Hhd Htl]; subst; constructor; [| exact (IH _ Htl)].
    destruct Hhd as (Hcn & sp & Efc & Hin_sp & Hstrip & Hlen_a & Hlen_v & Hargs & Hdv).
    rewrite Efc in Hargs, Hlen_a.
    unfold a64_call_event_matches; split; [exact Hcn | exists sp; repeat split; try assumption].
    intros k sp0 Hlt Hsp0.
    assert (Evm : nth_error (List.map (fun j => a64_read_reg (N.of_nat j) rf_c) (seq 0 (List.length (mcs_args sp)))) k =
                  Some (a64_read_reg (N.of_nat k) rf_c))
      by (rewrite nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
    exact (Hargs k sp0 _ Hsp0 Evm).
Qed.

(** *** 5.6 Caller/Callee Concrete Oracle Composition *)

Record rv_leaf_callee {Pa : Params} : Type := mk_rv_leaf_callee {
  rlc_spec : mc_callee_spec;
  rlc_cfg : CFG.cfg dtyp;
  rlc_insts : list decoded_rv_inst;
  rlc_exec : forall rf_call mstk_call,
    mc_valid_sp0 (rv_read_reg 2%N rf_call) ->
    exists rf_ret (v_ret : @Integers.bit_int (mcs_ret_width rlc_spec)),
      rv_exec_mem (S (2 * List.length rlc_insts)) rlc_insts 0%N (rv_read_reg 2%N rf_call) rf_call mstk_call =
        Some (rf_ret, mstk_call) /\
      rv_callee_saved_preserved rf_call rf_ret /\
      rv_abi_ret_matches (mcs_ret_width rlc_spec) (mcs_ret_ext rlc_spec) v_ret (rv_read_reg 10%N rf_ret);
  rlc_ir : forall (vs : list (@dvalue Pa)) rf_call mstk_call rf_ret mstk_ret,
    rv_rf_matches_args (build_param_env (List.map ras_name (mcs_args rlc_spec)) vs) (mcs_args rlc_spec) rf_call ->
    List.length vs = List.length (mcs_args rlc_spec) ->
    rv_exec_mem (S (2 * List.length rlc_insts)) rlc_insts 0%N (rv_read_reg 2%N rf_call) rf_call mstk_call =
      Some (rf_ret, mstk_ret) ->
    exists sigma_ir,
      wf_draw_strat sigma_ir /\
      (cfg_steps_to_ub sigma_ir (init_cfg_locals (args rlc_cfg) vs) (denote_cfg rlc_cfg None) \/
       exists sigma_ir' env_out dv_ir,
         cfg_steps_to_ret sigma_ir (init_cfg_locals (args rlc_cfg) vs) (denote_cfg rlc_cfg None)
           sigma_ir' env_out dv_ir /\
         dvalue_refines dv_ir
           (DVALUE_Base (@DVALUE_I Pa (mcs_ret_width rlc_spec)
              (rv_trunc_ret_val (mcs_ret_width rlc_spec) (rv_read_reg 10%N rf_ret)))));
}.

Fixpoint find_rv_leaf_callee {Pa : Params} (cs : list (@rv_leaf_callee Pa)) (cname : string)
  : option (@rv_leaf_callee Pa) :=
  match cs with
  | [] => None
  | lc :: rest =>
      if String.eqb (mc_strip_leading_at (mcs_name (rlc_spec lc))) cname then Some lc
      else find_rv_leaf_callee rest cname
  end.

Lemma find_rv_leaf_callee_in {Pa : Params} :
  forall (cs : list (@rv_leaf_callee Pa)) lc,
    NoDup (List.map (fun x => mc_strip_leading_at (mcs_name (rlc_spec x))) cs) ->
    In lc cs ->
    find_rv_leaf_callee cs (mc_strip_leading_at (mcs_name (rlc_spec lc))) = Some lc.
Proof.
  intros cs lc Hnd Hlc; induction cs as [| x rest IH]; cbn in *; [contradiction |].
  inversion Hnd as [| ? ? Hni Hndr]; subst.
  destruct Hlc as [<- | Hr]; [rewrite String.eqb_refl; reflexivity |].
  destruct (String.eqb (mc_strip_leading_at (mcs_name (rlc_spec x))) (mc_strip_leading_at (mcs_name (rlc_spec lc)))) eqn:Eeq.
  - apply String.eqb_eq in Eeq; exfalso; apply Hni; rewrite Eeq; apply in_map_iff; exists lc; split; [reflexivity | exact Hr].
  - exact (IH Hndr Hr).
Qed.

Definition rv_leaf_oracle {Pa : Params} (cs : list (@rv_leaf_callee Pa)) : rv_call_oracle :=
  fun cname rf_call mstk_call =>
    match find_rv_leaf_callee cs cname with
    | None => None
    | Some lc =>
        rv_exec_mem (S (2 * List.length (rlc_insts lc))) (rlc_insts lc) 0%N (rv_read_reg 2%N rf_call) rf_call mstk_call
    end.

Lemma rv_leaf_oracle_wf {Pa : Params} :
  forall (cs : list (@rv_leaf_callee Pa)),
    NoDup (List.map (fun lc => mc_strip_leading_at (mcs_name (rlc_spec lc))) cs) ->
    wf_rv_call_oracle (List.map rlc_spec cs) (rv_leaf_oracle cs).
Proof.
  intros cs Hnd c rf_call mstk_call Hinc Hsp.
  apply in_map_iff in Hinc as [lc [<- Hlc]].
  unfold rv_leaf_oracle; rewrite (find_rv_leaf_callee_in cs lc Hnd Hlc).
  exact (rlc_exec lc rf_call mstk_call Hsp).
Qed.

Lemma rv_exec_with_calls_events :
  forall fuel insts O pc sp0 rf mstk tr rf_end mstk_end,
    rv_exec_with_calls fuel insts O pc sp0 rf mstk = Some (tr, rf_end, mstk_end) ->
    Forall (fun '(cn_m, rf_call, a0_ret) =>
      exists mstk_call rf_ret mstk_ret,
        O cn_m rf_call mstk_call = Some (rf_ret, mstk_ret) /\
        rv_read_reg 10%N rf_ret = a0_ret) tr.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros insts O pc sp0 rf mstk tr rf_end mstk_end Hexec;
    cbn [rv_exec_with_calls] in Hexec; [discriminate Hexec |].
  destruct (lookup_rv_call_inst insts pc) as [d |]; [| discriminate Hexec].
  destruct (drci_inst d) as [i | cname].
  - destruct i; try discriminate Hexec;
      try (destruct (rv_exec_one_nonret _ _ _ _ _) as [[[pc1 rf1] mstk1] |]; [exact (IH _ _ _ _ _ _ _ _ _ Hexec) | discriminate Hexec]).
    inversion Hexec; constructor.
  - destruct (mc_sp_aligned16 (mc_addr_to_off sp0 (rv_read_reg 2%N rf))); [| discriminate Hexec].
    destruct (O cname _ mstk) as [[rf_ret mstk_ret] |] eqn:Eo; [| discriminate Hexec].
    destruct (rv_exec_with_calls fuel' insts O _ sp0 rf_ret mstk_ret) as [[[tr' rf_e] mstk_e] |] eqn:Erec;
      [| discriminate Hexec].
    inversion Hexec; subst; clear Hexec.
    constructor; [exists mstk, rf_ret, mstk_ret; split; [exact Eo | reflexivity] | exact (IH _ _ _ _ _ _ _ _ _ Erec)].
Qed.

Theorem compose_rv64_caller_callee_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (insts : list decoded_rv_call_inst) (ret_w : positive)
         (cs : list (@rv_leaf_callee Pa)) (vs : list (@dvalue Pa))
         rf0 mstk0 genv,
    NoDup (List.map (fun lc => mc_strip_leading_at (mcs_name (rlc_spec lc))) cs) ->
    rv_call_sound_spec ir_cfg insts ret_w (List.map rlc_spec cs) vs rf0 mstk0 ->
    wf_callee_genv (List.map rlc_spec cs) genv ->
    let rv_fuel := S (2 * List.length insts) in
    exists tr_mc rf_end mstk_end,
      rv_exec_with_calls rv_fuel insts (rv_leaf_oracle cs) 0%N (rv_read_reg 2%N rf0) rf0 mstk0 =
        Some (tr_mc, rf_end, mstk_end) /\
      rv_callee_saved_preserved rf0 rf_end /\
      rf_end 1%N = rf0 1%N /\
      ((exists sigma_ir tr_ir_pre,
          wf_draw_strat sigma_ir /\
          prefix_matches (rv_call_event_matches (List.map rlc_spec cs)) tr_ir_pre tr_mc /\
          cfg_call_steps_to_ub genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
            (denote_cfg ir_cfg None) tr_ir_pre) \/
       (exists sigma_ir tr_ir sigma_ir' env_out dv_ir,
          wf_draw_strat sigma_ir /\
          Forall2
            (fun '(cn_m, rf_call, a0_ret) '(cn_i, vs_i, dv_ret) =>
               rv_call_event_matches (List.map rlc_spec cs) (cn_m, rf_call, a0_ret) (cn_i, vs_i, dv_ret) /\
               exists lc,
                 find_rv_leaf_callee cs cn_m = Some lc /\
                 exists sigma_c,
                   wf_draw_strat sigma_c /\
                   (cfg_steps_to_ub sigma_c (init_cfg_locals (args (rlc_cfg lc)) vs_i) (denote_cfg (rlc_cfg lc) None) \/
                    exists sigma_c' env_c' dv_c,
                      cfg_steps_to_ret sigma_c (init_cfg_locals (args (rlc_cfg lc)) vs_i) (denote_cfg (rlc_cfg lc) None)
                        sigma_c' env_c' dv_c /\
                      dvalue_refines dv_c dv_ret))
            tr_mc tr_ir /\
          cfg_call_steps_to_ret genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
            (denote_cfg ir_cfg None) tr_ir sigma_ir' env_out dv_ir /\
          dvalue_refines dv_ir
            (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))))).
Proof.
  intros ir_cfg insts ret_w cs vs rf0 mstk0 genv Hnd Hcaller Hgenv.
  destruct (Hcaller genv (rv_leaf_oracle cs) Hgenv (rv_leaf_oracle_wf cs Hnd))
    as (tr_mc & rf_end & mstk_end & Hexec & Hcs & Hra & [Hub | (sigma_ir & tr_ir & sigma_ir' & env_out & dv_ir & Hwf_s & Hfa & Hret & Href)]).
  - exists tr_mc, rf_end, mstk_end; repeat split; try assumption; left; exact Hub.
  - pose proof (rv_exec_with_calls_events _ _ _ _ _ _ _ _ _ _ Hexec) as Hevs.
    exists tr_mc, rf_end, mstk_end; repeat split; try assumption.
    right; exists sigma_ir, tr_ir, sigma_ir', env_out, dv_ir.
    split; [exact Hwf_s | split; [| split; [exact Hret | exact Href]]].
    clear -Hnd Hevs Hfa; generalize dependent tr_ir; induction tr_mc as [| [[cn_m rf_call] a0_ret] r_mc IH];
      intros [| [[cn_i vs_i] dv_ret] r_i] Hfa; [constructor | inversion Hfa | inversion Hfa |].
    inversion Hfa as [| ? ? ? ? Hmfa Hfa_r]; subst.
    pose proof (Forall_inv Hevs) as (mstk_call & rf_ret & mstk_ret & Ho & Ha0).
    constructor.
    + split; [exact Hmfa |].
      destruct Hmfa as [_ (c & Hinc & Hstrip & Hrf & Hlen & Hdv)].
      apply in_map_iff in Hinc as [lc [<- Hlc]].
      pose proof (find_rv_leaf_callee_in cs lc Hnd Hlc) as Hfind; rewrite Hstrip in Hfind.
      exists lc; split; [exact Hfind |].
      unfold rv_leaf_oracle in Ho; rewrite Hfind in Ho.
      destruct (rlc_ir lc vs_i rf_call mstk_call rf_ret mstk_ret Hrf Hlen Ho) as (sigma_c & Hwf_c & Hbody).
      exists sigma_c; split; [exact Hwf_c |].
      rewrite Hdv, <- Ha0; exact Hbody.
    + exact (IH (Forall_inv_tail Hevs) _ Hfa_r).
Qed.

Record a64_leaf_callee {Pa : Params} : Type := mk_a64_leaf_callee {
  alc_spec : mc_callee_spec;
  alc_cfg : CFG.cfg dtyp;
  alc_insts : list decoded_a64_inst;
  alc_exec : forall rf_call sp_call fl_call mstk_call,
    mc_valid_sp0 sp_call ->
    exists rf_ret fl_ret (v_ret : @Integers.bit_int (mcs_ret_width alc_spec)),
      a64_exec_mem (S (2 * List.length alc_insts)) alc_insts 0%N sp_call rf_call sp_call fl_call mstk_call =
        Some (rf_ret, sp_call, fl_ret, mstk_call) /\
      a64_callee_saved_preserved rf_call rf_ret /\
      rv_abi_ret_matches (mcs_ret_width alc_spec) (mcs_ret_ext alc_spec) v_ret (a64_read_reg 0%N rf_ret);
  alc_ir : forall (vs : list (@dvalue Pa)) rf_call sp_call fl_call mstk_call rf_ret sp_ret fl_ret mstk_ret,
    a64_rf_matches_args (build_param_env (List.map ras_name (mcs_args alc_spec)) vs) (mcs_args alc_spec) rf_call ->
    List.length vs = List.length (mcs_args alc_spec) ->
    a64_exec_mem (S (2 * List.length alc_insts)) alc_insts 0%N sp_call rf_call sp_call fl_call mstk_call =
      Some (rf_ret, sp_ret, fl_ret, mstk_ret) ->
    exists sigma_ir,
      wf_draw_strat sigma_ir /\
      (cfg_steps_to_ub sigma_ir (init_cfg_locals (args alc_cfg) vs) (denote_cfg alc_cfg None) \/
       exists sigma_ir' env_out dv_ir,
         cfg_steps_to_ret sigma_ir (init_cfg_locals (args alc_cfg) vs) (denote_cfg alc_cfg None)
           sigma_ir' env_out dv_ir /\
         dvalue_refines dv_ir
           (DVALUE_Base (@DVALUE_I Pa (mcs_ret_width alc_spec)
              (rv_trunc_ret_val (mcs_ret_width alc_spec) (a64_read_reg 0%N rf_ret)))));
}.

Fixpoint find_a64_leaf_callee {Pa : Params} (cs : list (@a64_leaf_callee Pa)) (cname : string)
  : option (@a64_leaf_callee Pa) :=
  match cs with
  | [] => None
  | lc :: rest =>
      if String.eqb (mc_strip_leading_at (mcs_name (alc_spec lc))) cname then Some lc
      else find_a64_leaf_callee rest cname
  end.

Lemma find_a64_leaf_callee_in {Pa : Params} :
  forall (cs : list (@a64_leaf_callee Pa)) lc,
    NoDup (List.map (fun x => mc_strip_leading_at (mcs_name (alc_spec x))) cs) ->
    In lc cs ->
    find_a64_leaf_callee cs (mc_strip_leading_at (mcs_name (alc_spec lc))) = Some lc.
Proof.
  intros cs lc Hnd Hlc; induction cs as [| x rest IH]; cbn in *; [contradiction |].
  inversion Hnd as [| ? ? Hni Hndr]; subst.
  destruct Hlc as [<- | Hr]; [rewrite String.eqb_refl; reflexivity |].
  destruct (String.eqb (mc_strip_leading_at (mcs_name (alc_spec x))) (mc_strip_leading_at (mcs_name (alc_spec lc)))) eqn:Eeq.
  - apply String.eqb_eq in Eeq; exfalso; apply Hni; rewrite Eeq; apply in_map_iff; exists lc; split; [reflexivity | exact Hr].
  - exact (IH Hndr Hr).
Qed.

Definition a64_leaf_oracle {Pa : Params} (cs : list (@a64_leaf_callee Pa)) : a64_call_oracle :=
  fun cname rf_call sp_call fl_call mstk_call =>
    match find_a64_leaf_callee cs cname with
    | None => None
    | Some lc =>
        a64_exec_mem (S (2 * List.length (alc_insts lc))) (alc_insts lc) 0%N sp_call rf_call sp_call fl_call mstk_call
    end.

Lemma a64_leaf_oracle_wf {Pa : Params} :
  forall (cs : list (@a64_leaf_callee Pa)),
    NoDup (List.map (fun lc => mc_strip_leading_at (mcs_name (alc_spec lc))) cs) ->
    wf_a64_call_oracle (List.map alc_spec cs) (a64_leaf_oracle cs).
Proof.
  intros cs Hnd c rf_call sp_call fl_call mstk_call Hinc Hsp.
  apply in_map_iff in Hinc as [lc [<- Hlc]].
  unfold a64_leaf_oracle; rewrite (find_a64_leaf_callee_in cs lc Hnd Hlc).
  exact (alc_exec lc rf_call sp_call fl_call mstk_call Hsp).
Qed.

Lemma a64_exec_with_calls_events :
  forall fuel insts O pc sp0 rf sp fl mstk tr rf_end sp_end fl_end mstk_end,
    a64_exec_with_calls fuel insts O pc sp0 rf sp fl mstk = Some (tr, rf_end, sp_end, fl_end, mstk_end) ->
    Forall (fun '(cn_m, rf_call, x0_ret) =>
      exists sp_call fl_call mstk_call rf_ret sp_ret fl_ret mstk_ret,
        O cn_m rf_call sp_call fl_call mstk_call = Some (rf_ret, sp_ret, fl_ret, mstk_ret) /\
        a64_read_reg 0%N rf_ret = x0_ret) tr.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros insts O pc sp0 rf sp fl mstk tr rf_end sp_end fl_end mstk_end Hexec;
    cbn [a64_exec_with_calls] in Hexec; [discriminate Hexec |].
  destruct (lookup_a64_call_inst insts pc) as [d |]; [| discriminate Hexec].
  destruct (daci_inst d) as [i | cname].
  - destruct i; try discriminate Hexec;
      try (destruct (a64_exec_one_nonret _ _ _ _ _ _ _) as [[[[[pc1 rf1] sp1] fl1] mstk1] |];
           [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec) | discriminate Hexec]).
    inversion Hexec; constructor.
  - destruct (mc_sp_aligned16 (mc_addr_to_off sp0 sp)); [| discriminate Hexec].
    destruct (O cname _ sp fl mstk) as [[[[rf_ret sp_ret] fl_ret] mstk_ret] |] eqn:Eo; [| discriminate Hexec].
    destruct (a64_exec_with_calls fuel' insts O _ sp0 rf_ret sp_ret fl_ret mstk_ret)
      as [[[[[tr' rf_e] sp_e] fl_e] mstk_e] |] eqn:Erec; [| discriminate Hexec].
    inversion Hexec; subst; clear Hexec.
    constructor; [exists sp, fl, mstk, rf_ret, sp_ret, fl_ret, mstk_ret; split; [exact Eo | reflexivity]
                 | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Erec)].
Qed.

Theorem compose_a64_caller_callee_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (insts : list decoded_a64_call_inst) (ret_w : positive)
         (cs : list (@a64_leaf_callee Pa)) (vs : list (@dvalue Pa))
         rf0 sp0 fl0 mstk0 genv,
    NoDup (List.map (fun lc => mc_strip_leading_at (mcs_name (alc_spec lc))) cs) ->
    a64_call_sound_spec ir_cfg insts ret_w (List.map alc_spec cs) vs rf0 sp0 fl0 mstk0 ->
    wf_callee_genv (List.map alc_spec cs) genv ->
    let a64_fuel := S (2 * List.length insts) in
    exists tr_mc rf_end fl_end mstk_end,
      a64_exec_with_calls a64_fuel insts (a64_leaf_oracle cs) 0%N sp0 rf0 sp0 fl0 mstk0 =
        Some (tr_mc, rf_end, sp0, fl_end, mstk_end) /\
      a64_callee_saved_preserved rf0 rf_end /\
      ((exists sigma_ir tr_ir_pre,
          wf_draw_strat sigma_ir /\
          prefix_matches (a64_call_event_matches (List.map alc_spec cs)) tr_ir_pre tr_mc /\
          cfg_call_steps_to_ub genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
            (denote_cfg ir_cfg None) tr_ir_pre) \/
       (exists sigma_ir tr_ir sigma_ir' env_out dv_ir,
          wf_draw_strat sigma_ir /\
          Forall2
            (fun '(cn_m, rf_call, x0_ret) '(cn_i, vs_i, dv_ret) =>
               a64_call_event_matches (List.map alc_spec cs) (cn_m, rf_call, x0_ret) (cn_i, vs_i, dv_ret) /\
               exists lc,
                 find_a64_leaf_callee cs cn_m = Some lc /\
                 exists sigma_c,
                   wf_draw_strat sigma_c /\
                   (cfg_steps_to_ub sigma_c (init_cfg_locals (args (alc_cfg lc)) vs_i) (denote_cfg (alc_cfg lc) None) \/
                    exists sigma_c' env_c' dv_c,
                      cfg_steps_to_ret sigma_c (init_cfg_locals (args (alc_cfg lc)) vs_i) (denote_cfg (alc_cfg lc) None)
                        sigma_c' env_c' dv_c /\
                      dvalue_refines dv_c dv_ret))
            tr_mc tr_ir /\
          cfg_call_steps_to_ret genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
            (denote_cfg ir_cfg None) tr_ir sigma_ir' env_out dv_ir /\
          dvalue_refines dv_ir
            (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))).
Proof.
  intros ir_cfg insts ret_w cs vs rf0 sp0 fl0 mstk0 genv Hnd Hcaller Hgenv.
  destruct (Hcaller genv (a64_leaf_oracle cs) Hgenv (a64_leaf_oracle_wf cs Hnd))
    as (tr_mc & rf_end & fl_end & mstk_end & Hexec & Hcs & [Hub | (sigma_ir & tr_ir & sigma_ir' & env_out & dv_ir & Hwf_s & Hfa & Hret & Href)]).
  - exists tr_mc, rf_end, fl_end, mstk_end; repeat split; try assumption; left; exact Hub.
  - pose proof (a64_exec_with_calls_events _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec) as Hevs.
    exists tr_mc, rf_end, fl_end, mstk_end; repeat split; try assumption.
    right; exists sigma_ir, tr_ir, sigma_ir', env_out, dv_ir.
    split; [exact Hwf_s | split; [| split; [exact Hret | exact Href]]].
    clear -Hnd Hevs Hfa; generalize dependent tr_ir; induction tr_mc as [| [[cn_m rf_call] x0_ret] r_mc IH];
      intros [| [[cn_i vs_i] dv_ret] r_i] Hfa; [constructor | inversion Hfa | inversion Hfa |].
    inversion Hfa as [| ? ? ? ? Hmfa Hfa_r]; subst.
    pose proof (Forall_inv Hevs) as (sp_call & fl_call & mstk_call & rf_ret & sp_ret & fl_ret & mstk_ret & Ho & Hx0).
    constructor.
    + split; [exact Hmfa |].
      destruct Hmfa as [_ (c & Hinc & Hstrip & Hrf & Hlen & Hdv)].
      apply in_map_iff in Hinc as [lc [<- Hlc]].
      pose proof (find_a64_leaf_callee_in cs lc Hnd Hlc) as Hfind; rewrite Hstrip in Hfind.
      exists lc; split; [exact Hfind |].
      unfold a64_leaf_oracle in Ho; rewrite Hfind in Ho.
      destruct (alc_ir lc vs_i rf_call sp_call fl_call mstk_call rf_ret sp_ret fl_ret mstk_ret Hrf Hlen Ho)
        as (sigma_c & Hwf_c & Hbody).
      exists sigma_c; split; [exact Hwf_c |].
      rewrite Hdv, <- Hx0; exact Hbody.
    + exact (IH (Forall_inv_tail Hevs) _ Hfa_r).
Qed.
