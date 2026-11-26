(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Bounds-Checked ELF64 Inspector & Relocation Security Gate ([CertValidator.Elf64Spec])

    Pure, total, axiom-free Rocq specification for parsing little-endian
    ELF64 relocatable objects ([ET_REL]) and post-[ld.lld] linked binaries
    ([ET_EXEC] / [ET_DYN]) on [RISC-V] and [AArch64].

    Enforces:
    1. Exact ELF64 header, section table, unique [SHT_SYMTAB], and [F-27]
       [EF_RISCV_RVE] / [R_RISCV_RELAX] / [R_RISCV_ALIGN] checks.
    2. Unique [STT_FUNC] resolution into a valid [SHF_EXECINSTR] non-[SHT_NOBITS]
       section with non-overlapping relocations across [[fn_lo, fn_hi)).
    3. Exact bounds-checked byte slicing proved by [elf64_extract_func_sound]
       with zero axioms ([Closed under the global context]). *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.Ascii
  Strings.String
  List
  Bool
  Lia.
Import ListNotations.

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
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments Nat.leb _ _ : simpl nomatch.
#[local] Arguments Nat.ltb _ _ : simpl nomatch.
#[local] Arguments String.eqb _ _ : simpl nomatch.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. Byte-Stream Slicing & Little-Endian Decoders *)

Fixpoint string_to_bytes (s : string) : list N :=
  match s with
  | EmptyString => []
  | String a rest => Ascii.N_of_ascii a :: string_to_bytes rest
  end.

Definition slice_bytes (raw : list N) (off len : nat) : option (list N) :=
  if Nat.leb (off + len) (List.length raw)
  then Some (firstn len (skipn off raw))
  else None.

Lemma length_skipn_exact : forall (A : Type) (n : nat) (xs : list A),
  n <= List.length xs ->
  List.length (skipn n xs) = List.length xs - n.
Proof.
  intros A n; induction n as [| n' IH]; intros [| x xs'] Hle; cbn in *; try lia.
  apply IH; lia.
Qed.

Lemma length_firstn_le_exact : forall (A : Type) (n : nat) (xs : list A),
  n <= List.length xs ->
  List.length (firstn n xs) = n.
Proof.
  intros A n; induction n as [| n' IH]; intros [| x xs'] Hle; cbn in *; try lia; try reflexivity.
  f_equal; apply IH; lia.
Qed.

Lemma slice_bytes_spec : forall raw off len bs,
  slice_bytes raw off len = Some bs ->
  off + len <= List.length raw /\
  bs = firstn len (skipn off raw) /\
  List.length bs = len.
Proof.
  intros raw off len bs H.
  unfold slice_bytes in H.
  destruct (Nat.leb (off + len) (List.length raw)) eqn:Eb; [| discriminate H].
  apply Nat.leb_le in Eb.
  inversion H; subst bs; clear H.
  split; [exact Eb |].
  split; [reflexivity |].
  apply length_firstn_le_exact.
  rewrite length_skipn_exact; lia.
Qed.

Fixpoint bytes_to_N_le (bs : list N) : N :=
  match bs with
  | [] => 0%N
  | b :: rest => (N.modulo b 256 + 256 * bytes_to_N_le rest)%N
  end.

Definition read_le_n (raw : list N) (off n : nat) : option N :=
  option_map bytes_to_N_le (slice_bytes raw off n).

Definition read_u8 (raw : list N) (off : nat) : option N :=
  read_le_n raw off 1.

Definition read_u16_le (raw : list N) (off : nat) : option N :=
  read_le_n raw off 2.

Definition read_u32_le (raw : list N) (off : nat) : option N :=
  read_le_n raw off 4.

Definition read_u64_le (raw : list N) (off : nat) : option N :=
  read_le_n raw off 8.

Fixpoint read_cstr_aux (fuel : nat) (raw : list N) (pos limit : nat) : option string :=
  match fuel with
  | O => None
  | S fuel' =>
      if Nat.leb limit pos then None
      else
        match nth_error raw pos with
        | None => None
        | Some b =>
            let b' := N.modulo b 256 in
            if N.eqb b' 0%N then Some EmptyString
            else option_map (String (Ascii.ascii_of_N b')) (read_cstr_aux fuel' raw (S pos) limit)
        end
  end.

Definition read_cstr_at (raw : list N) (str_off str_len name_off : nat) : option string :=
  let limit := str_off + str_len in
  let pos := str_off + name_off in
  if negb (Nat.leb limit (List.length raw)) || Nat.leb limit pos then None
  else
    let fuel := Nat.min 256 (limit - pos) in
    read_cstr_aux fuel raw pos limit.

Definition n_to_nat_checked (raw_len : nat) (v : N) : option nat :=
  if N.leb v (N.of_nat raw_len) then Some (N.to_nat v) else None.

(** ** 2. ELF64 Architectural Types & Security Constants *)

Variant elf_arch : Set :=
| EA_Riscv64
| EA_AArch64.

Definition elf_arch_eqb (a b : elf_arch) : bool :=
  match a, b with
  | EA_Riscv64, EA_Riscv64 => true
  | EA_AArch64, EA_AArch64 => true
  | _, _ => false
  end.

Lemma elf_arch_eqb_eq : forall a b, elf_arch_eqb a b = true <-> a = b.
Proof.
  intros [] []; cbn; split; intro H; try reflexivity; discriminate H.
Qed.

Variant elf_kind : Set :=
| EK_Rel
| EK_Exec
| EK_Dyn.

Definition elf_kind_eqb (a b : elf_kind) : bool :=
  match a, b with
  | EK_Rel, EK_Rel => true
  | EK_Exec, EK_Exec => true
  | EK_Dyn, EK_Dyn => true
  | _, _ => false
  end.

Lemma elf_kind_eqb_eq : forall a b, elf_kind_eqb a b = true <-> a = b.
Proof.
  intros [] []; cbn; split; intro H; try reflexivity; discriminate H.
Qed.

Definition ELFCLASS64 : N := 2%N.
Definition ELFDATA2LSB : N := 1%N.
Definition EV_CURRENT : N := 1%N.

Definition ET_REL : N := 1%N.
Definition ET_EXEC : N := 2%N.
Definition ET_DYN : N := 3%N.

Definition EM_AARCH64 : N := 183%N.
Definition EM_RISCV : N := 243%N.

Definition SHT_SYMTAB : N := 2%N.
Definition SHT_RELA : N := 4%N.
Definition SHT_NOBITS : N := 8%N.
Definition SHF_EXECINSTR : N := 4%N.
Definition STT_FUNC : N := 2%N.

Definition EF_RISCV_RVC : N := 1%N.
Definition EF_RISCV_RVE : N := 8%N.

Definition R_RISCV_ALIGN : N := 43%N.
Definition R_RISCV_RELAX : N := 51%N.

Record elf64_hdr : Set := mk_elf64_hdr {
  eh_kind : elf_kind;
  eh_arch : elf_arch;
  eh_shoff : N;
  eh_flags : N;
  eh_rvc : bool;
  eh_shentsize : nat;
  eh_shnum : nat;
}.

Record elf64_shdr : Set := mk_elf64_shdr {
  esh_idx : nat;
  esh_type : N;
  esh_flags : N;
  esh_addr : N;
  esh_offset : N;
  esh_size : N;
  esh_link : nat;
  esh_info : nat;
  esh_entsize : N;
}.

Record elf64_sym : Set := mk_elf64_sym {
  esym_name : string;
  esym_type : N;
  esym_shndx : nat;
  esym_value : N;
  esym_size : N;
}.

Record elf64_rela : Set := mk_elf64_rela {
  er_offset : N;
  er_sym : N;
  er_type : N;
  er_addend : N;
}.

Record elf_func_slice : Set := mk_elf_func_slice {
  efs_arch : elf_arch;
  efs_kind : elf_kind;
  efs_rvc : bool;
  efs_shndx : nat;
  efs_file_off : nat;
  efs_size : nat;
  efs_bytes : list N;
  efs_range_lo : N;
  efs_range_hi : N;
}.

(** ** 3. Total Bounds-Checked ELF64 Header, Section, and Symbol Parsers *)

Definition has_elf_magic (raw : list N) : bool :=
  match raw with
  | b0 :: b1 :: b2 :: b3 :: _ =>
      N.eqb (N.modulo b0 256) 127%N &&
      N.eqb (N.modulo b1 256) 69%N &&
      N.eqb (N.modulo b2 256) 76%N &&
      N.eqb (N.modulo b3 256) 70%N
  | _ => false
  end.

Definition bit_is_set (v bit_pos : N) : bool :=
  N.eqb (N.modulo (N.div v (N.pow 2%N bit_pos)) 2%N) 1%N.

Definition parse_elf64_header (raw : list N) : string + elf64_hdr :=
  let len := List.length raw in
  if negb (Nat.leb 64 len) then inl "ELF64 buffer shorter than 64-byte header"
  else if negb (has_elf_magic raw) then inl "invalid ELF magic"
  else
    match read_u8 raw 4, read_u8 raw 5, read_u8 raw 6,
          read_u16_le raw 16, read_u16_le raw 18, read_u32_le raw 20,
          read_u64_le raw 40, read_u32_le raw 48, read_u16_le raw 52,
          read_u16_le raw 58, read_u16_le raw 60
    with
    | Some e_class, Some e_data, Some e_ident_ver,
      Some e_type, Some e_machine, Some e_ver,
      Some e_shoff, Some e_flags, Some e_ehsize,
      Some e_shentsize, Some e_shnum =>
        if negb (N.eqb e_class ELFCLASS64) then inl "only ELFCLASS64 is supported"
        else if negb (N.eqb e_data ELFDATA2LSB) then inl "only little-endian ELFDATA2LSB is supported"
        else if negb (N.eqb e_ident_ver EV_CURRENT && N.eqb e_ver EV_CURRENT) then inl "invalid ELF version"
        else if negb (N.eqb e_ehsize 64%N && N.eqb e_shentsize 64%N) then inl "unexpected ELF64 header/section entry size"
        else
          match
            (if N.eqb e_type ET_REL then Some EK_Rel
             else if N.eqb e_type ET_EXEC then Some EK_Exec
             else if N.eqb e_type ET_DYN then Some EK_Dyn
             else None),
            (if N.eqb e_machine EM_RISCV then Some EA_Riscv64
             else if N.eqb e_machine EM_AARCH64 then Some EA_AArch64
             else None)
          with
          | Some kind, Some arch =>
              if N.eqb e_shnum 0%N then inl "ELF64 has zero section headers"
              else if negb (N.leb (e_shoff + e_shnum * 64%N) (N.of_nat len))
              then inl "ELF64 section header table out of bounds"
              else if elf_arch_eqb arch EA_Riscv64 && bit_is_set e_flags 3%N
              then inl "EF_RISCV_RVE is forbidden by LP64 safety profile"
              else
                let rvc := elf_arch_eqb arch EA_Riscv64 && bit_is_set e_flags 0%N in
                inr (mk_elf64_hdr kind arch e_shoff e_flags rvc (N.to_nat e_shentsize) (N.to_nat e_shnum))
          | None, _ => inl "unsupported ELF64 e_type (must be ET_REL/ET_EXEC/ET_DYN)"
          | _, None => inl "unsupported ELF64 e_machine (must be EM_RISCV/EM_AARCH64)"
          end
    | _, _, _, _, _, _, _, _, _, _, _ =>
        inl "truncated ELF64 header fields"
    end.

Definition parse_one_shdr (raw : list N) (base idx : nat) : string + elf64_shdr :=
  let off := base + idx * 64 in
  match read_u32_le raw (off + 4), read_u64_le raw (off + 8),
        read_u64_le raw (off + 16), read_u64_le raw (off + 24),
        read_u64_le raw (off + 32), read_u32_le raw (off + 40),
        read_u32_le raw (off + 44), read_u64_le raw (off + 56)
  with
  | Some sh_type, Some sh_flags, Some sh_addr, Some sh_offset,
    Some sh_size, Some sh_link, Some sh_info, Some sh_entsize =>
      if negb (N.eqb sh_type SHT_NOBITS) &&
         negb (N.leb (sh_offset + sh_size) (N.of_nat (List.length raw)))
      then inl "ELF64 section payload out of bounds"
      else if negb (N.leb sh_link 1000000%N && N.leb sh_info 1000000%N)
      then inl "ELF64 section link/info index out of range"
      else
        inr (mk_elf64_shdr idx sh_type sh_flags sh_addr sh_offset sh_size
               (N.to_nat sh_link) (N.to_nat sh_info) sh_entsize)
  | _, _, _, _, _, _, _, _ => inl "truncated ELF64 section header"
  end.

Fixpoint parse_shdrs_aux (fuel : nat) (raw : list N) (base idx : nat) : string + list elf64_shdr :=
  match fuel with
  | O => inr []
  | S fuel' =>
      match parse_one_shdr raw base idx, parse_shdrs_aux fuel' raw base (S idx) with
      | inr s, inr rest => inr (s :: rest)
      | inl err, _ => inl err
      | _, inl err => inl err
      end
  end.

Definition parse_elf64_shdrs (raw : list N) (hdr : elf64_hdr) : string + list elf64_shdr :=
  match n_to_nat_checked (List.length raw) (eh_shoff hdr) with
  | None => inl "ELF64 shoff out of bounds"
  | Some shoff =>
      if negb (Nat.leb (shoff + eh_shnum hdr * 64) (List.length raw))
      then inl "ELF64 section header table exceeds file length"
      else parse_shdrs_aux (eh_shnum hdr) raw shoff 0
  end.

Definition find_unique_symtab (shdrs : list elf64_shdr) : option elf64_shdr :=
  match List.filter (fun s => N.eqb (esh_type s) SHT_SYMTAB) shdrs with
  | [sym_s] => Some sym_s
  | _ => None
  end.

Fixpoint parse_syms_aux
  (fuel : nat) (raw : list N) (sym_off str_off str_len idx : nat)
  : string + list elf64_sym :=
  match fuel with
  | O => inr []
  | S fuel' =>
      let off := sym_off + idx * 24 in
      match read_u32_le raw off, read_u8 raw (off + 4),
            read_u16_le raw (off + 6), read_u64_le raw (off + 8),
            read_u64_le raw (off + 16)
      with
      | Some st_name_off, Some st_info, Some st_shndx, Some st_value, Some st_size =>
          let name :=
            match read_cstr_at raw str_off str_len (N.to_nat st_name_off) with
            | Some s => s
            | None => EmptyString
            end
          in
          let sym := mk_elf64_sym name (N.modulo st_info 16%N) (N.to_nat st_shndx) st_value st_size in
          match parse_syms_aux fuel' raw sym_off str_off str_len (S idx) with
          | inr rest => inr (sym :: rest)
          | inl err => inl err
          end
      | _, _, _, _, _ => inl "truncated ELF64 symbol entry"
      end
  end.

Definition parse_elf64_symtab (raw : list N) (shdrs : list elf64_shdr)
  : string + list elf64_sym :=
  match find_unique_symtab shdrs with
  | None => inl "ELF64 must contain a unique SHT_SYMTAB section"
  | Some sym_sh =>
      if negb (N.eqb (esh_entsize sym_sh) 24%N && N.eqb (N.modulo (esh_size sym_sh) 24%N) 0%N)
      then inl "ELF64 SHT_SYMTAB has invalid entsize or unaligned size"
      else
        match nth_error shdrs (esh_link sym_sh) with
        | None => inl "ELF64 SHT_SYMTAB sh_link out of range"
        | Some str_sh =>
            if N.eqb (esh_type str_sh) SHT_NOBITS then inl "ELF64 string table cannot be SHT_NOBITS"
            else
              match n_to_nat_checked (List.length raw) (esh_offset sym_sh),
                    n_to_nat_checked (List.length raw) (esh_size sym_sh),
                    n_to_nat_checked (List.length raw) (esh_offset str_sh),
                    n_to_nat_checked (List.length raw) (esh_size str_sh)
              with
              | Some sym_off, Some sym_sz, Some str_off, Some str_sz =>
                  let count := Nat.div sym_sz 24 in
                  if negb (Nat.leb (sym_off + count * 24) (List.length raw))
                  then inl "ELF64 symbol table out of bounds"
                  else parse_syms_aux count raw sym_off str_off str_sz 0
              | _, _, _, _ => inl "ELF64 symbol or string table offset exceeds bounds"
              end
        end
  end.

Definition find_unique_func_sym (syms : list elf64_sym) (fn_name : string)
  : option elf64_sym :=
  match List.filter
          (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) fn_name)
          syms
  with
  | [sym] => Some sym
  | _ => None
  end.

(** ** 4. [F-27] Relocation & Linker-Relaxation Gate *)

Fixpoint parse_relas_aux (fuel : nat) (raw : list N) (base idx : nat)
  : option (list elf64_rela) :=
  match fuel with
  | O => Some []
  | S fuel' =>
      let off := base + idx * 24 in
      match read_u64_le raw off, read_u64_le raw (off + 8), read_u64_le raw (off + 16) with
      | Some r_off, Some r_info, Some r_add =>
          let r_type := N.modulo r_info 4294967296%N in
          let r_sym := N.div r_info 4294967296%N in
          match parse_relas_aux fuel' raw base (S idx) with
          | Some rest => Some (mk_elf64_rela r_off r_sym r_type r_add :: rest)
          | None => None
          end
      | _, _, _ => None
      end
  end.

Definition rela_entry_allowed
  (arch : elf_arch) (rela_info target_shndx : nat)
  (fn_lo fn_hi : N) (r : elf64_rela) : bool :=
  let forbidden_riscv :=
    elf_arch_eqb arch EA_Riscv64 &&
    (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN)
  in
  if forbidden_riscv then false
  else if Nat.eqb rela_info target_shndx then
    N.ltb (er_offset r) fn_lo || N.leb fn_hi (er_offset r)
  else true.

Definition check_one_rela_section
  (raw : list N) (arch : elf_arch) (shdrs : list elf64_shdr)
  (target_shndx : nat) (fn_lo fn_hi : N) (sh : elf64_shdr) : bool :=
  if negb (N.eqb (esh_type sh) SHT_RELA) then true
  else
    match nth_error shdrs (esh_info sh) with
    | None => false
    | Some tgt_sh =>
        if negb (bit_is_set (esh_flags tgt_sh) 2%N) then true
        else if negb (N.eqb (esh_entsize sh) 24%N && N.eqb (N.modulo (esh_size sh) 24%N) 0%N)
        then false
        else
          match n_to_nat_checked (List.length raw) (esh_offset sh),
                n_to_nat_checked (List.length raw) (esh_size sh)
          with
          | Some r_off, Some r_sz =>
              let count := Nat.div r_sz 24 in
              if negb (Nat.leb (r_off + count * 24) (List.length raw)) then false
              else
                match parse_relas_aux count raw r_off 0 with
                | None => false
                | Some rs =>
                    forallb (rela_entry_allowed arch (esh_info sh) target_shndx fn_lo fn_hi) rs
                end
          | _, _ => false
          end
    end.

Definition check_exec_relocations
  (raw : list N) (arch : elf_arch) (shdrs : list elf64_shdr)
  (target_shndx : nat) (fn_lo fn_hi : N) : bool :=
  forallb (check_one_rela_section raw arch shdrs target_shndx fn_lo fn_hi) shdrs.

(** ** 5. End-to-End Function Extraction & Top-Level Soundness Theorem *)

Definition compute_func_slice_offsets
  (kind : elf_kind) (sh : elf64_shdr) (sym : elf64_sym)
  : string + (N * N * N) :=
  if N.eqb (esym_size sym) 0%N then inl "zero-sized ELF64 function symbol"
  else if N.eqb (esh_type sh) SHT_NOBITS then inl "function symbol cannot reside in SHT_NOBITS"
  else if negb (bit_is_set (esh_flags sh) 2%N) then inl "function section lacks SHF_EXECINSTR"
  else
    match kind with
    | EK_Rel =>
        if negb (N.leb (esym_value sym + esym_size sym) (esh_size sh))
        then inl "ET_REL function slice exceeds section bounds"
        else
          let foff := (esh_offset sh + esym_value sym)%N in
          let rlo := esym_value sym in
          let rhi := (rlo + esym_size sym)%N in
          inr (foff, rlo, rhi)
    | EK_Exec | EK_Dyn =>
        if negb (N.leb (esh_addr sh) (esym_value sym))
        then inl "linked ELF function vaddr precedes section sh_addr"
        else
          let sec_rel := (esym_value sym - esh_addr sh)%N in
          if negb (N.leb (sec_rel + esym_size sym) (esh_size sh))
          then inl "linked ELF function slice exceeds section bounds"
          else
            let foff := (esh_offset sh + sec_rel)%N in
            let rlo := esym_value sym in
            let rhi := (rlo + esym_size sym)%N in
            inr (foff, rlo, rhi)
    end.

Definition elf64_extract_func
  (raw : list N) (want_arch : elf_arch) (want_kind : elf_kind) (fn_name : string)
  : string + elf_func_slice :=
  match parse_elf64_header raw with
  | inl err => inl err
  | inr hdr =>
      if negb (elf_arch_eqb (eh_arch hdr) want_arch) then inl "ELF64 architecture mismatch"
      else if negb (elf_kind_eqb (eh_kind hdr) want_kind) then inl "ELF64 e_type mismatch"
      else
        match parse_elf64_shdrs raw hdr with
        | inl err => inl err
        | inr shdrs =>
            match parse_elf64_symtab raw shdrs with
            | inl err => inl err
            | inr syms =>
                match find_unique_func_sym syms fn_name with
                | None => inl (String.append "missing or non-unique ELF64 STT_FUNC symbol: " fn_name)
                | Some sym =>
                    match nth_error shdrs (esym_shndx sym) with
                    | None => inl "ELF64 function st_shndx out of bounds"
                    | Some sh =>
                        match compute_func_slice_offsets (eh_kind hdr) sh sym with
                        | inl err => inl err
                        | inr (foff, rlo, rhi) =>
                            if negb (check_exec_relocations raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi)
                            then inl "ELF64 executable relocation/relaxation gate rejected binary"
                            else
                              match n_to_nat_checked (List.length raw) foff,
                                    n_to_nat_checked (List.length raw) (esym_size sym)
                              with
                              | Some foff_nat, Some fsz_nat =>
                                  match slice_bytes raw foff_nat fsz_nat with
                                  | None => inl "ELF64 function byte slice out of bounds"
                                  | Some bytes =>
                                      inr (mk_elf_func_slice
                                             (eh_arch hdr) (eh_kind hdr) (eh_rvc hdr)
                                             (esym_shndx sym) foff_nat fsz_nat bytes rlo rhi)
                                  end
                              | _, _ => inl "ELF64 function slice offset/size exceeds file length"
                              end
                        end
                    end
                end
            end
        end
  end.

Theorem elf64_extract_func_sound :
  forall raw want_arch want_kind fn_name sl,
    elf64_extract_func raw want_arch want_kind fn_name = inr sl ->
    efs_arch sl = want_arch /\
    efs_kind sl = want_kind /\
    0 < efs_size sl /\
    efs_file_off sl + efs_size sl <= List.length raw /\
    efs_bytes sl = firstn (efs_size sl) (skipn (efs_file_off sl) raw) /\
    List.length (efs_bytes sl) = efs_size sl /\
    exists hdr shdrs syms sym sh,
      parse_elf64_header raw = inr hdr /\
      parse_elf64_shdrs raw hdr = inr shdrs /\
      parse_elf64_symtab raw shdrs = inr syms /\
      find_unique_func_sym syms fn_name = Some sym /\
      nth_error shdrs (esym_shndx sym) = Some sh /\
      esh_type sh <> SHT_NOBITS /\
      bit_is_set (esh_flags sh) 2%N = true /\
      check_exec_relocations raw want_arch shdrs (efs_shndx sl) (efs_range_lo sl) (efs_range_hi sl) = true.
Proof.
  intros raw want_arch want_kind fn_name sl H.
  unfold elf64_extract_func in H.
  destruct (parse_elf64_header raw) as [err | hdr] eqn:Eh; [discriminate H |].
  destruct (elf_arch_eqb (eh_arch hdr) want_arch) eqn:Ea; cbn [negb] in H; [| discriminate H].
  apply elf_arch_eqb_eq in Ea.
  destruct (elf_kind_eqb (eh_kind hdr) want_kind) eqn:Ek; cbn [negb] in H; [| discriminate H].
  apply elf_kind_eqb_eq in Ek.
  destruct (parse_elf64_shdrs raw hdr) as [err | shdrs] eqn:Eshs; [discriminate H |].
  destruct (parse_elf64_symtab raw shdrs) as [err | syms] eqn:Esyms; [discriminate H |].
  destruct (find_unique_func_sym syms fn_name) as [sym |] eqn:Ef; [| discriminate H].
  destruct (nth_error shdrs (esym_shndx sym)) as [sh |] eqn:Eth; [| discriminate H].
  destruct (compute_func_slice_offsets (eh_kind hdr) sh sym) as [err | [[foff rlo] rhi]] eqn:Eoff;
    [discriminate H |].
  destruct (check_exec_relocations raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi) eqn:Erel;
    cbn [negb] in H; [| discriminate H].
  destruct (n_to_nat_checked (List.length raw) foff) as [foff_nat |] eqn:Efn; [| discriminate H].
  destruct (n_to_nat_checked (List.length raw) (esym_size sym)) as [fsz_nat |] eqn:Esn;
    [| discriminate H].
  destruct (slice_bytes raw foff_nat fsz_nat) as [bytes |] eqn:Esl; [| discriminate H].
  inversion H; subst sl; clear H.
  destruct (slice_bytes_spec _ _ _ _ Esl) as (Hle & Hfirst & Hlen).
  unfold compute_func_slice_offsets in Eoff.
  destruct (N.eqb (esym_size sym) 0%N) eqn:Esz0; [discriminate Eoff |].
  destruct (N.eqb (esh_type sh) SHT_NOBITS) eqn:Enob; [discriminate Eoff |].
  destruct (bit_is_set (esh_flags sh) 2%N) eqn:Eex; cbn [negb] in Eoff; [| discriminate Eoff].
  apply N.eqb_neq in Esz0.
  apply N.eqb_neq in Enob.
  unfold n_to_nat_checked in Esn.
  destruct (N.leb (esym_size sym) (N.of_nat (List.length raw))); [| discriminate Esn].
  inversion Esn as [Hfsz]; clear Esn.
  assert (Hpos_sz : 0 < N.to_nat (esym_size sym)) by lia.
  cbn [efs_arch efs_kind efs_shndx efs_file_off efs_size efs_bytes efs_range_lo efs_range_hi].
  rewrite !Ea, Ek in *.
  rewrite <- Hfsz in Hle, Hfirst, Hlen.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [lia |].
  split; [exact Hle |].
  split; [exact Hfirst |].
  split; [exact Hlen |].
  exists hdr, shdrs, syms, sym, sh.
  split; [reflexivity |].
  split; [exact Eshs |].
  split; [exact Esyms |].
  split; [exact Ef |].
  split; [exact Eth |].
  split; [exact Enob |].
  split; [exact Eex | exact Erel].
Qed.

(** ** 6. Additive Call-Relocation & Linked Symbol-Address Extraction (M3c) *)

Definition R_RISCV_JAL : N := 17%N.
Definition R_RISCV_CALL : N := 18%N.
Definition R_RISCV_CALL_PLT : N := 19%N.
Definition R_AARCH64_CALL26 : N := 283%N.

Record elf_call_info : Set := mk_elf_call_info {
  eci_relocs : list (N * string);
  eci_sym_addrs : list (string * N);
}.

Definition elf_str_in_list (s : string) (xs : list string) : bool :=
  existsb (String.eqb s) xs.

Definition elf_n_in_list (x : N) (xs : list N) : bool :=
  existsb (N.eqb x) xs.

Fixpoint elf_no_dup_N (xs : list N) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (elf_n_in_list x rest) && elf_no_dup_N rest
  end.

Lemma elf_n_in_list_spec : forall x xs, elf_n_in_list x xs = true <-> In x xs.
Proof.
  intros x xs; unfold elf_n_in_list; rewrite existsb_exists; split.
  - intros [y [Hy Heq]]; apply N.eqb_eq in Heq; subst y; exact Hy.
  - intros Hin; exists x; split; [exact Hin | apply N.eqb_refl].
Qed.

Lemma elf_no_dup_N_sound : forall xs,
  elf_no_dup_N xs = true -> NoDup xs.
Proof.
  induction xs as [| x xs IH]; intro H; cbn [elf_no_dup_N] in H; [constructor |].
  apply andb_true_iff in H as [Hnin Hnd].
  constructor; [intro Hin; apply elf_n_in_list_spec in Hin; rewrite Hin in Hnin; discriminate Hnin | exact (IH Hnd)].
Qed.

Definition rela_type_is_direct_call (arch : elf_arch) (r_type : N) : bool :=
  match arch with
  | EA_Riscv64 =>
      N.eqb r_type R_RISCV_JAL ||
      N.eqb r_type R_RISCV_CALL ||
      N.eqb r_type R_RISCV_CALL_PLT
  | EA_AArch64 =>
      N.eqb r_type R_AARCH64_CALL26
  end.

Definition check_and_collect_call_rela_entry
  (arch : elf_arch) (kind : elf_kind) (shdrs : list elf64_shdr)
  (syms : list elf64_sym) (rela_info target_shndx : nat)
  (fn_lo fn_hi : N) (allowed_callees : list string) (r : elf64_rela)
  : string + option (N * string) :=
  let forbidden_riscv :=
    elf_arch_eqb arch EA_Riscv64 &&
    (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN)
  in
  if forbidden_riscv then inl "ELF64 relocation/relaxation gate rejected R_RISCV_RELAX/ALIGN"
  else if negb (Nat.eqb rela_info target_shndx) then inr None
  else if N.ltb (er_offset r) fn_lo || N.leb fn_hi (er_offset r) then inr None
  else
    match kind with
    | EK_Exec | EK_Dyn =>
        inl "relocation inside function slice forbidden in linked ELF"
    | EK_Rel =>
        if negb (rela_type_is_direct_call arch (er_type r)) then
          inl "unsupported relocation type inside function slice"
        else if negb (N.eqb (er_addend r) 0%N) then
          inl "non-zero relocation addend inside function slice"
        else if negb (N.leb (er_sym r) (N.of_nat (List.length syms))) then
          inl "call relocation symbol index out of range"
        else
          match nth_error syms (N.to_nat (er_sym r)) with
          | None => inl "call relocation symbol index out of bounds"
          | Some csym =>
              if negb (N.eqb (esym_type csym) STT_FUNC) then
                inl "call relocation does not target STT_FUNC symbol"
              else if negb (elf_str_in_list (esym_name csym) allowed_callees) then
                inl (String.append "unapproved callee relocation target: " (esym_name csym))
              else
                match find_unique_func_sym syms (esym_name csym) with
                | None => inl "ambiguous callee STT_FUNC symbol"
                | Some _ =>
                    match nth_error shdrs (esym_shndx csym) with
                    | None => inl "callee st_shndx out of bounds"
                    | Some csh =>
                        match compute_func_slice_offsets EK_Rel csh csym with
                        | inl err => inl err
                        | inr _ => inr (Some ((er_offset r - fn_lo)%N, esym_name csym))
                        end
                    end
                end
          end
    end.

Fixpoint collect_call_rela_entries
  (arch : elf_arch) (kind : elf_kind) (shdrs : list elf64_shdr)
  (syms : list elf64_sym) (rela_info target_shndx : nat)
  (fn_lo fn_hi : N) (allowed_callees : list string) (rs : list elf64_rela)
  {struct rs} : string + list (N * string) :=
  match rs with
  | [] => inr []
  | r :: rest =>
      match check_and_collect_call_rela_entry arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r with
      | inl err => inl err
      | inr opt_p =>
          match collect_call_rela_entries arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rest with
          | inl err => inl err
          | inr tl =>
              match opt_p with
              | None => inr tl
              | Some p => inr (p :: tl)
              end
          end
      end
  end.

Definition collect_one_rela_section
  (raw : list N) (arch : elf_arch) (kind : elf_kind) (shdrs : list elf64_shdr)
  (syms : list elf64_sym) (target_shndx : nat) (fn_lo fn_hi : N)
  (allowed_callees : list string) (sh : elf64_shdr) : string + list (N * string) :=
  if negb (N.eqb (esh_type sh) SHT_RELA) then inr []
  else
    match nth_error shdrs (esh_info sh) with
    | None => inl "ELF64 SHT_RELA sh_info out of bounds"
    | Some tgt_sh =>
        if negb (bit_is_set (esh_flags tgt_sh) 2%N) then inr []
        else if negb (N.eqb (esh_entsize sh) 24%N && N.eqb (N.modulo (esh_size sh) 24%N) 0%N) then
          inl "ELF64 SHT_RELA has invalid entsize or unaligned size"
        else
          match n_to_nat_checked (List.length raw) (esh_offset sh),
                n_to_nat_checked (List.length raw) (esh_size sh)
          with
          | Some r_off, Some r_sz =>
              let count := Nat.div r_sz 24 in
              if negb (Nat.leb (r_off + count * 24) (List.length raw)) then
                inl "ELF64 SHT_RELA payload out of bounds"
              else
                match parse_relas_aux count raw r_off 0 with
                | None => inl "truncated ELF64 SHT_RELA entries"
                | Some rs =>
                    collect_call_rela_entries arch kind shdrs syms (esh_info sh) target_shndx fn_lo fn_hi allowed_callees rs
                end
          | _, _ => inl "ELF64 SHT_RELA offset or size out of bounds"
          end
    end.

Fixpoint collect_all_call_relocs
  (raw : list N) (arch : elf_arch) (kind : elf_kind) (all_shdrs rem_shdrs : list elf64_shdr)
  (syms : list elf64_sym) (target_shndx : nat) (fn_lo fn_hi : N)
  (allowed_callees : list string) {struct rem_shdrs} : string + list (N * string) :=
  match rem_shdrs with
  | [] => inr []
  | sh :: rest =>
      match collect_one_rela_section raw arch kind all_shdrs syms target_shndx fn_lo fn_hi allowed_callees sh,
            collect_all_call_relocs raw arch kind all_shdrs rest syms target_shndx fn_lo fn_hi allowed_callees with
      | inl err, _ => inl err
      | _, inl err => inl err
      | inr xs, inr ys => inr (xs ++ ys)
      end
  end.

Fixpoint collect_exec_callee_addrs
  (kind : elf_kind) (shdrs : list elf64_shdr) (syms : list elf64_sym)
  (allowed_callees : list string) {struct allowed_callees} : string + list (string * N) :=
  match allowed_callees with
  | [] => inr []
  | cn :: rest =>
      match find_unique_func_sym syms cn with
      | None => inl (String.append "missing or ambiguous linked callee STT_FUNC symbol: " cn)
      | Some csym =>
          match nth_error shdrs (esym_shndx csym) with
          | None => inl "linked callee st_shndx out of bounds"
          | Some csh =>
              match compute_func_slice_offsets kind csh csym with
              | inl err => inl err
              | inr _ =>
                  match collect_exec_callee_addrs kind shdrs syms rest with
                  | inl err => inl err
                  | inr rest_addrs => inr ((cn, esym_value csym) :: rest_addrs)
                  end
              end
          end
      end
  end.

(** Extract a caller function slice and verified direct-call relocation / symbol metadata.
    [allowed_callees] contains bare ELF symbol names (without leading '@'). *)
Definition elf64_extract_func_with_calls
  (raw : list N) (want_arch : elf_arch) (want_kind : elf_kind)
  (fn_name : string) (allowed_callees : list string)
  : string + (elf_func_slice * elf_call_info) :=
  match parse_elf64_header raw with
  | inl err => inl err
  | inr hdr =>
      if negb (elf_arch_eqb (eh_arch hdr) want_arch) then inl "ELF64 architecture mismatch"
      else if negb (elf_kind_eqb (eh_kind hdr) want_kind) then inl "ELF64 e_type mismatch"
      else
        match parse_elf64_shdrs raw hdr with
        | inl err => inl err
        | inr shdrs =>
            match parse_elf64_symtab raw shdrs with
            | inl err => inl err
            | inr syms =>
                match find_unique_func_sym syms fn_name with
                | None => inl (String.append "missing or non-unique ELF64 STT_FUNC symbol: " fn_name)
                | Some sym =>
                    match nth_error shdrs (esym_shndx sym) with
                    | None => inl "ELF64 function st_shndx out of bounds"
                    | Some sh =>
                        match compute_func_slice_offsets (eh_kind hdr) sh sym with
                        | inl err => inl err
                        | inr (foff, rlo, rhi) =>
                            match n_to_nat_checked (List.length raw) foff,
                                  n_to_nat_checked (List.length raw) (esym_size sym)
                            with
                            | Some foff_nat, Some fsz_nat =>
                                match slice_bytes raw foff_nat fsz_nat with
                                | None => inl "ELF64 function byte slice out of bounds"
                                | Some bytes =>
                                    let sl := mk_elf_func_slice
                                                (eh_arch hdr) (eh_kind hdr) (eh_rvc hdr)
                                                (esym_shndx sym) foff_nat fsz_nat bytes rlo rhi in
                                    match eh_kind hdr with
                                    | EK_Rel =>
                                        match collect_all_call_relocs raw (eh_arch hdr) EK_Rel shdrs shdrs syms (esym_shndx sym) rlo rhi allowed_callees with
                                        | inl err => inl err
                                        | inr rels =>
                                            if negb (elf_no_dup_N (List.map fst rels)) then
                                              inl "duplicate call relocation offset inside function slice"
                                            else
                                              inr (sl, mk_elf_call_info rels [])
                                        end
                                    | EK_Exec | EK_Dyn =>
                                        if negb (check_exec_relocations raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi) then
                                          inl "ELF64 executable relocation/relaxation gate rejected binary"
                                        else
                                          match collect_exec_callee_addrs (eh_kind hdr) shdrs syms allowed_callees with
                                          | inl err => inl err
                                          | inr addrs => inr (sl, mk_elf_call_info [] addrs)
                                          end
                                    end
                                end
                            | _, _ => inl "ELF64 function slice offset/size exceeds file length"
                            end
                        end
                    end
                end
            end
        end
  end.

Lemma check_and_collect_call_rela_entry_sound :
  forall arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r opt_p,
    check_and_collect_call_rela_entry arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r = inr opt_p ->
    rela_info = target_shndx ->
    (fn_lo <= fn_hi)%N ->
    forall rel_off cname,
      opt_p = Some (rel_off, cname) ->
      kind = EK_Rel /\
      (rel_off < fn_hi - fn_lo)%N /\
      er_offset r = (fn_lo + rel_off)%N /\
      rela_type_is_direct_call arch (er_type r) = true /\
      er_addend r = 0%N /\
      In cname allowed_callees /\
      exists csym csh,
        nth_error syms (N.to_nat (er_sym r)) = Some csym /\
        esym_name csym = cname /\
        esym_type csym = STT_FUNC /\
        find_unique_func_sym syms cname = Some csym /\
        nth_error shdrs (esym_shndx csym) = Some csh /\
        exists r_, compute_func_slice_offsets EK_Rel csh csym = inr r_.
Proof.
  intros arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r opt_p H Hi Hlohi rel_off cname Hop.
  unfold check_and_collect_call_rela_entry in H.
  destruct (elf_arch_eqb arch EA_Riscv64 && (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN));
    [discriminate H |].
  destruct (Nat.eqb rela_info target_shndx) eqn:Einfo; cbn [negb] in H;
    [| subst; rewrite Nat.eqb_refl in Einfo; discriminate Einfo].
  destruct (N.ltb (er_offset r) fn_lo || N.leb fn_hi (er_offset r)) eqn:Eout;
    [inversion H; rewrite Hop in *; discriminate |].
  apply orb_false_iff in Eout as [Hge Hlt].
  apply N.ltb_ge in Hge; apply N.leb_gt in Hlt.
  destruct kind; [| discriminate H | discriminate H].
  destruct (rela_type_is_direct_call arch (er_type r)) eqn:Ety; cbn [negb] in H; [| discriminate H].
  destruct (N.eqb (er_addend r) 0%N) eqn:Eadd; cbn [negb] in H; [| discriminate H].
  apply N.eqb_eq in Eadd.
  destruct (N.leb (er_sym r) (N.of_nat (List.length syms))); cbn [negb] in H; [| discriminate H].
  destruct (nth_error syms (N.to_nat (er_sym r))) as [csym |] eqn:Esym; [| discriminate H].
  destruct (N.eqb (esym_type csym) STT_FUNC) eqn:Eft; cbn [negb] in H; [| discriminate H].
  apply N.eqb_eq in Eft.
  destruct (elf_str_in_list (esym_name csym) allowed_callees) eqn:Eal; cbn [negb] in H; [| discriminate H].
  unfold elf_str_in_list in Eal; apply existsb_exists in Eal as [cn [Hcn Hceq]].
  apply String.eqb_eq in Hceq; subst cn.
  destruct (find_unique_func_sym syms (esym_name csym)) as [usym |] eqn:Eu; [| discriminate H].
  destruct (nth_error shdrs (esym_shndx csym)) as [csh |] eqn:Ecsh; [| discriminate H].
  destruct (compute_func_slice_offsets EK_Rel csh csym) as [| r_] eqn:Eoff; [discriminate H |].
  inversion H as [Hopt]; clear H.
  rewrite <- Hopt in Hop; inversion Hop; subst rel_off cname; clear Hopt Hop.
  assert (Husym : usym = csym).
  { unfold find_unique_func_sym in Eu.
    destruct (List.filter (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) (esym_name csym)) syms)
      as [| s0 [| ? ?]] eqn:Ef; try discriminate Eu.
    inversion Eu; subst s0; clear Eu.
    assert (Hin : In csym (List.filter (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) (esym_name csym)) syms)).
    { apply filter_In; split; [exact (nth_error_In _ _ Esym) |].
      rewrite Eft, N.eqb_refl, String.eqb_refl; reflexivity. }
    rewrite Ef in Hin; destruct Hin as [-> | []]; reflexivity. }
  subst usym.
  repeat split; try lia; try assumption.
  exists csym, csh; repeat split; try assumption; eexists; exact Eoff.
Qed.

Lemma check_and_collect_call_rela_entry_disallows_relax :
  forall arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r opt_p,
    check_and_collect_call_rela_entry arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r = inr opt_p ->
    (elf_arch_eqb arch EA_Riscv64 && (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN)) = false.
Proof.
  intros arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r opt_p H.
  unfold check_and_collect_call_rela_entry in H.
  destruct (elf_arch_eqb arch EA_Riscv64 && (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN));
    [discriminate H | reflexivity].
Qed.

Lemma collect_call_rela_entries_to_exec_check :
  forall arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rs rels,
    collect_call_rela_entries arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rs = inr rels ->
    (kind = EK_Exec \/ kind = EK_Dyn) ->
    rels = [] /\
    forallb (rela_entry_allowed arch rela_info target_shndx fn_lo fn_hi) rs = true.
Proof.
  intros arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rs.
  induction rs as [| r rest IH]; intros rels H Hkind; cbn [collect_call_rela_entries] in H.
  - inversion H; subst; split; reflexivity.
  - destruct (check_and_collect_call_rela_entry arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r)
      as [| opt_p] eqn:He; [discriminate H |].
    destruct (collect_call_rela_entries arch kind shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rest)
      as [| tl] eqn:Hr; [discriminate H |].
    destruct (IH tl eq_refl Hkind) as [Htl Hfb]; subst tl.
    assert (Hnot_rel : rela_entry_allowed arch rela_info target_shndx fn_lo fn_hi r = true /\ opt_p = None).
    { unfold check_and_collect_call_rela_entry in He; unfold rela_entry_allowed.
      destruct (elf_arch_eqb arch EA_Riscv64 && (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN));
        [discriminate He |].
      destruct (Nat.eqb rela_info target_shndx); cbn [negb] in He.
      - destruct (N.ltb (er_offset r) fn_lo || N.leb fn_hi (er_offset r)); [inversion He; split; reflexivity |].
        destruct Hkind as [-> | ->]; discriminate He.
      - inversion He; split; reflexivity. }
    destruct Hnot_rel as [Hr_ok ->]; inversion H; split; [reflexivity | cbn [forallb]; rewrite Hr_ok, Hfb; reflexivity].
Qed.

Lemma collect_call_rela_entries_rel_sound :
  forall arch shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rs rels,
    (fn_lo <= fn_hi)%N ->
    collect_call_rela_entries arch EK_Rel shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rs = inr rels ->
    forall rel_off cname,
      In (rel_off, cname) rels ->
      (rel_off < fn_hi - fn_lo)%N /\
      In cname allowed_callees /\
      exists r csym csh,
        In r rs /\
        rela_info = target_shndx /\
        er_offset r = (fn_lo + rel_off)%N /\
        rela_type_is_direct_call arch (er_type r) = true /\
        er_addend r = 0%N /\
        nth_error syms (N.to_nat (er_sym r)) = Some csym /\
        esym_name csym = cname /\
        esym_type csym = STT_FUNC /\
        find_unique_func_sym syms cname = Some csym /\
        nth_error shdrs (esym_shndx csym) = Some csh /\
        exists r_, compute_func_slice_offsets EK_Rel csh csym = inr r_.
Proof.
  intros arch shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rs.
  induction rs as [| r rest IH]; intros rels Hlohi H rel_off cname Hin; cbn [collect_call_rela_entries] in H.
  - inversion H; subst; contradiction Hin.
  - destruct (check_and_collect_call_rela_entry arch EK_Rel shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees r)
      as [| opt_p] eqn:He; [discriminate H |].
    destruct (collect_call_rela_entries arch EK_Rel shdrs syms rela_info target_shndx fn_lo fn_hi allowed_callees rest)
      as [| tl] eqn:Hr; [discriminate H |].
    destruct opt_p as [[ro cn] |].
    + inversion H; subst rels; clear H.
      destruct Hin as [Heq | Hin].
      * inversion Heq; subst ro cn; clear Heq.
        assert (Hinfo : rela_info = target_shndx).
        { unfold check_and_collect_call_rela_entry in He.
          destruct (elf_arch_eqb _ _ && _); [discriminate He |].
          destruct (Nat.eqb rela_info target_shndx) eqn:En; cbn [negb] in He;
            [apply Nat.eqb_eq in En; exact En | discriminate He]. }
        destruct (check_and_collect_call_rela_entry_sound _ _ _ _ _ _ _ _ _ _ _ He Hinfo Hlohi _ _ eq_refl)
          as (_ & Hlt & Hoff & Hty & Hadd & Hcn & [csym [csh Hrest]]).
        split; [exact Hlt | split; [exact Hcn |]].
        exists r, csym, csh; repeat split; try (left; reflexivity); try assumption; tauto.
      * destruct (IH _ Hlohi eq_refl _ _ Hin) as (Hlt & Hcn & [r0 [csym [csh Hrest]]]).
        split; [exact Hlt | split; [exact Hcn |]].
        exists r0, csym, csh; destruct Hrest as [Hin0 Hr_ok]; split; [right; exact Hin0 | exact Hr_ok].
    + inversion H; subst rels; clear H.
      destruct (IH _ Hlohi eq_refl _ _ Hin) as (Hlt & Hcn & [r0 [csym [csh Hrest]]]).
      split; [exact Hlt | split; [exact Hcn |]].
      exists r0, csym, csh; destruct Hrest as [Hin0 Hr_ok]; split; [right; exact Hin0 | exact Hr_ok].
Qed.

Lemma collect_all_call_relocs_rel_sound :
  forall raw arch all_shdrs rem_shdrs syms target_shndx fn_lo fn_hi allowed_callees rels,
    (fn_lo <= fn_hi)%N ->
    collect_all_call_relocs raw arch EK_Rel all_shdrs rem_shdrs syms target_shndx fn_lo fn_hi allowed_callees = inr rels ->
    forall rel_off cname,
      In (rel_off, cname) rels ->
      (rel_off < fn_hi - fn_lo)%N /\
      In cname allowed_callees /\
      exists csym csh r_,
        find_unique_func_sym syms cname = Some csym /\
        esym_name csym = cname /\
        esym_type csym = STT_FUNC /\
        nth_error all_shdrs (esym_shndx csym) = Some csh /\
        compute_func_slice_offsets EK_Rel csh csym = inr r_.
Proof.
  intros raw arch all_shdrs rem_shdrs syms target_shndx fn_lo fn_hi allowed_callees.
  induction rem_shdrs as [| sh rest IH]; intros rels Hlohi H rel_off cname Hin;
    cbn [collect_all_call_relocs] in H.
  - inversion H; subst; contradiction Hin.
  - destruct (collect_one_rela_section raw arch EK_Rel all_shdrs syms target_shndx fn_lo fn_hi allowed_callees sh)
      as [| xs] eqn:Hx; [discriminate H |].
    destruct (collect_all_call_relocs raw arch EK_Rel all_shdrs rest syms target_shndx fn_lo fn_hi allowed_callees)
      as [| ys] eqn:Hy; [discriminate H |].
    inversion H; subst rels; clear H.
    apply in_app_iff in Hin as [Hx_in | Hy_in]; [| exact (IH _ Hlohi eq_refl _ _ Hy_in)].
    unfold collect_one_rela_section in Hx.
    destruct (N.eqb (esh_type sh) SHT_RELA); cbn [negb] in Hx; [| inversion Hx; subst; contradiction Hx_in].
    destruct (nth_error all_shdrs (esh_info sh)); [| discriminate Hx].
    destruct (bit_is_set (esh_flags e) 2%N); cbn [negb] in Hx; [| inversion Hx; subst; contradiction Hx_in].
    destruct (N.eqb (esh_entsize sh) 24%N && N.eqb (N.modulo (esh_size sh) 24%N) 0%N); cbn [negb] in Hx; [| discriminate Hx].
    destruct (n_to_nat_checked (List.length raw) (esh_offset sh)); [| discriminate Hx].
    destruct (n_to_nat_checked (List.length raw) (esh_size sh)); [| discriminate Hx].
    destruct (Nat.leb (n + Nat.div n0 24 * 24) (List.length raw)); cbn [negb] in Hx; [| discriminate Hx].
    destruct (parse_relas_aux (Nat.div n0 24) raw n 0) as [rs |]; [| discriminate Hx].
    destruct (collect_call_rela_entries_rel_sound _ _ _ _ _ _ _ _ _ _ Hlohi Hx _ _ Hx_in)
      as (Hlt & Hcn & [r [csym [csh (_ & _ & _ & _ & _ & _ & Hnm & Hty & Huniq & Hcsh & [r_ Hoff])]]]).
    split; [exact Hlt | split; [exact Hcn |]].
    exists csym, csh, r_; repeat split; assumption.
Qed.

Lemma collect_exec_callee_addrs_sound :
  forall kind shdrs syms allowed_callees addrs,
    collect_exec_callee_addrs kind shdrs syms allowed_callees = inr addrs ->
    forall cn,
      In cn allowed_callees ->
      exists csym csh r_,
        In (cn, esym_value csym) addrs /\
        find_unique_func_sym syms cn = Some csym /\
        nth_error shdrs (esym_shndx csym) = Some csh /\
        compute_func_slice_offsets kind csh csym = inr r_.
Proof.
  intros kind shdrs syms allowed_callees.
  induction allowed_callees as [| cn0 rest IH]; intros addrs H cn Hin;
    cbn [collect_exec_callee_addrs] in H; [contradiction Hin |].
  destruct (find_unique_func_sym syms cn0) as [csym |] eqn:Ef; [| discriminate H].
  destruct (nth_error shdrs (esym_shndx csym)) as [csh |] eqn:Ecsh; [| discriminate H].
  destruct (compute_func_slice_offsets kind csh csym) as [| r_] eqn:Eoff; [discriminate H |].
  destruct (collect_exec_callee_addrs kind shdrs syms rest) as [| rest_addrs] eqn:Hr; [discriminate H |].
  inversion H; subst addrs; clear H.
  destruct Hin as [<- | Hin].
  - exists csym, csh, r_; repeat split; [left; reflexivity | exact Ef | exact Ecsh | exact Eoff].
  - destruct (IH _ eq_refl _ Hin) as (cs & ch & rr & Hina & Hfs & Hcs & Hof).
    exists cs, ch, rr; repeat split; [right; exact Hina | exact Hfs | exact Hcs | exact Hof].
Qed.

Theorem elf64_extract_func_with_calls_sound :
  forall raw want_arch want_kind fn_name allowed_callees sl ci,
    elf64_extract_func_with_calls raw want_arch want_kind fn_name allowed_callees = inr (sl, ci) ->
    efs_arch sl = want_arch /\
    efs_kind sl = want_kind /\
    0 < efs_size sl /\
    efs_file_off sl + efs_size sl <= List.length raw /\
    efs_bytes sl = firstn (efs_size sl) (skipn (efs_file_off sl) raw) /\
    List.length (efs_bytes sl) = efs_size sl /\
    (want_kind = EK_Rel ->
      eci_sym_addrs ci = [] /\
      NoDup (List.map fst (eci_relocs ci)) /\
      forall rel_off cname,
        In (rel_off, cname) (eci_relocs ci) ->
        (rel_off < efs_range_hi sl - efs_range_lo sl)%N /\
        In cname allowed_callees) /\
    ((want_kind = EK_Exec \/ want_kind = EK_Dyn) ->
      eci_relocs ci = [] /\
      forall cn,
        In cn allowed_callees ->
        exists csym, In (cn, esym_value csym) (eci_sym_addrs ci)) /\
    exists hdr shdrs syms sym sh,
      parse_elf64_header raw = inr hdr /\
      parse_elf64_shdrs raw hdr = inr shdrs /\
      parse_elf64_symtab raw shdrs = inr syms /\
      find_unique_func_sym syms fn_name = Some sym /\
      nth_error shdrs (esym_shndx sym) = Some sh /\
      esh_type sh <> SHT_NOBITS /\
      bit_is_set (esh_flags sh) 2%N = true /\
      (want_kind = EK_Exec \/ want_kind = EK_Dyn ->
       check_exec_relocations raw want_arch shdrs (efs_shndx sl) (efs_range_lo sl) (efs_range_hi sl) = true).
Proof.
  intros raw want_arch want_kind fn_name allowed_callees sl ci H.
  unfold elf64_extract_func_with_calls in H.
  destruct (parse_elf64_header raw) as [err | hdr] eqn:Eh; [discriminate H |].
  destruct (elf_arch_eqb (eh_arch hdr) want_arch) eqn:Ea; cbn [negb] in H; [| discriminate H].
  apply elf_arch_eqb_eq in Ea.
  destruct (elf_kind_eqb (eh_kind hdr) want_kind) eqn:Ek; cbn [negb] in H; [| discriminate H].
  apply elf_kind_eqb_eq in Ek.
  destruct (parse_elf64_shdrs raw hdr) as [err | shdrs] eqn:Eshs; [discriminate H |].
  destruct (parse_elf64_symtab raw shdrs) as [err | syms] eqn:Esyms; [discriminate H |].
  destruct (find_unique_func_sym syms fn_name) as [sym |] eqn:Ef; [| discriminate H].
  destruct (nth_error shdrs (esym_shndx sym)) as [sh |] eqn:Eth; [| discriminate H].
  destruct (compute_func_slice_offsets (eh_kind hdr) sh sym) as [err | [[foff rlo] rhi]] eqn:Eoff;
    [discriminate H |].
  destruct (n_to_nat_checked (List.length raw) foff) as [foff_nat |] eqn:Efn; [| discriminate H].
  destruct (n_to_nat_checked (List.length raw) (esym_size sym)) as [fsz_nat |] eqn:Esn;
    [| discriminate H].
  destruct (slice_bytes raw foff_nat fsz_nat) as [bytes |] eqn:Esl; [| discriminate H].
  destruct (slice_bytes_spec _ _ _ _ Esl) as (Hle & Hfirst & Hlen).
  assert (Eoff_copy : compute_func_slice_offsets (eh_kind hdr) sh sym = inr (foff, rlo, rhi)) by exact Eoff.
  unfold compute_func_slice_offsets in Eoff_copy.
  destruct (N.eqb (esym_size sym) 0%N) eqn:Esz0; [discriminate Eoff_copy |].
  destruct (N.eqb (esh_type sh) SHT_NOBITS) eqn:Enob; [discriminate Eoff_copy |].
  destruct (bit_is_set (esh_flags sh) 2%N) eqn:Eex; cbn [negb] in Eoff_copy; [| discriminate Eoff_copy].
  apply N.eqb_neq in Esz0; apply N.eqb_neq in Enob.
  assert (Hlohi : (rlo <= rhi)%N).
  { rewrite Ek in Eoff_copy; destruct want_kind;
      [destruct (N.leb (esym_value sym + esym_size sym) (esh_size sh)); try discriminate Eoff_copy;
       inversion Eoff_copy; lia
      | destruct (N.leb (esh_addr sh) (esym_value sym)); try discriminate Eoff_copy;
        destruct (N.leb (esym_value sym - esh_addr sh + esym_size sym) (esh_size sh)); try discriminate Eoff_copy;
        inversion Eoff_copy; lia
      | destruct (N.leb (esh_addr sh) (esym_value sym)); try discriminate Eoff_copy;
        destruct (N.leb (esym_value sym - esh_addr sh + esym_size sym) (esh_size sh)); try discriminate Eoff_copy;
        inversion Eoff_copy; lia]. }
  unfold n_to_nat_checked in Esn.
  destruct (N.leb (esym_size sym) (N.of_nat (List.length raw))); [| discriminate Esn].
  inversion Esn as [Hfsz]; clear Esn.
  assert (Hpos_sz : 0 < N.to_nat (esym_size sym)) by lia.
  destruct (eh_kind hdr) eqn:Ehk.
  - destruct (collect_all_call_relocs raw (eh_arch hdr) EK_Rel shdrs shdrs syms (esym_shndx sym) rlo rhi allowed_callees)
      as [| rels] eqn:Erels; [discriminate H |].
    destruct (elf_no_dup_N (List.map fst rels)) eqn:End; cbn [negb] in H; [| discriminate H].
    inversion H; subst sl ci; clear H.
    cbn [efs_arch efs_kind efs_shndx efs_file_off efs_size efs_bytes efs_range_lo efs_range_hi eci_relocs eci_sym_addrs].
    rewrite Ea, Ek in *.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [lia |].
    split; [exact Hle |].
    split; [exact Hfirst |].
    split; [exact Hlen |].
    split.
    + intros _; split; [reflexivity | split; [exact (elf_no_dup_N_sound _ End) |]].
      intros rel_off cname Hin.
      rewrite <- Ek in Erels.
      destruct (collect_all_call_relocs_rel_sound _ _ _ _ _ _ _ _ _ _ Hlohi Erels _ _ Hin) as (Hlt & Hcn & _);
        exact (conj Hlt Hcn).
    + split.
      * intros [C | C]; rewrite <- Ek in C; discriminate C.
      * exists hdr, shdrs, syms, sym, sh; repeat split; try assumption.
        intros [C | C]; rewrite <- Ek in C; discriminate C.
  - destruct (check_exec_relocations raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi) eqn:Ecr;
      cbn [negb] in H; [| discriminate H].
    destruct (collect_exec_callee_addrs EK_Exec shdrs syms allowed_callees) as [| addrs] eqn:Ead;
      [discriminate H |].
    inversion H; subst sl ci; clear H.
    cbn [efs_arch efs_kind efs_shndx efs_file_off efs_size efs_bytes efs_range_lo efs_range_hi eci_relocs eci_sym_addrs].
    rewrite Ea, Ek in *.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [lia |].
    split; [exact Hle |].
    split; [exact Hfirst |].
    split; [exact Hlen |].
    split; [intro C; rewrite <- Ek in C; discriminate C |].
    split.
    + intros _; split; [reflexivity |].
      intros cn Hcn; destruct (collect_exec_callee_addrs_sound _ _ _ _ _ Ead cn Hcn) as (csym & _ & _ & Hina & _).
      exists csym; exact Hina.
    + exists hdr, shdrs, syms, sym, sh; repeat split; try assumption.
      intros _; exact Ecr.
  - destruct (check_exec_relocations raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi) eqn:Ecr;
      cbn [negb] in H; [| discriminate H].
    destruct (collect_exec_callee_addrs EK_Dyn shdrs syms allowed_callees) as [| addrs] eqn:Ead;
      [discriminate H |].
    inversion H; subst sl ci; clear H.
    cbn [efs_arch efs_kind efs_shndx efs_file_off efs_size efs_bytes efs_range_lo efs_range_hi eci_relocs eci_sym_addrs].
    rewrite Ea, Ek in *.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [lia |].
    split; [exact Hle |].
    split; [exact Hfirst |].
    split; [exact Hlen |].
    split; [intro C; rewrite <- Ek in C; discriminate C |].
    split.
    + intros _; split; [reflexivity |].
      intros cn Hcn; destruct (collect_exec_callee_addrs_sound _ _ _ _ _ Ead cn Hcn) as (csym & _ & _ & Hina & _).
      exists csym; exact Hina.
    + exists hdr, shdrs, syms, sym, sh; repeat split; try assumption.
      intros _; exact Ecr.
Qed.
