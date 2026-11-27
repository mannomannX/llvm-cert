(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Bounds-Checked ELF64 Inspector & Relocation Gate ([CertValidator.Elf64Spec])

    Purpose:
      Pure, total specification for parsing little-endian ELF64 relocatable ([ET_REL]) and
      linked ([ET_EXEC] / [ET_DYN]) binaries on RISC-V and AArch64, slicing [STT_FUNC]
      bodies and collecting direct-call relocations and target symbol addresses.

    Trust Contract & Fail-Closed Boundary:
      [elf64_extract_func] and [elf64_extract_func_with_calls] fail closed ([inl err]) on
      invalid headers, missing/duplicate [SHT_SYMTAB] or [STT_FUNC], disallowed relocations
      ([R_RISCV_RELAX] / [R_RISCV_ALIGN] or non-call relocs), or out-of-bounds slices; [inr]
      outputs satisfy [elf64_extract_func_sound] / [elf64_extract_func_with_calls_sound].
      Extracted to OCaml via [Extract.v].

    Assumptions:
      [Stdlib] and [CertValidator.common.{Options,Diag}] only; zero Vellvm dependencies and
      zero custom axioms.

    Section Outline:
      1. Byte-stream slicing & LE decoders; 2. ELF64 types & constants; 3. Header/section/
      symbol parsers; 4. Relocation gate; 5. Function slicing; 6. Call-reloc extraction. *)

From CertValidator.common Require Import Options Diag.

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

Fixpoint elf_length_tr_acc {A : Type} (acc : nat) (xs : list A) {struct xs} : nat :=
  match xs with
  | [] => acc
  | _ :: rest => elf_length_tr_acc (S acc) rest
  end.

Definition elf_length_tr {A : Type} (xs : list A) : nat :=
  elf_length_tr_acc O xs.

Lemma elf_length_tr_acc_eq : forall {A : Type} (acc : nat) (xs : list A),
  elf_length_tr_acc acc xs = (acc + List.length xs)%nat.
Proof.
  intros A acc xs; revert acc; induction xs as [| x rest IH];
  intro acc; cbn; [lia | rewrite IH; lia].
Qed.

Lemma elf_length_tr_eq : forall {A : Type} (xs : list A),
  elf_length_tr xs = List.length xs.
Proof.
  intros A xs; unfold elf_length_tr; rewrite elf_length_tr_acc_eq; reflexivity.
Qed.

Definition elf_rev_tr {A : Type} (xs : list A) : list A :=
  List.rev_append xs [].

Lemma elf_rev_tr_eq : forall {A : Type} (xs : list A),
  elf_rev_tr xs = List.rev xs.
Proof.
  intros A xs; unfold elf_rev_tr; rewrite rev_append_rev, app_nil_r; reflexivity.
Qed.

Fixpoint elf_map_tr_acc {A B : Type} (f : A -> B) (acc : list B) (xs : list A) {struct xs} : list B :=
  match xs with
  | [] => List.rev_append acc []
  | x :: rest => elf_map_tr_acc f (f x :: acc) rest
  end.

Definition elf_map_tr {A B : Type} (f : A -> B) (xs : list A) : list B :=
  elf_map_tr_acc f [] xs.

Lemma elf_map_tr_acc_eq : forall {A B : Type} (f : A -> B) (acc : list B) (xs : list A),
  elf_map_tr_acc f acc xs = List.rev_append acc (List.map f xs).
Proof.
  intros A B f acc xs; revert acc; induction xs as [| x rest IH]; intros acc;
    cbn [elf_map_tr_acc List.map]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma elf_map_tr_eq : forall {A B : Type} (f : A -> B) (xs : list A),
  elf_map_tr f xs = List.map f xs.
Proof.
  intros A B f xs; unfold elf_map_tr; exact (elf_map_tr_acc_eq f [] xs).
Qed.

Fixpoint elf_firstn_rev {A : Type} (n : nat) (acc xs : list A) {struct n} : list A :=
  match n with
  | O => List.rev_append acc []
  | S n' =>
      match xs with
      | [] => List.rev_append acc []
      | x :: rest => elf_firstn_rev n' (x :: acc) rest
      end
  end.

Definition elf_firstn_tr {A : Type} (n : nat) (xs : list A) : list A :=
  elf_firstn_rev n [] xs.

Lemma elf_firstn_rev_eq : forall {A : Type} (n : nat) (acc xs : list A),
  elf_firstn_rev n acc xs = List.rev_append acc (firstn n xs).
Proof.
  intros A n; induction n as [| n' IH]; intros acc [| x rest];
    cbn [elf_firstn_rev firstn]; try reflexivity;
    rewrite IH; reflexivity.
Qed.

Lemma elf_firstn_tr_eq : forall {A : Type} (n : nat) (xs : list A),
  elf_firstn_tr n xs = firstn n xs.
Proof.
  intros A n xs; unfold elf_firstn_tr; exact (elf_firstn_rev_eq n [] xs).
Qed.

Fixpoint find_unique_tr {A : Type} (p : A -> bool) (found : option A) (xs : list A)
  {struct xs} : option A :=
  match xs with
  | [] => found
  | x :: rest =>
      if p x then
        match found with
        | None => find_unique_tr p (Some x) rest
        | Some _ => None
        end
      else find_unique_tr p found rest
  end.

Lemma find_unique_tr_some : forall {A : Type} (p : A -> bool) (xs : list A) (found : option A) (res : A),
  find_unique_tr p found xs = Some res ->
  (match found with Some f => f = res | None => In res xs /\ p res = true end) /\
  (forall y, In y xs -> p y = true -> y = res).
Proof.
  intros A p xs; induction xs as [| x rest IH]; intros [f |] res H;
    cbn [find_unique_tr] in H.
  - inversion H; subst; split; [reflexivity | intros y []].
  - discriminate H.
  - destruct (p x) eqn:Epx; [discriminate H |].
    destruct (IH (Some f) res H) as [Hf Hrest].
    split; [exact Hf |].
    intros y [-> | Hy] Hpy; [rewrite Hpy in Epx; discriminate Epx | exact (Hrest y Hy Hpy)].
  - destruct (p x) eqn:Epx.
    + destruct (IH (Some x) res H) as [Hx Hrest].
      subst res; split; [split; [left; reflexivity | exact Epx] |].
      intros y [-> | Hy] Hpy; [reflexivity | exact (Hrest y Hy Hpy)].
    + destruct (IH None res H) as [[Hin Hpr] Hrest].
      split; [split; [right; exact Hin | exact Hpr] |].
      intros y [-> | Hy] Hpy; [rewrite Hpy in Epx; discriminate Epx | exact (Hrest y Hy Hpy)].
Qed.

Lemma find_unique_tr_spec : forall {A : Type} (p : A -> bool) (xs : list A) (res : A),
  find_unique_tr p None xs = Some res ->
  In res xs /\ p res = true /\ forall y, In y xs -> p y = true -> y = res.
Proof.
  intros A p xs res H.
  destruct (find_unique_tr_some p xs None res H) as [[Hin Hpr] Huniq].
  exact (conj Hin (conj Hpr Huniq)).
Qed.

Lemma find_unique_diag_acc_eq_tr : forall {A : Type} (p : A -> bool) found xs x,
  find_unique_diag_acc p found xs = UM_Unique x ->
  find_unique_tr p found xs = Some x.
Proof.
  intros A p found xs; revert found; induction xs as [| y rest IH]; intros [f |] x H;
    cbn [find_unique_diag_acc find_unique_tr] in *.
  - inversion H; reflexivity.
  - discriminate H.
  - destruct (p y); [discriminate H | exact (IH _ _ H)].
  - destruct (p y); [exact (IH _ _ H) | exact (IH _ _ H)].
Qed.

Lemma find_unique_diag_eq_tr : forall {A : Type} (p : A -> bool) xs x,
  find_unique_diag p xs = UM_Unique x ->
  find_unique_tr p None xs = Some x.
Proof.
  intros A p xs x H; exact (find_unique_diag_acc_eq_tr p None xs x H).
Qed.

Fixpoint string_to_bytes_acc (acc : list N) (s : string) {struct s} : list N :=
  match s with
  | EmptyString => List.rev_append acc []
  | String a rest => string_to_bytes_acc (Ascii.N_of_ascii a :: acc) rest
  end.

Definition string_to_bytes (s : string) : list N :=
  string_to_bytes_acc [] s.

Lemma string_to_bytes_acc_app : forall s acc,
  string_to_bytes_acc acc s = List.rev_append acc (string_to_bytes s).
Proof.
  induction s as [| a rest IH]; intros acc.
  - reflexivity.
  - change (string_to_bytes_acc (Ascii.N_of_ascii a :: acc) rest =
            List.rev_append acc (string_to_bytes_acc [Ascii.N_of_ascii a] rest)).
    rewrite IH, (IH [Ascii.N_of_ascii a]); reflexivity.
Qed.

Lemma string_to_bytes_nil : string_to_bytes EmptyString = [].
Proof. reflexivity. Qed.

Lemma string_to_bytes_cons : forall a rest,
  string_to_bytes (String a rest) = Ascii.N_of_ascii a :: string_to_bytes rest.
Proof.
  intros a rest; unfold string_to_bytes; cbn [string_to_bytes_acc].
  rewrite string_to_bytes_acc_app; reflexivity.
Qed.

Definition slice_bytes (raw : list N) (off len : nat) : option (list N) :=
  if Nat.leb (off + len) (elf_length_tr raw)
  then Some (elf_firstn_tr len (skipn off raw))
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
  intros A n; induction n as [| n' IH]; intros [| x xs'] Hle;
  cbn in *; try lia; try reflexivity.
  f_equal; apply IH; lia.
Qed.

Lemma slice_bytes_spec : forall raw off len bs,
  slice_bytes raw off len = Some bs ->
  off + len <= List.length raw /\
  bs = firstn len (skipn off raw) /\
  List.length bs = len.
Proof.
  intros raw off len bs H.
  unfold slice_bytes in H; rewrite elf_length_tr_eq, elf_firstn_tr_eq in H.
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

Fixpoint take_le_n_acc (n : nat) (shift acc : N) (bs : list N) {struct n}
  : option (N * list N) :=
  match n with
  | O => Some (acc, bs)
  | S n' =>
      match bs with
      | [] => None
      | b :: rest =>
          take_le_n_acc n' (256 * shift)%N (acc + N.modulo b 256 * shift)%N rest
      end
  end.

Definition take_le_n (n : nat) (bs : list N) : option (N * list N) :=
  take_le_n_acc n 1%N 0%N bs.

Definition take_u8 (bs : list N) : option (N * list N) := take_le_n 1 bs.
Definition take_u16_le (bs : list N) : option (N * list N) := take_le_n 2 bs.
Definition take_u32_le (bs : list N) : option (N * list N) := take_le_n 4 bs.
Definition take_u64_le (bs : list N) : option (N * list N) := take_le_n 8 bs.

Fixpoint rev_chars_to_string (acc : list ascii) (s : string) {struct acc} : string :=
  match acc with
  | [] => s
  | c :: rest => rev_chars_to_string rest (String c s)
  end.

Fixpoint read_cstr_bytes (acc : list ascii) (bs : list N) {struct bs} : option string :=
  match bs with
  | [] => None
  | b :: rest =>
      let b' := N.modulo b 256 in
      if N.eqb b' 0%N then Some (rev_chars_to_string acc EmptyString)
      else read_cstr_bytes (Ascii.ascii_of_N b' :: acc) rest
  end.

Definition read_cstr_from_strtab (strtab : list N) (str_len : nat) (name_off : N) : option string :=
  if N.ltb name_off (N.of_nat str_len) then
    read_cstr_bytes [] (skipn (N.to_nat name_off) strtab)
  else None.

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
  intros [] []; cbn; split; intro H;
  try reflexivity; discriminate H.
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
  intros [] []; cbn; split; intro H;
  try reflexivity; discriminate H.
Qed.

Definition elf_arch_name (a : elf_arch) : string :=
  match a with
  | EA_Riscv64 => "rv64"
  | EA_AArch64 => "aarch64"
  end.

Definition elf_kind_name (k : elf_kind) : string :=
  match k with
  | EK_Rel => "ET_REL"
  | EK_Exec => "ET_EXEC"
  | EK_Dyn => "ET_DYN"
  end.

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

Definition R_RISCV_JAL : N := 17%N.
Definition R_RISCV_CALL : N := 18%N.
Definition R_RISCV_CALL_PLT : N := 19%N.
Definition R_RISCV_ALIGN : N := 43%N.
Definition R_RISCV_RELAX : N := 51%N.
Definition R_AARCH64_CALL26 : N := 283%N.

Definition elf_rela_type_name (arch : elf_arch) (r_type : N) : string :=
  match arch with
  | EA_Riscv64 =>
      if N.eqb r_type R_RISCV_JAL then "R_RISCV_JAL"
      else if N.eqb r_type R_RISCV_CALL then "R_RISCV_CALL"
      else if N.eqb r_type R_RISCV_CALL_PLT then "R_RISCV_CALL_PLT"
      else if N.eqb r_type R_RISCV_ALIGN then "R_RISCV_ALIGN"
      else if N.eqb r_type R_RISCV_RELAX then "R_RISCV_RELAX"
      else "R_RISCV_" ++ diag_N_dec r_type
  | EA_AArch64 =>
      if N.eqb r_type R_AARCH64_CALL26 then "R_AARCH64_CALL26"
      else "R_AARCH64_" ++ diag_N_dec r_type
  end.

#[local] Arguments elf_arch_name _ : simpl never.
#[local] Arguments elf_kind_name _ : simpl never.
#[local] Arguments elf_rela_type_name _ _ : simpl never.

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
  let len := elf_length_tr raw in
  if negb (Nat.leb 64 len) then
    inl (diag "elf-hdr" ("buffer shorter than 64-byte header (len=" ++ diag_nat_dec len ++ ")"))
  else if negb (has_elf_magic raw) then
    inl (diag "elf-hdr" "invalid ELF magic (expected 0x7f ELF)")
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
        if negb (N.eqb e_class ELFCLASS64) then
          inl (diag "elf-hdr" ("only ELFCLASS64 supported, got EI_CLASS=" ++ diag_N_dec e_class))
        else if negb (N.eqb e_data ELFDATA2LSB) then
          inl (diag "elf-hdr" ("only little-endian ELFDATA2LSB supported, got EI_DATA=" ++ diag_N_dec e_data))
        else if negb (N.eqb e_ident_ver EV_CURRENT && N.eqb e_ver EV_CURRENT) then
          inl (diag "elf-hdr"
                 ("invalid ELF version (EI_VERSION=" ++ diag_N_dec e_ident_ver ++
                  ", e_version=" ++ diag_N_dec e_ver ++ ")"))
        else if negb (N.eqb e_ehsize 64%N && N.eqb e_shentsize 64%N) then
          inl (diag "elf-hdr"
                 ("unexpected ELF64 entry size (e_ehsize=" ++ diag_N_dec e_ehsize ++
                  ", e_shentsize=" ++ diag_N_dec e_shentsize ++ ")"))
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
              if N.eqb e_shnum 0%N then
                inl (diag "elf-hdr" "ELF64 has zero section headers (e_shnum=0)")
              else if negb (N.leb (e_shoff + e_shnum * 64%N) (N.of_nat len)) then
                inl (diag "elf-hdr"
                       ("section header table out of bounds (e_shoff=" ++ diag_N_hex e_shoff ++
                        ", e_shnum=" ++ diag_N_dec e_shnum ++ ", len=" ++ diag_nat_dec len ++ ")"))
              else if elf_arch_eqb arch EA_Riscv64 && bit_is_set e_flags 3%N then
                inl (diag "elf-hdr"
                       ("EF_RISCV_RVE forbidden by LP64 safety profile (e_flags=" ++ diag_N_hex e_flags ++ ")"))
              else
                let rvc := elf_arch_eqb arch EA_Riscv64 && bit_is_set e_flags 0%N in
                inr (mk_elf64_hdr kind arch e_shoff e_flags rvc (N.to_nat e_shentsize) (N.to_nat e_shnum))
          | None, _ =>
              inl (diag "elf-hdr" ("unsupported e_type=" ++ diag_N_dec e_type ++ " (expected ET_REL/ET_EXEC/ET_DYN)"))
          | _, None =>
              inl (diag "elf-hdr"
                     ("unsupported e_machine=" ++ diag_N_dec e_machine ++
                      " (expected EM_RISCV/EM_AARCH64)"))
          end
    | _, _, _, _, _, _, _, _, _, _, _ =>
        inl (diag "elf-hdr" "truncated ELF64 header fields")
    end.

Definition shdr_trunc_err (idx : nat) (field : string) : string :=
  diag "elf-shdr" ("truncated " ++ field ++ " in shdr#" ++ diag_nat_dec idx).

#[local] Arguments shdr_trunc_err _ _ : simpl never.

Definition parse_shdr_cursor (raw_len idx : nat) (cur : list N)
  : string + (elf64_shdr * list N) :=
  let c1 := skipn 4 cur in
  match take_u32_le c1 with
  | None => inl (shdr_trunc_err idx "sh_type")
  | Some (sh_type, c2) =>
      match take_u64_le c2 with
      | None => inl (shdr_trunc_err idx "sh_flags")
      | Some (sh_flags, c3) =>
          match take_u64_le c3 with
          | None => inl (shdr_trunc_err idx "sh_addr")
          | Some (sh_addr, c4) =>
              match take_u64_le c4 with
              | None => inl (shdr_trunc_err idx "sh_offset")
              | Some (sh_offset, c5) =>
                  match take_u64_le c5 with
                  | None => inl (shdr_trunc_err idx "sh_size")
                  | Some (sh_size, c6) =>
                      match take_u32_le c6 with
                      | None => inl (shdr_trunc_err idx "sh_link")
                      | Some (sh_link, c7) =>
                          match take_u32_le c7 with
                          | None => inl (shdr_trunc_err idx "sh_info")
                          | Some (sh_info, c8) =>
                              match take_u64_le (skipn 8 c8) with
                              | None => inl (shdr_trunc_err idx "sh_entsize")
                              | Some (sh_entsize, rest) =>
                                  if negb (N.eqb sh_type SHT_NOBITS) &&
                                     negb (N.leb (sh_offset + sh_size) (N.of_nat raw_len)) then
                                    inl (diag "elf-shdr"
                                           ("shdr#" ++ diag_nat_dec idx ++
                                            " payload out of bounds (sh_offset=" ++ diag_N_hex sh_offset ++
                                            ", sh_size=" ++ diag_N_hex sh_size ++
                                            ", file_len=" ++ diag_nat_dec raw_len ++ ")"))
                                  else if negb (N.leb sh_link 1000000%N && N.leb sh_info 1000000%N) then
                                    inl (diag "elf-shdr"
                                           ("shdr#" ++ diag_nat_dec idx ++
                                            " sh_link/sh_info out of range (sh_link=" ++ diag_N_dec sh_link ++
                                            ", sh_info=" ++ diag_N_dec sh_info ++ ")"))
                                  else
                                    inr (mk_elf64_shdr idx sh_type sh_flags sh_addr sh_offset sh_size
                                           (N.to_nat sh_link) (N.to_nat sh_info) sh_entsize, rest)
                              end
                          end
                      end
                  end
              end
          end
      end
  end.

Fixpoint parse_shdrs_cursor (fuel raw_len idx : nat) (cur : list N) (acc : list elf64_shdr)
  {struct fuel} : string + list elf64_shdr :=
  match fuel with
  | O => inr (elf_rev_tr acc)
  | S fuel' =>
      match parse_shdr_cursor raw_len idx cur with
      | inl err => inl err
      | inr (s, rest) => parse_shdrs_cursor fuel' raw_len (S idx) rest (s :: acc)
      end
  end.

Definition parse_elf64_shdrs (raw : list N) (hdr : elf64_hdr) : string + list elf64_shdr :=
  let raw_len := elf_length_tr raw in
  match n_to_nat_checked raw_len (eh_shoff hdr) with
  | None =>
      inl (diag "elf-shdr"
             ("e_shoff=" ++ diag_N_hex (eh_shoff hdr) ++
              " out of bounds (file_len=" ++ diag_nat_dec raw_len ++ ")"))
  | Some shoff =>
      if negb (Nat.leb (shoff + eh_shnum hdr * 64) raw_len) then
        inl (diag "elf-shdr"
               ("section header table exceeds file length (shoff=" ++ diag_nat_dec shoff ++
                ", shnum=" ++ diag_nat_dec (eh_shnum hdr) ++ ", file_len=" ++ diag_nat_dec raw_len ++ ")"))
      else parse_shdrs_cursor (eh_shnum hdr) raw_len 0 (skipn shoff raw) []
  end.

Definition find_unique_symtab (shdrs : list elf64_shdr) : option elf64_shdr :=
  find_unique_tr (fun s => N.eqb (esh_type s) SHT_SYMTAB) None shdrs.

Definition sym_trunc_err (sym_idx : nat) (field : string) : string :=
  diag "elf-symtab" ("truncated " ++ field ++ " in sym#" ++ diag_nat_dec sym_idx).

#[local] Arguments sym_trunc_err _ _ : simpl never.

Fixpoint parse_syms_cursor
  (fuel sym_idx : nat) (cur strtab : list N) (str_len : nat) (acc : list elf64_sym)
  {struct fuel} : string + list elf64_sym :=
  match fuel with
  | O => inr (elf_rev_tr acc)
  | S fuel' =>
      match take_u32_le cur with
      | None => inl (sym_trunc_err sym_idx "st_name")
      | Some (st_name_off, c1) =>
          match take_u8 c1 with
          | None => inl (sym_trunc_err sym_idx "st_info")
          | Some (st_info, c2) =>
              match take_u16_le (skipn 1 c2) with
              | None => inl (sym_trunc_err sym_idx "st_shndx")
              | Some (st_shndx, c3) =>
                  match take_u64_le c3 with
                  | None => inl (sym_trunc_err sym_idx "st_value")
                  | Some (st_value, c4) =>
                      match take_u64_le c4 with
                      | None => inl (sym_trunc_err sym_idx "st_size")
                      | Some (st_size, rest) =>
                          match read_cstr_from_strtab strtab str_len st_name_off with
                          | None =>
                              inl (diag "elf-symtab"
                                     ("sym#" ++ diag_nat_dec sym_idx ++
                                      " st_name=" ++ diag_N_hex st_name_off ++
                                      " out of bounds or unterminated in .strtab (str_len=" ++
                                      diag_nat_dec str_len ++ ")"))
                          | Some name =>
                              let sym := mk_elf64_sym name (N.modulo st_info 16%N)
                                           (N.to_nat st_shndx) st_value st_size in
                              parse_syms_cursor fuel' (S sym_idx) rest strtab str_len (sym :: acc)
                          end
                      end
                  end
              end
          end
      end
  end.

Definition parse_elf64_symtab (raw : list N) (shdrs : list elf64_shdr)
  : string + list elf64_sym :=
  match find_unique_diag (fun s => N.eqb (esh_type s) SHT_SYMTAB) shdrs with
  | UM_Missing => inl (diag "elf-symtab" "missing SHT_SYMTAB section")
  | UM_Duplicate s1 s2 =>
      inl (diag "elf-symtab"
             ("duplicate SHT_SYMTAB sections: shdr#" ++ diag_nat_dec (esh_idx s1) ++
              " and shdr#" ++ diag_nat_dec (esh_idx s2)))
  | UM_Unique sym_sh =>
      if negb (N.eqb (esh_entsize sym_sh) 24%N && N.eqb (N.modulo (esh_size sym_sh) 24%N) 0%N) then
        inl (diag "elf-symtab"
               ("SHT_SYMTAB shdr#" ++ diag_nat_dec (esh_idx sym_sh) ++
                " invalid entsize=" ++ diag_N_dec (esh_entsize sym_sh) ++
                " or unaligned size=" ++ diag_N_dec (esh_size sym_sh)))
      else
        match nth_error shdrs (esh_link sym_sh) with
        | None =>
            inl (diag "elf-symtab"
                   ("SHT_SYMTAB shdr#" ++ diag_nat_dec (esh_idx sym_sh) ++
                    " sh_link=" ++ diag_nat_dec (esh_link sym_sh) ++ " out of range"))
        | Some str_sh =>
            if N.eqb (esh_type str_sh) SHT_NOBITS then
              inl (diag "elf-symtab"
                     ("string table shdr#" ++ diag_nat_dec (esh_idx str_sh) ++ " cannot be SHT_NOBITS"))
            else
              let raw_len := elf_length_tr raw in
              match n_to_nat_checked raw_len (esh_offset sym_sh),
                    n_to_nat_checked raw_len (esh_size sym_sh),
                    n_to_nat_checked raw_len (esh_offset str_sh),
                    n_to_nat_checked raw_len (esh_size str_sh)
              with
              | Some sym_off, Some sym_sz, Some str_off, Some str_sz =>
                  let count := Nat.div sym_sz 24 in
                  if negb (Nat.leb (sym_off + count * 24) raw_len) then
                    inl (diag "elf-symtab"
                           ("symbol table shdr#" ++ diag_nat_dec (esh_idx sym_sh) ++
                            " out of bounds (off=" ++ diag_nat_dec sym_off ++
                            ", size=" ++ diag_nat_dec sym_sz ++ ", file_len=" ++ diag_nat_dec raw_len ++ ")"))
                  else if negb (Nat.leb (str_off + str_sz) raw_len) then
                    inl (diag "elf-symtab"
                           ("string table shdr#" ++ diag_nat_dec (esh_idx str_sh) ++
                            " out of bounds (off=" ++ diag_nat_dec str_off ++
                            ", size=" ++ diag_nat_dec str_sz ++ ", file_len=" ++ diag_nat_dec raw_len ++ ")"))
                  else
                    let strtab := elf_firstn_tr str_sz (skipn str_off raw) in
                    parse_syms_cursor count 0 (skipn sym_off raw) strtab str_sz []
              | _, _, _, _ =>
                  inl (diag "elf-symtab"
                         ("symbol table shdr#" ++ diag_nat_dec (esh_idx sym_sh) ++
                          " or string table shdr#" ++ diag_nat_dec (esh_idx str_sh) ++ " offset/size exceeds bounds"))
              end
        end
  end.

Definition find_unique_func_sym (syms : list elf64_sym) (fn_name : string)
  : option elf64_sym :=
  find_unique_tr
    (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) fn_name)
    None syms.

(** ** 4. [F-27] Relocation & Linker-Relaxation Gate *)

Definition parse_rela_cursor (cur : list N) : option (elf64_rela * list N) :=
  match take_u64_le cur with
  | None => None
  | Some (r_off, c1) =>
      match take_u64_le c1 with
      | None => None
      | Some (r_info, c2) =>
          match take_u64_le c2 with
          | None => None
          | Some (r_add, rest) =>
              let r_type := N.modulo r_info 4294967296%N in
              let r_sym := N.div r_info 4294967296%N in
              Some (mk_elf64_rela r_off r_sym r_type r_add, rest)
          end
      end
  end.

Fixpoint parse_relas_cursor (fuel : nat) (cur : list N) (acc : list elf64_rela)
  {struct fuel} : option (list elf64_rela) :=
  match fuel with
  | O => Some (elf_rev_tr acc)
  | S fuel' =>
      match parse_rela_cursor cur with
      | Some (r, rest) => parse_relas_cursor fuel' rest (r :: acc)
      | None => None
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
          let raw_len := elf_length_tr raw in
          match n_to_nat_checked raw_len (esh_offset sh),
                n_to_nat_checked raw_len (esh_size sh)
          with
          | Some r_off, Some r_sz =>
              let count := Nat.div r_sz 24 in
              if negb (Nat.leb (r_off + count * 24) raw_len) then false
              else
                match parse_relas_cursor count (skipn r_off raw) [] with
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

Definition check_rela_entry_diag
  (arch : elf_arch) (rela_shndx rela_info target_shndx entry_idx : nat)
  (fn_lo fn_hi : N) (r : elf64_rela) : string + unit :=
  if elf_arch_eqb arch EA_Riscv64 &&
     (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN)
  then
    inl (diag "elf-reloc"
           ("forbidden relaxation/alignment relocation " ++
            elf_rela_type_name arch (er_type r) ++ "(" ++ diag_N_dec (er_type r) ++ ")" ++
            " at shdr#" ++ diag_nat_dec rela_shndx ++
            " entry#" ++ diag_nat_dec entry_idx ++
            " offset=" ++ diag_N_hex (er_offset r)))
  else if Nat.eqb rela_info target_shndx then
    if N.ltb (er_offset r) fn_lo || N.leb fn_hi (er_offset r) then inr tt
    else
      inl (diag "elf-reloc"
             ("relocation inside executable slice [" ++
              diag_N_hex fn_lo ++ ".." ++ diag_N_hex fn_hi ++ ")" ++
              " at shdr#" ++ diag_nat_dec rela_shndx ++
              " entry#" ++ diag_nat_dec entry_idx ++
              " offset=" ++ diag_N_hex (er_offset r) ++
              " type=" ++ elf_rela_type_name arch (er_type r) ++
              "(" ++ diag_N_dec (er_type r) ++ ")"))
  else inr tt.

Lemma check_rela_entry_diag_sound :
  forall arch rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi r,
    check_rela_entry_diag arch rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi r = inr tt ->
    rela_entry_allowed arch rela_info target_shndx fn_lo fn_hi r = true.
Proof.
  intros arch rsh rinfo tsh eidx fn_lo fn_hi r H.
  unfold check_rela_entry_diag, rela_entry_allowed in *.
  destruct (elf_arch_eqb arch EA_Riscv64 && (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN));
    [discriminate H |].
  destruct (Nat.eqb rinfo tsh); [| reflexivity].
  destruct (N.ltb (er_offset r) fn_lo || N.leb fn_hi (er_offset r)); [reflexivity | discriminate H].
Qed.

Fixpoint check_rela_entries_diag_acc
  (arch : elf_arch) (rela_shndx rela_info target_shndx entry_idx : nat)
  (fn_lo fn_hi : N) (rs : list elf64_rela) {struct rs} : string + unit :=
  match rs with
  | [] => inr tt
  | r :: rest =>
      match check_rela_entry_diag arch rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi r with
      | inl err => inl err
      | inr tt => check_rela_entries_diag_acc arch rela_shndx rela_info target_shndx (S entry_idx) fn_lo fn_hi rest
      end
  end.

Lemma check_rela_entries_diag_acc_sound :
  forall arch rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi rs,
    check_rela_entries_diag_acc arch rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi rs = inr tt ->
    forallb (rela_entry_allowed arch rela_info target_shndx fn_lo fn_hi) rs = true.
Proof.
  intros arch rsh rinfo tsh eidx fn_lo fn_hi rs; revert eidx;
    induction rs as [| r rest IH]; intros eidx H;
    cbn [check_rela_entries_diag_acc forallb] in *; [reflexivity |].
  destruct (check_rela_entry_diag arch rsh rinfo tsh eidx fn_lo fn_hi r) as [err | []] eqn:Hr;
    [discriminate H |].
  rewrite (check_rela_entry_diag_sound _ _ _ _ _ _ _ _ Hr), (IH _ H); reflexivity.
Qed.

Definition check_one_rela_section_diag
  (raw : list N) (arch : elf_arch) (shdrs : list elf64_shdr)
  (target_shndx : nat) (fn_lo fn_hi : N) (sh : elf64_shdr) : string + unit :=
  if negb (N.eqb (esh_type sh) SHT_RELA) then inr tt
  else
    match nth_error shdrs (esh_info sh) with
    | None =>
        inl (diag "elf-reloc"
               ("SHT_RELA shdr#" ++ diag_nat_dec (esh_idx sh) ++
                " sh_info=" ++ diag_nat_dec (esh_info sh) ++ " out of bounds"))
    | Some tgt_sh =>
        if negb (bit_is_set (esh_flags tgt_sh) 2%N) then inr tt
        else if negb (N.eqb (esh_entsize sh) 24%N && N.eqb (N.modulo (esh_size sh) 24%N) 0%N) then
          inl (diag "elf-reloc"
                 ("SHT_RELA shdr#" ++ diag_nat_dec (esh_idx sh) ++
                  " invalid entsize=" ++ diag_N_dec (esh_entsize sh) ++
                  " or unaligned size=" ++ diag_N_dec (esh_size sh)))
        else
          let raw_len := elf_length_tr raw in
          match n_to_nat_checked raw_len (esh_offset sh),
                n_to_nat_checked raw_len (esh_size sh)
          with
          | Some r_off, Some r_sz =>
              let count := Nat.div r_sz 24 in
              if negb (Nat.leb (r_off + count * 24) raw_len) then
                inl (diag "elf-reloc"
                       ("SHT_RELA shdr#" ++ diag_nat_dec (esh_idx sh) ++
                        " payload out of bounds (off=" ++ diag_nat_dec r_off ++
                        ", size=" ++ diag_nat_dec r_sz ++ ", file_len=" ++ diag_nat_dec raw_len ++ ")"))
              else
                match parse_relas_cursor count (skipn r_off raw) [] with
                | None =>
                    inl (diag "elf-reloc" ("truncated SHT_RELA entries in shdr#" ++ diag_nat_dec (esh_idx sh)))
                | Some rs =>
                    check_rela_entries_diag_acc arch (esh_idx sh) (esh_info sh) target_shndx 0 fn_lo fn_hi rs
                end
          | _, _ =>
              inl (diag "elf-reloc"
                     ("SHT_RELA shdr#" ++ diag_nat_dec (esh_idx sh) ++ " offset or size exceeds bounds"))
          end
    end.

Lemma check_one_rela_section_diag_sound :
  forall raw arch shdrs target_shndx fn_lo fn_hi sh,
    check_one_rela_section_diag raw arch shdrs target_shndx fn_lo fn_hi sh = inr tt ->
    check_one_rela_section raw arch shdrs target_shndx fn_lo fn_hi sh = true.
Proof.
  intros raw arch shdrs tsh fn_lo fn_hi sh H.
  unfold check_one_rela_section_diag, check_one_rela_section in *.
  destruct (N.eqb (esh_type sh) SHT_RELA); cbn [negb] in H |- *; [| reflexivity].
  destruct (nth_error shdrs (esh_info sh)) as [tgt_sh |]; [| discriminate H].
  destruct (bit_is_set (esh_flags tgt_sh) 2%N); cbn [negb] in H |- *; [| reflexivity].
  destruct (N.eqb (esh_entsize sh) 24%N && N.eqb (N.modulo (esh_size sh) 24%N) 0%N);
    cbn [negb] in H |- *; [| discriminate H].
  destruct (n_to_nat_checked (elf_length_tr raw) (esh_offset sh)) as [r_off |]; [| discriminate H].
  destruct (n_to_nat_checked (elf_length_tr raw) (esh_size sh)) as [r_sz |]; [| discriminate H].
  destruct (Nat.leb (r_off + Nat.div r_sz 24 * 24) (elf_length_tr raw));
    cbn [negb] in H |- *; [| discriminate H].
  destruct (parse_relas_cursor (Nat.div r_sz 24) (skipn r_off raw) []) as [rs |]; [| discriminate H].
  exact (check_rela_entries_diag_acc_sound _ _ _ _ _ _ _ _ H).
Qed.

Fixpoint check_exec_relocations_diag_list
  (raw : list N) (arch : elf_arch) (shdrs : list elf64_shdr)
  (target_shndx : nat) (fn_lo fn_hi : N) (rem : list elf64_shdr)
  {struct rem} : string + unit :=
  match rem with
  | [] => inr tt
  | sh :: rest =>
      match check_one_rela_section_diag raw arch shdrs target_shndx fn_lo fn_hi sh with
      | inl err => inl err
      | inr tt => check_exec_relocations_diag_list raw arch shdrs target_shndx fn_lo fn_hi rest
      end
  end.

Definition check_exec_relocations_diag
  (raw : list N) (arch : elf_arch) (shdrs : list elf64_shdr)
  (target_shndx : nat) (fn_lo fn_hi : N) : string + unit :=
  check_exec_relocations_diag_list raw arch shdrs target_shndx fn_lo fn_hi shdrs.

Lemma check_exec_relocations_diag_list_sound :
  forall raw arch shdrs target_shndx fn_lo fn_hi rem,
    check_exec_relocations_diag_list raw arch shdrs target_shndx fn_lo fn_hi rem = inr tt ->
    forallb (check_one_rela_section raw arch shdrs target_shndx fn_lo fn_hi) rem = true.
Proof.
  intros raw arch shdrs tsh fn_lo fn_hi rem;
    induction rem as [| sh rest IH]; intro H;
    cbn [check_exec_relocations_diag_list forallb] in *; [reflexivity |].
  destruct (check_one_rela_section_diag raw arch shdrs tsh fn_lo fn_hi sh) as [err | []] eqn:Hs;
    [discriminate H |].
  rewrite (check_one_rela_section_diag_sound _ _ _ _ _ _ _ Hs), (IH H); reflexivity.
Qed.

Lemma check_exec_relocations_diag_sound :
  forall raw arch shdrs target_shndx fn_lo fn_hi,
    check_exec_relocations_diag raw arch shdrs target_shndx fn_lo fn_hi = inr tt ->
    check_exec_relocations raw arch shdrs target_shndx fn_lo fn_hi = true.
Proof.
  intros raw arch shdrs tsh fn_lo fn_hi H.
  exact (check_exec_relocations_diag_list_sound raw arch shdrs tsh fn_lo fn_hi shdrs H).
Qed.

(** ** 5. End-to-End Function Extraction & Top-Level Soundness Theorem *)

Definition compute_func_slice_offsets
  (kind : elf_kind) (sh : elf64_shdr) (sym : elf64_sym)
  : string + (N * N * N) :=
  if N.eqb (esym_size sym) 0%N then
    inl (diag "elf-slice" ("zero-sized ELF64 STT_FUNC symbol '" ++ esym_name sym ++ "'"))
  else if N.eqb (esh_type sh) SHT_NOBITS then
    inl (diag "elf-slice"
           ("symbol '" ++ esym_name sym ++ "' cannot reside in SHT_NOBITS shdr#" ++
            diag_nat_dec (esh_idx sh)))
  else if negb (bit_is_set (esh_flags sh) 2%N) then
    inl (diag "elf-slice"
           ("symbol '" ++ esym_name sym ++ "' section shdr#" ++
            diag_nat_dec (esh_idx sh) ++ " lacks SHF_EXECINSTR"))
  else
    match kind with
    | EK_Rel =>
        if negb (N.leb (esym_value sym + esym_size sym) (esh_size sh)) then
          inl (diag "elf-slice"
                 ("ET_REL slice for '" ++ esym_name sym ++ "' exceeds shdr#" ++
                  diag_nat_dec (esh_idx sh) ++ " (st_value=" ++ diag_N_hex (esym_value sym) ++
                  ", st_size=" ++ diag_N_hex (esym_size sym) ++
                  ", sh_size=" ++ diag_N_hex (esh_size sh) ++ ")"))
        else
          let foff := (esh_offset sh + esym_value sym)%N in
          let rlo := esym_value sym in
          let rhi := (rlo + esym_size sym)%N in
          inr (foff, rlo, rhi)
    | EK_Exec | EK_Dyn =>
        if negb (N.leb (esh_addr sh) (esym_value sym)) then
          inl (diag "elf-slice"
                 ("linked slice for '" ++ esym_name sym ++ "' vaddr=" ++
                  diag_N_hex (esym_value sym) ++ " precedes sh_addr=" ++
                  diag_N_hex (esh_addr sh) ++ " in shdr#" ++ diag_nat_dec (esh_idx sh)))
        else
          let sec_rel := (esym_value sym - esh_addr sh)%N in
          if negb (N.leb (sec_rel + esym_size sym) (esh_size sh)) then
            inl (diag "elf-slice"
                   ("linked slice for '" ++ esym_name sym ++ "' exceeds shdr#" ++
                    diag_nat_dec (esh_idx sh) ++ " (sec_rel=" ++ diag_N_hex sec_rel ++
                    ", st_size=" ++ diag_N_hex (esym_size sym) ++
                    ", sh_size=" ++ diag_N_hex (esh_size sh) ++ ")"))
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
      if negb (elf_arch_eqb (eh_arch hdr) want_arch) then
        inl (diag "elf-hdr"
               ("architecture mismatch: expected " ++ elf_arch_name want_arch ++
                ", binary is " ++ elf_arch_name (eh_arch hdr)))
      else if negb (elf_kind_eqb (eh_kind hdr) want_kind) then
        inl (diag "elf-hdr"
               ("e_type mismatch: expected " ++ elf_kind_name want_kind ++
                ", binary is " ++ elf_kind_name (eh_kind hdr)))
      else
        match parse_elf64_shdrs raw hdr with
        | inl err => inl err
        | inr shdrs =>
            match parse_elf64_symtab raw shdrs with
            | inl err => inl err
            | inr syms =>
                match find_unique_diag
                        (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) fn_name)
                        syms
                with
                | UM_Missing =>
                    inl (diag "elf-sym" ("missing ELF64 STT_FUNC symbol '" ++ fn_name ++ "'"))
                | UM_Duplicate _ _ =>
                    inl (diag "elf-sym" ("duplicate ELF64 STT_FUNC symbol '" ++ fn_name ++ "'"))
                | UM_Unique sym =>
                    match nth_error shdrs (esym_shndx sym) with
                    | None =>
                        inl (diag "elf-sym"
                               ("symbol '" ++ fn_name ++ "' st_shndx=" ++
                                diag_nat_dec (esym_shndx sym) ++ " out of bounds"))
                    | Some sh =>
                        match compute_func_slice_offsets (eh_kind hdr) sh sym with
                        | inl err => inl err
                        | inr (foff, rlo, rhi) =>
                            match check_exec_relocations_diag raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi with
                            | inl err => inl err
                            | inr tt =>
                                let raw_len := elf_length_tr raw in
                                match n_to_nat_checked raw_len foff,
                                      n_to_nat_checked raw_len (esym_size sym)
                                with
                                | Some foff_nat, Some fsz_nat =>
                                    match slice_bytes raw foff_nat fsz_nat with
                                    | None =>
                                        inl (diag "elf-slice"
                                               ("symbol '" ++ fn_name ++ "' byte slice out of bounds (off=" ++
                                                diag_nat_dec foff_nat ++ ", size=" ++ diag_nat_dec fsz_nat ++
                                                ", file_len=" ++ diag_nat_dec raw_len ++ ")"))
                                    | Some bytes =>
                                        inr (mk_elf_func_slice
                                               (eh_arch hdr) (eh_kind hdr) (eh_rvc hdr)
                                               (esym_shndx sym) foff_nat fsz_nat bytes rlo rhi)
                                    end
                                | _, _ =>
                                    inl (diag "elf-slice"
                                           ("symbol '" ++ fn_name ++ "' offset=" ++ diag_N_hex foff ++
                                            " or size=" ++ diag_N_hex (esym_size sym) ++ " exceeds file length"))
                                end
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
  destruct (find_unique_diag (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) fn_name) syms)
    as [| sym | ? ?] eqn:Ef; [discriminate H | | discriminate H].
  apply find_unique_diag_eq_tr in Ef.
  destruct (nth_error shdrs (esym_shndx sym)) as [sh |] eqn:Eth; [| discriminate H].
  destruct (compute_func_slice_offsets (eh_kind hdr) sh sym) as [err | [[foff rlo] rhi]] eqn:Eoff;
    [discriminate H |].
  destruct (check_exec_relocations_diag raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi)
    as [err | []] eqn:Erel; [discriminate H |].
  apply check_exec_relocations_diag_sound in Erel.
  cbn zeta in H.
  destruct (n_to_nat_checked (elf_length_tr raw) foff) as [foff_nat |] eqn:Efn; [| discriminate H].
  destruct (n_to_nat_checked (elf_length_tr raw) (esym_size sym)) as [fsz_nat |] eqn:Esn;
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
  unfold n_to_nat_checked in Esn; rewrite elf_length_tr_eq in Esn.
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
  (syms : list elf64_sym) (syms_len : N) (rela_shndx rela_info target_shndx entry_idx : nat)
  (fn_lo fn_hi : N) (allowed_callees : list string) (r : elf64_rela)
  : string + option (N * string) :=
  let forbidden_riscv :=
    elf_arch_eqb arch EA_Riscv64 &&
    (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN)
  in
  if forbidden_riscv then
    inl (diag "elf-reloc"
           ("forbidden relaxation/alignment relocation " ++
            elf_rela_type_name arch (er_type r) ++ "(" ++ diag_N_dec (er_type r) ++ ")" ++
            " at shdr#" ++ diag_nat_dec rela_shndx ++
            " entry#" ++ diag_nat_dec entry_idx ++
            " offset=" ++ diag_N_hex (er_offset r)))
  else if negb (Nat.eqb rela_info target_shndx) then inr None
  else if N.ltb (er_offset r) fn_lo || N.leb fn_hi (er_offset r) then inr None
  else
    let loc_str (_ : unit) : string :=
      ("at shdr#" ++ diag_nat_dec rela_shndx ++
       " entry#" ++ diag_nat_dec entry_idx ++
       " offset=" ++ diag_N_hex (er_offset r) ++
       " type=" ++ elf_rela_type_name arch (er_type r) ++ "(" ++ diag_N_dec (er_type r) ++ ")")%string
    in
    match kind with
    | EK_Exec | EK_Dyn =>
        inl (diag "elf-reloc"
               ("relocation inside slice forbidden in linked ELF (" ++
                elf_kind_name kind ++ ") " ++ loc_str tt))
    | EK_Rel =>
        if negb (rela_type_is_direct_call arch (er_type r)) then
          inl (diag "elf-reloc" ("unsupported relocation type inside slice " ++ loc_str tt))
        else if negb (N.eqb (er_addend r) 0%N) then
          inl (diag "elf-reloc"
                 ("non-zero relocation addend=" ++ diag_N_hex (er_addend r) ++ " " ++ loc_str tt))
        else if negb (N.leb (er_sym r) syms_len) then
          inl (diag "elf-reloc"
                 ("relocation symbol index=" ++ diag_N_dec (er_sym r) ++ " out of range " ++ loc_str tt))
        else
          match nth_error syms (N.to_nat (er_sym r)) with
          | None =>
              inl (diag "elf-reloc"
                     ("relocation symbol index=" ++ diag_N_dec (er_sym r) ++ " out of bounds " ++ loc_str tt))
          | Some csym =>
              if negb (N.eqb (esym_type csym) STT_FUNC) then
                inl (diag "elf-reloc"
                       ("call relocation does not target STT_FUNC (sym='" ++
                        esym_name csym ++ "', st_type=" ++ diag_N_dec (esym_type csym) ++ ") " ++ loc_str tt))
              else if negb (elf_str_in_list (esym_name csym) allowed_callees) then
                inl (diag "elf-reloc"
                       ("unapproved callee relocation target '" ++ esym_name csym ++ "' " ++ loc_str tt))
              else
                match find_unique_diag
                        (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) (esym_name csym))
                        syms
                with
                | UM_Missing =>
                    inl (diag "elf-reloc"
                           ("missing callee STT_FUNC symbol '" ++ esym_name csym ++ "' " ++ loc_str tt))
                | UM_Duplicate _ _ =>
                    inl (diag "elf-reloc"
                           ("duplicate callee STT_FUNC symbol '" ++ esym_name csym ++ "' " ++ loc_str tt))
                | UM_Unique _ =>
                    match nth_error shdrs (esym_shndx csym) with
                    | None =>
                        inl (diag "elf-reloc"
                               ("callee '" ++ esym_name csym ++ "' st_shndx=" ++
                                diag_nat_dec (esym_shndx csym) ++ " out of bounds " ++ loc_str tt))
                    | Some csh =>
                        match compute_func_slice_offsets EK_Rel csh csym with
                        | inl err => inl err
                        | inr _ => inr (Some ((er_offset r - fn_lo)%N, esym_name csym))
                        end
                    end
                end
          end
    end.

Fixpoint collect_call_rela_entries_acc
  (arch : elf_arch) (kind : elf_kind) (shdrs : list elf64_shdr)
  (syms : list elf64_sym) (syms_len : N) (rela_shndx rela_info target_shndx entry_idx : nat)
  (fn_lo fn_hi : N) (allowed_callees : list string)
  (acc_rev : list (N * string)) (rs : list elf64_rela)
  {struct rs} : string + list (N * string) :=
  match rs with
  | [] => inr (elf_rev_tr acc_rev)
  | r :: rest =>
      match check_and_collect_call_rela_entry arch kind shdrs syms syms_len
              rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees r with
      | inl err => inl err
      | inr None =>
          collect_call_rela_entries_acc arch kind shdrs syms syms_len
            rela_shndx rela_info target_shndx (S entry_idx) fn_lo fn_hi allowed_callees acc_rev rest
      | inr (Some p) =>
          collect_call_rela_entries_acc arch kind shdrs syms syms_len
            rela_shndx rela_info target_shndx (S entry_idx) fn_lo fn_hi allowed_callees (p :: acc_rev) rest
      end
  end.

Definition collect_call_rela_entries
  (arch : elf_arch) (kind : elf_kind) (shdrs : list elf64_shdr)
  (syms : list elf64_sym) (syms_len : N) (rela_shndx rela_info target_shndx : nat)
  (fn_lo fn_hi : N) (allowed_callees : list string) (rs : list elf64_rela)
  : string + list (N * string) :=
  collect_call_rela_entries_acc arch kind shdrs syms syms_len
    rela_shndx rela_info target_shndx 0 fn_lo fn_hi allowed_callees [] rs.

Definition collect_one_rela_section
  (raw : list N) (arch : elf_arch) (kind : elf_kind) (shdrs : list elf64_shdr)
  (syms : list elf64_sym) (syms_len : N) (target_shndx : nat) (fn_lo fn_hi : N)
  (allowed_callees : list string) (sh : elf64_shdr) : string + list (N * string) :=
  if negb (N.eqb (esh_type sh) SHT_RELA) then inr []
  else
    match nth_error shdrs (esh_info sh) with
    | None =>
        inl (diag "elf-reloc"
               ("SHT_RELA shdr#" ++ diag_nat_dec (esh_idx sh) ++
                " sh_info=" ++ diag_nat_dec (esh_info sh) ++ " out of bounds"))
    | Some tgt_sh =>
        if negb (bit_is_set (esh_flags tgt_sh) 2%N) then inr []
        else if negb (N.eqb (esh_entsize sh) 24%N && N.eqb (N.modulo (esh_size sh) 24%N) 0%N) then
          inl (diag "elf-reloc"
                 ("SHT_RELA shdr#" ++ diag_nat_dec (esh_idx sh) ++
                  " invalid entsize=" ++ diag_N_dec (esh_entsize sh) ++
                  " or unaligned size=" ++ diag_N_dec (esh_size sh)))
        else
          let raw_len := elf_length_tr raw in
          match n_to_nat_checked raw_len (esh_offset sh),
                n_to_nat_checked raw_len (esh_size sh)
          with
          | Some r_off, Some r_sz =>
              let count := Nat.div r_sz 24 in
              if negb (Nat.leb (r_off + count * 24) raw_len) then
                inl (diag "elf-reloc"
                       ("SHT_RELA shdr#" ++ diag_nat_dec (esh_idx sh) ++
                        " payload out of bounds (off=" ++ diag_nat_dec r_off ++
                        ", size=" ++ diag_nat_dec r_sz ++ ", file_len=" ++ diag_nat_dec raw_len ++ ")"))
              else
                match parse_relas_cursor count (skipn r_off raw) [] with
                | None =>
                    inl (diag "elf-reloc" ("truncated SHT_RELA entries in shdr#" ++ diag_nat_dec (esh_idx sh)))
                | Some rs =>
                    collect_call_rela_entries arch kind shdrs syms syms_len
                      (esh_idx sh) (esh_info sh) target_shndx fn_lo fn_hi allowed_callees rs
                end
          | _, _ =>
              inl (diag "elf-reloc"
                     ("SHT_RELA shdr#" ++ diag_nat_dec (esh_idx sh) ++ " offset or size exceeds bounds"))
          end
    end.

Fixpoint collect_all_call_relocs_acc
  (raw : list N) (arch : elf_arch) (kind : elf_kind) (all_shdrs : list elf64_shdr)
  (syms : list elf64_sym) (syms_len : N) (target_shndx : nat) (fn_lo fn_hi : N)
  (allowed_callees : list string) (acc_rev : list (N * string)) (rem_shdrs : list elf64_shdr)
  {struct rem_shdrs} : string + list (N * string) :=
  match rem_shdrs with
  | [] => inr (elf_rev_tr acc_rev)
  | sh :: rest =>
      match collect_one_rela_section raw arch kind all_shdrs syms syms_len
              target_shndx fn_lo fn_hi allowed_callees sh with
      | inl err => inl err
      | inr xs =>
          collect_all_call_relocs_acc raw arch kind all_shdrs syms syms_len target_shndx fn_lo fn_hi allowed_callees
            (List.rev_append xs acc_rev) rest
      end
  end.

Definition collect_all_call_relocs
  (raw : list N) (arch : elf_arch) (kind : elf_kind) (all_shdrs rem_shdrs : list elf64_shdr)
  (syms : list elf64_sym) (syms_len : N) (target_shndx : nat) (fn_lo fn_hi : N)
  (allowed_callees : list string) : string + list (N * string) :=
  collect_all_call_relocs_acc raw arch kind all_shdrs syms syms_len
    target_shndx fn_lo fn_hi allowed_callees [] rem_shdrs.

Fixpoint collect_exec_callee_addrs_acc
  (kind : elf_kind) (shdrs : list elf64_shdr) (syms : list elf64_sym)
  (acc_rev : list (string * N)) (allowed_callees : list string)
  {struct allowed_callees} : string + list (string * N) :=
  match allowed_callees with
  | [] => inr (elf_rev_tr acc_rev)
  | cn :: rest =>
      match find_unique_diag
              (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) cn)
              syms
      with
      | UM_Missing =>
          inl (diag "elf-sym" ("missing linked callee STT_FUNC symbol '" ++ cn ++ "'"))
      | UM_Duplicate _ _ =>
          inl (diag "elf-sym" ("duplicate linked callee STT_FUNC symbol '" ++ cn ++ "'"))
      | UM_Unique csym =>
          match nth_error shdrs (esym_shndx csym) with
          | None =>
              inl (diag "elf-sym"
                     ("linked callee '" ++ cn ++ "' st_shndx=" ++
                      diag_nat_dec (esym_shndx csym) ++ " out of bounds"))
          | Some csh =>
              match compute_func_slice_offsets kind csh csym with
              | inl err => inl err
              | inr _ =>
                  collect_exec_callee_addrs_acc kind shdrs syms ((cn, esym_value csym) :: acc_rev) rest
              end
          end
      end
  end.

Definition collect_exec_callee_addrs
  (kind : elf_kind) (shdrs : list elf64_shdr) (syms : list elf64_sym)
  (allowed_callees : list string) : string + list (string * N) :=
  collect_exec_callee_addrs_acc kind shdrs syms [] allowed_callees.

(** Extract a caller function slice and verified direct-call relocation / symbol metadata.
    [allowed_callees] contains bare ELF symbol names (without leading '@'). *)
Definition elf64_extract_func_with_calls
  (raw : list N) (want_arch : elf_arch) (want_kind : elf_kind)
  (fn_name : string) (allowed_callees : list string)
  : string + (elf_func_slice * elf_call_info) :=
  match parse_elf64_header raw with
  | inl err => inl err
  | inr hdr =>
      if negb (elf_arch_eqb (eh_arch hdr) want_arch) then
        inl (diag "elf-hdr"
               ("architecture mismatch: expected " ++ elf_arch_name want_arch ++
                ", binary is " ++ elf_arch_name (eh_arch hdr)))
      else if negb (elf_kind_eqb (eh_kind hdr) want_kind) then
        inl (diag "elf-hdr"
               ("e_type mismatch: expected " ++ elf_kind_name want_kind ++
                ", binary is " ++ elf_kind_name (eh_kind hdr)))
      else
        match parse_elf64_shdrs raw hdr with
        | inl err => inl err
        | inr shdrs =>
            match parse_elf64_symtab raw shdrs with
            | inl err => inl err
            | inr syms =>
                match find_unique_diag
                        (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) fn_name)
                        syms
                with
                | UM_Missing =>
                    inl (diag "elf-sym" ("missing ELF64 STT_FUNC symbol '" ++ fn_name ++ "'"))
                | UM_Duplicate _ _ =>
                    inl (diag "elf-sym" ("duplicate ELF64 STT_FUNC symbol '" ++ fn_name ++ "'"))
                | UM_Unique sym =>
                    match nth_error shdrs (esym_shndx sym) with
                    | None =>
                        inl (diag "elf-sym"
                               ("symbol '" ++ fn_name ++ "' st_shndx=" ++
                                diag_nat_dec (esym_shndx sym) ++ " out of bounds"))
                    | Some sh =>
                        match compute_func_slice_offsets (eh_kind hdr) sh sym with
                        | inl err => inl err
                        | inr (foff, rlo, rhi) =>
                            let raw_len := elf_length_tr raw in
                            match n_to_nat_checked raw_len foff,
                                  n_to_nat_checked raw_len (esym_size sym)
                            with
                            | Some foff_nat, Some fsz_nat =>
                                match slice_bytes raw foff_nat fsz_nat with
                                | None =>
                                    inl (diag "elf-slice"
                                           ("symbol '" ++ fn_name ++ "' byte slice out of bounds (off=" ++
                                            diag_nat_dec foff_nat ++ ", size=" ++ diag_nat_dec fsz_nat ++
                                            ", file_len=" ++ diag_nat_dec raw_len ++ ")"))
                                | Some bytes =>
                                    let sl := mk_elf_func_slice
                                                (eh_arch hdr) (eh_kind hdr) (eh_rvc hdr)
                                                (esym_shndx sym) foff_nat fsz_nat bytes rlo rhi in
                                    match eh_kind hdr with
                                    | EK_Rel =>
                                        let syms_len := N.of_nat (elf_length_tr syms) in
                                        match collect_all_call_relocs raw (eh_arch hdr) EK_Rel shdrs shdrs
                                                syms syms_len (esym_shndx sym) rlo rhi allowed_callees with
                                        | inl err => inl err
                                        | inr rels =>
                                            if negb (elf_no_dup_N (elf_map_tr fst rels)) then
                                              inl (diag "elf-reloc"
                                                     ("duplicate call relocation offset inside slice of '" ++
                                                      fn_name ++ "'"))
                                            else
                                              inr (sl, mk_elf_call_info rels [])
                                        end
                                    | EK_Exec | EK_Dyn =>
                                        match check_exec_relocations_diag raw (eh_arch hdr) shdrs
                                                (esym_shndx sym) rlo rhi with
                                        | inl err => inl err
                                        | inr tt =>
                                            match collect_exec_callee_addrs (eh_kind hdr) shdrs syms
                                                    allowed_callees with
                                            | inl err => inl err
                                            | inr addrs => inr (sl, mk_elf_call_info [] addrs)
                                            end
                                        end
                                    end
                                end
                            | _, _ =>
                                inl (diag "elf-slice"
                                       ("symbol '" ++ fn_name ++ "' offset=" ++ diag_N_hex foff ++
                                        " or size=" ++ diag_N_hex (esym_size sym) ++ " exceeds file length"))
                            end
                        end
                    end
                end
            end
        end
  end.

Lemma check_and_collect_call_rela_entry_sound :
  forall arch kind shdrs syms syms_len rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees r opt_p,
    check_and_collect_call_rela_entry arch kind shdrs syms syms_len
      rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees r = inr opt_p ->
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
  intros arch kind shdrs syms syms_len rela_shndx rela_info target_shndx
    entry_idx fn_lo fn_hi allowed_callees r opt_p H Hi Hlohi rel_off cname Hop.
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
  destruct (N.leb (er_sym r) syms_len); cbn [negb] in H; [| discriminate H].
  destruct (nth_error syms (N.to_nat (er_sym r))) as [csym |] eqn:Esym; [| discriminate H].
  destruct (N.eqb (esym_type csym) STT_FUNC) eqn:Eft; cbn [negb] in H; [| discriminate H].
  apply N.eqb_eq in Eft.
  destruct (elf_str_in_list (esym_name csym) allowed_callees) eqn:Eal; cbn [negb] in H; [| discriminate H].
  unfold elf_str_in_list in Eal; apply existsb_exists in Eal as [cn [Hcn Hceq]].
  apply String.eqb_eq in Hceq; subst cn.
  destruct (find_unique_diag (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) (esym_name csym)) syms)
    as [| usym | ? ?] eqn:Eu; [discriminate H | | discriminate H].
  apply find_unique_diag_eq_tr in Eu.
  destruct (nth_error shdrs (esym_shndx csym)) as [csh |] eqn:Ecsh; [| discriminate H].
  destruct (compute_func_slice_offsets EK_Rel csh csym) as [| r_] eqn:Eoff; [discriminate H |].
  inversion H as [Hopt]; clear H.
  rewrite <- Hopt in Hop; inversion Hop; subst rel_off cname; clear Hopt Hop.
  assert (Husym : usym = csym).
  { unfold find_unique_tr in Eu.
    destruct (find_unique_tr_spec _ _ _ Eu) as (_ & _ & Huniq).
    symmetry; apply Huniq; [exact (nth_error_In _ _ Esym) | rewrite Eft, N.eqb_refl, String.eqb_refl; reflexivity]. }
  subst usym.
  repeat split; try lia; try assumption.
  exists csym, csh; repeat split; try assumption; eexists; exact Eoff.
Qed.

Lemma check_and_collect_call_rela_entry_disallows_relax :
  forall arch kind shdrs syms syms_len rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees r opt_p,
    check_and_collect_call_rela_entry arch kind shdrs syms syms_len
      rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees r = inr opt_p ->
    (elf_arch_eqb arch EA_Riscv64 && (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN)) = false.
Proof.
  intros arch kind shdrs syms syms_len rela_shndx rela_info target_shndx
    entry_idx fn_lo fn_hi allowed_callees r opt_p H.
  unfold check_and_collect_call_rela_entry in H.
  destruct (elf_arch_eqb arch EA_Riscv64 && (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN));
    [discriminate H | reflexivity].
Qed.

Lemma collect_call_rela_entries_acc_to_exec_check :
  forall arch kind shdrs syms syms_len rela_shndx rela_info target_shndx
    entry_idx fn_lo fn_hi allowed_callees acc_rev rs rels,
    collect_call_rela_entries_acc arch kind shdrs syms syms_len
      rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees acc_rev rs = inr rels ->
    (kind = EK_Exec \/ kind = EK_Dyn) ->
    rels = elf_rev_tr acc_rev /\
    forallb (rela_entry_allowed arch rela_info target_shndx fn_lo fn_hi) rs = true.
Proof.
  intros arch kind shdrs syms syms_len rela_shndx rela_info target_shndx
    entry_idx fn_lo fn_hi allowed_callees acc_rev rs.
  revert entry_idx acc_rev; induction rs as [| r rest IH]; intros entry_idx acc_rev rels H Hkind;
    cbn [collect_call_rela_entries_acc] in H.
  - inversion H; subst; split; reflexivity.
  - destruct (check_and_collect_call_rela_entry arch kind shdrs syms syms_len
                rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees r)
      as [| opt_p] eqn:He; [discriminate H |].
    assert (Hnot_rel : rela_entry_allowed arch rela_info target_shndx fn_lo fn_hi r = true /\ opt_p = None).
    { unfold check_and_collect_call_rela_entry in He; unfold rela_entry_allowed.
      destruct (elf_arch_eqb arch EA_Riscv64 && (N.eqb (er_type r) R_RISCV_RELAX || N.eqb (er_type r) R_RISCV_ALIGN));
        [discriminate He |].
      destruct (Nat.eqb rela_info target_shndx); cbn [negb] in He.
      - destruct (N.ltb (er_offset r) fn_lo || N.leb fn_hi (er_offset r)); [inversion He; split; reflexivity |].
        destruct Hkind as [-> | ->]; discriminate He.
      - inversion He; split; reflexivity. }
    destruct Hnot_rel as [Hr_ok ->].
    destruct (IH (S entry_idx) acc_rev rels H Hkind) as [Hrels Hfb].
    split; [exact Hrels | cbn [forallb]; rewrite Hr_ok, Hfb; reflexivity].
Qed.

Lemma collect_call_rela_entries_to_exec_check :
  forall arch kind shdrs syms syms_len rela_shndx rela_info target_shndx fn_lo fn_hi allowed_callees rs rels,
    collect_call_rela_entries arch kind shdrs syms syms_len
      rela_shndx rela_info target_shndx fn_lo fn_hi allowed_callees rs = inr rels ->
    (kind = EK_Exec \/ kind = EK_Dyn) ->
    rels = [] /\
    forallb (rela_entry_allowed arch rela_info target_shndx fn_lo fn_hi) rs = true.
Proof.
  intros arch kind shdrs syms syms_len rela_shndx rela_info target_shndx fn_lo fn_hi allowed_callees rs rels H Hkind.
  exact (collect_call_rela_entries_acc_to_exec_check arch kind shdrs syms syms_len
           rela_shndx rela_info target_shndx 0 fn_lo fn_hi allowed_callees [] rs rels H Hkind).
Qed.

Lemma collect_call_rela_entries_acc_rel_sound :
  forall arch shdrs syms syms_len rela_shndx rela_info target_shndx
    entry_idx fn_lo fn_hi allowed_callees acc_rev rs rels,
    (fn_lo <= fn_hi)%N ->
    collect_call_rela_entries_acc arch EK_Rel shdrs syms syms_len
      rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees acc_rev rs = inr rels ->
    forall rel_off cname,
      In (rel_off, cname) rels ->
      In (rel_off, cname) acc_rev \/
      ((rel_off < fn_hi - fn_lo)%N /\
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
         exists r_, compute_func_slice_offsets EK_Rel csh csym = inr r_).
Proof.
  intros arch shdrs syms syms_len rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees acc_rev rs.
  revert entry_idx acc_rev; induction rs as [| r rest IH]; intros entry_idx acc_rev rels Hlohi H rel_off cname Hin;
    cbn [collect_call_rela_entries_acc] in H.
  - inversion H; subst rels; clear H.
    rewrite elf_rev_tr_eq, <- in_rev in Hin; left; exact Hin.
  - destruct (check_and_collect_call_rela_entry arch EK_Rel shdrs syms syms_len
                rela_shndx rela_info target_shndx entry_idx fn_lo fn_hi allowed_callees r)
      as [| [[ro cn] |]] eqn:He; [discriminate H | |].
    + destruct (IH (S entry_idx) ((ro, cn) :: acc_rev) rels Hlohi H rel_off cname Hin)
        as [[Heq | Hacc] | (Hlt & Hcn & [r0 [csym [csh [Hin0 Hr_ok]]]])].
      * inversion Heq; subst ro cn; clear Heq; right.
        assert (Hinfo : rela_info = target_shndx).
        { unfold check_and_collect_call_rela_entry in He.
          destruct (elf_arch_eqb _ _ && _); [discriminate He |].
          destruct (Nat.eqb rela_info target_shndx) eqn:En; cbn [negb] in He;
            [apply Nat.eqb_eq in En; exact En | discriminate He]. }
        destruct (check_and_collect_call_rela_entry_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ He Hinfo Hlohi _ _ eq_refl)
          as (_ & Hlt & Hoff & Hty & Hadd & Hcn & [csym [csh Hrest]]).
        split; [exact Hlt | split; [exact Hcn |]].
        exists r, csym, csh; repeat split;
          try (left; reflexivity); try assumption; tauto.
      * left; exact Hacc.
      * right; split; [exact Hlt | split; [exact Hcn |]].
        exists r0, csym, csh; split; [right; exact Hin0 | exact Hr_ok].
    + destruct (IH (S entry_idx) acc_rev rels Hlohi H rel_off cname Hin)
        as [Hacc | (Hlt & Hcn & [r0 [csym [csh [Hin0 Hr_ok]]]])].
      * left; exact Hacc.
      * right; split; [exact Hlt | split; [exact Hcn |]].
        exists r0, csym, csh; split; [right; exact Hin0 | exact Hr_ok].
Qed.

Lemma collect_call_rela_entries_rel_sound :
  forall arch shdrs syms syms_len rela_shndx rela_info target_shndx fn_lo fn_hi allowed_callees rs rels,
    (fn_lo <= fn_hi)%N ->
    collect_call_rela_entries arch EK_Rel shdrs syms syms_len
      rela_shndx rela_info target_shndx fn_lo fn_hi allowed_callees rs = inr rels ->
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
  intros arch shdrs syms syms_len rela_shndx rela_info target_shndx
    fn_lo fn_hi allowed_callees rs rels Hlohi H rel_off cname Hin.
  destruct (collect_call_rela_entries_acc_rel_sound arch shdrs syms syms_len
              rela_shndx rela_info target_shndx 0 fn_lo fn_hi allowed_callees [] rs rels
              Hlohi H rel_off cname Hin)
    as [[] | Hres]; exact Hres.
Qed.

Lemma collect_all_call_relocs_acc_rel_sound :
  forall raw arch all_shdrs syms syms_len target_shndx fn_lo fn_hi allowed_callees acc_rev rem_shdrs rels,
    (fn_lo <= fn_hi)%N ->
    collect_all_call_relocs_acc raw arch EK_Rel all_shdrs syms syms_len
      target_shndx fn_lo fn_hi allowed_callees acc_rev rem_shdrs = inr rels ->
    forall rel_off cname,
      In (rel_off, cname) rels ->
      In (rel_off, cname) acc_rev \/
      ((rel_off < fn_hi - fn_lo)%N /\
       In cname allowed_callees /\
       exists csym csh r_,
         find_unique_func_sym syms cname = Some csym /\
         esym_name csym = cname /\
         esym_type csym = STT_FUNC /\
         nth_error all_shdrs (esym_shndx csym) = Some csh /\
         compute_func_slice_offsets EK_Rel csh csym = inr r_).
Proof.
  intros raw arch all_shdrs syms syms_len target_shndx fn_lo fn_hi allowed_callees acc_rev rem_shdrs.
  revert acc_rev; induction rem_shdrs as [| sh rest IH]; intros acc_rev rels Hlohi H rel_off cname Hin;
    cbn [collect_all_call_relocs_acc] in H.
  - inversion H; subst rels; clear H.
    rewrite elf_rev_tr_eq, <- in_rev in Hin; left; exact Hin.
  - destruct (collect_one_rela_section raw arch EK_Rel all_shdrs syms syms_len
                target_shndx fn_lo fn_hi allowed_callees sh)
      as [| xs] eqn:Hx; [discriminate H |].
    destruct (IH (List.rev_append xs acc_rev) rels Hlohi H rel_off cname Hin) as [Hrev | Hres];
      [| right; exact Hres].
    rewrite rev_append_rev in Hrev; apply in_app_iff in Hrev as [Hx_rev | Hacc].
    + rewrite <- in_rev in Hx_rev; right.
      unfold collect_one_rela_section in Hx; cbn zeta in Hx.
      destruct (N.eqb (esh_type sh) SHT_RELA); cbn [negb] in Hx; [| inversion Hx; subst; contradiction Hx_rev].
      destruct (nth_error all_shdrs (esh_info sh)); [| discriminate Hx].
      destruct (bit_is_set (esh_flags e) 2%N); cbn [negb] in Hx; [| inversion Hx; subst; contradiction Hx_rev].
      destruct (N.eqb (esh_entsize sh) 24%N && N.eqb (N.modulo (esh_size sh) 24%N) 0%N);
        cbn [negb] in Hx; [| discriminate Hx].
      destruct (n_to_nat_checked (elf_length_tr raw) (esh_offset sh)); [| discriminate Hx].
      destruct (n_to_nat_checked (elf_length_tr raw) (esh_size sh)); [| discriminate Hx].
      destruct (Nat.leb (n + Nat.div n0 24 * 24) (elf_length_tr raw)); cbn [negb] in Hx; [| discriminate Hx].
      destruct (parse_relas_cursor (Nat.div n0 24) (skipn n raw) []) as [rs |]; [| discriminate Hx].
      destruct (collect_call_rela_entries_rel_sound _ _ _ _ _ _ _ _ _ _ _ _ Hlohi Hx _ _ Hx_rev)
        as (Hlt & Hcn & [r [csym [csh (_ & _ & _ & _ & _ & _ & Hnm & Hty & Huniq & Hcsh & [r_ Hoff])]]]).
      split; [exact Hlt | split; [exact Hcn |]].
      exists csym, csh, r_; repeat split; assumption.
    + left; exact Hacc.
Qed.

Lemma collect_all_call_relocs_rel_sound :
  forall raw arch all_shdrs rem_shdrs syms syms_len target_shndx fn_lo fn_hi allowed_callees rels,
    (fn_lo <= fn_hi)%N ->
    collect_all_call_relocs raw arch EK_Rel all_shdrs rem_shdrs syms syms_len
      target_shndx fn_lo fn_hi allowed_callees = inr rels ->
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
  intros raw arch all_shdrs rem_shdrs syms syms_len target_shndx
    fn_lo fn_hi allowed_callees rels Hlohi H rel_off cname Hin.
  destruct (collect_all_call_relocs_acc_rel_sound raw arch all_shdrs syms syms_len
              target_shndx fn_lo fn_hi allowed_callees [] rem_shdrs rels Hlohi H rel_off cname Hin)
    as [[] | Hres]; exact Hres.
Qed.

Lemma collect_exec_callee_addrs_acc_mono :
  forall kind shdrs syms acc_rev allowed_callees addrs,
    collect_exec_callee_addrs_acc kind shdrs syms acc_rev allowed_callees = inr addrs ->
    forall p, In p acc_rev -> In p addrs.
Proof.
  intros kind shdrs syms acc_rev allowed_callees; revert acc_rev;
    induction allowed_callees as [| cn0 rest IH]; intros acc_rev addrs H p Hp;
    cbn [collect_exec_callee_addrs_acc] in H.
  - inversion H; subst; rewrite elf_rev_tr_eq, <- in_rev; exact Hp.
  - destruct (find_unique_diag (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) cn0) syms);
      [discriminate H | | discriminate H].
    destruct (nth_error shdrs _); [| discriminate H].
    destruct (compute_func_slice_offsets _ _ _); [discriminate H |].
    apply (IH _ _ H); right; exact Hp.
Qed.

Lemma collect_exec_callee_addrs_acc_sound :
  forall kind shdrs syms acc_rev allowed_callees addrs,
    collect_exec_callee_addrs_acc kind shdrs syms acc_rev allowed_callees = inr addrs ->
    forall cn,
      In cn allowed_callees ->
      exists csym csh r_,
        In (cn, esym_value csym) addrs /\
        find_unique_func_sym syms cn = Some csym /\
        nth_error shdrs (esym_shndx csym) = Some csh /\
        compute_func_slice_offsets kind csh csym = inr r_.
Proof.
  intros kind shdrs syms acc_rev allowed_callees; revert acc_rev;
    induction allowed_callees as [| cn0 rest IH]; intros acc_rev addrs H cn Hin;
    cbn [collect_exec_callee_addrs_acc] in H; [contradiction Hin |].
  destruct (find_unique_diag (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) cn0) syms)
    as [| csym | ? ?] eqn:Ef; [discriminate H | | discriminate H].
  apply find_unique_diag_eq_tr in Ef.
  destruct (nth_error shdrs (esym_shndx csym)) as [csh |] eqn:Ecsh; [| discriminate H].
  destruct (compute_func_slice_offsets kind csh csym) as [| r_] eqn:Eoff; [discriminate H |].
  destruct Hin as [<- | Hin].
  - exists csym, csh, r_; repeat split; [| exact Ef | exact Ecsh | exact Eoff].
    exact (collect_exec_callee_addrs_acc_mono _ _ _ _ _ _ H _ (or_introl eq_refl)).
  - exact (IH _ _ H _ Hin).
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
  intros kind shdrs syms allowed_callees addrs H.
  exact (collect_exec_callee_addrs_acc_sound kind shdrs syms [] allowed_callees addrs H).
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
  destruct (find_unique_diag (fun s => N.eqb (esym_type s) STT_FUNC && String.eqb (esym_name s) fn_name) syms)
    as [| sym | ? ?] eqn:Ef; [discriminate H | | discriminate H].
  apply find_unique_diag_eq_tr in Ef.
  destruct (nth_error shdrs (esym_shndx sym)) as [sh |] eqn:Eth; [| discriminate H].
  destruct (compute_func_slice_offsets (eh_kind hdr) sh sym) as [err | [[foff rlo] rhi]] eqn:Eoff;
    [discriminate H |].
  cbn zeta in H.
  destruct (n_to_nat_checked (elf_length_tr raw) foff) as [foff_nat |] eqn:Efn; [| discriminate H].
  destruct (n_to_nat_checked (elf_length_tr raw) (esym_size sym)) as [fsz_nat |] eqn:Esn;
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
  unfold n_to_nat_checked in Esn; rewrite elf_length_tr_eq in Esn.
  destruct (N.leb (esym_size sym) (N.of_nat (List.length raw))); [| discriminate Esn].
  inversion Esn as [Hfsz]; clear Esn.
  assert (Hpos_sz : 0 < N.to_nat (esym_size sym)) by lia.
  destruct (eh_kind hdr) eqn:Ehk; cbn zeta in H.
  - destruct (collect_all_call_relocs raw (eh_arch hdr) EK_Rel shdrs shdrs syms
                (N.of_nat (elf_length_tr syms)) (esym_shndx sym) rlo rhi allowed_callees)
      as [| rels] eqn:Erels; [discriminate H |].
    destruct (elf_no_dup_N (elf_map_tr fst rels)) eqn:End; cbn [negb] in H; [| discriminate H].
    rewrite elf_map_tr_eq in End.
    inversion H; subst sl ci; clear H.
    cbn [efs_arch efs_kind efs_shndx efs_file_off efs_size efs_bytes
         efs_range_lo efs_range_hi eci_relocs eci_sym_addrs].
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
      destruct (collect_all_call_relocs_rel_sound _ _ _ _ _ _ _ _ _ _ _ Hlohi Erels _ _ Hin) as (Hlt & Hcn & _);
        exact (conj Hlt Hcn).
    + split.
      * intros [C | C]; rewrite <- Ek in C; discriminate C.
      * exists hdr, shdrs, syms, sym, sh; repeat split; try assumption.
        intros [C | C]; rewrite <- Ek in C; discriminate C.
  - destruct (check_exec_relocations_diag raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi)
      as [err | []] eqn:Ecr; [discriminate H |].
    apply check_exec_relocations_diag_sound in Ecr.
    destruct (collect_exec_callee_addrs EK_Exec shdrs syms allowed_callees) as [| addrs] eqn:Ead;
      [discriminate H |].
    inversion H; subst sl ci; clear H.
    cbn [efs_arch efs_kind efs_shndx efs_file_off efs_size efs_bytes
         efs_range_lo efs_range_hi eci_relocs eci_sym_addrs].
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
  - destruct (check_exec_relocations_diag raw (eh_arch hdr) shdrs (esym_shndx sym) rlo rhi)
      as [err | []] eqn:Ecr; [discriminate H |].
    apply check_exec_relocations_diag_sound in Ecr.
    destruct (collect_exec_callee_addrs EK_Dyn shdrs syms allowed_callees) as [| addrs] eqn:Ead;
      [discriminate H |].
    inversion H; subst sl ci; clear H.
    cbn [efs_arch efs_kind efs_shndx efs_file_off efs_size efs_bytes
         efs_range_lo efs_range_hi eci_relocs eci_sym_addrs].
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
