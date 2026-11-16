(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for PowerPC *)

From Stdlib Require Import ZArith List.


Definition ptr64 := false.

Definition big_endian := true.

Definition align_int64 := 8%Z.
Definition align_float64 := 8%Z.

(** Can we use the 64-bit extensions to the PowerPC architecture? *)
Definition ppc64 : bool := false.

Definition splitlong := negb ppc64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  reflexivity.
Qed.

Definition default_nan_64 := (false, iter_nat 51 _ xO xH).
Definition default_nan_32 := (false, iter_nat 22 _ xO xH).

(* Always choose the first NaN argument, if any *)

Definition choose_nan_64 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_64 | n :: _ => n end.

Definition choose_nan_32 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_32 | n :: _ => n end.

Lemma choose_nan_64_idem: forall n,
  choose_nan_64 (n :: n :: nil) = choose_nan_64 (n :: nil).
Proof. auto. Qed.

Lemma choose_nan_32_idem: forall n,
  choose_nan_32 (n :: n :: nil) = choose_nan_32 (n :: nil).
Proof. auto. Qed.

Definition fma_order {A: Type} (x y z: A) := (x, z, y).

Definition fma_invalid_mul_is_nan := false.

Definition float_of_single_preserves_sNaN := true.

Global Opaque ptr64 big_endian splitlong
              default_nan_64 choose_nan_64
              default_nan_32 choose_nan_32
              fma_order fma_invalid_mul_is_nan
              float_of_single_preserves_sNaN.

(** Target-parameterized IEEE-754 NaN payload profiles for AArch64 and RISC-V. *)

Variant target_nan_profile : Type :=
  | NaN_CompCert_Legacy
  | NaN_AArch64_DefaultNaN0
  | NaN_AArch64_DefaultNaN1
  | NaN_RISCV_Canonical.

Definition riscv_canonical_nan_64 : bool * positive :=
  (false, iter_nat 51 _ xO xH).

Definition riscv_canonical_nan_32 : bool * positive :=
  (false, iter_nat 22 _ xO xH).

Definition choose_nan_64_profile
  (prof : target_nan_profile) (l : list (bool * positive)) : bool * positive :=
  match prof with
  | NaN_CompCert_Legacy | NaN_AArch64_DefaultNaN0 =>
      match l with
      | nil => riscv_canonical_nan_64
      | n :: _ => n
      end
  | NaN_AArch64_DefaultNaN1 | NaN_RISCV_Canonical =>
      riscv_canonical_nan_64
  end.

Definition choose_nan_32_profile
  (prof : target_nan_profile) (l : list (bool * positive)) : bool * positive :=
  match prof with
  | NaN_CompCert_Legacy | NaN_AArch64_DefaultNaN0 =>
      match l with
      | nil => riscv_canonical_nan_32
      | n :: _ => n
      end
  | NaN_AArch64_DefaultNaN1 | NaN_RISCV_Canonical =>
      riscv_canonical_nan_32
  end.

Definition float_of_single_preserves_sNaN_profile (prof : target_nan_profile) : bool :=
  match prof with
  | NaN_CompCert_Legacy => true
  | NaN_AArch64_DefaultNaN0 | NaN_AArch64_DefaultNaN1 | NaN_RISCV_Canonical => false
  end.

Lemma choose_nan_64_riscv_canonical : forall l,
  choose_nan_64_profile NaN_RISCV_Canonical l = riscv_canonical_nan_64.
Proof.
  reflexivity.
Qed.

Lemma choose_nan_32_riscv_canonical : forall l,
  choose_nan_32_profile NaN_RISCV_Canonical l = riscv_canonical_nan_32.
Proof.
  reflexivity.
Qed.

Lemma float_of_single_quiets_on_aarch64_and_riscv : forall prof,
  prof <> NaN_CompCert_Legacy ->
  float_of_single_preserves_sNaN_profile prof = false.
Proof.
  intros [] Hne; [contradiction Hne; reflexivity | reflexivity | reflexivity | reflexivity].
Qed.
