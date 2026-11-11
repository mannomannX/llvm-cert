(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)
(* Clean-room OCaml <-> Rocq primitive conversion helpers for libvellvm. *)

open BinNums

let camlstring_of_coqstring (chars : char list) : string =
  String.of_seq (List.to_seq chars)

let coqstring_of_camlstring (s : string) : char list =
  List.of_seq (String.to_seq s)

module P = struct
  type t = positive

  let rec of_int64 (n : int64) : positive =
    if Int64.compare n 1L <= 0 then Coq_xH
    else
      let half = Int64.shift_right_logical n 1 in
      if Int64.logand n 1L = 0L then Coq_xO (of_int64 half)
      else Coq_xI (of_int64 half)

  let rec to_int64 (p : positive) : int64 =
    match p with
    | Coq_xH -> 1L
    | Coq_xO q -> Int64.shift_left (to_int64 q) 1
    | Coq_xI q -> Int64.logor (Int64.shift_left (to_int64 q) 1) 1L

  let of_int (n : int) : positive = of_int64 (Int64.of_int n)
  let to_int (p : positive) : int = Int64.to_int (to_int64 p)
end

module N = struct
  type t = coq_N

  let of_int64 (n : int64) : coq_N =
    if Int64.compare n 0L <= 0 then N0 else Npos (P.of_int64 n)

  let to_int64 (n : coq_N) : int64 =
    match n with
    | N0 -> 0L
    | Npos p -> P.to_int64 p

  let of_int (n : int) : coq_N = of_int64 (Int64.of_int n)
  let to_int (n : coq_N) : int = Int64.to_int (to_int64 n)
end

module Z = struct
  type t = coq_Z

  let of_sint64 (n : int64) : coq_Z =
    if n = 0L then Z0
    else if Int64.compare n 0L > 0 then Zpos (P.of_int64 n)
    else Zneg (P.of_int64 (Int64.neg n))

  let of_uint64 (n : int64) : coq_Z =
    if n = 0L then Z0
    else if Int64.compare n 0L > 0 then Zpos (P.of_int64 n)
    else
      let hi = P.of_int64 (Int64.shift_right_logical n 1) in
      if Int64.logand n 1L = 0L then Zpos (Coq_xO hi)
      else Zpos (Coq_xI hi)

  let to_int64 (z : coq_Z) : int64 =
    match z with
    | Z0 -> 0L
    | Zpos p -> P.to_int64 p
    | Zneg p -> Int64.neg (P.to_int64 p)

  let of_sint (n : int) : coq_Z = of_sint64 (Int64.of_int n)
  let of_uint (n : int) : coq_Z = of_sint64 (Int64.logand (Int64.of_int n) 0xFFFFFFFFL)
  let to_int (z : coq_Z) : int = Int64.to_int (to_int64 z)
end

let coqint_of_camlint (v : int32) : Integers.bit_int =
  let u = Int64.logand (Int64.of_int32 v) 0xFFFFFFFFL in
  Integers.repr (P.of_int 32) (Z.of_sint64 u)

let camlint_of_coqint (v : Integers.bit_int) : int32 =
  Int64.to_int32 (Z.to_int64 (Integers.unsigned (P.of_int 32) v))

let coqint_of_camlint64 (v : int64) : Integers.bit_int =
  Integers.repr (P.of_int 64) (Z.of_uint64 v)

let camlint64_of_coqint (v : Integers.bit_int) : int64 =
  Z.to_int64 (Integers.unsigned (P.of_int 64) v)

let coqfloat_of_camlfloat (f : float) : Floats.float =
  Floats.Float.of_bits (coqint_of_camlint64 (Int64.bits_of_float f))

let camlfloat_of_coqfloat (f : Floats.float) : float =
  Int64.float_of_bits (camlint64_of_coqint (Floats.Float.to_bits f))

let coqfloat32_of_camlfloat (f : float) : Floats.float32 =
  Floats.Float32.of_bits (coqint_of_camlint (Int32.bits_of_float f))

let camlfloat_of_coqfloat32 (f : Floats.float32) : float =
  Int32.float_of_bits (camlint_of_coqint (Floats.Float32.to_bits f))

