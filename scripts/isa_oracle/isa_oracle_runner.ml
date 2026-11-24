(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)
(* Test-only CLI wrapper over Rocq-extracted A64CoreSem & Rv64Sem concrete evaluators.
   Lives outside vellvm/passes/validator so zero LOC are added to the OCaml TCB. *)

let rec nat_of_int n =
  if n <= 0 then Datatypes.O else Datatypes.S (nat_of_int (n - 1))

let rec pos_of_z z =
  if Z.equal z Z.one then BinNums.Coq_xH
  else if Z.equal (Z.logand z Z.one) Z.one then
    BinNums.Coq_xI (pos_of_z (Z.shift_right z 1))
  else
    BinNums.Coq_xO (pos_of_z (Z.shift_right z 1))

let rec z_of_pos = function
  | BinNums.Coq_xH -> Z.one
  | BinNums.Coq_xI p -> Z.logor (Z.shift_left (z_of_pos p) 1) Z.one
  | BinNums.Coq_xO p -> Z.shift_left (z_of_pos p) 1

let coq_n_of_z z =
  if Z.leq z Z.zero then BinNums.N0 else BinNums.Npos (pos_of_z z)

let z_of_coq_n = function
  | BinNums.N0 -> Z.zero
  | BinNums.Npos p -> z_of_pos p

let coq_n_of_int i = coq_n_of_z (Z.of_int i)

let coq_n_of_hex s =
  let clean =
    if String.length s >= 2 && s.[0] = '0' && (s.[1] = 'x' || s.[1] = 'X') then
      String.sub s 2 (String.length s - 2)
    else s
  in
  coq_n_of_z (Z.of_string_base 16 clean)

let hex64_of_coq_n n = Z.format "%016x" (z_of_coq_n n)

let bytes_of_hex hex =
  let len = String.length hex in
  if len mod 2 <> 0 then invalid_arg "odd hex string length";
  let rec go i acc =
    if i < 0 then acc
    else
      let byte_val = int_of_string ("0x" ^ String.sub hex i 2) in
      go (i - 2) (coq_n_of_int byte_val :: acc)
  in
  go (len - 2) []

let string_of_coq_chars (chars : char list) : string =
  String.of_seq (List.to_seq chars)

let bool_of_tok = function
  | "1" | "true" -> true
  | "0" | "false" -> false
  | s -> invalid_arg ("invalid bool token: " ^ s)

let bit_of_bool b = if b then 1 else 0

let clean_err s =
  String.map (function '\n' | '\r' -> ' ' | c -> c) s

let handle_line line =
  let parts =
    String.split_on_char ' ' (String.trim line)
    |> List.filter (fun s -> s <> "")
  in
  match parts with
  | [] -> ()
  | [ "PING" ] ->
      Printf.printf "PONG\n%!"
  | [ "A64_BITMASK"; sf; n; imms; immr ] ->
      (match
         A64CoreSem.a64_decode_bitmasks
           (bool_of_tok sf) (bool_of_tok n)
           (coq_n_of_int (int_of_string imms))
           (coq_n_of_int (int_of_string immr))
       with
       | Some m -> Printf.printf "OK %s\n%!" (hex64_of_coq_n m)
       | None -> Printf.printf "NONE\n%!")
  | [ "A64_DECODE"; word_hex ] ->
      if A64CoreSem.a64_decode_word_ok (coq_n_of_hex word_hex) then
        Printf.printf "OK\n%!"
      else
        Printf.printf "ERR\n%!"
  | "A64_EXEC" :: fuel_s :: hex_bytes :: ns :: zs :: cs :: vs :: reg_toks ->
      let fuel = int_of_string fuel_s in
      let code = bytes_of_hex hex_bytes in
      let regs = List.map coq_n_of_hex reg_toks in
      (match
         A64CoreSem.a64_eval_bytes_concrete
           (nat_of_int fuel) code regs
           (bool_of_tok ns) (bool_of_tok zs) (bool_of_tok cs) (bool_of_tok vs)
       with
       | Datatypes.Coq_inl err ->
           Printf.printf "ERR %s\n%!" (clean_err (string_of_coq_chars err))
       | Datatypes.Coq_inr (out_regs, (((on, oz), oc), ov)) ->
           let regs_s = String.concat " " (List.map hex64_of_coq_n out_regs) in
           Printf.printf "OK %d %d %d %d %s\n%!"
             (bit_of_bool on) (bit_of_bool oz) (bit_of_bool oc) (bit_of_bool ov) regs_s)
  | [ "RV64_DECODE"; rvc_s; hex_bytes ] ->
      if Rv64Sem.rv_decode_bytes_ok (bool_of_tok rvc_s) (bytes_of_hex hex_bytes) then
        Printf.printf "OK\n%!"
      else
        Printf.printf "ERR\n%!"
  | "RV64_EXEC" :: rvc_s :: fuel_s :: hex_bytes :: reg_toks ->
      let fuel = int_of_string fuel_s in
      let code = bytes_of_hex hex_bytes in
      let regs = List.map coq_n_of_hex reg_toks in
      (match Rv64Sem.rv_eval_bytes_concrete (bool_of_tok rvc_s) (nat_of_int fuel) code regs with
       | Datatypes.Coq_inl err ->
           Printf.printf "ERR %s\n%!" (clean_err (string_of_coq_chars err))
       | Datatypes.Coq_inr out_regs ->
           let regs_s = String.concat " " (List.map hex64_of_coq_n out_regs) in
           Printf.printf "OK %s\n%!" regs_s)
  | cmd :: _ ->
      Printf.printf "ERR unknown command %s\n%!" cmd

let () =
  try
    while true do
      let line = input_line stdin in
      handle_line line
    done
  with End_of_file -> ()
