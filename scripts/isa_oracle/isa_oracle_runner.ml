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

let z_of_coq_z = function
  | BinNums.Z0 -> Z.zero
  | BinNums.Zpos p -> z_of_pos p
  | BinNums.Zneg p -> Z.neg (z_of_pos p)

let int_of_pos p = Z.to_int (z_of_pos p)

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

let json_str s =
  let buf = Buffer.create (String.length s + 8) in
  Buffer.add_char buf '"';
  String.iter
    (function
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\n' -> Buffer.add_string buf "\\n"
      | '\r' -> Buffer.add_string buf "\\r"
      | '\t' -> Buffer.add_string buf "\\t"
      | c -> Buffer.add_char buf c)
    s;
  Buffer.add_char buf '"';
  Buffer.contents buf

let smt2_ident name =
  let valid =
    String.length name > 0
    && String.for_all
         (function
           | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '.' -> true
           | _ -> false)
         name
  in
  if valid then name else "|" ^ name ^ "|"

let smt2_bv_const w v =
  let mask = Z.pred (Z.shift_left Z.one w) in
  let mv = Z.logand v mask in
  Printf.sprintf "(_ bv%s %d)" (Z.to_string mv) w

let rec smt2_of_cert_expr (e : CertFormatAst.cert_expr) : string =
  match e with
  | CertFormatAst.CE_BvConst (w, n) ->
      smt2_bv_const (int_of_pos w) (z_of_coq_n n)
  | CertFormatAst.CE_Poison w ->
      failwith (Printf.sprintf "unexpected CE_Poison(%d)" (int_of_pos w))
  | CertFormatAst.CE_Var (nm, _w) ->
      smt2_ident (string_of_coq_chars nm)
  | CertFormatAst.CE_BinOp (op, _w, _fl, l, r) ->
      let sop =
        match op with
        | CertFormatAst.CB_Add -> "bvadd"
        | CertFormatAst.CB_Sub -> "bvsub"
        | CertFormatAst.CB_Mul -> "bvmul"
        | CertFormatAst.CB_UDiv -> "bvudiv"
        | CertFormatAst.CB_SDiv -> "bvsdiv"
        | CertFormatAst.CB_URem -> "bvurem"
        | CertFormatAst.CB_SRem -> "bvsrem"
        | CertFormatAst.CB_Shl -> "bvshl"
        | CertFormatAst.CB_LShr -> "bvlshr"
        | CertFormatAst.CB_AShr -> "bvashr"
        | CertFormatAst.CB_And -> "bvand"
        | CertFormatAst.CB_Or -> "bvor"
        | CertFormatAst.CB_Xor -> "bvxor"
      in
      Printf.sprintf "(%s %s %s)" sop (smt2_of_cert_expr l) (smt2_of_cert_expr r)
  | CertFormatAst.CE_ICmp (pred, _ss, _w, l, r) ->
      let sl = smt2_of_cert_expr l in
      let sr = smt2_of_cert_expr r in
      let cond =
        match pred with
        | CertFormatAst.CIP_Eq -> Printf.sprintf "(= %s %s)" sl sr
        | CertFormatAst.CIP_Ne -> Printf.sprintf "(not (= %s %s))" sl sr
        | CertFormatAst.CIP_Ult -> Printf.sprintf "(bvult %s %s)" sl sr
        | CertFormatAst.CIP_Ule -> Printf.sprintf "(bvule %s %s)" sl sr
        | CertFormatAst.CIP_Ugt -> Printf.sprintf "(bvugt %s %s)" sl sr
        | CertFormatAst.CIP_Uge -> Printf.sprintf "(bvuge %s %s)" sl sr
        | CertFormatAst.CIP_Slt -> Printf.sprintf "(bvslt %s %s)" sl sr
        | CertFormatAst.CIP_Sle -> Printf.sprintf "(bvsle %s %s)" sl sr
        | CertFormatAst.CIP_Sgt -> Printf.sprintf "(bvsgt %s %s)" sl sr
        | CertFormatAst.CIP_Sge -> Printf.sprintf "(bvsge %s %s)" sl sr
      in
      Printf.sprintf "(ite %s (_ bv1 1) (_ bv0 1))" cond
  | CertFormatAst.CE_Cast (kind, fw_p, tw_p, _fl, inner) ->
      let fw = int_of_pos fw_p in
      let tw = int_of_pos tw_p in
      let si = smt2_of_cert_expr inner in
      (match kind with
       | CertFormatAst.CCK_Trunc ->
           if tw = fw then si
           else Printf.sprintf "((_ extract %d 0) %s)" (tw - 1) si
       | CertFormatAst.CCK_ZExt ->
           if tw = fw then si
           else Printf.sprintf "((_ zero_extend %d) %s)" (tw - fw) si
       | CertFormatAst.CCK_SExt ->
           if tw = fw then si
           else Printf.sprintf "((_ sign_extend %d) %s)" (tw - fw) si)
  | CertFormatAst.CE_Select (_w, c, t, f) ->
      Printf.sprintf "(ite (= %s (_ bv1 1)) %s %s)"
        (smt2_of_cert_expr c) (smt2_of_cert_expr t) (smt2_of_cert_expr f)
  | CertFormatAst.CE_Freeze (_w, inner) ->
      smt2_of_cert_expr inner
  | CertFormatAst.CE_Let (bindings, body) ->
      List.fold_right
        (fun (nm, rhs) acc ->
           Printf.sprintf "(let ((%s %s)) %s)"
             (smt2_ident (string_of_coq_chars nm))
             (smt2_of_cert_expr rhs) acc)
        bindings
        (smt2_of_cert_expr body)

let json_opt_str = function
  | Some s -> json_str s
  | None -> "null"

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
         A64Decode.a64_decode_bitmasks
           (bool_of_tok sf) (bool_of_tok n)
           (coq_n_of_int (int_of_string imms))
           (coq_n_of_int (int_of_string immr))
       with
       | Some m -> Printf.printf "OK %s\n%!" (hex64_of_coq_n m)
       | None -> Printf.printf "NONE\n%!")
  | [ "A64_DECODE"; word_hex ] ->
      if A64SymOracle.a64_decode_word_ok (coq_n_of_hex word_hex) then
        Printf.printf "OK\n%!"
      else
        Printf.printf "ERR\n%!"
  | "A64_EXEC" :: fuel_s :: hex_bytes :: ns :: zs :: cs :: vs :: reg_toks ->
      let fuel = int_of_string fuel_s in
      let code = bytes_of_hex hex_bytes in
      let regs = List.map coq_n_of_hex reg_toks in
      (match
         A64SymOracle.a64_eval_bytes_concrete
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
      if Rv64SymOracle.rv_decode_bytes_ok (bool_of_tok rvc_s) (bytes_of_hex hex_bytes) then
        Printf.printf "OK\n%!"
      else
        Printf.printf "ERR\n%!"
  | [ "A64_SYM"; word_hex ] ->
      (try
         match A64SymOracle.a64_step_sym_oracle (coq_n_of_hex word_hex) with
         | None -> Printf.printf "NONE\n%!"
         | Some out ->
             let rd_json, rd_expr_json =
               match out.A64SymOracle.aso_rd_write with
               | None -> ("null", "null")
               | Some (rd, e) ->
                   (Z.to_string (z_of_coq_n rd), json_str (smt2_of_cert_expr e))
             in
             let flags_json =
               match out.A64SymOracle.aso_flags_write with
               | None -> "null"
               | Some (((fn, fz), fc), fv) ->
                   Printf.sprintf "[%s,%s,%s,%s]"
                     (json_str (smt2_of_cert_expr fn))
                     (json_str (smt2_of_cert_expr fz))
                     (json_str (smt2_of_cert_expr fc))
                     (json_str (smt2_of_cert_expr fv))
             in
             let br_json =
               json_opt_str (Option.map smt2_of_cert_expr out.A64SymOracle.aso_br_cond)
             in
             Printf.printf
               "OK {\"rd\":%s,\"rd_expr\":%s,\"flags\":%s,\"pc_kind\":%s,\"br_cond\":%s,\"rel_bytes\":%s}\n%!"
               rd_json rd_expr_json flags_json
               (Z.to_string (z_of_coq_n out.A64SymOracle.aso_pc_kind))
               br_json
               (Z.to_string (z_of_coq_z out.A64SymOracle.aso_rel_bytes))
       with Failure msg -> Printf.printf "ERR %s\n%!" (clean_err msg))
  | [ "RV64_SYM"; rvc_s; hex_bytes ] ->
      (try
         match Rv64SymOracle.rv_step_sym_oracle (bool_of_tok rvc_s) (bytes_of_hex hex_bytes) with
         | None -> Printf.printf "NONE\n%!"
         | Some out ->
             let rd_json, rd_expr_json =
               match out.Rv64SymOracle.rso_rd_write with
               | None -> ("null", "null")
               | Some (rd, e) ->
                   (Z.to_string (z_of_coq_n rd), json_str (smt2_of_cert_expr e))
             in
             let br_json =
               json_opt_str (Option.map smt2_of_cert_expr out.Rv64SymOracle.rso_br_cond)
             in
             Printf.printf
               "OK {\"len\":%s,\"rd\":%s,\"rd_expr\":%s,\"pc_kind\":%s,\"br_cond\":%s,\"rel_bytes\":%s}\n%!"
               (Z.to_string (z_of_coq_n out.Rv64SymOracle.rso_len))
               rd_json rd_expr_json
               (Z.to_string (z_of_coq_n out.Rv64SymOracle.rso_pc_kind))
               br_json
               (Z.to_string (z_of_coq_z out.Rv64SymOracle.rso_rel_bytes))
       with Failure msg -> Printf.printf "ERR %s\n%!" (clean_err msg))
  | "RV64_EXEC" :: rvc_s :: fuel_s :: hex_bytes :: reg_toks ->
      let fuel = int_of_string fuel_s in
      let code = bytes_of_hex hex_bytes in
      let regs = List.map coq_n_of_hex reg_toks in
      (match Rv64SymOracle.rv_eval_bytes_concrete (bool_of_tok rvc_s) (nat_of_int fuel) code regs with
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
