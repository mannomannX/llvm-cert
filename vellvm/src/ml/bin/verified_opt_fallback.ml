(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

let usage =
  "usage: verified-opt-fallback [--pass pipeline|mem2reg|inline|sccp|dce|simplifycfg] -o <output.ll> <input.ll>"

let die code msg =
  Stdlib.Printf.eprintf "verified-opt-fallback: %s\n%!" msg;
  Stdlib.exit code

let select_pass = function
  | "pipeline" -> Pipeline.optimize_mcfg_typ
  | "mem2reg" -> Mem2RegSpec.mem2reg_mcfg_typ
  | "inline" -> InlineSpec.inline_mcfg_typ
  | "sccp" -> SCCPSpec.sccp_mcfg_typ
  | "dce" -> DCE.dce_mcfg_typ
  | "simplifycfg" -> SimplifyCFG.simplifycfg_mcfg_typ
  | p -> die 2 (Stdlib.Printf.sprintf "unknown --pass '%s' (%s)" p usage)

let rec parse_args pass_opt out_opt in_opt = function
  | [] -> ((match pass_opt with Some p -> p | None -> "pipeline"), out_opt, in_opt)
  | "--pass" :: p :: rest ->
      if pass_opt <> None then die 2 "duplicate --pass option"
      else parse_args (Some p) out_opt in_opt rest
  | ("--pass" | "-o") :: [] -> die 2 ("missing option argument (" ^ usage ^ ")")
  | "-o" :: o :: rest ->
      if out_opt <> None then die 2 "duplicate -o option"
      else parse_args pass_opt (Some o) in_opt rest
  | a :: rest when Stdlib.String.starts_with ~prefix:"--pass=" a ->
      if pass_opt <> None then die 2 "duplicate --pass option"
      else parse_args (Some (Stdlib.String.sub a 7 (Stdlib.String.length a - 7))) out_opt in_opt rest
  | a :: _ when Stdlib.String.length a > 0 && a.[0] = '-' ->
      die 2 (Stdlib.Printf.sprintf "unknown option '%s' (%s)" a usage)
  | a :: rest ->
      if in_opt <> None then die 2 (Stdlib.Printf.sprintf "unexpected argument '%s' (%s)" a usage)
      else parse_args pass_opt out_opt (Some a) rest

let write_tle path out_tle =
  let ch = try Stdlib.open_out path with Sys_error msg -> die 5 msg in
  try
    let fmt = Stdlib.Format.formatter_of_out_channel ch in
    Llvm_printer.toplevel_entities fmt out_tle;
    Stdlib.Format.pp_print_newline fmt ();
    Stdlib.Format.pp_print_flush fmt ();
    Stdlib.close_out ch
  with exn ->
    Stdlib.close_out_noerr ch;
    die 5 (Stdlib.Printexc.to_string exn)

let () =
  let argv = match Stdlib.Array.to_list Stdlib.Sys.argv with _ :: tl -> tl | [] -> [] in
  let pass_name, out_opt, in_opt = parse_args None None None argv in
  let out_path = match out_opt with Some p when p <> "" -> p | _ -> die 2 ("missing -o <output.ll> (" ^ usage ^ ")") in
  let in_path = match in_opt with Some p when p <> "" -> p | _ -> die 2 ("missing <input.ll> (" ^ usage ^ ")") in
  let run_pass = select_pass pass_name in
  let raw_tle =
    try VellvmLib.IO.parse_file in_path with
    | Sys_error msg | Failure msg -> die 3 msg
    | exn -> die 3 (Stdlib.Printexc.to_string exn)
  in
  let resolved_tle = McfgExport.resolve_for_opt_tle raw_tle in
  let m_opt = run_pass (CFG.mcfg_of_tle resolved_tle) in
  match McfgExport.export_mcfg_with_tle resolved_tle m_opt with
  | Datatypes.Coq_inl err -> die 4 (Camlcoq.camlstring_of_coqstring err)
  | Datatypes.Coq_inr out_tle -> write_tle out_path out_tle
