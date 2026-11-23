(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

let usage =
  "usage: cert-validator --src <src.ll> --tgt <tgt.ll> --cert <fn.cert> | --check-merge --orig <orig.ll> --merged <merged.ll> [--slice-cert <fn> <src.ll> <opt_fast.ll> <cert> | --slice-safe <fn> <src.ll> <opt_safe.ll> | --slice-safe-cert <fn> <src.ll> <mid_safe.ll> <opt_fast.ll> <cert>]* | --check-lrat --cnf <formula.cnf> --lrat <proof.lrat>"

let max_input_bytes = 67108864

let die code msg =
  Stdlib.Printf.eprintf "cert-validator: %s\n%!" msg;
  Stdlib.exit code

let check_size_limit path label =
  let ch = try Stdlib.open_in_bin path with Sys_error msg -> die 3 msg in
  Stdlib.Fun.protect ~finally:(fun () -> Stdlib.close_in_noerr ch) (fun () ->
    let len = try Stdlib.in_channel_length ch with Sys_error msg -> die 3 msg in
    if len < 0 || len > max_input_bytes then die 3 (label ^ " exceeds 64 MiB safety limit"))

let parse_ll path =
  if path = "" then die 2 ("empty .ll path (" ^ usage ^ ")");
  check_size_limit path "LLVM IR input";
  try VellvmLib.IO.parse_file path with
  | Sys_error msg | Failure msg -> die 3 msg
  | Stack_overflow -> die 3 "stack overflow limit exceeded"
  | Out_of_memory -> die 3 "out of memory"
  | exn -> die 3 (Stdlib.Printexc.to_string exn)

let read_cert_file path =
  if path = "" then die 2 ("empty .cert path (" ^ usage ^ ")");
  let ch = try Stdlib.open_in_bin path with Sys_error msg -> die 3 msg in
  Stdlib.Fun.protect ~finally:(fun () -> Stdlib.close_in_noerr ch) (fun () ->
    let len = try Stdlib.in_channel_length ch with Sys_error msg -> die 3 msg in
    if len < 0 || len > max_input_bytes then die 3 "certificate exceeds 64 MiB safety limit";
    try Stdlib.really_input_string ch len with End_of_file | Sys_error _ -> die 3 "truncated read")

let check_result = function
  | Datatypes.Coq_inr () -> ()
  | Datatypes.Coq_inl err -> die 4 ("rejected: " ^ Camlcoq.camlstring_of_coqstring err)

let rec parse_tv src tgt cert = function
  | [] -> (src, tgt, cert)
  | "--src" :: v :: tl -> if src <> None then die 2 "duplicate --src" else parse_tv (Some v) tgt cert tl
  | "--tgt" :: v :: tl -> if tgt <> None then die 2 "duplicate --tgt" else parse_tv src (Some v) cert tl
  | "--cert" :: v :: tl -> if cert <> None then die 2 "duplicate --cert" else parse_tv src tgt (Some v) tl
  | ("--src" | "--tgt" | "--cert") :: [] -> die 2 ("missing option argument (" ^ usage ^ ")")
  | a :: _ -> die 2 (Stdlib.Printf.sprintf "unknown argument '%s' (%s)" a usage)

let rec parse_merge orig merged certs safes safe_certs = function
  | [] -> (orig, merged, Stdlib.List.rev certs, Stdlib.List.rev safes, Stdlib.List.rev safe_certs)
  | "--orig" :: v :: tl -> if orig <> None then die 2 "duplicate --orig" else parse_merge (Some v) merged certs safes safe_certs tl
  | "--merged" :: v :: tl -> if merged <> None then die 2 "duplicate --merged" else parse_merge orig (Some v) certs safes safe_certs tl
  | "--slice-cert" :: fn :: s :: t :: c :: tl ->
      if fn = "" then die 2 ("empty slice function name (" ^ usage ^ ")");
      parse_merge orig merged ((fn, s, t, c) :: certs) safes safe_certs tl
  | "--slice-safe" :: fn :: s :: t :: tl ->
      if fn = "" then die 2 ("empty slice function name (" ^ usage ^ ")");
      parse_merge orig merged certs ((fn, s, t) :: safes) safe_certs tl
  | "--slice-safe-cert" :: fn :: s :: m :: t :: c :: tl ->
      if fn = "" then die 2 ("empty slice function name (" ^ usage ^ ")");
      parse_merge orig merged certs safes ((fn, s, m, t, c) :: safe_certs) tl
  | "--slice" :: _ -> die 2 ("unauthenticated --slice is forbidden; use --slice-cert, --slice-safe, or --slice-safe-cert (" ^ usage ^ ")")
  | ("--orig" | "--merged" | "--slice-cert" | "--slice-safe" | "--slice-safe-cert") :: _ -> die 2 ("missing option argument (" ^ usage ^ ")")
  | a :: _ -> die 2 (Stdlib.Printf.sprintf "unknown argument '%s' (%s)" a usage)

let rec parse_lrat cnf lrat = function
  | [] -> (cnf, lrat)
  | "--cnf" :: v :: tl -> if cnf <> None then die 2 "duplicate --cnf" else parse_lrat (Some v) lrat tl
  | "--lrat" :: v :: tl -> if lrat <> None then die 2 "duplicate --lrat" else parse_lrat cnf (Some v) tl
  | ("--cnf" | "--lrat") :: [] -> die 2 ("missing option argument (" ^ usage ^ ")")
  | a :: _ -> die 2 (Stdlib.Printf.sprintf "unknown argument '%s' (%s)" a usage)

let run () =
  let argv = match Stdlib.Array.to_list Stdlib.Sys.argv with _ :: tl -> tl | [] -> [] in
  match argv with
  | "--check-lrat" :: rest ->
      let cnf_opt, lrat_opt = parse_lrat None None rest in
      let cnf_p = match cnf_opt with Some p -> p | None -> die 2 ("missing --cnf (" ^ usage ^ ")") in
      let lrat_p = match lrat_opt with Some p -> p | None -> die 2 ("missing --lrat (" ^ usage ^ ")") in
      let cnf_s = Camlcoq.coqstring_of_camlstring (read_cert_file cnf_p) in
      let lrat_s = Camlcoq.coqstring_of_camlstring (read_cert_file lrat_p) in
      check_result (CertFormat.validate_dimacs_lrat_str cnf_s lrat_s)
  | "--check-merge" :: rest ->
      let orig_opt, merged_opt, raw_certs, raw_safes, raw_sc = parse_merge None None [] [] [] rest in
      let orig_p = match orig_opt with Some p -> p | None -> die 2 ("missing --orig (" ^ usage ^ ")") in
      let merged_p = match merged_opt with Some p -> p | None -> die 2 ("missing --merged (" ^ usage ^ ")") in
      let orig_tle = parse_ll orig_p in
      let merged_tle = parse_ll merged_p in
      let check_cert s_tle t_tle cp =
        check_result (CertValidator.validate_tle_pair_with_cert_str s_tle t_tle (Camlcoq.coqstring_of_camlstring (read_cert_file cp)))
      in
      let cert_slices =
        Stdlib.List.map
          (fun (fn, sp, tp, cp) ->
            let s_tle = parse_ll sp in
            let t_tle = parse_ll tp in
            check_cert s_tle t_tle cp;
            ((Camlcoq.coqstring_of_camlstring fn, s_tle), t_tle))
          raw_certs
      in
      let safe_slices =
        Stdlib.List.map
          (fun (fn, sp, tp) -> ((Camlcoq.coqstring_of_camlstring fn, parse_ll sp), parse_ll tp))
          raw_safes
      in
      let safe_cert_slices =
        Stdlib.List.map
          (fun (fn, sp, mp, tp, cp) ->
            let m_tle = parse_ll mp in
            let t_tle = parse_ll tp in
            check_cert m_tle t_tle cp;
            (((Camlcoq.coqstring_of_camlstring fn, parse_ll sp), m_tle), t_tle))
          raw_sc
      in
      check_result (ModuleMerge.validate_module_merge_certified_tle_composed orig_tle merged_tle cert_slices safe_slices safe_cert_slices)
  | _ ->
      let src_opt, tgt_opt, cert_opt = parse_tv None None None argv in
      let src_p = match src_opt with Some p -> p | None -> die 2 ("missing --src (" ^ usage ^ ")") in
      let tgt_p = match tgt_opt with Some p -> p | None -> die 2 ("missing --tgt (" ^ usage ^ ")") in
      let cert_p = match cert_opt with Some p -> p | None -> die 2 ("missing --cert (" ^ usage ^ ")") in
      let src_tle = parse_ll src_p in
      let tgt_tle = parse_ll tgt_p in
      let cert_str = Camlcoq.coqstring_of_camlstring (read_cert_file cert_p) in
      check_result (CertValidator.validate_tle_pair_with_cert_str src_tle tgt_tle cert_str)

let () =
  try run () with
  | Sys_error msg | Failure msg -> die 3 msg
  | Stack_overflow -> die 3 "stack overflow limit exceeded"
  | Out_of_memory -> die 3 "out of memory"
  | exn -> die 3 (Stdlib.Printexc.to_string exn)
