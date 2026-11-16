(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

let usage =
  "usage: cert-validator --src <src.ll> --tgt <tgt.ll> --cert <fn.cert> | --check-merge --orig <orig.ll> --merged <merged.ll> [--slice <fn> <src.ll> <tgt.ll> ...]"

let die code msg =
  Stdlib.Printf.eprintf "cert-validator: %s\n%!" msg;
  Stdlib.exit code

let parse_ll path =
  if path = "" then die 2 ("empty .ll path (" ^ usage ^ ")");
  try VellvmLib.IO.parse_file path with
  | Sys_error msg | Failure msg -> die 3 msg
  | exn -> die 3 (Stdlib.Printexc.to_string exn)

let read_cert_file path =
  if path = "" then die 2 ("empty .cert path (" ^ usage ^ ")");
  let ch = try Stdlib.open_in_bin path with Sys_error msg -> die 3 msg in
  Stdlib.Fun.protect ~finally:(fun () -> Stdlib.close_in_noerr ch) (fun () ->
    let len = try Stdlib.in_channel_length ch with Sys_error msg -> die 3 msg in
    if len > 67108864 then die 3 "certificate exceeds 64 MiB safety limit";
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

let rec parse_merge orig merged slices = function
  | [] -> (orig, merged, Stdlib.List.rev slices)
  | "--orig" :: v :: tl -> if orig <> None then die 2 "duplicate --orig" else parse_merge (Some v) merged slices tl
  | "--merged" :: v :: tl -> if merged <> None then die 2 "duplicate --merged" else parse_merge orig (Some v) slices tl
  | "--slice" :: fn :: s :: t :: tl -> parse_merge orig merged ((fn, s, t) :: slices) tl
  | ("--orig" | "--merged" | "--slice") :: _ -> die 2 ("missing option argument (" ^ usage ^ ")")
  | a :: _ -> die 2 (Stdlib.Printf.sprintf "unknown argument '%s' (%s)" a usage)

let () =
  let argv = match Stdlib.Array.to_list Stdlib.Sys.argv with _ :: tl -> tl | [] -> [] in
  match argv with
  | "--check-merge" :: rest ->
      let orig_opt, merged_opt, raw_slices = parse_merge None None [] rest in
      let orig_p = match orig_opt with Some p -> p | None -> die 2 ("missing --orig (" ^ usage ^ ")") in
      let merged_p = match merged_opt with Some p -> p | None -> die 2 ("missing --merged (" ^ usage ^ ")") in
      let orig_tle = parse_ll orig_p in
      let merged_tle = parse_ll merged_p in
      let slices =
        Stdlib.List.map
          (fun (fn, sp, tp) -> ((Camlcoq.coqstring_of_camlstring fn, parse_ll sp), parse_ll tp))
          raw_slices
      in
      check_result (ModuleMerge.validate_module_merge_tle orig_tle merged_tle slices)
  | _ ->
      let src_opt, tgt_opt, cert_opt = parse_tv None None None argv in
      let src_p = match src_opt with Some p -> p | None -> die 2 ("missing --src (" ^ usage ^ ")") in
      let tgt_p = match tgt_opt with Some p -> p | None -> die 2 ("missing --tgt (" ^ usage ^ ")") in
      let cert_p = match cert_opt with Some p -> p | None -> die 2 ("missing --cert (" ^ usage ^ ")") in
      let src_tle = parse_ll src_p in
      let tgt_tle = parse_ll tgt_p in
      let cert_str = Camlcoq.coqstring_of_camlstring (read_cert_file cert_p) in
      check_result (CertValidator.validate_tle_pair_with_cert_str src_tle tgt_tle cert_str)
