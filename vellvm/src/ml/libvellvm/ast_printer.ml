(*  ------------------------------------------------------------------------- *)
(* Adapted for use in Vellvm by Steve Zdancewic (c) 2017                      *)
(*  ------------------------------------------------------------------------- *)

let toplevel_entities (fmt : Format.formatter) (tles: (LLVMAst.typ , (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities) : unit =
  (* list formatting so the resulting term is valid *)
  let print_list f lst =
    let rec print_elements = function
      | []   -> ()
      | [h]  -> f h
      | h::t -> f h; Format.pp_print_string fmt ";"; print_elements t
    in
    Format.pp_print_string fmt "[";
    print_elements lst;
    Format.pp_print_string fmt "]"
  in 
  print_list
  (fun tle ->
      Format.pp_print_string fmt (Camlcoq.camlstring_of_coqstring (ReprAST.repr_tle tle)))
      tles


