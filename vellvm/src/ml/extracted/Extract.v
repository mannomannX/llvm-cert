From Stdlib Require Import
     Morphisms String.

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.
Import ZArith.BinInt.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eqit.

From Vellvm Require Import
     Utils
     Syntax
     Semantics
     Handlers.

Import ITreeNotations.

Import ListNotations.

From Vellvm Require
     Semantics.TopLevel
     Utils.ParserHelper
     Syntax.ModuleRefs
     Syntax.ShowAST
     Syntax.ReprAST.

From CertPasses Require
     SimplifyCFG
     DCE
     SCCP
     Mem2Reg
     Inline
     Pipeline
     McfgExport
     ModuleMerge.

From CertValidator Require
     CertFormat
     AigLrat
     AlgRules
     CertValidator.

Set Extraction AccessOpaque.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlIntConv.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z Format.

(* strings ------------------------------------------------------------------ *)

(* camlstring_of_coqstring is from Camlcoq *)
(* [loc_state] holds the raw [file_info option] of the current instruction;
   the location string is only formatted (AstLib.location_string) when read,
   so the per-instruction [set_loc] is a single pointer write. *)
Extract Constant printer_object => "
  let loc_state = ref None in
  let camlstring_of_coqstring (s: char list) =
    let r = Bytes.create (List.length s) in
    let rec fill pos = function
      | [] -> r
      | c :: s -> Bytes.set r pos c; fill (pos + 1) s
    in Bytes.to_string (fill 0 s)
  in
  let printer_set_loc fi = (loc_state := fi; []) in
  let printer_print_msg msg =
    print_string ((camlstring_of_coqstring (AstLib.location_string !loc_state)) ^ "": "" ^ (camlstring_of_coqstring msg) ^ ""\n"")
  in
  let printer_get_loc = fun _ -> AstLib.location_string !loc_state in
  { printer_set_loc;
    printer_print_msg;
    printer_get_loc; }
  ".

Extract Constant fast_mode_object => "
  let fast_mode_state = ref false in
  let fast_mode_set b = (fast_mode_state := b) in
  let fast_mode_get = fun _ -> !fast_mode_state in
  { fast_mode_set;
    fast_mode_get;
  }
  ".

Extract Constant locals_object => "
  let locals_ref = ref RawIdMaps.RM.empty in
  let locals_set ls = (locals_ref := ls; ()) in
  let locals_get = fun _ -> !locals_ref in
  fun _ -> { locals_set;
    locals_get;
  }
  ".

Extract Constant globals_object => "
  let globals_ref = ref RawIdMaps.RM.empty in
  let globals_set gs = (globals_ref := gs; ()) in
  let globals_get = fun _ -> !globals_ref in
  fun _ -> { globals_set;
    globals_get;
  }
  ".

Extract Constant local_stack_object => "
  let local_stack_ref = ref [{ stack_vars = RawIdMaps.RM.empty; stack_exc = None; stack_loc = None }] in
  let local_stack_set ls = (local_stack_ref := match !local_stack_ref with [] -> Stdlib.failwith ""Empty stack, can't set"" | _::xs -> ls :: xs) in
  let local_stack_get = fun _ -> !local_stack_ref in
  let local_stack_push ls = local_stack_ref := ls :: !local_stack_ref in
  let local_stack_pop = fun _ -> local_stack_ref := List.tl !local_stack_ref in
  fun _ -> { local_stack_set;
    local_stack_get;
    local_stack_push;
    local_stack_pop;
  }
  ".

(* OCaml pervasive types ---------------------------------------------------- *)
(* Extract Inlined Constant LLVMAst.int => "int". *)
(* Extract Inlined Constant LLVMAst.float => "float". *)

(* Cutting the dependency to R. *)
Extract Inlined Constant Flocq.Core.Defs.F2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.FF2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.B2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.BinarySingleNaN.round_mode => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.Calc.Bracket.inbetween_loc => "(fun _ -> assert false)".
Extract Inlined Constant Reals.ClassicalDedekindReals.sig_forall_dec => "(fun _ -> assert false)".
Extract Inlined Constant Reals.ClassicalDedekindReals.sig_not_dec => "false".

Extract Inlined Constant Archi.ppc64 => "false".

(* (* Extract Inlined Constant nat => "nat". *) *)
(* Export TopLevelBigIntptr. *)

(* (* NOTE: assumes that this file is compiled from /src *) *)
Cd "ml/extracted".

Separate Extraction ExtrOcamlIntConv TopLevel AstLib ParserHelper ShowAST ReprAST Handlers Numeric.Floats BinNums BinPos
  LLVMAst.nofpclass_mask LLVMAst.nofpclass_mask_valid
  SimplifyCFG.simplifycfg_mcfg SimplifyCFG.simplifycfg_mcfg_typ
  DCE.dce_mcfg DCE.dce_mcfg_typ
  SCCP.sccp_mcfg SCCP.sccp_mcfg_typ
  Mem2Reg.mem2reg_mcfg Mem2Reg.mem2reg_mcfg_typ
  Inline.inline_mcfg Inline.inline_mcfg_typ
  Pipeline.optimize_mcfg Pipeline.optimize_mcfg_typ
  ModuleRefs.resolve_module_refs
  McfgExport.resolve_for_opt_tle
  McfgExport.export_mcfg_to_tle McfgExport.export_mcfg_with_typ McfgExport.export_mcfg_with_tle
  ModuleMerge.validate_module_merge ModuleMerge.validate_module_merge_parsed ModuleMerge.validate_module_merge_tle
  ModuleMerge.check_safe_slice_tle ModuleMerge.check_module_merge_certified_tle ModuleMerge.validate_module_merge_certified_tle
  CertFormat.parse_sexp CertFormat.parse_cert CertFormat.check_validator_syntax_gates CertFormat.check_prototype_contract
  AigLrat.check_lrat_unsat
  AlgRules.check_expr_refines AlgRules.check_expr_refines_with_lrat
  CertValidator.check_cert_cfg CertValidator.check_cert_cfg_with_lrat CertValidator.check_cert_defn
  CertValidator.validate_mcfg_with_cert CertValidator.validate_tle_pair_with_cert CertValidator.validate_tle_pair_with_cert_str (* QCVellvm *).
