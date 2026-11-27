(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Module-Merge Linking & Safe-Path Slice Splicing ([CertPasses.ModuleMergeLink])

    Purpose:
      Defines [check_module_merge] and [validate_module_merge], proves
      structural reflection and compositional linking to [@prog_refines] and
      [I2F_toplevel.model_refine], and proves [optimize_mcfg_slice_valid] for
      heterogeneous Safe-Path slice splicing.

    Trust Contract & Fail-Closed Boundary:
      Extracted to OCaml ([Extract.v]: [validate_module_merge]). Fails closed
      with [inl msg] on mismatched globals, declarations, [LINKAGE_Extern_weak],
      duplicate symbols, [blockaddress] tables, or unverified prototypes/bodies.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.ModuleMergeEqb],
      and [CertPasses.{PassCommon,SimplifyCFG,DCE,SCCP,Mem2Reg,Inline,Pipeline,
      McfgExport}]; zero custom axioms.

    Section Outline:
      (2) Validator & [validate_module_merge_ok_iff]; (3) Structural reflection;
      (4) Compositional linking & [check_module_merge_refines];
      (5) Heterogeneous [slice_valid_in_any_host] & [optimize_mcfg_slice_valid]. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Number
  Decimal
  Hexadecimal
  Strings.Ascii
  Strings.String
  List
  Bool
  Lia
  Classes.RelationClasses.
Import ListNotations.

From Paco Require Import
  paco.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.HeterogeneousRelations.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads.

From Vellvm Require Import
  Semantics.VellvmIntegers
  Utils
  Syntax
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.DynamicTypes
  Semantics
  ScopeTheory
  Utils.rutt_cutoff
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.IPtrInfinite
  Semantics.Implementations.IPtrFinite
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.Denotation
  Semantics.TopLevel
  Semantics.Libraries
  Semantics.LLVMEvents
  Theory.I2F.Refinement
  Theory.I2F.I2F_interp
  Theory.I2F.I2F_toplevel.

From CertPasses Require Import
  PassCommon
  SimplifyCFG
  DCE
  SCCP
  Mem2Reg
  Inline
  Pipeline
  McfgExport.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.
#[local] Open Scope list_scope.
#[local] Existing Instance MemoryModelStateV.
#[local] Existing Instance MemoryModelPrimitivesV.

From CertPasses Require Import ModuleMergeEqb.

(** * 2. Module Split/Merge Soundness Invariants & Executable Validator *)

Fixpoint mm_nodup_raw_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (in_raw_ids x rest) && mm_nodup_raw_ids rest
  end.

Lemma mm_nodup_raw_ids_spec (xs : list raw_id) :
  mm_nodup_raw_ids xs = true <-> NoDup xs.
Proof.
  induction xs as [| x rest IH]; cbn [mm_nodup_raw_ids].
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite Bool.andb_true_iff, Bool.negb_true_iff, in_raw_ids_false, IH.
    split; [intros [Hnin Hnd]; constructor; assumption
           | intros Hnd; inversion Hnd; subst; split; assumption].
Qed.

Definition opt_linkage_no_extern_weak (ol : option linkage) : bool :=
  match ol with
  | Some LINKAGE_Extern_weak => false
  | _ => true
  end.

Lemma opt_linkage_no_extern_weak_spec (ol : option linkage) :
  opt_linkage_no_extern_weak ol = true <-> ol <> Some LINKAGE_Extern_weak.
Proof.
  destruct ol as [l |]; [destruct l |]; cbn [opt_linkage_no_extern_weak];
    first [split; [discriminate | intros H; exfalso; exact (H Logic.eq_refl)]
          | split; [intros _ H; discriminate H | intros _; reflexivity]].
Qed.

Definition global_no_extern_weak (g : global dtyp) : bool :=
  opt_linkage_no_extern_weak (g_linkage g).

Definition decl_no_extern_weak (d : declaration dtyp) : bool :=
  opt_linkage_no_extern_weak (dc_linkage d).

(** [ir-bridge split] externalizes internal/private linkage on extracted
    per-function slices so LLVM [-O2] ([GlobalDCE]) cannot delete the slice
    entry definition.  Slice linkage is therefore compatible when it is either
    externalized ([None] / [Some LINKAGE_External]) or identical to [m_orig],
    and never [LINKAGE_Extern_weak]. *)
Definition dc_linkage_slice_compatible
  (orig_lnk slice_lnk : option linkage) : bool :=
  opt_linkage_no_extern_weak slice_lnk &&
  match slice_lnk with
  | None | Some LINKAGE_External => true
  | _ => mm_option_eqb mm_linkage_eqb slice_lnk orig_lnk
  end.

Lemma dc_linkage_slice_compatible_spec
  (orig_lnk slice_lnk : option linkage) :
  dc_linkage_slice_compatible orig_lnk slice_lnk = true ->
  slice_lnk <> Some LINKAGE_Extern_weak /\
  (slice_lnk = None \/ slice_lnk = Some LINKAGE_External \/ slice_lnk = orig_lnk).
Proof.
  unfold dc_linkage_slice_compatible.
  rewrite Bool.andb_true_iff, opt_linkage_no_extern_weak_spec.
  intros [Hnw Hlnk]; split; [exact Hnw |].
  destruct slice_lnk as [l |]; [| left; reflexivity].
  destruct l;
    try (apply (mm_option_eqb_eq _ mm_linkage_eqb_eq) in Hlnk; right; right; exact Hlnk).
  right; left; reflexivity.
Qed.

(** Match a single [(df_orig, df_merged)] pair against one verified slice entry
    [(fid, m_slice_src, m_slice_tgt)]. *)
Definition check_slice_matches_defn
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp))
  (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : bool :=
  let '(fid, m_slice_src, m_slice_tgt) := entry in
  let proto_orig := df_prototype df_orig in
  raw_id_eqb (dc_name proto_orig) fid &&
  match m_definitions m_slice_src, m_definitions m_slice_tgt with
  | [df_src], [df_tgt] =>
      let proto_src := df_prototype df_src in
      let proto_tgt := df_prototype df_tgt in
      raw_id_eqb (dc_name proto_src) fid &&
      mm_dtyp_eqb (dc_type proto_src) (dc_type proto_orig) &&
      mm_param_attrs_pair_eqb (dc_param_attrs proto_src) (dc_param_attrs proto_orig) &&
      cconv_eqb (anns_cconv (dc_annotations proto_src))
                (anns_cconv (dc_annotations proto_orig)) &&
      dc_linkage_slice_compatible (dc_linkage proto_orig) (dc_linkage proto_src) &&
      mm_list_eqb raw_id_eqb (df_args df_src) (df_args df_orig) &&
      mm_cfg_eqb (df_instrs df_src) (df_instrs df_orig) &&
      raw_id_eqb (dc_name proto_tgt) fid &&
      decl_no_extern_weak proto_tgt &&
      mm_list_eqb raw_id_eqb (df_args df_tgt) (df_args df_merged) &&
      mm_cfg_eqb (df_instrs df_tgt) (df_instrs df_merged)
  | _, _ => false
  end.

Definition check_defn_pair
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp)) : bool :=
  mm_declaration_eqb (df_prototype df_merged) (df_prototype df_orig) &&
  mm_list_eqb raw_id_eqb (df_args df_merged) (df_args df_orig) &&
  (mm_definition_eqb df_merged df_orig ||
   existsb (check_slice_matches_defn df_orig df_merged) verified_slices).

Fixpoint check_defs_merge
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (defs_orig defs_merged : list (definition dtyp (CFG.cfg dtyp))) : bool :=
  match defs_orig, defs_merged with
  | [], [] => true
  | d1 :: r1, d2 :: r2 =>
      check_defn_pair verified_slices d1 d2 && check_defs_merge verified_slices r1 r2
  | _, _ => false
  end.

(** True when declaration [d] names a built-in Vellvm LLVM intrinsic, which
    [TopLevel.allocate_declaration] skips (zero heap/address effect) and
    [Libraries.library_functions] never binds as an external library symbol. *)
Definition is_defined_intrinsic_decl (d : declaration dtyp) : bool :=
  match lookup_intrinsic_declaration (dc_name d) with
  | Some _ => true
  | None => false
  end.

Definition non_intrinsic_decls (ds : list (declaration dtyp)) : list (declaration dtyp) :=
  List.filter (fun d => negb (is_defined_intrinsic_decl d)) ds.

(** Decidable boolean module-merge checker closing F-19, F-24, F-33, and F-47. *)
Definition check_module_merge
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) : bool :=
  mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig) &&
  forallb global_no_extern_weak (m_globals m_orig) &&
  mm_list_eqb mm_declaration_eqb
    (non_intrinsic_decls (m_declarations m_merged))
    (non_intrinsic_decls (m_declarations m_orig)) &&
  forallb decl_no_extern_weak (m_declarations m_orig) &&
  forallb decl_no_extern_weak (m_declarations m_merged) &&
  forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig) &&
  mm_nodup_raw_ids
    (List.map dc_name
       (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig))) &&
  mm_nodup_raw_ids
    (List.map dc_name
       (m_declarations m_merged ++ List.map df_prototype (m_definitions m_merged))) &&
  mm_list_eqb mm_block_addr_eqb
    (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
    (nodup block_address_eq_dec (mcfg_block_addresses m_orig)) &&
  check_defs_merge verified_slices (m_definitions m_orig) (m_definitions m_merged).

Fixpoint validate_defs_merge
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (defs_orig defs_merged : list (definition dtyp (CFG.cfg dtyp)))
  : string + unit :=
  match defs_orig, defs_merged with
  | [], [] => inr tt
  | [], _ :: _ =>
      inl "validate_module_merge: extra function definition in m_merged"%string
  | _ :: _, [] =>
      inl "validate_module_merge: missing function definition in m_merged"%string
  | df_orig :: r1, df_merged :: r2 =>
      let fname := show_raw_id (dc_name (df_prototype df_orig)) in
      if negb (mm_declaration_eqb (df_prototype df_merged) (df_prototype df_orig)) then
        inl ("validate_module_merge: prototype/attribute desync on @" ++ fname)%string
      else if negb (mm_list_eqb raw_id_eqb (df_args df_merged) (df_args df_orig)) then
        inl ("validate_module_merge: formal parameter list desync on @" ++ fname)%string
      else if negb (mm_definition_eqb df_merged df_orig ||
                    existsb (check_slice_matches_defn df_orig df_merged) verified_slices) then
        inl ("validate_module_merge: unverified body modification on @" ++ fname)%string
      else
        validate_defs_merge verified_slices r1 r2
  end.

(** Diagnostic wrapper suitable for OCaml CLI extraction ([Extract.v]). *)
Definition validate_module_merge
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  : string + unit :=
  if negb (mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig)) then
    inl "validate_module_merge: m_globals layout or alignment mismatch"%string
  else if negb (forallb global_no_extern_weak (m_globals m_orig)) then
    inl "validate_module_merge: extern_weak global linkage is unsupported"%string
  else if negb (mm_list_eqb mm_declaration_eqb
                  (non_intrinsic_decls (m_declarations m_merged))
                  (non_intrinsic_decls (m_declarations m_orig))) then
    inl "validate_module_merge: m_declarations symbol table mismatch"%string
  else if negb (forallb decl_no_extern_weak (m_declarations m_orig)) then
    inl "validate_module_merge: extern_weak declaration linkage is unsupported"%string
  else if negb (forallb decl_no_extern_weak (m_declarations m_merged)) then
    inl "validate_module_merge: extern_weak synthesized declaration linkage is unsupported"%string
  else if negb (forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig)) then
    inl "validate_module_merge: extern_weak definition linkage is unsupported"%string
  else if negb (mm_nodup_raw_ids
                  (List.map dc_name
                     (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig)))) then
    inl "validate_module_merge: duplicate function symbol in declarations/definitions"%string
  else if negb (mm_nodup_raw_ids
                  (List.map dc_name
                     (m_declarations m_merged ++ List.map df_prototype (m_definitions m_merged)))) then
    inl "validate_module_merge: duplicate function symbol in merged declarations/definitions"%string
  else if negb (mm_list_eqb mm_block_addr_eqb
                  (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
                  (nodup block_address_eq_dec (mcfg_block_addresses m_orig))) then
    inl "validate_module_merge: module blockaddress table mismatch"%string
  else
    validate_defs_merge verified_slices (m_definitions m_orig) (m_definitions m_merged).

Lemma validate_defs_merge_ok_iff
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  forall defs_orig defs_merged,
    validate_defs_merge verified_slices defs_orig defs_merged = inr tt <->
    check_defs_merge verified_slices defs_orig defs_merged = true.
Proof.
  induction defs_orig as [| d1 r1 IH]; intros [| d2 r2];
    cbn [validate_defs_merge check_defs_merge].
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - unfold check_defn_pair; cbv zeta.
    destruct (mm_declaration_eqb (df_prototype d2) (df_prototype d1)); cbn [negb andb];
      [| split; discriminate].
    destruct (mm_list_eqb raw_id_eqb (df_args d2) (df_args d1)); cbn [negb andb];
      [| split; discriminate].
    destruct (mm_definition_eqb d2 d1 ||
              existsb (check_slice_matches_defn d1 d2) verified_slices);
      cbn [negb andb]; [exact (IH r2) | split; discriminate].
Qed.

Theorem validate_module_merge_ok_iff
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  validate_module_merge m_orig m_merged verified_slices = inr tt <->
  check_module_merge m_orig m_merged verified_slices = true.
Proof.
  unfold validate_module_merge, check_module_merge.
  destruct (mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (forallb global_no_extern_weak (m_globals m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (mm_list_eqb mm_declaration_eqb
              (non_intrinsic_decls (m_declarations m_merged))
              (non_intrinsic_decls (m_declarations m_orig)));
    cbn [negb andb]; [| split; discriminate].
  destruct (forallb decl_no_extern_weak (m_declarations m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (forallb decl_no_extern_weak (m_declarations m_merged));
    cbn [negb andb]; [| split; discriminate].
  destruct (forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (mm_nodup_raw_ids
              (List.map dc_name
                 (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig))));
    cbn [negb andb]; [| split; discriminate].
  destruct (mm_nodup_raw_ids
              (List.map dc_name
                 (m_declarations m_merged ++ List.map df_prototype (m_definitions m_merged))));
    cbn [negb andb]; [| split; discriminate].
  destruct (mm_list_eqb mm_block_addr_eqb
              (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
              (nodup block_address_eq_dec (mcfg_block_addresses m_orig)));
    cbn [negb andb]; [| split; discriminate].
  apply validate_defs_merge_ok_iff.
Qed.


(** * 3. Structural Reflection Lemmas *)

Record slice_witness_prop
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp))
  (fid : function_id)
  (m_slice_src m_slice_tgt : CFG.mcfg dtyp)
  (df_src df_tgt : definition dtyp (CFG.cfg dtyp)) : Prop :=
  { sw_fid_eq :
      dc_name (df_prototype df_orig) = fid;
    sw_src_defs :
      m_definitions m_slice_src = [df_src];
    sw_tgt_defs :
      m_definitions m_slice_tgt = [df_tgt];
    sw_src_name :
      dc_name (df_prototype df_src) = fid;
    sw_src_type :
      dc_type (df_prototype df_src) = dc_type (df_prototype df_orig);
    sw_src_param_attrs :
      dc_param_attrs (df_prototype df_src) = dc_param_attrs (df_prototype df_orig);
    sw_src_cconv :
      cconv_eqb (anns_cconv (dc_annotations (df_prototype df_src)))
                (anns_cconv (dc_annotations (df_prototype df_orig))) = true;
    sw_src_linkage_no_ew :
      dc_linkage (df_prototype df_src) <> Some LINKAGE_Extern_weak;
    sw_src_linkage_compat :
      dc_linkage (df_prototype df_src) = None \/
      dc_linkage (df_prototype df_src) = Some LINKAGE_External \/
      dc_linkage (df_prototype df_src) = dc_linkage (df_prototype df_orig);
    sw_src_args :
      df_args df_src = df_args df_orig;
    sw_src_instrs :
      df_instrs df_src = df_instrs df_orig;
    sw_tgt_name :
      dc_name (df_prototype df_tgt) = fid;
    sw_tgt_no_ew :
      dc_linkage (df_prototype df_tgt) <> Some LINKAGE_Extern_weak;
    sw_tgt_args :
      df_args df_tgt = df_args df_merged;
    sw_tgt_instrs :
      df_instrs df_tgt = df_instrs df_merged }.

Lemma check_slice_matches_defn_spec
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp))
  (fid : function_id)
  (m_slice_src m_slice_tgt : CFG.mcfg dtyp) :
  check_slice_matches_defn df_orig df_merged (fid, m_slice_src, m_slice_tgt) = true ->
  exists df_src df_tgt,
    slice_witness_prop df_orig df_merged fid m_slice_src m_slice_tgt df_src df_tgt.
Proof.
  unfold check_slice_matches_defn; cbv zeta.
  rewrite Bool.andb_true_iff, raw_id_eqb_spec.
  intros [Hfid Hm].
  destruct (m_definitions m_slice_src) as [| df_src [| ? ?]] eqn:Hsrc; try discriminate Hm.
  destruct (m_definitions m_slice_tgt) as [| df_tgt [| ? ?]] eqn:Htgt; try discriminate Hm.
  rewrite !Bool.andb_true_iff in Hm.
  destruct Hm as [[[[[[[[[[Hsn Hsty] Hspa] Hscc] Hslnk] Hsargs] Hscfg] Htn] Htew] Htargs] Htcfg].
  apply raw_id_eqb_spec in Hsn.
  apply mm_dtyp_eqb_eq in Hsty.
  apply mm_param_attrs_pair_eqb_eq in Hspa.
  apply dc_linkage_slice_compatible_spec in Hslnk as [Hs_noew Hs_compat].
  apply (mm_list_eqb_eq _ raw_id_eqb_spec) in Hsargs.
  apply mm_cfg_eqb_eq in Hscfg.
  apply raw_id_eqb_spec in Htn.
  apply opt_linkage_no_extern_weak_spec in Htew.
  apply (mm_list_eqb_eq _ raw_id_eqb_spec) in Htargs.
  apply mm_cfg_eqb_eq in Htcfg.
  exists df_src, df_tgt; constructor; (assumption + reflexivity).
Qed.

Definition defn_pair_provenance
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp)) : Prop :=
  df_prototype df_merged = df_prototype df_orig /\
  df_args df_merged = df_args df_orig /\
  (df_merged = df_orig \/
   exists fid m_slice_src m_slice_tgt df_src df_tgt,
     In (fid, m_slice_src, m_slice_tgt) verified_slices /\
     slice_witness_prop df_orig df_merged fid m_slice_src m_slice_tgt df_src df_tgt).

Lemma check_defn_pair_spec
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp)) :
  check_defn_pair verified_slices df_orig df_merged = true ->
  defn_pair_provenance verified_slices df_orig df_merged.
Proof.
  unfold check_defn_pair.
  rewrite !Bool.andb_true_iff, Bool.orb_true_iff.
  intros [[Hproto Hargs] Hdisj].
  apply mm_declaration_eqb_eq in Hproto.
  apply (mm_list_eqb_eq _ raw_id_eqb_spec) in Hargs.
  refine (conj Hproto (conj Hargs _)).
  destruct Hdisj as [Heq | Hex].
  - left; apply mm_definition_eqb_eq, Heq.
  - right; apply existsb_exists in Hex as [[[fid m_src] m_tgt] [Hin Hmatch]].
    destruct (check_slice_matches_defn_spec df_orig df_merged fid m_src m_tgt Hmatch)
      as [df_src [df_tgt Hsw]].
    exists fid, m_src, m_tgt, df_src, df_tgt; exact (conj Hin Hsw).
Qed.

Lemma check_defs_merge_Forall2
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  forall defs_orig defs_merged,
    check_defs_merge verified_slices defs_orig defs_merged = true ->
    Forall2 (defn_pair_provenance verified_slices) defs_orig defs_merged.
Proof.
  induction defs_orig as [| d1 r1 IH]; intros [| d2 r2] H;
    cbn [check_defs_merge] in H; try discriminate H.
  - constructor.
  - apply Bool.andb_true_iff in H as [Hhd Htl].
    constructor; [exact (check_defn_pair_spec verified_slices d1 d2 Hhd) | exact (IH r2 Htl)].
Qed.

Lemma check_defs_merge_prototypes_eq
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (defs_orig defs_merged : list (definition dtyp (CFG.cfg dtyp))) :
  check_defs_merge verified_slices defs_orig defs_merged = true ->
  List.map df_prototype defs_merged = List.map df_prototype defs_orig.
Proof.
  intros H; pose proof (check_defs_merge_Forall2 verified_slices defs_orig defs_merged H) as HF.
  clear H; induction HF as [| d1 d2 r1 r2 [Hpr _] _ IH]; cbn [List.map];
    [reflexivity | rewrite Hpr, IH; reflexivity].
Qed.

Theorem check_module_merge_globals_eq
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  m_globals m_merged = m_globals m_orig.
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [[[[[[[[[H _] _] _] _] _] _] _] _] _].
  exact (proj1 (mm_list_eqb_eq _ mm_global_eqb_eq _ _) H).
Qed.

Theorem check_module_merge_globals_no_extern_weak
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  Forall (fun g => g_linkage g <> Some LINKAGE_Extern_weak) (m_globals m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [[[[[[[[[_ H] _] _] _] _] _] _] _] _].
  apply Forall_forall; intros g Hg.
  rewrite forallb_forall in H; apply opt_linkage_no_extern_weak_spec, (H g Hg).
Qed.

Theorem check_module_merge_declarations_eq
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  non_intrinsic_decls (m_declarations m_merged) =
  non_intrinsic_decls (m_declarations m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros (((((((((_ & _) & H) & _) & _) & _) & _) & _) & _) & _).
  exact (proj1 (mm_list_eqb_eq _ mm_declaration_eqb_eq _ _) H).
Qed.

Theorem check_module_merge_declarations_no_extern_weak
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  Forall (fun d => dc_linkage d <> Some LINKAGE_Extern_weak) (m_declarations m_orig) /\
  Forall (fun df => dc_linkage (df_prototype df) <> Some LINKAGE_Extern_weak) (m_definitions m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros (((((((((_ & _) & _) & Hd) & _) & Hdf) & _) & _) & _) & _).
  split; apply Forall_forall.
  - intros d Hin; rewrite forallb_forall in Hd; apply opt_linkage_no_extern_weak_spec, (Hd d Hin).
  - intros df Hin; rewrite forallb_forall in Hdf; apply opt_linkage_no_extern_weak_spec, (Hdf df Hin).
Qed.

Theorem check_module_merge_symbol_nodup
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  NoDup (List.map dc_name (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig))).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros (((((((((_ & _) & _) & _) & _) & _) & Hnd) & _) & _) & _).
  exact (proj1 (mm_nodup_raw_ids_spec _) Hnd).
Qed.

Theorem check_module_merge_block_addresses_eq
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  nodup block_address_eq_dec (mcfg_block_addresses m_merged) =
  nodup block_address_eq_dec (mcfg_block_addresses m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros (((((((((_ & _) & _) & _) & _) & _) & _) & _) & H) & _).
  exact (proj1 (mm_list_eqb_eq _ mm_block_addr_eqb_eq _ _) H).
Qed.

Theorem check_module_merge_prototypes_eq
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  List.map df_prototype (m_definitions m_merged) =
  List.map df_prototype (m_definitions m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros (((((((((_ & _) & _) & _) & _) & _) & _) & _) & _) & H).
  exact (check_defs_merge_prototypes_eq verified_slices _ _ H).
Qed.

Theorem check_module_merge_defs_Forall2
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  Forall2 (defn_pair_provenance verified_slices) (m_definitions m_orig) (m_definitions m_merged).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros (((((((((_ & _) & _) & _) & _) & _) & _) & _) & _) & H).
  exact (check_defs_merge_Forall2 verified_slices _ _ H).
Qed.

Lemma allocate_declarations_non_intrinsic_eqit {Pa : Params} :
  forall ds,
    @allocate_declarations Pa ds ≅
    @allocate_declarations Pa (non_intrinsic_decls ds).
Proof.
  induction ds as [| d rest IH];
    cbn [non_intrinsic_decls List.filter allocate_declarations loop_monad];
    [reflexivity |].
  unfold allocate_declaration at 1, is_defined_intrinsic_decl.
  destruct (lookup_intrinsic_declaration (dc_name d)) eqn:Elk; cbn [negb].
  - etransitivity; [apply (Eqit.bind_ret_l tt (fun _ => loop_monad allocate_declaration rest)) | exact IH].
  - cbn [allocate_declarations loop_monad].
    unfold allocate_declaration at 2; rewrite Elk.
    unfold allocate_declarations, non_intrinsic_decls in IH.
    eapply Eqit.eqit_bind; [reflexivity | intros []; exact IH].
Qed.

Lemma build_global_environment_non_intrinsic_eqit {Pa : Params} (M1 M2 : CFG.mcfg dtyp) :
  non_intrinsic_decls (m_declarations M1) = non_intrinsic_decls (m_declarations M2) ->
  List.map df_prototype (m_definitions M1) = List.map df_prototype (m_definitions M2) ->
  nodup block_address_eq_dec (mcfg_block_addresses M1) =
  nodup block_address_eq_dec (mcfg_block_addresses M2) ->
  m_globals M1 = m_globals M2 ->
  @build_global_environment Pa M1 ≅ @build_global_environment Pa M2.
Proof.
  intros Hdecl Hpr Hba Hg.
  unfold build_global_environment.
  assert (Hall :
    forall ds1 ds2 : list (declaration dtyp),
      non_intrinsic_decls ds1 = non_intrinsic_decls ds2 ->
      @allocate_declarations Pa ds1 ≅ @allocate_declarations Pa ds2).
  { intros ds1 ds2 Hd.
    rewrite (allocate_declarations_non_intrinsic_eqit ds1),
            (allocate_declarations_non_intrinsic_eqit ds2), Hd; reflexivity. }
  assert (Hni_app :
    non_intrinsic_decls (m_declarations M1 ++ List.map df_prototype (m_definitions M1)) =
    non_intrinsic_decls (m_declarations M2 ++ List.map df_prototype (m_definitions M2))).
  { unfold non_intrinsic_decls in *; rewrite !filter_app, Hpr, Hdecl; reflexivity. }
  rewrite (Hall _ _ Hni_app), Hba, Hg; reflexivity.
Qed.

Lemma lookup_intrinsic_puts_putchar_none :
  lookup_intrinsic_declaration (Name "puts") = None /\
  lookup_intrinsic_declaration (Name "putchar") = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Lemma library_functions_non_intrinsic_eq {Pa : Params} :
  forall ds,
    @library_functions Pa ds = @library_functions Pa (non_intrinsic_decls ds).
Proof.
  intros ds; unfold library_functions, _LIBRARIES; cbn [filter].
  destruct lookup_intrinsic_puts_putchar_none as [Hputs Hputc].
  assert (Hex :
    forall n,
      (n = Name "puts" \/ n = Name "putchar") ->
      existsb (fun s => Rocqlib.proj_sumbool (Syntax.AstLib.RawIDOrd.eq_dec s n))
        (List.map (@dc_name dtyp) ds) =
      existsb (fun s => Rocqlib.proj_sumbool (Syntax.AstLib.RawIDOrd.eq_dec s n))
        (List.map (@dc_name dtyp) (non_intrinsic_decls ds))).
  { intros n Hn; induction ds as [| d rest IH];
      cbn [non_intrinsic_decls List.filter List.map existsb]; [reflexivity |].
    destruct (is_defined_intrinsic_decl d) eqn:Hid; cbn [negb existsb].
    - destruct (Syntax.AstLib.RawIDOrd.eq_dec (dc_name d) n) as [Heq | Hne]; cbn [orb];
        [| exact IH].
      exfalso; unfold is_defined_intrinsic_decl in Hid.
      rewrite Heq in Hid; destruct Hn as [-> | ->];
        [rewrite Hputs in Hid | rewrite Hputc in Hid]; discriminate Hid.
    - cbn [List.map existsb]; rewrite IH; reflexivity. }
  rewrite (Hex (Name "puts") (or_introl eq_refl)),
          (Hex (Name "putchar") (or_intror eq_refl)); reflexivity.
Qed.

Theorem check_module_merge_build_global_environment_eq
  {Pa : Params}
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (Hchk : check_module_merge m_orig m_merged verified_slices = true) :
  @build_global_environment Pa m_merged ≅ @build_global_environment Pa m_orig.
Proof.
  apply build_global_environment_non_intrinsic_eqit.
  - exact (check_module_merge_declarations_eq m_orig m_merged verified_slices Hchk).
  - exact (check_module_merge_prototypes_eq m_orig m_merged verified_slices Hchk).
  - exact (check_module_merge_block_addresses_eq m_orig m_merged verified_slices Hchk).
  - exact (check_module_merge_globals_eq m_orig m_merged verified_slices Hchk).
Qed.


(** * 4. Open-World Per-Slice Refinement & Whole-Module Compositional Linking *)

Section CompositionalLinking.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  (** General relational lifter for [cfg_local_sim] across arbitrary pairs of
      modules sharing [build_global_environment] and [m_declarations]. *)
  Lemma map_monad_address_defs_stack_sim
    (defs1 defs2 : list (definition dtyp (CFG.cfg dtyp)))
    (Hdefs : Forall2
               (fun d1 d2 =>
                  df_prototype d2 = df_prototype d1 /\
                  df_args d2 = df_args d1 /\
                  forall env va,
                    (forall x, In x (df_args d1) -> exists v, Maps.lookup x env = Some v) ->
                    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                      env env (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
               defs1 defs2) :
    forall stk env1 env2,
      mcfg_stack_sim
        (fun stk' e1' e2' l1 l2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_stack_sim
                    (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                    s0 a1 a2 (fn1 cc args) (fn2 cc args))
             l1 l2)
        stk env1 env2
        (map_monad address_one_function defs1)
        (map_monad address_one_function defs2).
  Proof using.
    induction Hdefs as [| d1 d2 r1 r2 (Hpr & Har & Hbd) _ IH];
      intros stk env1 env2; cbn [map_monad].
    - apply gen_stack_sim_ret; repeat split; constructor.
    - eapply gen_stack_sim_bind with
        (RR := fun stk' e1' e2'
                 (p1 p2 : Z * @function_denotation (@ParamsV IP IPT)) =>
                 stk' = stk /\ e1' = env1 /\ e2' = env2 /\
                 fst p1 = fst p2 /\
                 forall s0 a1 a2 cc args,
                   cfg_stack_sim
                     (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                     s0 a1 a2 (snd p1 cc args) (snd p2 cc args)).
      + unfold address_one_function; rewrite Hpr.
        eapply gen_stack_sim_bind.
        * unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? fv _ (-> & -> & -> & <-).
          destruct fv as [[p | | | | | | |] | |];
            try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
                 [reflexivity | apply EqE_MCFG_refl]).
          apply gen_stack_sim_ret; cbn [fst snd]; repeat split; try reflexivity.
          apply cfg_stack_sim_denote_function;
            [symmetry; exact Hpr | symmetry; exact Har | exact Hbd].
      + intros ? ? ? [k1 fn1] [k2 fn2] (-> & -> & -> & Hk & Hhd); cbn [fst snd] in Hk, Hhd.
        eapply gen_stack_sim_bind; [apply IH |].
        intros ? ? ? tl1 tl2 (-> & -> & -> & Htl).
        apply gen_stack_sim_ret; repeat split; constructor; [split; assumption | assumption].
  Qed.

  Definition mm_mrec_ctx
    (fundefs : IntMap (@function_denotation (@ParamsV IP IPT)))
    : @CallE (@ParamsV IP IPT) ~> @CFGtop (@ParamsV IP IPT) :=
    fun T call_ev =>
      match call_ev with
      | Call dt cc fv args =>
          @ExtLib.Structures.Monad.bind (@CFGtop (@ParamsV IP IPT)) _ _ _
            (EOU_to_itree (check_callee fv))
            (fun _ =>
               match lookup_defn fv fundefs with
               | Some f_den => f_den cc args
               | None => Functor.fmap inr (external_call dt fv args)
               end)
      end.

  Lemma module_defs_cfg_sim_refines
    (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M1 ≅
           @build_global_environment (@ParamsV IP IPT) M2)
    (Hdecls : non_intrinsic_decls (m_declarations M2) =
              non_intrinsic_decls (m_declarations M1))
    (Hdefs : Forall2
               (fun d1 d2 =>
                  df_prototype d2 = df_prototype d1 /\
                  df_args d2 = df_args d1 /\
                  forall env va,
                    (forall x, In x (df_args d1) -> exists v, Maps.lookup x env = Some v) ->
                    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                      env env (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
               (m_definitions M1) (m_definitions M2)) :
    @prog_refines IP IPT M1 M2.
  Proof using.
    intros ret_typ entry args U.
    unfold run_mcfg_model, interp_mcfg_model.
    eapply refine_prov_antitone with (U := U);
      [| apply incl_refl
       | eapply mcfg_stack_sim_to_model with
           (RR := fun _ _ _ r1 r2 => r1 = r2) (stk := []) (env1 := Maps.empty) (env2 := Maps.empty)];
      [intros _ _ [s1 r1] [s2 r2] _ (_ & _ & _ & _ & <-); reflexivity | ..].
    { unfold init_fused_state, fused_state_match; repeat split; try reflexivity; constructor. }
    apply mcfg_stack_sim_interp_intrinsics.
    unfold denote_vellvm.
    assert (Hlibs_eq :
      library_functions (m_declarations M2) = library_functions (m_declarations M1)).
    { rewrite (library_functions_non_intrinsic_eq (m_declarations M2)),
              (library_functions_non_intrinsic_eq (m_declarations M1)), Hdecls;
        reflexivity. }
    rewrite Hlibs_eq.
    eapply gen_stack_sim_bind.
    { eapply gen_stack_sim_obs_eq;
        [reflexivity | exact Hbg
         | apply mcfg_stack_sim_refl_diag; constructor]. }
    intros stk1 e1 e2 [] _ (_ & <- & _).
    eapply gen_stack_sim_bind;
      [apply (map_monad_address_defs_stack_sim _ _ Hdefs) |].
    intros ? ? ? defns1 defns2 (-> & -> & -> & Hdefns).
    eapply gen_stack_sim_bind;
      [apply (map_monad_address_library_stack_sim _
                (library_functions_stack_sync (m_declarations M1))) |].
    intros ? ? ? libs1 libs2 (-> & -> & -> & Hlibs).
    eapply gen_stack_sim_bind.
    { unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]. }
    intros ? ? ? addr _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    - assert (Hmrec_eq : forall fundefs,
                denote_mcfg fundefs ret_typ addr args =
                interp_mrec (mm_mrec_ctx fundefs)
                  (mm_mrec_ctx fundefs _ (Call ret_typ CC_Ccc addr args)))
        by (intros fundefs; unfold denote_mcfg, mrec; reflexivity).
      rewrite !Hmrec_eq.
      assert (Hctx : forall k,
                option_rel
                  (fun f1 f2 =>
                     forall stk env1 env2 cc fargs,
                       cfg_stack_sim
                         (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                         stk env1 env2 (f1 cc fargs) (f2 cc fargs))
                  (lookup k (IntMaps.IP.of_list (defns1 ++ libs1)))
                  (lookup k (IntMaps.IP.of_list (defns2 ++ libs2)))).
      { apply of_list_fn_ctx_stack_sim, Forall2_app; assumption. }
      eapply cfg_to_mcfg_stack_sim_mrec with
        (ctx1 := IntMaps.IP.of_list (defns1 ++ libs1))
        (ctx2 := IntMaps.IP.of_list (defns2 ++ libs2));
        [exact Hctx | reflexivity | reflexivity |].
      unfold mm_mrec_ctx; cbn [ExtLib.Structures.Monad.bind Monad_itree].
      eapply gen_stack_sim_bind;
        [apply cfg_stack_sim_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
      assert (Hext :
        cfg_stack_sim
          (fun stk' e1' e2' r1 r2 => stk' = stk1 /\ e1' = e1 /\ e2' = e1 /\ r1 = r2)
          stk1 e1 e1
          (Functor.fmap (@inr (@exc (@ParamsV IP IPT)) _) (external_call ret_typ addr args))
          (Functor.fmap (@inr (@exc (@ParamsV IP IPT)) _) (external_call ret_typ addr args))).
      { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
        eapply gen_stack_sim_bind.
        - apply gen_stack_sim_trigger_sync; [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
        - intros ? ? ? dv _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity. }
      unfold lookup_defn.
      destruct addr as [[p | | | | | | |] | |]; try exact Hext.
      pose proof (Hctx (ptr_to_int p)) as Hlk.
      destruct Hlk as [| f1 f2 Hf12]; [exact Hext | apply Hf12].
    - intros ? ? ? rv _ (-> & -> & -> & <-).
      destruct rv as [ex | v].
      + unfold raiseLLVM, trigger_cast, ITree.trigger; pstep; apply GSS_Step;
          unfold gss_step_body; rewrite !observe_bind; cbn.
        right; left; split; [reflexivity | split; [reflexivity | intros [] [] _ _]].
      + apply gen_stack_sim_ret; reflexivity.
  Qed.

  (** General relational lifter for [refine_cfg Logic.eq] ([ruttc]) across
      arbitrary pairs of modules sharing [build_global_environment] and
      [m_declarations]. *)
  Lemma map_monad_address_defs_refines
    (defs1 defs2 : list (definition dtyp (CFG.cfg dtyp)))
    (Hdefs : Forall2
               (fun d1 d2 =>
                  df_prototype d2 = df_prototype d1 /\
                  df_args d2 = df_args d1 /\
                  forall va,
                    @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                      (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
               defs1 defs2) :
    refine_mcfg
      (Forall2
         (fun '(k1, fn1) '(k2, fn2) =>
            k1 = k2 /\
            forall cc args, refine_cfg Logic.eq (fn1 cc args) (fn2 cc args)))
      (map_monad address_one_function defs1)
      (map_monad address_one_function defs2).
  Proof using.
    induction Hdefs as [| d1 d2 r1 r2 (Hpr & Har & Hbd) _ IH]; cbn [map_monad].
    - apply ruttc_ret; constructor.
    - eapply ruttc_bind with
        (RR := fun '(k1, fn1) '(k2, fn2) =>
                 k1 = k2 /\
                 forall cc args, refine_cfg Logic.eq (fn1 cc args) (fn2 cc args)).
      + unfold address_one_function; rewrite Hpr.
        eapply ruttc_bind; [apply refine_mcfg_refl | intros fv _ <-].
        destruct fv as [[p | | | | | | |] | |];
          [| unfold raise, trigger_cast; eapply ruttc_trigger';
               [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _] ..].
        apply ruttc_ret; split; [reflexivity |].
        apply refine_cfg_denote_function;
          [symmetry; exact Hpr | symmetry; exact Har | exact Hbd].
      + intros [k1 fn1] [k2 fn2] Hhd.
        eapply ruttc_bind; [exact IH | intros tl1 tl2 Htl; apply ruttc_ret; constructor; assumption].
  Qed.

  Lemma module_defs_ruttc_refines
    (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hdefs : Forall2
               (fun d1 d2 =>
                  df_prototype d2 = df_prototype d1 /\
                  df_args d2 = df_args d1 /\
                  forall va,
                    @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                      (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
               (m_definitions M1) (m_definitions M2)) :
    @prog_refines IP IPT M1 M2.
  Proof using.
    apply refine_vellvm_to_prog; intros ret_typ entry args.
    unfold denote_vellvm; rewrite Hbg, Hdecls.
    eapply ruttc_bind; [apply refine_mcfg_refl | intros [] _ <-].
    eapply ruttc_bind; [exact (map_monad_address_defs_refines _ _ Hdefs) |].
    intros defns1 defns2 Hdefns.
    eapply ruttc_bind; [apply refine_mcfg_refl | intros libs _ <-].
    eapply ruttc_bind; [apply refine_mcfg_refl | intros addr _ <-].
    eapply ruttc_bind.
    - apply refine_mcfg_denote_mcfg, of_list_fn_ctx_refines.
      apply Forall2_app; [exact Hdefns | apply Forall2_fn_refl].
    - intros rv _ <-; destruct rv; apply refine_mcfg_refl.
  Qed.

  (** Open-world per-CFG refinement contract for a verified slice
      [(fid, m_slice_src, m_slice_tgt)]: at the [denote_cfg] level, [CallE],
      [MemoryE], [IntrinsicE], [GlobalE], [StackE], and [LLVMExcE] are all
      uninterpreted events, so [cfg_local_sim] makes zero closed-world
      assumptions about sibling callees or external calls (closing F-33). *)
  Definition slice_body_refines
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : Prop :=
    let '(_, m_slice_src, m_slice_tgt) := entry in
    forall df_src df_tgt,
      m_definitions m_slice_src = [df_src] ->
      m_definitions m_slice_tgt = [df_tgt] ->
      forall (env : @local_env (@ParamsV IP IPT))
             (va : option (@ptr (@PROV (@ParamsV IP IPT)) (@PTR (@ParamsV IP IPT)))),
        (forall x, In x (df_args df_src) -> exists v, Maps.lookup x env = Some v) ->
        cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
          env env (denote_cfg (df_instrs df_src) va) (denote_cfg (df_instrs df_tgt) va).

  Definition slice_ruttc_refines
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : Prop :=
    let '(_, m_slice_src, m_slice_tgt) := entry in
    forall df_src df_tgt,
      m_definitions m_slice_src = [df_src] ->
      m_definitions m_slice_tgt = [df_tgt] ->
      forall va : option (@ptr (@PROV (@ParamsV IP IPT)) (@PTR (@ParamsV IP IPT))),
        @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
          (denote_cfg (df_instrs df_src) va) (denote_cfg (df_instrs df_tgt) va).

  (** Master Open-World Compositional Module-Merge Refinement Theorem:
      If [check_module_merge m_orig m_merged verified_slices = true] and every
      slice in [verified_slices] satisfies [slice_body_refines], then
      [m_merged] refines [m_orig] under whole-module Vellvm 3.0 model
      semantics [@prog_refines IP IPT]. *)
  Theorem check_module_merge_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge m_orig m_merged verified_slices = true)
    (Hslices : Forall slice_body_refines verified_slices) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    apply module_defs_cfg_sim_refines.
    - symmetry; exact (check_module_merge_build_global_environment_eq m_orig m_merged verified_slices Hchk).
    - exact (check_module_merge_declarations_eq m_orig m_merged verified_slices Hchk).
    - pose proof (check_module_merge_defs_Forall2 m_orig m_merged verified_slices Hchk) as Hprov.
      induction Hprov as [| df_orig df_merged r1 r2 (Hpr & Har & Hdisj) _ IH];
        [constructor | constructor; [| exact IH]].
      refine (conj Hpr (conj Har _)).
      intros env va Henv.
      destruct Hdisj as [-> | (fid & m_src & m_tgt & df_src & df_tgt & Hin & Hsw)].
      + apply SCCP.denote_cfg_refl_sim.
      + rewrite Forall_forall in Hslices.
        pose proof (Hslices (fid, m_src, m_tgt) Hin df_src df_tgt
                      (sw_src_defs _ _ _ _ _ _ _ Hsw)
                      (sw_tgt_defs _ _ _ _ _ _ _ Hsw)
                      env va) as Hsim.
        rewrite (sw_src_args _ _ _ _ _ _ _ Hsw),
                (sw_src_instrs _ _ _ _ _ _ _ Hsw),
                (sw_tgt_instrs _ _ _ _ _ _ _ Hsw) in Hsim.
        exact (Hsim Henv).
  Qed.

  Theorem check_module_merge_ruttc_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge m_orig m_merged verified_slices = true)
    (Hslices : Forall slice_ruttc_refines verified_slices) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    pose proof (check_module_merge_globals_eq m_orig m_merged verified_slices Hchk) as Hglob.
    pose proof (check_module_merge_declarations_eq m_orig m_merged verified_slices Hchk) as Hdecl.
    pose proof (check_module_merge_prototypes_eq m_orig m_merged verified_slices Hchk) as Hpr.
    pose proof (check_module_merge_block_addresses_eq m_orig m_merged verified_slices Hchk) as Hba.
    set (m_mid :=
      {| m_name         := m_name m_merged;
         m_target       := m_target m_merged;
         m_datalayout   := m_datalayout m_merged;
         m_type_defs    := m_type_defs m_merged;
         m_globals      := m_globals m_merged;
         m_declarations := m_declarations m_orig;
         m_definitions  := m_definitions m_merged |}).
    eapply prog_refines_trans with (M2 := m_mid).
    - apply module_defs_ruttc_refines.
      + unfold build_global_environment.
        change (mcfg_block_addresses m_mid) with (mcfg_block_addresses m_merged).
        cbn [m_declarations m_definitions m_globals m_mid].
        rewrite Hpr, Hba, Hglob; reflexivity.
      + reflexivity.
      + cbn [m_definitions m_mid].
        pose proof (check_module_merge_defs_Forall2 m_orig m_merged verified_slices Hchk) as Hprov.
        eapply Forall2_impl; [| exact Hprov].
        intros df_orig df_merged (Hpr1 & Har1 & Hdisj).
        refine (conj Hpr1 (conj Har1 _)).
        intros va; destruct Hdisj as [-> | (fid & m_src & m_tgt & df_src & df_tgt & Hin & Hsw)].
        * apply refine_cfg_refl.
        * rewrite Forall_forall in Hslices.
          pose proof (Hslices (fid, m_src, m_tgt) Hin df_src df_tgt
                        (sw_src_defs _ _ _ _ _ _ _ Hsw)
                        (sw_tgt_defs _ _ _ _ _ _ _ Hsw)
                        va) as Hsim.
          rewrite (sw_src_instrs _ _ _ _ _ _ _ Hsw),
                  (sw_tgt_instrs _ _ _ _ _ _ _ Hsw) in Hsim.
          exact Hsim.
    - apply module_defs_cfg_sim_refines.
      + apply build_global_environment_non_intrinsic_eqit; cbn; try reflexivity.
        symmetry; exact Hdecl.
      + exact Hdecl.
      + clear; induction (m_definitions m_merged) as [| d r IH]; constructor; [| exact IH].
        refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
        intros env va _; apply SCCP.denote_cfg_refl_sim.
  Qed.

  Corollary validate_module_merge_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hval : validate_module_merge m_orig m_merged verified_slices = inr tt)
    (Hslices : Forall slice_body_refines verified_slices) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    apply (check_module_merge_refines m_orig m_merged verified_slices);
      [exact (proj1 (validate_module_merge_ok_iff m_orig m_merged verified_slices) Hval)
      | exact Hslices].
  Qed.

End CompositionalLinking.

(** Concrete instantiations at [IPZ] and [IP64Bit], plus end-to-end
    [IPZ -> IPZ -> IP64Bit] composition with [I2F_toplevel.model_refine]. *)
Theorem check_module_merge_refines_IPZ
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (Hchk : check_module_merge m_orig m_merged verified_slices = true)
  (Hslices : Forall (@slice_body_refines IPZ IPZTheory) verified_slices) :
  @prog_refines IPZ IPZTheory m_orig m_merged.
Proof.
  exact (@check_module_merge_refines IPZ IPZTheory m_orig m_merged verified_slices Hchk Hslices).
Qed.

Theorem check_module_merge_refines_64
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (Hchk : check_module_merge m_orig m_merged verified_slices = true)
  (Hslices : Forall (@slice_body_refines IP64Bit IP64BitTheory) verified_slices) :
  @prog_refines IP64Bit IP64BitTheory m_orig m_merged.
Proof.
  exact (@check_module_merge_refines IP64Bit IP64BitTheory m_orig m_merged verified_slices Hchk Hslices).
Qed.

Theorem check_module_merge_I2F_model_refine
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (ret_typ : dtyp) (entry : function_id)
  (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
  (s1 : @FusedS PInf) (s2 : @FusedS PFin)
  (Hchk : check_module_merge m_orig m_merged verified_slices = true)
  (Hslices : Forall (@slice_body_refines IPZ IPZTheory) verified_slices)
  (Hargs : Forall2 I2F_dvalue args1 args2)
  (Hs : I2F_FusedS s1 s2) :
  @prog_refines IPZ IPZTheory m_orig m_merged /\
  I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
    (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 m_merged) s1)
    (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 m_merged) s2).
Proof.
  split.
  - exact (check_module_merge_refines_IPZ m_orig m_merged verified_slices Hchk Hslices).
  - exact (@I2F_toplevel.model_refine ret_typ entry args1 args2 m_merged s1 s2 Hargs Hs).
Qed.

Corollary validate_module_merge_I2F_model_refine
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (ret_typ : dtyp) (entry : function_id)
  (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
  (s1 : @FusedS PInf) (s2 : @FusedS PFin)
  (Hval : validate_module_merge m_orig m_merged verified_slices = inr tt)
  (Hslices : Forall (@slice_body_refines IPZ IPZTheory) verified_slices)
  (Hargs : Forall2 I2F_dvalue args1 args2)
  (Hs : I2F_FusedS s1 s2) :
  @prog_refines IPZ IPZTheory m_orig m_merged /\
  I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
    (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 m_merged) s1)
    (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 m_merged) s2).
Proof.
  exact (check_module_merge_I2F_model_refine m_orig m_merged verified_slices
           ret_typ entry args1 args2 s1 s2
           (proj1 (validate_module_merge_ok_iff m_orig m_merged verified_slices) Hval)
           Hslices Hargs Hs).
Qed.


(** * 5. Safe-Path [Pipeline.optimize_mcfg] & Heterogeneous Slice Splicing (F-20) *)

Section SafePathSlices.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  (** Direct [slice_body_refines] instances for [SCCP] and [DCE] single-CFG
      passes, plus [slice_ruttc_refines] for [SimplifyCFG] sub-passes. *)
  Lemma sccp_mcfg_satisfies_slice_body_refines
    (fid : function_id) (M : CFG.mcfg dtyp) :
    slice_body_refines (fid, M, sccp_mcfg M).
  Proof using.
    intros df_src df_tgt Hsrc Htgt env va Henv.
    unfold sccp_mcfg, map_mcfg_with_args in Htgt; rewrite Hsrc in Htgt.
    cbn [m_definitions List.map map_defn_with_args] in Htgt.
    injection Htgt as <-; cbn [df_instrs].
    exact (SCCP.sccp_cfg_sim (df_args df_src) (df_instrs df_src) env va Henv).
  Qed.

  Lemma dce_mcfg_once_satisfies_slice_body_refines
    (fid : function_id) (M : CFG.mcfg dtyp) :
    slice_body_refines (fid, M, dce_mcfg_once M).
  Proof using.
    intros df_src df_tgt Hsrc Htgt env va Henv.
    unfold dce_mcfg_once, map_mcfg_with_args in Htgt; rewrite Hsrc in Htgt.
    cbn [m_definitions List.map map_defn_with_args] in Htgt.
    injection Htgt as <-; cbn [df_instrs].
    exact (DCE.dce_cfg_once_sim (df_args df_src) (df_instrs df_src) env va Henv).
  Qed.

  (** Universal contextual splicing contract for a verified single-function
      slice: replacing [c_src] with [c_tgt] inside ANY host module [M_host]
      refines [M_host] and preserves [blockaddress] tables. *)
  Definition splice_valid_defn
    (fargs : list local_id) (c_src c_tgt : CFG.cfg dtyp) : Prop :=
    flat_map block_block_addresses (blks c_tgt) =
      flat_map block_block_addresses (blks c_src) /\
    forall (M_host : CFG.mcfg dtyp)
           (pre post : list (definition dtyp (CFG.cfg dtyp)))
           (proto : declaration dtyp),
      m_definitions M_host =
        pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c_src |} :: post ->
      @prog_refines IP IPT M_host
        {| m_name         := m_name M_host;
           m_target       := m_target M_host;
           m_datalayout   := m_datalayout M_host;
           m_type_defs    := m_type_defs M_host;
           m_globals      := m_globals M_host;
           m_declarations := m_declarations M_host;
           m_definitions  :=
             pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c_tgt |} :: post |}.

  Definition slice_valid_in_any_host
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : Prop :=
    let '(_, m_slice_src, m_slice_tgt) := entry in
    forall df_src df_tgt,
      m_definitions m_slice_src = [df_src] ->
      m_definitions m_slice_tgt = [df_tgt] ->
      splice_valid_defn (df_args df_src) (df_instrs df_src) (df_instrs df_tgt).

  Lemma splice_valid_defn_refl (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c c.
  Proof using.
    split; [reflexivity |].
    intros M_host pre post proto Hdefs.
    rewrite <- Hdefs; destruct M_host; cbn; apply prog_refines_refl.
  Qed.

  Lemma splice_valid_defn_trans
    (fargs : list local_id) (c1 c2 c3 : CFG.cfg dtyp) :
    splice_valid_defn fargs c1 c2 ->
    splice_valid_defn fargs c2 c3 ->
    splice_valid_defn fargs c1 c3.
  Proof using.
    intros [Hba12 Href12] [Hba23 Href23].
    split; [etransitivity; [exact Hba23 | exact Hba12] |].
    intros M_host pre post proto Hdefs.
    eapply prog_refines_trans.
    - exact (Href12 M_host pre post proto Hdefs).
    - exact (Href23
               {| m_name         := m_name M_host;
                  m_target       := m_target M_host;
                  m_datalayout   := m_datalayout M_host;
                  m_type_defs    := m_type_defs M_host;
                  m_globals      := m_globals M_host;
                  m_declarations := m_declarations M_host;
                  m_definitions  :=
                    pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c2 |} :: post |}
               pre post proto Logic.eq_refl).
  Qed.

  Lemma build_global_env_splice_eq
    (M_host : CFG.mcfg dtyp)
    (pre post : list (definition dtyp (CFG.cfg dtyp)))
    (proto : declaration dtyp)
    (fargs : list local_id)
    (c1 c2 : CFG.cfg dtyp)
    (Hdefs : m_definitions M_host =
               pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c1 |} :: post)
    (Hba : flat_map block_block_addresses (blks c2) =
           flat_map block_block_addresses (blks c1)) :
    @build_global_environment (@ParamsV IP IPT)
      {| m_name         := m_name M_host;
         m_target       := m_target M_host;
         m_datalayout   := m_datalayout M_host;
         m_type_defs    := m_type_defs M_host;
         m_globals      := m_globals M_host;
         m_declarations := m_declarations M_host;
         m_definitions  :=
           pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c2 |} :: post |} =
    @build_global_environment (@ParamsV IP IPT) M_host.
  Proof using.
    apply Mem2Reg.build_global_environment_defs_eq.
    - rewrite Hdefs, !map_app; cbn [List.map df_prototype]; reflexivity.
    - rewrite Hdefs, !flat_map_app; cbn [flat_map df_instrs]; rewrite Hba; reflexivity.
  Qed.

  Lemma splice_valid_of_cfg_local_sim
    (fargs : list local_id) (c1 c2 : CFG.cfg dtyp)
    (Hba : flat_map block_block_addresses (blks c2) =
           flat_map block_block_addresses (blks c1))
    (Hsim : forall env va,
              (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
              cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                env env (denote_cfg c1 va) (denote_cfg c2 va)) :
    splice_valid_defn fargs c1 c2.
  Proof using.
    split; [exact Hba |].
    intros M_host pre post proto Hdefs.
    apply module_defs_cfg_sim_refines.
    - rewrite (build_global_env_splice_eq M_host pre post proto fargs c1 c2 Hdefs Hba);
        reflexivity.
    - reflexivity.
    - rewrite Hdefs; cbn [m_definitions].
      assert (Hrefl : forall ds,
                Forall2
                  (fun d1 d2 : definition dtyp (CFG.cfg dtyp) =>
                     df_prototype d2 = df_prototype d1 /\
                     df_args d2 = df_args d1 /\
                     forall env va,
                       (forall x, In x (df_args d1) -> exists v, Maps.lookup x env = Some v) ->
                       cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                         env env (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
                  ds ds).
      { induction ds as [| d rest IH]; constructor; [| exact IH].
        refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
        intros env va _; apply SCCP.denote_cfg_refl_sim. }
      apply Forall2_app; [apply Hrefl |].
      constructor; [| apply Hrefl].
      exact (conj Logic.eq_refl (conj Logic.eq_refl Hsim)).
  Qed.

  Lemma splice_valid_of_ruttc
    (fargs : list local_id) (c1 c2 : CFG.cfg dtyp)
    (Hba : flat_map block_block_addresses (blks c2) =
           flat_map block_block_addresses (blks c1))
    (Hsim : forall va,
              @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                (denote_cfg c1 va) (denote_cfg c2 va)) :
    splice_valid_defn fargs c1 c2.
  Proof using.
    split; [exact Hba |].
    intros M_host pre post proto Hdefs.
    apply module_defs_ruttc_refines.
    - exact (build_global_env_splice_eq M_host pre post proto fargs c1 c2 Hdefs Hba).
    - reflexivity.
    - rewrite Hdefs; cbn [m_definitions].
      assert (Hrefl : forall ds,
                Forall2
                  (fun d1 d2 : definition dtyp (CFG.cfg dtyp) =>
                     df_prototype d2 = df_prototype d1 /\
                     df_args d2 = df_args d1 /\
                     forall va,
                       @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                         (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
                  ds ds).
      { induction ds as [| d rest IH]; constructor; [| exact IH].
        refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
        intros va; apply refine_cfg_refl. }
      apply Forall2_app; [apply Hrefl |].
      constructor; [| apply Hrefl].
      exact (conj Logic.eq_refl (conj Logic.eq_refl Hsim)).
  Qed.

  Lemma slice_body_refines_to_valid_in_any_host
    (fid : function_id) (m_src m_tgt : CFG.mcfg dtyp)
    (Hba : forall df_src df_tgt,
             m_definitions m_src = [df_src] ->
             m_definitions m_tgt = [df_tgt] ->
             flat_map block_block_addresses (blks (df_instrs df_tgt)) =
             flat_map block_block_addresses (blks (df_instrs df_src)))
    (Hbody : slice_body_refines (fid, m_src, m_tgt)) :
    slice_valid_in_any_host (fid, m_src, m_tgt).
  Proof using.
    intros df_src df_tgt Hsrc Htgt.
    exact (splice_valid_of_cfg_local_sim (df_args df_src)
             (df_instrs df_src) (df_instrs df_tgt)
             (Hba df_src df_tgt Hsrc Htgt)
             (Hbody df_src df_tgt Hsrc Htgt)).
  Qed.

  (** Sequential Heterogeneous Module-Merge Refinement Theorem:
      Lifts [check_module_merge] when each verified slice satisfies
      [slice_valid_in_any_host] (covering [cfg_local_sim], [ruttc], AND
      Safe-Path [Pipeline.optimize_mcfg] including [Mem2Reg]). *)
  Theorem check_module_merge_universal_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge m_orig m_merged verified_slices = true)
    (Hslices : Forall slice_valid_in_any_host verified_slices) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    pose proof (check_module_merge_globals_eq m_orig m_merged verified_slices Hchk) as Hglob.
    pose proof (check_module_merge_declarations_eq m_orig m_merged verified_slices Hchk) as Hdecl.
    pose proof (check_module_merge_block_addresses_eq m_orig m_merged verified_slices Hchk) as Hba.
    pose proof (check_module_merge_prototypes_eq m_orig m_merged verified_slices Hchk) as Hpr.
    pose proof (check_module_merge_defs_Forall2 m_orig m_merged verified_slices Hchk) as Hprov.
    assert (Hstep :
      forall pre r_orig r_merged,
        Forall2 (defn_pair_provenance verified_slices) r_orig r_merged ->
        @prog_refines IP IPT
          {| m_name         := m_name m_orig;
             m_target       := m_target m_orig;
             m_datalayout   := m_datalayout m_orig;
             m_type_defs    := m_type_defs m_orig;
             m_globals      := m_globals m_orig;
             m_declarations := m_declarations m_orig;
             m_definitions  := pre ++ r_orig |}
          {| m_name         := m_name m_orig;
             m_target       := m_target m_orig;
             m_datalayout   := m_datalayout m_orig;
             m_type_defs    := m_type_defs m_orig;
             m_globals      := m_globals m_orig;
             m_declarations := m_declarations m_orig;
             m_definitions  := pre ++ r_merged |}).
    { intros pre r_orig; revert pre.
      induction r_orig as [| d1 r1 IH]; intros pre [| d2 r2] HF;
        inversion HF as [| ? ? ? ? (Hpr_i & Har & Hdisj) HF_tl]; subst.
      - apply prog_refines_refl.
      - destruct Hdisj as [-> | (fid & m_src & m_tgt & df_src & df_tgt & Hin & Hsw)].
        + change (pre ++ d1 :: r1) with (pre ++ [d1] ++ r1).
          change (pre ++ d1 :: r2) with (pre ++ [d1] ++ r2).
          rewrite !app_assoc; exact (IH (pre ++ [d1]) r2 HF_tl).
        + rewrite Forall_forall in Hslices.
          destruct (Hslices (fid, m_src, m_tgt) Hin df_src df_tgt
                      (sw_src_defs _ _ _ _ _ _ _ Hsw)
                      (sw_tgt_defs _ _ _ _ _ _ _ Hsw))
            as [_ Hsplice].
          assert (Hd1 :
            d1 = {| df_prototype := df_prototype d1;
                    df_args      := df_args df_src;
                    df_instrs    := df_instrs df_src |}).
          { destruct d1; cbn in *.
            rewrite (sw_src_args _ _ _ _ _ _ _ Hsw), (sw_src_instrs _ _ _ _ _ _ _ Hsw); reflexivity. }
          assert (Hd2 :
            d2 = {| df_prototype := df_prototype d1;
                    df_args      := df_args df_src;
                    df_instrs    := df_instrs df_tgt |}).
          { destruct d2; cbn in *.
            rewrite (sw_src_args _ _ _ _ _ _ _ Hsw), (sw_tgt_instrs _ _ _ _ _ _ _ Hsw),
                    <- Har, <- Hpr_i; reflexivity. }
          eapply prog_refines_trans.
          * eapply (Hsplice _ pre r1 (df_prototype d1)).
            cbn [m_definitions]; rewrite <- Hd1; reflexivity.
          * cbn [m_name m_target m_datalayout m_type_defs m_globals m_declarations].
            rewrite <- Hd2.
            change (pre ++ d2 :: r1) with (pre ++ [d2] ++ r1).
            change (pre ++ d2 :: r2) with (pre ++ [d2] ++ r2).
            rewrite !app_assoc; exact (IH (pre ++ [d2]) r2 HF_tl). }
    eapply prog_refines_trans.
    - destruct m_orig; exact (Hstep [] _ _ Hprov).
    - cbn [app].
      apply module_defs_cfg_sim_refines.
      + apply build_global_environment_non_intrinsic_eqit; cbn.
        * symmetry; exact Hdecl.
        * reflexivity.
        * unfold mcfg_block_addresses; cbn; rewrite Hglob; reflexivity.
        * symmetry; exact Hglob.
      + cbn; exact Hdecl.
      + cbn; clear; induction (m_definitions m_merged) as [| d r IH]; constructor; [| exact IH].
        refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
        intros env va _; apply SCCP.denote_cfg_refl_sim.
  Qed.

  (** ** Proof that [Pipeline.optimize_mcfg] on a Safe Single-Function Slice
         Satisfies [slice_valid_in_any_host] (Closing F-20) *)

  (** Single-definition modules have no distinct internal callees, so
      [InlineSpec.inline_mcfg] is an exact syntactic identity. *)
  Lemma match_inlinable_call_single_def_none
    (df : definition dtyp (CFG.cfg dtyp))
    (im : instr_id * instr dtyp * list (metadata dtyp)) :
    InlineSpec.match_inlinable_call_instr [df] (dc_name (df_prototype df)) im = None.
  Proof using.
    unfold InlineSpec.match_inlinable_call_instr.
    destruct im as [[iid ins] md].
    destruct ins as [| | [ret_dt fn_e] call_args call_anns obs | | | | | | | |];
      try reflexivity.
    destruct fn_e; try reflexivity.
    destruct id as [callee_gid |]; try reflexivity.
    destruct obs; [| reflexivity].
    cbn [InlineSpec.find_defn_by_gid].
    destruct (raw_id_eqb (dc_name (df_prototype df)) callee_gid); reflexivity.
  Qed.

  Lemma find_call_in_code_single_def_none
    (df : definition dtyp (CFG.cfg dtyp))
    (acc : code dtyp) (cd : code dtyp) :
    InlineSpec.find_call_in_code [df] (dc_name (df_prototype df)) acc cd = None.
  Proof using.
    revert acc; induction cd as [| im rest IH]; intros acc;
      cbn [InlineSpec.find_call_in_code]; [reflexivity |].
    rewrite match_inlinable_call_single_def_none; exact (IH (im :: acc)).
  Qed.

  Lemma find_call_in_blks_single_def_none
    (df : definition dtyp (CFG.cfg dtyp))
    (all_bks acc : ocfg dtyp) (bks : ocfg dtyp) :
    InlineSpec.find_call_in_blks [df] (dc_name (df_prototype df)) all_bks acc bks = None.
  Proof using.
    revert acc; induction bks as [| bk rest IH]; intros acc;
      cbn [InlineSpec.find_call_in_blks]; [reflexivity |].
    destruct (InlineSpec.block_in_cfg_loop all_bks bk); [exact (IH (bk :: acc)) |].
    rewrite find_call_in_code_single_def_none; exact (IH (bk :: acc)).
  Qed.

  Lemma inline_one_site_single_def_id (M : CFG.mcfg dtyp)
    (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    inline_one_site_mcfg M = M.
  Proof using.
    intros Hdefs; unfold inline_one_site_mcfg.
    destruct (InlineSpec.is_hygienic_module M); [| reflexivity].
    rewrite Hdefs; cbn [InlineSpec.inline_first_in_defs].
    destruct (InlineSpec.is_inlinable_caller df); [| reflexivity].
    rewrite find_call_in_blks_single_def_none; reflexivity.
  Qed.

  Lemma inline_mcfg_single_def_id (M : CFG.mcfg dtyp)
    (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    inline_mcfg M = M.
  Proof using.
    intros Hdefs; unfold inline_mcfg.
    assert (Hiter : forall fuel (M0 : CFG.mcfg dtyp),
              m_definitions M0 = [df] -> InlineSpec.inline_iter fuel M0 = M0).
    { induction fuel as [| fuel' IH]; intros M0 HM0; cbn [InlineSpec.inline_iter]; [reflexivity |].
      rewrite (inline_one_site_single_def_id M0 df HM0); exact (IH M0 HM0). }
    exact (Hiter InlineSpec.inline_default_fuel M Hdefs).
  Qed.

  (** Splicing lemmas for [sccp_mcfg], [dce_mcfg], and [simplifycfg_mcfg]. *)
  Lemma map_mcfg_cfg_single_def
    (f : CFG.cfg dtyp -> CFG.cfg dtyp) (M : CFG.mcfg dtyp)
    (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    m_definitions (map_mcfg_cfg f M) =
      [{| df_prototype := df_prototype df;
          df_args      := df_args df;
          df_instrs    := f (df_instrs df) |}].
  Proof using.
    intros Hdefs; unfold map_mcfg_cfg; rewrite Hdefs; reflexivity.
  Qed.

  Lemma map_mcfg_with_args_single_def
    (f : list local_id -> CFG.cfg dtyp -> CFG.cfg dtyp) (M : CFG.mcfg dtyp)
    (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    m_definitions (map_mcfg_with_args f M) =
      [{| df_prototype := df_prototype df;
          df_args      := df_args df;
          df_instrs    := f (df_args df) (df_instrs df) |}].
  Proof using.
    intros Hdefs; unfold map_mcfg_with_args; rewrite Hdefs; reflexivity.
  Qed.

  Lemma sccp_cfg_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (SCCPSpec.sccp_cfg fargs c).
  Proof using.
    exact (splice_valid_of_cfg_local_sim fargs c (SCCPSpec.sccp_cfg fargs c)
             (SCCP.sccp_cfg_block_addresses fargs c)
             (SCCP.sccp_cfg_sim fargs c)).
  Qed.

  Lemma dce_cfg_once_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (DCESpec.dce_cfg_once fargs c).
  Proof using.
    exact (splice_valid_of_cfg_local_sim fargs c (DCESpec.dce_cfg_once fargs c)
             (DCESpec.dce_cfg_once_block_addresses fargs c)
             (DCE.dce_cfg_once_sim fargs c)).
  Qed.

  Lemma fold_const_term_cfg_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (SimplifyCFG.fold_const_term_cfg c).
  Proof using.
    exact (splice_valid_of_ruttc fargs c (SimplifyCFG.fold_const_term_cfg c)
             (SimplifyCFG.fold_const_term_cfg_block_addresses c)
             (SimplifyCFG.denote_cfg_fold_const c)).
  Qed.

  Lemma elim_unreachable_cfg_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (SimplifyCFG.elim_unreachable_cfg c).
  Proof using.
    exact (splice_valid_of_ruttc fargs c (SimplifyCFG.elim_unreachable_cfg c)
             (SimplifyCFG.elim_unreachable_cfg_block_addresses c)
             (SimplifyCFG.denote_cfg_elim_unreachable c)).
  Qed.

  Lemma coalesce_one_cfg_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (SimplifyCFG.coalesce_one_cfg c).
  Proof using.
    exact (splice_valid_of_ruttc fargs c (SimplifyCFG.coalesce_one_cfg c)
             (SimplifyCFG.coalesce_one_cfg_block_addresses c)
             (SimplifyCFG.denote_cfg_coalesce_one c)).
  Qed.

  Lemma coalesce_mcfg_single_def
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    exists c',
      m_definitions (SimplifyCFG.coalesce_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (SimplifyCFG.coalesce_mcfg M) = m_declarations M /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    unfold SimplifyCFG.coalesce_mcfg.
    assert (Hiter :
      forall fuel (M0 : CFG.mcfg dtyp) (c0 : CFG.cfg dtyp),
        m_definitions M0 =
          [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c0 |}] ->
        exists c',
          m_definitions (SimplifyCFG.coalesce_mcfg_iter fuel M0) =
            [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
          m_declarations (SimplifyCFG.coalesce_mcfg_iter fuel M0) = m_declarations M0 /\
          splice_valid_defn (df_args df) c0 c').
    { induction fuel as [| fuel' IH]; intros M0 c0 HM0; cbn [SimplifyCFG.coalesce_mcfg_iter].
      - exists c0; refine (conj HM0 (conj Logic.eq_refl (splice_valid_defn_refl _ _))).
      - assert (HM1 :
          m_definitions (SimplifyCFG.coalesce_one_mcfg M0) =
            [{| df_prototype := df_prototype df;
                df_args      := df_args df;
                df_instrs    := SimplifyCFG.coalesce_one_cfg c0 |}]).
        { unfold SimplifyCFG.coalesce_one_mcfg, map_mcfg_cfg; rewrite HM0; reflexivity. }
        destruct (IH (SimplifyCFG.coalesce_one_mcfg M0)
                     (SimplifyCFG.coalesce_one_cfg c0) HM1)
          as (c' & Hdefs' & Hdecls' & Hsv').
        exists c'; split; [exact Hdefs' | split; [exact Hdecls' |]].
        exact (splice_valid_defn_trans _ _ _ _ (coalesce_one_cfg_splice_valid _ c0) Hsv'). }
    intros Hdefs; destruct df as [pr ar c0]; exact (Hiter _ M c0 Hdefs).
  Qed.

  Lemma simplifycfg_mcfg_single_def
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    exists c',
      m_definitions (simplifycfg_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (simplifycfg_mcfg M) = m_declarations M /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    intros Hdefs; unfold simplifycfg_mcfg.
    set (M1 := SimplifyCFG.fold_const_term_mcfg M).
    set (M2 := SimplifyCFG.elim_unreachable_mcfg M1).
    pose proof (map_mcfg_cfg_single_def SimplifyCFG.fold_const_term_cfg M df Hdefs) as HM1.
    pose proof (map_mcfg_cfg_single_def SimplifyCFG.elim_unreachable_cfg M1 _ HM1) as HM2.
    cbn [df_prototype df_args df_instrs] in HM2.
    destruct (coalesce_mcfg_single_def M2 _ HM2) as (c' & HM3 & Hdecl3 & Hsv3).
    cbn [df_prototype df_args df_instrs] in HM3, Hsv3.
    exists c'; split; [exact HM3 | split; [exact Hdecl3 |]].
    eapply splice_valid_defn_trans; [apply fold_const_term_cfg_splice_valid |].
    eapply splice_valid_defn_trans; [apply elim_unreachable_cfg_splice_valid | exact Hsv3].
  Qed.

  Lemma dce_mcfg_single_def
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    exists c',
      m_definitions (dce_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (dce_mcfg M) = m_declarations M /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    intros Hdefs; unfold dce_mcfg.
    pose proof (map_mcfg_with_args_single_def DCESpec.dce_cfg_once M df Hdefs) as HM1.
    pose proof (map_mcfg_with_args_single_def DCESpec.dce_cfg_once (dce_mcfg_once M) _ HM1) as HM2.
    pose proof (map_mcfg_with_args_single_def DCESpec.dce_cfg_once (dce_mcfg_once (dce_mcfg_once M)) _ HM2) as HM3.
    cbn [df_prototype df_args df_instrs] in HM2, HM3.
    eexists; split; [exact HM3 | split; [reflexivity |]].
    eapply splice_valid_defn_trans; [apply dce_cfg_once_splice_valid |].
    eapply splice_valid_defn_trans; [apply dce_cfg_once_splice_valid | apply dce_cfg_once_splice_valid].
  Qed.

  (** ** [Mem2Reg] Leaf-Slice Splicing (Closing F-20)

      In [Mem2Reg], [m2r_module_interproc_safe M] is [false] whenever
      [m_declarations M] is non-empty (which holds for every slice produced by
      [ir-bridge split] from a multi-function module) OR when the slice
      definition contains no [INSTR_Call] instructions (in which case
      [try_promote_slot_in_defn true = try_promote_slot_in_defn false] and
      call-freeness is preserved across [promote_slot_in_cfg]).  In both cases,
      every promotion and dead-alloca step on the slice uses [Mem2Reg]'s
      open-world leaf simulation ([leaf_module_defs_refines]) and splices
      validly into ANY host module! *)

  Definition mm_code_entry_no_call
    (im : instr_id * instr dtyp * list (metadata dtyp)) : bool :=
    match snd (fst im) with
    | INSTR_Call _ _ _ _ => false
    | _ => true
    end.

  Definition mm_defn_no_calls (df : definition dtyp (CFG.cfg dtyp)) : bool :=
    forallb (fun bk => forallb mm_code_entry_no_call (blk_code bk)) (blks (df_instrs df)).

  Definition slice_m2r_safe (M : CFG.mcfg dtyp) : bool :=
    match m_declarations M with
    | _ :: _ => true
    | [] =>
        match m_definitions M with
        | [df] => mm_defn_no_calls df
        | _ => false
        end
    end.

  Lemma check_other_instr_no_call_indep
    (b : bool) (safe_no_p : list local_id) (p : local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp)) :
    mm_code_entry_no_call im = true ->
    Mem2RegSpec.check_other_instr_for_slot b safe_no_p p im =
    Mem2RegSpec.check_other_instr_for_slot false safe_no_p p im.
  Proof using.
    destruct im as [[iid ins] md]; cbn [mm_code_entry_no_call fst snd].
    destruct ins; try reflexivity; discriminate.
  Qed.

  Lemma forallb_eq_on {A : Type} (f g : A -> bool) (xs : list A)
    (Heq : forall x, In x xs -> f x = g x) :
    forallb f xs = forallb g xs.
  Proof using.
    induction xs as [| x rest IH]; [reflexivity |]; cbn [forallb].
    rewrite (Heq x (or_introl Logic.eq_refl)),
            (IH (fun y Hy => Heq y (or_intror Hy))); reflexivity.
  Qed.

  Lemma find_promotable_no_call_indep_and_inv
    (b : bool) (all_defs all_uses : list raw_id) (safe_locals : list local_id)
    (init_bid : block_id) (bks : ocfg dtyp) (b_init : block dtyp)
    (Hbks : forall bk, In bk bks -> forallb mm_code_entry_no_call (blk_code bk) = true) :
    forall acc rem,
      forallb mm_code_entry_no_call acc = true ->
      forallb mm_code_entry_no_call rem = true ->
      Mem2RegSpec.find_promotable_in_init_code b all_defs all_uses safe_locals
        init_bid bks b_init acc rem =
      Mem2RegSpec.find_promotable_in_init_code false all_defs all_uses safe_locals
        init_bid bks b_init acc rem /\
      (forall pre_al al_ins post_al p dt,
         Mem2RegSpec.find_promotable_in_init_code false all_defs all_uses safe_locals
           init_bid bks b_init acc rem = Some (pre_al, al_ins, post_al, p, dt) ->
         forallb mm_code_entry_no_call pre_al = true /\
         mm_code_entry_no_call al_ins = true /\
         forallb mm_code_entry_no_call post_al = true).
  Proof using.
    intros acc rem; revert acc.
    induction rem as [| im post_al IH]; intros acc Hacc Hrem;
      cbn [Mem2RegSpec.find_promotable_in_init_code].
    - split; [reflexivity | intros; discriminate].
    - cbn [forallb] in Hrem; apply Bool.andb_true_iff in Hrem as [Him Hpost].
      assert (Hpre : forallb mm_code_entry_no_call (List.rev acc) = true).
      { rewrite forallb_forall in Hacc |- *.
        intros x Hx; apply Hacc; apply in_rev; exact Hx. }
      assert (Hcand_eq :
        (let pre_al := List.rev acc in
         match im with
         | (IId p, INSTR_Alloca dt anns_al, md_al) =>
             let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
             if is_scalar_dtyp dt
                && Mem2RegSpec.is_only_align_anns anns_al
                && Mem2RegSpec.is_debug_or_file_md md_al
                && Nat.eqb (Mem2RegSpec.m2r_count_id p all_defs) 1%nat
                && in_raw_ids p all_uses
                && forallb (Mem2RegSpec.check_other_instr_for_slot b safe_no_p p) pre_al
                && forallb (Mem2RegSpec.check_code_entry_for_slot b safe_no_p p dt) post_al
                && negb (in_raw_ids p (Mem2RegSpec.m2r_term_entry_uses (blk_term b_init)))
                && Mem2RegSpec.m2r_non_invoke_term (snd (fst (blk_term b_init)))
                && forallb
                     (fun bk =>
                        if raw_id_eqb (blk_id bk) init_bid then true
                        else Mem2RegSpec.check_block_non_entry_for_slot b safe_no_p p dt bk)
                     bks
             then Some (pre_al, im, post_al, p, dt)
             else None
         | _ => None
         end) =
        (let pre_al := List.rev acc in
         match im with
         | (IId p, INSTR_Alloca dt anns_al, md_al) =>
             let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
             if is_scalar_dtyp dt
                && Mem2RegSpec.is_only_align_anns anns_al
                && Mem2RegSpec.is_debug_or_file_md md_al
                && Nat.eqb (Mem2RegSpec.m2r_count_id p all_defs) 1%nat
                && in_raw_ids p all_uses
                && forallb (Mem2RegSpec.check_other_instr_for_slot false safe_no_p p) pre_al
                && forallb (Mem2RegSpec.check_code_entry_for_slot false safe_no_p p dt) post_al
                && negb (in_raw_ids p (Mem2RegSpec.m2r_term_entry_uses (blk_term b_init)))
                && Mem2RegSpec.m2r_non_invoke_term (snd (fst (blk_term b_init)))
                && forallb
                     (fun bk =>
                        if raw_id_eqb (blk_id bk) init_bid then true
                        else Mem2RegSpec.check_block_non_entry_for_slot false safe_no_p p dt bk)
                     bks
             then Some (pre_al, im, post_al, p, dt)
             else None
         | _ => None
         end)).
      { cbv zeta; destruct im as [[iid ins] md]; destruct iid; try reflexivity;
          destruct ins as [| | | dt anns_al | | | | | | |]; try reflexivity.
        set (safe_no_p := List.filter (fun q => negb (raw_id_eqb q id)) safe_locals).
        assert (H1 : forallb (Mem2RegSpec.check_other_instr_for_slot b safe_no_p id) (List.rev acc) =
                     forallb (Mem2RegSpec.check_other_instr_for_slot false safe_no_p id) (List.rev acc)).
        { apply forallb_eq_on; intros x Hx; apply check_other_instr_no_call_indep.
          rewrite forallb_forall in Hpre; exact (Hpre x Hx). }
        assert (H2 : forall cd,
                       forallb mm_code_entry_no_call cd = true ->
                       forallb (Mem2RegSpec.check_code_entry_for_slot b safe_no_p id dt) cd =
                       forallb (Mem2RegSpec.check_code_entry_for_slot false safe_no_p id dt) cd).
        { intros cd Hcd; apply forallb_eq_on; intros x Hx.
          unfold Mem2RegSpec.check_code_entry_for_slot.
          destruct (Mem2RegSpec.is_promotable_load_of id dt x); [reflexivity |].
          destruct (Mem2RegSpec.is_promotable_store_of id dt x); [reflexivity |].
          apply check_other_instr_no_call_indep.
          rewrite forallb_forall in Hcd; exact (Hcd x Hx). }
        assert (H3 : forallb
                       (fun bk =>
                          if raw_id_eqb (blk_id bk) init_bid then true
                          else Mem2RegSpec.check_block_non_entry_for_slot b safe_no_p id dt bk) bks =
                     forallb
                       (fun bk =>
                          if raw_id_eqb (blk_id bk) init_bid then true
                          else Mem2RegSpec.check_block_non_entry_for_slot false safe_no_p id dt bk) bks).
        { apply forallb_eq_on; intros bk Hbk.
          destruct (raw_id_eqb (blk_id bk) init_bid); [reflexivity |].
          unfold Mem2RegSpec.check_block_non_entry_for_slot.
          rewrite (H2 (blk_code bk) (Hbks bk Hbk)); reflexivity. }
        rewrite H1, (H2 post_al Hpost), H3; reflexivity. }
      cbv zeta in Hcand_eq; rewrite Hcand_eq.
      assert (Hacc' : forallb mm_code_entry_no_call (im :: acc) = true)
        by (cbn [forallb]; rewrite Him, Hacc; reflexivity).
      destruct (IH (im :: acc) Hacc' Hpost) as [Heq_rec Hinv_rec].
      set (cand0 :=
             match im with
             | (IId p, INSTR_Alloca dt anns_al, md_al) =>
                 let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
                 if is_scalar_dtyp dt
                    && Mem2RegSpec.is_only_align_anns anns_al
                    && Mem2RegSpec.is_debug_or_file_md md_al
                    && Nat.eqb (Mem2RegSpec.m2r_count_id p all_defs) 1%nat
                    && in_raw_ids p all_uses
                    && forallb (Mem2RegSpec.check_other_instr_for_slot false safe_no_p p) (List.rev acc)
                    && forallb (Mem2RegSpec.check_code_entry_for_slot false safe_no_p p dt) post_al
                    && negb (in_raw_ids p (Mem2RegSpec.m2r_term_entry_uses (blk_term b_init)))
                    && Mem2RegSpec.m2r_non_invoke_term (snd (fst (blk_term b_init)))
                    && forallb
                         (fun bk =>
                            if raw_id_eqb (blk_id bk) init_bid then true
                            else Mem2RegSpec.check_block_non_entry_for_slot false safe_no_p p dt bk)
                         bks
                 then Some (List.rev acc, im, post_al, p, dt)
                 else None
             | _ => None
             end).
      destruct cand0 as [[[[[pa ai] po] p0] dt0] |] eqn:Ecand.
      + split; [reflexivity |].
        intros pre_al al_ins post_al0 p dt Hsome; injection Hsome as <- <- <- <- <-.
        unfold cand0 in Ecand.
        destruct im as [[iid ins] md]; try discriminate Ecand;
          destruct iid; try discriminate Ecand;
          destruct ins; try discriminate Ecand.
        match type of Ecand with (if ?c then _ else _) = _ => destruct c end;
          [injection Ecand as <- <- <- _ _; exact (conj Hpre (conj Him Hpost))
          | discriminate Ecand].
      + split; [exact Heq_rec | exact Hinv_rec].
  Qed.

  Lemma rewrite_code_for_slot_no_call
    (p : local_id) (dt : dtyp) :
    forall cur_reg avoid cd cd' end_r avoid',
      forallb mm_code_entry_no_call cd = true ->
      Mem2RegSpec.rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_r, avoid') ->
      forallb mm_code_entry_no_call cd' = true.
  Proof using.
    intros cur_reg avoid cd; revert cur_reg avoid.
    induction cd as [| im rest IH]; intros cur_reg avoid cd' end_r avoid' Hnc Hrw;
      cbn [Mem2RegSpec.rewrite_code_for_slot] in Hrw.
    - injection Hrw as <- _ _; reflexivity.
    - cbn [forallb] in Hnc; apply Bool.andb_true_iff in Hnc as [Him Hrest].
      destruct (Mem2RegSpec.is_promotable_load_of p dt im) as [dst |].
      + set (lv_reg := PassCommonSyntax.fresh_name "mlv"%string (p :: cur_reg :: avoid)) in *.
        destruct (Mem2RegSpec.rewrite_code_for_slot p dt cur_reg (lv_reg :: avoid) rest)
          as [[r' er] av'] eqn:Er.
        injection Hrw as <- _ _; cbn [forallb mm_code_entry_no_call fst snd].
        exact (IH cur_reg (lv_reg :: avoid) r' er av' Hrest Er).
      + destruct (Mem2RegSpec.is_promotable_store_of p dt im) as [val_e |].
        * set (sv_reg := PassCommonSyntax.fresh_name "msv"%string (p :: avoid)) in *.
          set (st_reg := PassCommonSyntax.fresh_name "mst"%string (p :: sv_reg :: avoid)) in *.
          destruct (Mem2RegSpec.rewrite_code_for_slot p dt st_reg (st_reg :: sv_reg :: avoid) rest)
            as [[r' er] av'] eqn:Er.
          injection Hrw as <- _ _; cbn [forallb mm_code_entry_no_call fst snd].
          exact (IH st_reg (st_reg :: sv_reg :: avoid) r' er av' Hrest Er).
        * destruct (Mem2RegSpec.rewrite_code_for_slot p dt cur_reg avoid rest) as [[r' er] av'] eqn:Er.
          injection Hrw as <- _ _; cbn [forallb]; rewrite Him.
          exact (IH cur_reg avoid r' er av' Hrest Er).
  Qed.

  Lemma pass1_no_call
    (init_bid : block_id) (p : local_id) (dt : dtyp)
    (init_end_reg : local_id) (init_code' : code dtyp)
    (Hinit_nc : forallb mm_code_entry_no_call init_code' = true) :
    forall avoid bk_phis pass1_out avoid',
      (forall bk pr, In (bk, pr) bk_phis -> forallb mm_code_entry_no_call (blk_code bk) = true) ->
      Mem2RegSpec.rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid bk_phis =
        (pass1_out, avoid') ->
      forall bk pr cd' er,
        In (bk, pr, cd', er) pass1_out ->
        forallb mm_code_entry_no_call cd' = true.
  Proof using.
    intros avoid bk_phis; revert avoid.
    induction bk_phis as [| [bk0 pr0] rest IH];
      intros avoid pass1_out avoid' Hbk Hrw bk pr cd' er Hin;
      cbn [Mem2RegSpec.rewrite_non_entry_blocks_pass1] in Hrw.
    - injection Hrw as <- _; contradiction.
    - destruct (raw_id_eqb (blk_id bk0) init_bid).
      + destruct (Mem2RegSpec.rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid rest)
          as [ro av'] eqn:Er.
        injection Hrw as <- _; destruct Hin as [Heq | Hin].
        * injection Heq as _ _ <- _; exact Hinit_nc.
        * exact (IH avoid ro av' (fun b q H => Hbk b q (or_intror H)) Er bk pr cd' er Hin).
      + destruct (Mem2RegSpec.rewrite_code_for_slot p dt pr0 avoid (blk_code bk0))
          as [[cd0 er0] av1] eqn:Ecd0.
        destruct (Mem2RegSpec.rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' av1 rest)
          as [ro av2] eqn:Er.
        injection Hrw as <- _; destruct Hin as [Heq | Hin].
        * injection Heq as _ _ <- _.
          exact (rewrite_code_for_slot_no_call p dt pr0 avoid (blk_code bk0) cd0 er0 av1
                   (Hbk bk0 pr0 (or_introl Logic.eq_refl)) Ecd0).
        * exact (IH av1 ro av2 (fun b q H => Hbk b q (or_intror H)) Er bk pr cd' er Hin).
  Qed.

  Lemma try_promote_slot_no_calls_indep_and_pres
    (b : bool) (df : definition dtyp (CFG.cfg dtyp)) :
    mm_defn_no_calls df = true ->
    Mem2RegSpec.try_promote_slot_in_defn b df = Mem2RegSpec.try_promote_slot_in_defn false df /\
    (forall df',
       Mem2RegSpec.try_promote_slot_in_defn false df = Some df' ->
       mm_defn_no_calls df' = true).
  Proof using.
    intros Hnc; unfold mm_defn_no_calls in Hnc.
    rewrite forallb_forall in Hnc.
    unfold Mem2RegSpec.try_promote_slot_in_defn; cbv zeta.
    destruct (Mem2RegSpec.m2r_nodup_ids _ && _ && _); [| split; [reflexivity | discriminate]].
    destruct (find_block (blks (df_instrs df)) (init (df_instrs df))) as [b_init |] eqn:Efb;
      [| split; [reflexivity | discriminate]].
    assert (Hin_init : In b_init (blks (df_instrs df)))
      by (eapply ScopeTheory.find_block_In'; exact Efb).
    destruct (Mem2RegSpec.m2r_is_empty (blk_phis b_init)); [| split; [reflexivity | discriminate]].
    destruct (find_promotable_no_call_indep_and_inv b
                (df_args df ++ flat_map PassCommonSyntax.full_block_defs (blks (df_instrs df)))
                (flat_map PassCommonSyntax.full_block_uses (blks (df_instrs df)))
                (Mem2RegSpec.m2r_collect_unique_allocas
                   (df_args df ++ flat_map PassCommonSyntax.full_block_defs (blks (df_instrs df)))
                   (blks (df_instrs df)))
                (init (df_instrs df)) (blks (df_instrs df)) b_init Hnc
                [] (blk_code b_init) Logic.eq_refl (Hnc b_init Hin_init))
      as [Hfind_eq Hfind_inv].
    rewrite Hfind_eq.
    destruct (Mem2RegSpec.find_promotable_in_init_code false _ _ _ _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Ef0;
      [| split; [reflexivity | discriminate]].
    split; [reflexivity |].
    intros df' Hsome; injection Hsome as <-.
    destruct (Hfind_inv pre_al al_ins post_al p dt Logic.eq_refl) as (Hpre & Hal & Hpost).
    unfold mm_defn_no_calls, Mem2RegSpec.promote_slot_in_cfg; cbn [df_instrs blks]; cbv zeta.
    set (c := df_instrs df).
    set (avoid0 := df_args df ++ PassCommonSyntax.cfg_all_ids c).
    set (init_reg := PassCommonSyntax.fresh_name "m2r_init"%string avoid0).
    set (avoid1 := init_reg :: avoid0).
    set (phi_regs := PassCommonSyntax.fresh_names "m2r_phi"%string (List.length (blks c)) avoid1).
    set (avoid2 := phi_regs ++ avoid1).
    destruct (Mem2RegSpec.rewrite_code_for_slot p dt init_reg avoid2 post_al)
      as [[post_al' init_end_reg] avoid3] eqn:Erw_post.
    pose proof (rewrite_code_for_slot_no_call p dt init_reg avoid2 post_al
                  post_al' init_end_reg avoid3 Hpost Erw_post) as Hpost'.
    set (init_op := (IId init_reg, INSTR_Op (PassCommonSyntax.mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison),
                     ([] : list (metadata dtyp)))).
    set (init_code' := pre_al ++ al_ins :: init_op :: post_al').
    assert (Hinit_nc : forallb mm_code_entry_no_call init_code' = true).
    { unfold init_code'; rewrite forallb_app; cbn [forallb].
      rewrite Hpre, Hal, Hpost'; reflexivity. }
    destruct (Mem2RegSpec.rewrite_non_entry_blocks_pass1 (init c) p dt init_end_reg init_code'
                avoid3 (List.combine (blks c) phi_regs))
      as [pass1_out avoid_out] eqn:Epass1.
    assert (Hcomb : forall bk pr, In (bk, pr) (List.combine (blks c) phi_regs) ->
                                  forallb mm_code_entry_no_call (blk_code bk) = true).
    { intros bk pr Hin; apply in_combine_l in Hin; exact (Hnc bk Hin). }
    pose proof (pass1_no_call (init c) p dt init_end_reg init_code' Hinit_nc
                  avoid3 _ pass1_out avoid_out Hcomb Epass1) as Hp1.
    unfold Mem2RegSpec.build_promoted_blocks; apply forallb_forall.
    intros bk_out Hbk_out; apply in_map_iff in Hbk_out as [[[[bk pr] cd'] er] [<- Hin_p1]].
    destruct (raw_id_eqb (blk_id bk) (init c)); cbn [blk_code]; exact (Hp1 bk pr cd' er Hin_p1).
  Qed.

  Lemma try_promote_slot_proto_indep
    (proto1 proto2 : declaration dtyp)
    (fargs : list local_id) (c : CFG.cfg dtyp)
    (df' : definition dtyp (CFG.cfg dtyp)) :
    Mem2RegSpec.try_promote_slot_in_defn false
      {| df_prototype := proto1; df_args := fargs; df_instrs := c |} = Some df' ->
    df_args df' = fargs /\
    Mem2RegSpec.try_promote_slot_in_defn false
      {| df_prototype := proto2; df_args := fargs; df_instrs := c |} =
      Some {| df_prototype := proto2; df_args := fargs; df_instrs := df_instrs df' |}.
  Proof using.
    unfold Mem2RegSpec.try_promote_slot_in_defn; cbn [df_args df_instrs df_prototype].
    destruct (Mem2RegSpec.m2r_nodup_ids _ && _ && _); [| discriminate].
    destruct (find_block (blks c) (init c)) as [b_init |]; [| discriminate].
    destruct (Mem2RegSpec.m2r_is_empty (blk_phis b_init)); [| discriminate].
    destruct (Mem2RegSpec.find_promotable_in_init_code false _ _ _ _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |]; [| discriminate].
    intros H; injection H as <-; cbn; split; reflexivity.
  Qed.

  Lemma try_elim_dead_alloca_proto_indep
    (proto1 proto2 : declaration dtyp)
    (fargs : list local_id) (c : CFG.cfg dtyp)
    (df' : definition dtyp (CFG.cfg dtyp)) :
    Mem2RegSpec.try_elim_dead_alloca_in_defn
      {| df_prototype := proto1; df_args := fargs; df_instrs := c |} = Some df' ->
    df_args df' = fargs /\
    Mem2RegSpec.try_elim_dead_alloca_in_defn
      {| df_prototype := proto2; df_args := fargs; df_instrs := c |} =
      Some {| df_prototype := proto2; df_args := fargs; df_instrs := df_instrs df' |}.
  Proof using.
    unfold Mem2RegSpec.try_elim_dead_alloca_in_defn; cbn [df_args df_instrs df_prototype].
    destruct (Mem2RegSpec.m2r_nodup_ids _ && _ && _); [| discriminate].
    destruct (find_block (blks c) (init c)) as [b_init |]; [| discriminate].
    destruct (Mem2RegSpec.m2r_is_empty _ && _); [| discriminate].
    destruct (Mem2RegSpec.find_trailing_dead_alloca_in_code _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |]; [| discriminate].
    destruct (forallb _ (blks c)); [| discriminate].
    intros H; injection H as <-; cbn; split; reflexivity.
  Qed.

  Lemma try_elim_dead_alloca_no_calls_pres
    (df df' : definition dtyp (CFG.cfg dtyp)) :
    mm_defn_no_calls df = true ->
    Mem2RegSpec.try_elim_dead_alloca_in_defn df = Some df' ->
    mm_defn_no_calls df' = true.
  Proof using.
    intros Hnc; unfold mm_defn_no_calls in Hnc; rewrite forallb_forall in Hnc.
    unfold Mem2RegSpec.try_elim_dead_alloca_in_defn; cbv zeta.
    destruct (Mem2RegSpec.m2r_nodup_ids _ && _ && _); [| discriminate].
    destruct (find_block (blks (df_instrs df)) (init (df_instrs df))) as [b_init |] eqn:Efb;
      [| discriminate].
    assert (Hin_init : In b_init (blks (df_instrs df)))
      by (eapply ScopeTheory.find_block_In'; exact Efb).
    destruct (Mem2RegSpec.m2r_is_empty _ && _); [| discriminate].
    destruct (Mem2RegSpec.find_trailing_dead_alloca_in_code _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Etr; [| discriminate].
    pose proof (Mem2RegExprLift.find_trailing_dead_alloca_in_code_inv _ _ _ [] (blk_code b_init)
                  pre_al al_ins post_al p dt Etr) as Hsplit.
    cbv zeta in Hsplit; cbn [List.rev app] in Hsplit.
    destruct Hsplit as (Hcode_eq & _).
    destruct (forallb _ (blks (df_instrs df))); [| discriminate].
    intros Hsome; injection Hsome as <-.
    unfold mm_defn_no_calls; cbn [df_instrs blks]; apply forallb_forall.
    intros bk' Hbk'; apply in_map_iff in Hbk' as [bk [<- Hin_bk]].
    destruct (raw_id_eqb (blk_id bk) (init (df_instrs df))); [| exact (Hnc bk Hin_bk)].
    cbn [blk_code]; pose proof (Hnc b_init Hin_init) as Hb0.
    rewrite Hcode_eq, forallb_app in Hb0; cbn [forallb] in Hb0.
    rewrite !Bool.andb_true_iff in Hb0; destruct Hb0 as [Hpre [_ Hpost]].
    rewrite forallb_app, Hpre, Hpost; reflexivity.
  Qed.

  Lemma splice_valid_of_try_promote_leaf
    (proto0 : declaration dtyp) (fargs : list local_id)
    (c : CFG.cfg dtyp) (df' : definition dtyp (CFG.cfg dtyp))
    (Etry : Mem2RegSpec.try_promote_slot_in_defn false
              {| df_prototype := proto0; df_args := fargs; df_instrs := c |} = Some df') :
    splice_valid_defn fargs c (df_instrs df').
  Proof using.
    destruct (Mem2RegStage1.promote_slot_in_defn_block_addresses false
                {| df_prototype := proto0; df_args := fargs; df_instrs := c |} df' Etry)
      as [_ Hba]; cbn [df_instrs] in Hba.
    split; [exact Hba |].
    intros M_host pre post proto Hdefs.
    destruct (try_promote_slot_proto_indep proto0 proto fargs c df' Etry) as [_ Etry_host].
    apply Mem2RegStage1.leaf_module_defs_refines.
    - exact (build_global_env_splice_eq M_host pre post proto fargs c (df_instrs df') Hdefs Hba).
    - reflexivity.
    - intros P0 g0 Hg0; rewrite Hdefs; cbn [m_definitions].
      apply Forall2_app; [apply Mem2Reg.leaf_ctx_fn_rel_refl_list |].
      constructor; [| apply Mem2Reg.leaf_ctx_fn_rel_refl_list].
      split; [reflexivity |].
      exact (Mem2RegStage1.try_promote_slot_leaf_denote_function_sim P0 g0 _ _ Hg0 Etry_host).
  Qed.

  Lemma splice_valid_of_try_elim_dead_alloca {IPWB : IPtrWellBehaved IP}
    (proto0 : declaration dtyp) (fargs : list local_id)
    (c : CFG.cfg dtyp) (df' : definition dtyp (CFG.cfg dtyp))
    (Etry : Mem2RegSpec.try_elim_dead_alloca_in_defn
              {| df_prototype := proto0; df_args := fargs; df_instrs := c |} = Some df') :
    splice_valid_defn fargs c (df_instrs df').
  Proof using.
    destruct (Mem2RegStage1.elim_dead_alloca_in_defn_block_addresses
                {| df_prototype := proto0; df_args := fargs; df_instrs := c |} df' Etry)
      as [_ Hba]; cbn [df_instrs] in Hba.
    split; [exact Hba |].
    intros M_host pre post proto Hdefs.
    destruct (try_elim_dead_alloca_proto_indep proto0 proto fargs c df' Etry) as [_ Etry_host].
    apply Mem2RegStage1.leaf_module_defs_refines.
    - exact (build_global_env_splice_eq M_host pre post proto fargs c (df_instrs df') Hdefs Hba).
    - reflexivity.
    - intros P0 g0 Hg0; rewrite Hdefs; cbn [m_definitions].
      apply Forall2_app; [apply Mem2Reg.leaf_ctx_fn_rel_refl_list |].
      constructor; [| apply Mem2Reg.leaf_ctx_fn_rel_refl_list].
      split; [reflexivity |].
      exact (Mem2RegStage2.try_elim_dead_alloca_denote_function_sim P0 g0 _ _ Hg0 Etry_host).
  Qed.

  Lemma promote_slot_step_safe_single_def
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp))
    (Hdefs : m_definitions M = [df])
    (Hsafe : slice_m2r_safe M = true) :
    exists c',
      m_definitions (Mem2RegSpec.promote_slot_step_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (Mem2RegSpec.promote_slot_step_mcfg M) = m_declarations M /\
      slice_m2r_safe (Mem2RegSpec.promote_slot_step_mcfg M) = true /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    unfold Mem2RegSpec.promote_slot_step_mcfg.
    destruct (PassCommonSyntax.mcfg_no_inttoptr M);
      [| exists (df_instrs df); destruct df;
         exact (conj Hdefs (conj Logic.eq_refl (conj Hsafe (splice_valid_defn_refl _ _))))].
    assert (Heq_try :
      Mem2RegSpec.try_promote_slot_in_defn (Mem2RegSpec.m2r_module_interproc_safe M) df =
      Mem2RegSpec.try_promote_slot_in_defn false df).
    { unfold slice_m2r_safe in Hsafe.
      destruct (m_declarations M) as [| decl0 rest_d] eqn:Edecl.
      - rewrite Hdefs in Hsafe.
        exact (proj1 (try_promote_slot_no_calls_indep_and_pres _ df Hsafe)).
      - unfold Mem2RegSpec.m2r_module_interproc_safe; rewrite Edecl, Bool.andb_false_r; cbn [andb]; reflexivity. }
    rewrite Hdefs; cbn [Mem2RegSpec.promote_first_in_defs]; rewrite Heq_try.
    destruct (Mem2RegSpec.try_promote_slot_in_defn false df) as [df' |] eqn:Etry.
    - destruct df as [pr ar c0].
      destruct (try_promote_slot_proto_indep pr pr ar c0 df' Etry) as [Har' Etry'].
      destruct (Mem2RegStage1.promote_slot_in_defn_block_addresses false _ df' Etry) as [Hpr' _].
      cbn [df_prototype df_args df_instrs] in *.
      assert (Hdf' : df' = {| df_prototype := pr; df_args := ar; df_instrs := df_instrs df' |})
        by (destruct df'; cbn in *; congruence).
      exists (df_instrs df'); rewrite <- Hdf'.
      refine (conj Logic.eq_refl (conj Logic.eq_refl (conj _ _))).
      + unfold slice_m2r_safe in Hsafe |- *; cbn [m_declarations m_definitions].
        destruct (m_declarations M); [| reflexivity].
        rewrite Hdefs in Hsafe.
        exact (proj2 (try_promote_slot_no_calls_indep_and_pres false _ Hsafe) df' Etry).
      + exact (splice_valid_of_try_promote_leaf pr ar c0 df' Etry).
    - cbn [option_map]; exists (df_instrs df); destruct df as [pr ar c0].
      exact (conj Hdefs (conj Logic.eq_refl (conj Hsafe (splice_valid_defn_refl _ _)))).
  Qed.

  Lemma elim_dead_alloca_step_safe_single_def {IPWB : IPtrWellBehaved IP}
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp))
    (Hdefs : m_definitions M = [df])
    (Hsafe : slice_m2r_safe M = true) :
    exists c',
      m_definitions (Mem2RegSpec.elim_dead_alloca_step_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (Mem2RegSpec.elim_dead_alloca_step_mcfg M) = m_declarations M /\
      slice_m2r_safe (Mem2RegSpec.elim_dead_alloca_step_mcfg M) = true /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    unfold Mem2RegSpec.elim_dead_alloca_step_mcfg.
    destruct (PassCommonSyntax.mcfg_no_inttoptr M);
      [| exists (df_instrs df); destruct df;
         exact (conj Hdefs (conj Logic.eq_refl (conj Hsafe (splice_valid_defn_refl _ _))))].
    rewrite Hdefs; cbn [Mem2RegSpec.elim_first_dead_alloca_in_defs].
    destruct (Mem2RegSpec.try_elim_dead_alloca_in_defn df) as [df' |] eqn:Etry.
    - destruct df as [pr ar c0].
      destruct (try_elim_dead_alloca_proto_indep pr pr ar c0 df' Etry) as [Har' _].
      destruct (Mem2RegStage1.elim_dead_alloca_in_defn_block_addresses _ df' Etry) as [Hpr' _].
      cbn [df_prototype df_args df_instrs] in *.
      assert (Hdf' : df' = {| df_prototype := pr; df_args := ar; df_instrs := df_instrs df' |})
        by (destruct df'; cbn in *; congruence).
      exists (df_instrs df'); rewrite <- Hdf'.
      refine (conj Logic.eq_refl (conj Logic.eq_refl (conj _ _))).
      + unfold slice_m2r_safe in Hsafe |- *; cbn [m_declarations m_definitions].
        destruct (m_declarations M); [| reflexivity].
        rewrite Hdefs in Hsafe.
        exact (try_elim_dead_alloca_no_calls_pres _ df' Hsafe Etry).
      + exact (splice_valid_of_try_elim_dead_alloca pr ar c0 df' Etry).
    - cbn [option_map]; exists (df_instrs df); destruct df as [pr ar c0].
      exact (conj Hdefs (conj Logic.eq_refl (conj Hsafe (splice_valid_defn_refl _ _)))).
  Qed.

  Lemma mem2reg_mcfg_safe_single_def {IPWB : IPtrWellBehaved IP}
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp))
    (Hdefs : m_definitions M = [df])
    (Hsafe : slice_m2r_safe M = true) :
    exists c',
      m_definitions (mem2reg_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (mem2reg_mcfg M) = m_declarations M /\
      slice_m2r_safe (mem2reg_mcfg M) = true /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    unfold mem2reg_mcfg.
    assert (Hprom :
      forall fuel (M0 : CFG.mcfg dtyp) (c0 : CFG.cfg dtyp),
        m_definitions M0 =
          [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c0 |}] ->
        slice_m2r_safe M0 = true ->
        exists c1,
          m_definitions (Mem2RegSpec.promote_slot_iter fuel M0) =
            [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c1 |}] /\
          m_declarations (Mem2RegSpec.promote_slot_iter fuel M0) = m_declarations M0 /\
          slice_m2r_safe (Mem2RegSpec.promote_slot_iter fuel M0) = true /\
          splice_valid_defn (df_args df) c0 c1).
    { induction fuel as [| fuel' IH]; intros M0 c0 HM0 Hs0; cbn [Mem2RegSpec.promote_slot_iter].
      - exists c0; exact (conj HM0 (conj Logic.eq_refl (conj Hs0 (splice_valid_defn_refl _ _)))).
      - destruct (promote_slot_step_safe_single_def M0 _ HM0 Hs0)
          as (c_mid & HM1 & Hd1 & Hs1 & Hsv1).
        cbn [df_prototype df_args df_instrs] in *.
        destruct (IH _ c_mid HM1 Hs1) as (c1 & HM2 & Hd2 & Hs2 & Hsv2).
        exists c1; refine (conj HM2 (conj (eq_trans Hd2 Hd1) (conj Hs2 _))).
        exact (splice_valid_defn_trans _ _ _ _ Hsv1 Hsv2). }
    assert (Helim :
      forall fuel (M0 : CFG.mcfg dtyp) (c0 : CFG.cfg dtyp),
        m_definitions M0 =
          [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c0 |}] ->
        slice_m2r_safe M0 = true ->
        exists c1,
          m_definitions (Mem2RegSpec.elim_dead_alloca_iter fuel M0) =
            [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c1 |}] /\
          m_declarations (Mem2RegSpec.elim_dead_alloca_iter fuel M0) = m_declarations M0 /\
          slice_m2r_safe (Mem2RegSpec.elim_dead_alloca_iter fuel M0) = true /\
          splice_valid_defn (df_args df) c0 c1).
    { induction fuel as [| fuel' IH]; intros M0 c0 HM0 Hs0; cbn [Mem2RegSpec.elim_dead_alloca_iter].
      - exists c0; exact (conj HM0 (conj Logic.eq_refl (conj Hs0 (splice_valid_defn_refl _ _)))).
      - destruct (elim_dead_alloca_step_safe_single_def M0 _ HM0 Hs0)
          as (c_mid & HM1 & Hd1 & Hs1 & Hsv1).
        cbn [df_prototype df_args df_instrs] in *.
        destruct (IH _ c_mid HM1 Hs1) as (c1 & HM2 & Hd2 & Hs2 & Hsv2).
        exists c1; refine (conj HM2 (conj (eq_trans Hd2 Hd1) (conj Hs2 _))).
        exact (splice_valid_defn_trans _ _ _ _ Hsv1 Hsv2). }
    destruct df as [pr ar c0].
    destruct (Hprom Mem2RegSpec.mem2reg_default_fuel M c0 Hdefs Hsafe)
      as (c1 & HM1 & Hd1 & Hs1 & Hsv1).
    destruct (Helim Mem2RegSpec.mem2reg_default_fuel _ c1 HM1 Hs1)
      as (c2 & HM2 & Hd2 & Hs2 & Hsv2).
    exists c2; refine (conj HM2 (conj (eq_trans Hd2 Hd1) (conj Hs2 _))).
    exact (splice_valid_defn_trans _ _ _ _ Hsv1 Hsv2).
  Qed.

  (** Full 7-stage [Pipeline.optimize_mcfg] slice theorem (F-20):
      When [m_slice_src] has a single definition and either has non-empty
      [m_declarations] (as emitted by [ir-bridge split] for any multi-function
      module) or is a call-free leaf, [(fid, m_slice_src, optimize_mcfg m_slice_src)]
      splices validly into ANY host module [m_orig]! *)
  Theorem optimize_mcfg_slice_valid {IPWB : IPtrWellBehaved IP}
    (fid : function_id) (m_slice_src : CFG.mcfg dtyp)
    (Hsafe : slice_m2r_safe m_slice_src = true) :
    slice_valid_in_any_host (fid, m_slice_src, optimize_mcfg m_slice_src).
  Proof using.
    intros df_src df_tgt Hsrc Htgt.
    unfold optimize_mcfg in Htgt.
    destruct (mem2reg_mcfg_safe_single_def m_slice_src df_src Hsrc Hsafe)
      as (c1 & HM1 & Hd1 & Hs1 & Hsv1).
    rewrite (inline_mcfg_single_def_id (mem2reg_mcfg m_slice_src) _ HM1) in Htgt.
    destruct (mem2reg_mcfg_safe_single_def (mem2reg_mcfg m_slice_src) _ HM1 Hs1)
      as (c2 & HM2 & _ & _ & Hsv2).
    cbn [df_prototype df_args df_instrs] in HM2, Hsv2.
    pose proof (map_mcfg_with_args_single_def SCCPSpec.sccp_cfg _ _ HM2) as HM3.
    cbn [df_prototype df_args df_instrs] in HM3.
    destruct (simplifycfg_mcfg_single_def _ _ HM3) as (c4 & HM4 & _ & Hsv4).
    cbn [df_prototype df_args df_instrs] in HM4, Hsv4.
    destruct (dce_mcfg_single_def _ _ HM4) as (c5 & HM5 & _ & Hsv5).
    cbn [df_prototype df_args df_instrs] in HM5, Hsv5.
    destruct (simplifycfg_mcfg_single_def _ _ HM5) as (c6 & HM6 & _ & Hsv6).
    cbn [df_prototype df_args df_instrs] in HM6, Hsv6.
    unfold SCCPSpec.sccp_mcfg in Htgt.
    rewrite HM6 in Htgt; injection Htgt as <-; cbn [df_instrs].
    eapply splice_valid_defn_trans; [exact Hsv1 |].
    eapply splice_valid_defn_trans; [exact Hsv2 |].
    eapply splice_valid_defn_trans; [apply sccp_cfg_splice_valid |].
    eapply splice_valid_defn_trans; [exact Hsv4 |].
    eapply splice_valid_defn_trans; [exact Hsv5 | exact Hsv6].
  Qed.

End SafePathSlices.

Theorem check_module_merge_universal_I2F_model_refine
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (ret_typ : dtyp) (entry : function_id)
  (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
  (s1 : @FusedS PInf) (s2 : @FusedS PFin)
  (Hchk : check_module_merge m_orig m_merged verified_slices = true)
  (Hslices : Forall (@slice_valid_in_any_host IPZ IPZTheory) verified_slices)
  (Hargs : Forall2 I2F_dvalue args1 args2)
  (Hs : I2F_FusedS s1 s2) :
  @prog_refines IPZ IPZTheory m_orig m_merged /\
  I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
    (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 m_merged) s1)
    (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 m_merged) s2).
Proof.
  split.
  - exact (@check_module_merge_universal_refines IPZ IPZTheory m_orig m_merged
             verified_slices Hchk Hslices).
  - exact (@I2F_toplevel.model_refine ret_typ entry args1 args2 m_merged s1 s2 Hargs Hs).
Qed.


