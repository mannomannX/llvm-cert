(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Module Split/Merge Composition Checker ([CertPasses.ModuleMerge])

    Removes [ir-bridge]'s module splitter and merger from the semantic TCB by
    validating [m_merged] directly against [m_orig] and a list of verified
    per-function slices [verified_slices]:

    1. **Global Layout & Alignment Identity (F-33, F-47)**:
       Enforces [m_globals m_merged = m_globals m_orig], rejects
       [LINKAGE_Extern_weak] on globals, and checks exact preservation of
       deduplicated module [blockaddress] allocations.
    2. **Declaration & Symbol Table Preservation (F-33)**:
       Enforces [m_declarations m_merged = m_declarations m_orig], rejects
       [LINKAGE_Extern_weak] on declarations and definitions, and enforces
       [NoDup] across all declared and defined function identifiers.
    3. **Prototype & Attribute Contract Preservation (F-19)**:
       Enforces positional [Forall2] alignment of [m_definitions] with exact
       equality of [df_prototype] and [df_args], statically blocking unverified
       [-O2]-inferred attributes ([willreturn], [readonly], [noalias],
       [memory(...)], [noundef], etc.) on merged function headers.
    4. **Per-Function Provenance & Compositional Linking (F-20, F-24, F-33)**:
       Requires every definition pair [(df_orig, df_merged)] either to be an
       unchanged pass-through ([df_merged = df_orig]) or to match a verified
       single-function slice [(fid, m_slice_src, m_slice_tgt)] (allowing
       externalized linkage on [m_slice_src] as emitted by [ir-bridge split]),
       and lifts open-world per-slice refinement to whole-module [@prog_refines]
       and end-to-end [IPZ -> IP64Bit] [I2F_toplevel.model_refine]. *)

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

From CertPasses Require Export ModuleMergeEqb ModuleMergeLink ModuleMergeVDrawCore ModuleMergeVDrawLift.

(** * 6. Parser [METADATA_File_info] Normalization for Multi-File CLI Validation *)

Definition keep_non_file_info_md (m : metadata dtyp) : bool :=
  match m with
  | METADATA_File_info _ => false
  | _ => true
  end.

Definition strip_file_info_mds (mds : list (metadata dtyp)) : list (metadata dtyp) :=
  List.filter keep_non_file_info_md mds.

Definition strip_file_info_block (bk : block dtyp) : block dtyp :=
  {| blk_id       := blk_id bk;
     blk_phis     := List.map (fun '(id, p, md) => (id, p, strip_file_info_mds md)) (blk_phis bk);
     blk_code     := List.map (fun '(iid, ins, md) => (iid, ins, strip_file_info_mds md)) (blk_code bk);
     blk_term     := let '(iid, tm, md) := blk_term bk in (iid, tm, strip_file_info_mds md);
     blk_comments := blk_comments bk |}.

Definition strip_file_info_cfg (c : CFG.cfg dtyp) : CFG.cfg dtyp :=
  {| init := init c;
     blks := List.map strip_file_info_block (blks c);
     args := args c |}.

Definition strip_file_info_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  map_mcfg_cfg strip_file_info_cfg M.

Definition check_module_merge_parsed
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) : bool :=
  check_module_merge
    (strip_file_info_mcfg m_orig)
    (strip_file_info_mcfg m_merged)
    (List.map
       (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
       verified_slices).

Definition validate_module_merge_parsed
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  : string + unit :=
  validate_module_merge
    (strip_file_info_mcfg m_orig)
    (strip_file_info_mcfg m_merged)
    (List.map
       (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
       verified_slices).

Lemma strip_file_info_mds_idem (mds : list (metadata dtyp)) :
  strip_file_info_mds (strip_file_info_mds mds) = strip_file_info_mds mds.
Proof.
  induction mds as [| m rest IH]; [reflexivity |]; unfold strip_file_info_mds in *; cbn [List.filter].
  destruct (keep_non_file_info_md m) eqn:Ek; [cbn [List.filter]; rewrite Ek, IH; reflexivity | exact IH].
Qed.

Lemma find_option_filter_none {A B : Type}
  (f : A -> option B) (p : A -> bool) (xs : list A)
  (Hnone : forall x, p x = false -> f x = None) :
  find_option f (List.filter p xs) = find_option f xs.
Proof.
  induction xs as [| x rest IH]; [reflexivity |]; cbn [List.filter find_option].
  destruct (p x) eqn:Ep.
  - cbn [find_option]; destruct (f x); [reflexivity | exact IH].
  - rewrite (Hnone x Ep); exact IH.
Qed.

Lemma load_metadata_attrs_strip (mds : list (metadata dtyp)) :
  load_metadata_attrs (strip_file_info_mds mds) = load_metadata_attrs mds.
Proof.
  unfold load_metadata_attrs, strip_file_info_mds.
  induction mds as [| m rest IH]; [reflexivity |]; cbn [List.filter flat_map].
  destruct m; cbn [keep_non_file_info_md flat_map load_metadata_attr];
    try (rewrite IH; reflexivity); exact IH.
Qed.

Lemma metadata_range_strip (mds : list (metadata dtyp)) :
  metadata_range (strip_file_info_mds mds) = metadata_range mds.
Proof.
  unfold metadata_range, strip_file_info_mds.
  apply find_option_filter_none; intros m Hm; destruct m; try discriminate Hm; reflexivity.
Qed.

Lemma load_metadata_dereferenceable_strip (mds : list (metadata dtyp)) :
  load_metadata_dereferenceable (strip_file_info_mds mds) = load_metadata_dereferenceable mds.
Proof.
  unfold load_metadata_dereferenceable, strip_file_info_mds.
  apply find_option_filter_none; intros m Hm; destruct m; try discriminate Hm; reflexivity.
Qed.

Lemma strip_file_info_cfg_block_addresses (c : CFG.cfg dtyp) :
  flat_map block_block_addresses (blks (strip_file_info_cfg c)) =
  flat_map block_block_addresses (blks c).
Proof.
  unfold strip_file_info_cfg; cbn [blks].
  induction (blks c) as [| bk rest IH]; [reflexivity |]; cbn [List.map flat_map].
  rewrite IH; f_equal.
  unfold block_block_addresses, strip_file_info_block; cbn [blk_phis blk_code blk_term].
  assert (Hph : forall ps : list (local_id * phi dtyp * list (metadata dtyp)),
            flat_map (fun '(_, Phi _ _ args, _) => flat_map (fun x => exp_block_addresses (snd x)) args)
              (List.map (fun '(id, p, md) => (id, p, strip_file_info_mds md)) ps) =
            flat_map (fun '(_, Phi _ _ args, _) => flat_map (fun x => exp_block_addresses (snd x)) args) ps).
  { induction ps as [| [[id [? ? args]] md] rp IHp]; [reflexivity | cbn; rewrite IHp; reflexivity]. }
  assert (Hcd : forall cd : code dtyp,
            flat_map (fun '(_, i, _) => instr_block_addresses i)
              (List.map (fun '(iid, ins, md) => (iid, ins, strip_file_info_mds md)) cd) =
            flat_map (fun '(_, i, _) => instr_block_addresses i) cd).
  { induction cd as [| [[iid ins] md] rc IHc]; [reflexivity | cbn; rewrite IHc; reflexivity]. }
  rewrite Hph, Hcd; destruct (blk_term bk) as [[iid tm] md]; reflexivity.
Qed.

Section StripFileInfoRefinement.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).

  Lemma refine_cfg_raise_any {A : Type} (s1 s2 : string) :
    @refine_cfg PaV A A Logic.eq (raise s1) (raise s2).
  Proof using.
    unfold raise, trigger_cast; eapply ruttc_trigger';
      [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
  Qed.

  Lemma refine_cfg_raiseUB_any {A : Type} (s1 s2 : string) :
    @refine_cfg PaV A A Logic.eq (raiseUB s1) (raiseUB s2).
  Proof using.
    unfold raiseUB, trigger_cast; apply ruttc_trigger_cutl; exact (CutUB_rel (print_msg s1)).
  Qed.

  Lemma refine_cfg_assert_alignment_msg
    (a : @dvalue PaV) (anns : list (annotation dtyp)) (m1 m2 : string) :
    @refine_cfg PaV unit unit Logic.eq
      (EOU_to_itree (assert_alignment a anns m1))
      (EOU_to_itree (assert_alignment a anns m2)).
  Proof using.
    apply refine_EOU_to_cfg; unfold assert_alignment, assert_aligned_to.
    destruct a as [[p | | | | | | |] | |], (find_option ann_align anns) as [al |];
      try (constructor; reflexivity).
    destruct (ptr_aligned_to p (Z.to_N (denote_int_syntax al))); constructor; reflexivity.
  Qed.

  Lemma refine_cfg_apply_value_attrs_msg
    (attrs : list param_attr) (m1 m2 : string) (v : @dvalue PaV) :
    @refine_cfg PaV _ _ Logic.eq
      (EOU_to_itree (apply_value_attrs attrs m1 v))
      (EOU_to_itree (apply_value_attrs attrs m2 v)).
  Proof using.
    apply refine_EOU_to_cfg; unfold apply_value_attrs.
    destruct (existsb attr_is_noundef attrs && negb (dvalue_well_defined (value_attrs_poison attrs v)));
      constructor; reflexivity.
  Qed.

  Lemma refine_cfg_assert_deref_msg
    (or_null : bool) (n : N) (v : @dvalue PaV) (m1 m2 : string) :
    @refine_cfg PaV unit unit Logic.eq
      (assert_dereferenceable or_null n v m1)
      (assert_dereferenceable or_null n v m2).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [[p | | | | | | |] | |];
      [apply refine_cfg_refl
      | apply refine_cfg_raise_any
      | apply refine_cfg_raise_any
      | apply refine_cfg_raise_any
      | apply refine_cfg_raise_any
      | apply refine_cfg_raiseUB_any
      | apply refine_cfg_raise_any
      | apply refine_cfg_raise_any
      | apply refine_cfg_raise_any
      | apply refine_cfg_raise_any].
  Qed.

  Lemma refine_cfg_apply_attrs_msg
    (attrs : list param_attr) (m1 m2 : string) (v : @dvalue PaV) :
    @refine_cfg PaV _ _ Logic.eq
      (apply_attrs attrs m1 v)
      (apply_attrs attrs m2 v).
  Proof using.
    unfold apply_attrs.
    eapply ruttc_bind; [apply refine_cfg_apply_value_attrs_msg | intros v' _ <-].
    eapply ruttc_bind.
    - unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[on n] |],
               v' as [[p | | | | | | |] | |];
        try apply refine_cfg_refl; apply refine_cfg_assert_deref_msg.
    - intros [] _ _; apply ruttc_ret; reflexivity.
  Qed.

  Lemma refine_cfg_call_args_msg
    (cargs : list (texp dtyp * list param_attr)) (m1 m2 : string) :
    @refine_cfg PaV _ _ Logic.eq
      (denote_call_args cargs m1)
      (denote_call_args cargs m2).
  Proof using.
    unfold denote_call_args; induction cargs as [| [[t op] attrs] rest IH]; cbn [map_monad].
    - apply ruttc_ret; reflexivity.
    - eapply ruttc_bind.
      + eapply ruttc_bind; [apply refine_cfg_refl | intros v _ <-].
        apply refine_cfg_apply_attrs_msg.
      + intros v' _ <-; eapply ruttc_bind; [exact IH | intros vs _ <-; apply ruttc_ret; reflexivity].
  Qed.

  Lemma refine_cfg_operand_bundles_msg
    (f : exp dtyp) (obs : list (@operand_bundle dtyp)) (l1 l2 : string) :
    @refine_cfg PaV unit unit Logic.eq
      (denote_operand_bundles l1 f obs)
      (denote_operand_bundles l2 f obs).
  Proof using.
    unfold denote_operand_bundles.
    eapply ruttc_bind; [| intros _ _ _; apply ruttc_ret; reflexivity].
    induction obs as [| ob rest IH]; cbn [map_monad]; [apply ruttc_ret; reflexivity |].
    eapply ruttc_bind with (RR := Logic.eq).
    - eapply ruttc_bind; [apply refine_cfg_refl | intros vs _ <-].
      unfold bundle_check.
      destruct (is_llvm_assume f); [| apply ruttc_ret; reflexivity].
      unfold assume_bundle_checks.
      repeat (cbn [find option_map snd];
              match goal with |- context [String.eqb ?a ?b] => destruct (String.eqb a b) end);
        cbn [find option_map snd];
        try (apply ruttc_ret; reflexivity).
      + unfold assume_nonnull, assume_violated, assume_malformed.
        destruct vs as [| p [| ? ?]]; [apply refine_cfg_raise_any | | apply refine_cfg_raise_any].
        destruct (dvalue_ptr_address p) as [a |]; [| apply refine_cfg_raiseUB_any].
        destruct (a =? 0)%Z; [apply refine_cfg_raiseUB_any | apply ruttc_ret; reflexivity].
      + unfold assume_noundef, assume_violated, assume_malformed.
        destruct vs as [| v [| ? ?]]; [apply refine_cfg_raise_any | | apply refine_cfg_raise_any].
        destruct (dvalue_well_defined v); [apply ruttc_ret; reflexivity | apply refine_cfg_raiseUB_any].
      + unfold assume_align, assume_violated, assume_malformed.
        destruct vs as [| p [| al off]]; try apply refine_cfg_raise_any.
        destruct (dvalue_ptr_address p), (bundle_uint al),
                 (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end);
          try apply refine_cfg_raiseUB_any.
        destruct (if is_power_of_two z0 then ((z - z1) mod z0 =? 0)%Z else (z =? 0)%Z);
          [apply ruttc_ret; reflexivity | apply refine_cfg_raiseUB_any].
      + unfold assume_dereferenceable, assume_violated, assume_malformed; cbv zeta.
        destruct vs as [| p [| sz [| ? ?]]]; try apply refine_cfg_raise_any.
        destruct (dvalue_ptr_address p), (bundle_uint sz); try apply refine_cfg_raiseUB_any.
        destruct (z0 =? 0)%Z; [apply ruttc_ret; reflexivity | apply refine_cfg_assert_deref_msg].
      + unfold assume_dereferenceable, assume_violated, assume_malformed; cbv zeta.
        destruct vs as [| p [| sz [| ? ?]]]; try apply refine_cfg_raise_any.
        destruct (dvalue_ptr_address p), (bundle_uint sz); try apply refine_cfg_raiseUB_any.
        destruct (z0 =? 0)%Z; [apply ruttc_ret; reflexivity | apply refine_cfg_assert_deref_msg].
    - intros u1 u2 ->; eapply ruttc_bind; [exact IH | intros bs1 bs2 ->; apply ruttc_ret; reflexivity].
  Qed.

  Lemma refine_cfg_check_call_return_msg
    (fattrs : list fn_attr) (rattrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax)))
    (l1 l2 : string) (vs : list (@dvalue PaV)) (res : @exc PaV + @dvalue PaV) :
    @refine_cfg PaV _ _ Logic.eq
      (check_call_return fattrs rattrs ranges l1 vs res)
      (check_call_return fattrs rattrs ranges l2 vs res).
  Proof using.
    unfold check_call_return.
    eapply ruttc_bind.
    - apply refine_EOU_to_cfg; unfold check_call_result.
      destruct res as [_ | v].
      + destruct (existsb fn_attr_is_nounwind fattrs); constructor; reflexivity.
      + destruct (existsb fn_attr_is_noreturn fattrs); [constructor |].
        destruct (existsb fn_attr_is_nocreateundeforpoison fattrs &&
                  forallb dvalue_well_defined vs && negb (dvalue_well_defined v));
          constructor; reflexivity.
    - intros [] _ _; destruct res as [ex | v]; [apply ruttc_ret; reflexivity |].
      eapply ruttc_bind; [apply refine_cfg_apply_attrs_msg | intros v' _ <-; apply ruttc_ret; reflexivity].
  Qed.

  Lemma denote_phis_strip_eq
    (from : block_id)
    (ps1 ps2 : list (local_id * phi dtyp * list (metadata dtyp)))
    (Heq : List.map (fun '(id, p, md) => (id, p, strip_file_info_mds md)) ps1 =
           List.map (fun '(id, p, md) => (id, p, strip_file_info_mds md)) ps2) :
    @refine_cfg PaV unit unit Logic.eq (denote_phis from ps1) (denote_phis from ps2).
  Proof using.
    unfold denote_phis.
    eapply ruttc_bind.
    - revert ps2 Heq; induction ps1 as [| [[id1 [fm1 dt1 args1]] md1] r1 IH];
        intros [| [[id2 [fm2 dt2 args2]] md2] r2] Heq;
        cbn [List.map] in Heq; try discriminate Heq; cbn [map_monad].
      + apply ruttc_ret; reflexivity.
      + injection Heq as <- <- <- <- _ Htl.
        eapply ruttc_bind.
        * unfold denote_phi; cbv zeta.
          destruct (assoc from args1) as [op |]; [apply refine_cfg_refl | apply refine_cfg_raise_any].
        * intros dv _ <-; eapply ruttc_bind;
            [exact (IH r2 Htl) | intros dvs _ <-; apply ruttc_ret; reflexivity].
    - intros dvs _ <-; apply refine_cfg_refl.
  Qed.

  Lemma denote_instr_strip_eq
    (iid : instr_id) (ins : instr dtyp)
    (md1 md2 : list (metadata dtyp))
    (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (Hmd : strip_file_info_mds md1 = strip_file_info_mds md2) :
    @refine_cfg PaV unit unit Logic.eq
      (denote_instr (iid, ins, md1) va)
      (denote_instr (iid, ins, md2) va).
  Proof using.
    assert (Hla : load_metadata_attrs md1 = load_metadata_attrs md2)
      by (rewrite <- (load_metadata_attrs_strip md1), <- (load_metadata_attrs_strip md2), Hmd; reflexivity).
    assert (Hmr : metadata_range md1 = metadata_range md2)
      by (rewrite <- (metadata_range_strip md1), <- (metadata_range_strip md2), Hmd; reflexivity).
    assert (Hld : load_metadata_dereferenceable md1 = load_metadata_dereferenceable md2)
      by (rewrite <- (load_metadata_dereferenceable_strip md1),
                  <- (load_metadata_dereferenceable_strip md2), Hmd; reflexivity).
    unfold denote_instr; cbv zeta.
    destruct iid as [id | vid], ins as
      [ msg
      | op
      | [dt f] cargs anns obs
      | dt anns
      | dt [du ptr_e] anns
      | [dt val_e] [du ptr_e] anns
      | ss ord
      | cpx
      | armw
      | [t va_e] argty
      | rty clp cs ];
      try apply refine_cfg_raise_any;
      try apply refine_cfg_refl.
    - (* INSTR_Call (IId) *)
      eapply ruttc_bind; [apply refine_cfg_call_args_msg | intros vs _ <-].
      eapply ruttc_bind; [apply refine_cfg_operand_bundles_msg | intros [] _ _].
      eapply ruttc_bind; [apply refine_cfg_refl | intros res _ <-].
      rewrite Hmr; eapply ruttc_bind; [apply refine_cfg_check_call_return_msg | intros res' _ <-].
      apply refine_cfg_refl.
    - (* INSTR_Load *)
      eapply ruttc_bind; [apply refine_cfg_refl | intros a _ <-].
      eapply ruttc_bind; [apply refine_cfg_assert_alignment_msg | intros [] _ _].
      eapply ruttc_bind; [apply refine_cfg_refl | intros v _ <-].
      rewrite Hla, Hmr; eapply ruttc_bind; [apply refine_cfg_apply_value_attrs_msg | intros v' _ <-].
      eapply ruttc_bind.
      + unfold assert_load_dereferenceable; rewrite Hld.
        destruct (load_metadata_dereferenceable md2) as [[on n] |];
          [apply refine_cfg_assert_deref_msg | apply ruttc_ret; reflexivity].
      + intros [] _ _; apply refine_cfg_refl.
    - (* INSTR_Call (IVoid) *)
      eapply ruttc_bind; [apply refine_cfg_call_args_msg | intros vs _ <-].
      eapply ruttc_bind; [apply refine_cfg_operand_bundles_msg | intros [] _ _].
      eapply ruttc_bind; [apply refine_cfg_refl | intros res _ <-].
      rewrite Hmr; eapply ruttc_bind; [apply refine_cfg_check_call_return_msg | intros res' _ <-].
      apply refine_cfg_refl.
    - (* INSTR_Store (IVoid) *)
      eapply ruttc_bind; [apply refine_cfg_refl | intros v _ <-].
      eapply ruttc_bind; [apply refine_cfg_refl | intros a _ <-].
      eapply ruttc_bind; [apply refine_cfg_assert_alignment_msg | intros [] _ _].
      apply refine_cfg_refl.
  Qed.

  Lemma denote_code_strip_eq
    (cd1 cd2 : code dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (Heq : List.map (fun '(iid, ins, md) => (iid, ins, strip_file_info_mds md)) cd1 =
           List.map (fun '(iid, ins, md) => (iid, ins, strip_file_info_mds md)) cd2) :
    @refine_cfg PaV unit unit Logic.eq (denote_code cd1 va) (denote_code cd2 va).
  Proof using.
    revert cd2 Heq; induction cd1 as [| [[iid1 ins1] md1] r1 IH];
      intros [| [[iid2 ins2] md2] r2] Heq;
      cbn [List.map] in Heq; try discriminate Heq; cbn [denote_code loop_monad].
    - apply ruttc_ret; reflexivity.
    - injection Heq as <- <- Hmd Htl.
      eapply ruttc_bind; [exact (denote_instr_strip_eq iid1 ins1 md1 md2 va Hmd) |].
      intros [] _ _; exact (IH r2 Htl).
  Qed.

  Lemma denote_term_strip_eq
    (iid : instr_id) (tm : terminator dtyp)
    (md1 md2 : list (metadata dtyp))
    (Hmd : strip_file_info_mds md1 = strip_file_info_mds md2) :
    @refine_cfg PaV _ _ Logic.eq
      (denote_terminator (iid, tm, md1))
      (denote_terminator (iid, tm, md2)).
  Proof using.
    assert (Hmr : metadata_range md1 = metadata_range md2)
      by (rewrite <- (metadata_range_strip md1), <- (metadata_range_strip md2), Hmd; reflexivity).
    unfold denote_terminator; cbv zeta.
    destruct tm as
      [ [dt op]
      |
      | [dt op] br1 br2
      | br
      | [dt e] def_br dests
      | [dt addr] brs fn
      | [dt expr]
      | [dt fn_e] cargs to_lbl uw_lbl anns obs
      | ];
      try apply refine_cfg_refl;
      try apply refine_cfg_raiseUB_any.
    (* TERM_Invoke *)
    eapply ruttc_bind; [apply refine_cfg_call_args_msg | intros uvs _ <-].
    eapply ruttc_bind; [apply refine_cfg_operand_bundles_msg | intros [] _ _].
    eapply ruttc_bind; [apply refine_cfg_refl | intros fv _ <-].
    eapply ruttc_bind; [apply refine_cfg_refl | intros rv _ <-].
    rewrite Hmr; eapply ruttc_bind; [apply refine_cfg_check_call_return_msg | intros rv' _ <-].
    apply refine_cfg_refl.
  Qed.

  Lemma denote_cfg_strip_gen
    (c1 c2 : CFG.cfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (Hstrip : strip_file_info_cfg c1 = strip_file_info_cfg c2) :
    @refine_cfg PaV _ _ Logic.eq (denote_cfg c1 va) (denote_cfg c2 va).
  Proof using.
    unfold strip_file_info_cfg in Hstrip; injection Hstrip as Hinit Hbks _.
    unfold denote_cfg, denote_cfg_map; rewrite Hinit.
    eapply ruttc_bind.
    - unfold denote_ocfg_map, refine_cfg.
      eapply ruttc_iter with (II := Logic.eq); [| reflexivity].
      intros [from src] _ <-; cbv beta iota.
      rewrite !ScopeTheory.ocfg_map_find_block.
      assert (Hfb :
        option_map strip_file_info_block (find_block (blks c1) src) =
        option_map strip_file_info_block (find_block (blks c2) src)).
      { rewrite <- !(@ScopeTheory.find_block_map _ strip_file_info_block _ src)
          by (intros ?; reflexivity).
        rewrite Hbks; reflexivity. }
      destruct (find_block (blks c1) src) as [bk1 |],
               (find_block (blks c2) src) as [bk2 |];
        cbn [option_map] in Hfb; try discriminate Hfb.
      + unfold strip_file_info_block in Hfb.
        injection Hfb as _ Hph Hcd Htm _.
        destruct (blk_term bk1) as [[ti1 tm1] tmd1] eqn:Et1,
                 (blk_term bk2) as [[ti2 tm2] tmd2] eqn:Et2.
        injection Htm as <- <- Htmd.
        eapply ruttc_bind.
        * unfold denote_block; rewrite Et1, Et2.
          eapply ruttc_bind; [exact (denote_phis_strip_eq from _ _ Hph) | intros [] _ _].
          eapply ruttc_bind; [exact (denote_code_strip_eq _ _ va Hcd) | intros [] _ _].
          exact (denote_term_strip_eq ti1 tm1 tmd1 tmd2 Htmd).
        * intros [tgt | dv] _ <-; cbv beta iota; apply ruttc_ret; constructor; reflexivity.
      + apply ruttc_ret; constructor; reflexivity.
    - intros [bid | uv] _ <-; cbv beta iota;
        [apply refine_cfg_raise_any | apply ruttc_ret; reflexivity].
  Qed.

  Lemma strip_file_info_cfg_idem (c : CFG.cfg dtyp) :
    strip_file_info_cfg (strip_file_info_cfg c) = strip_file_info_cfg c.
  Proof using.
    destruct c as [in0 bks0 ar0]; unfold strip_file_info_cfg; cbn [init blks args]; f_equal.
    induction bks0 as [| [id ph cd [[ti tm] tmd] cm] rest IH]; [reflexivity |].
    cbn [List.map]; f_equal; [| exact IH].
    unfold strip_file_info_block; cbn [blk_id blk_phis blk_code blk_term blk_comments].
    rewrite strip_file_info_mds_idem; f_equal.
    - induction ph as [| [[x p] md] rp IHp]; [reflexivity |].
      cbn [List.map]; rewrite strip_file_info_mds_idem, IHp; reflexivity.
    - induction cd as [| [[i ins] md] rc IHc]; [reflexivity |].
      cbn [List.map]; rewrite strip_file_info_mds_idem, IHc; reflexivity.
  Qed.

  Theorem strip_file_info_mcfg_refines_fwd (M : CFG.mcfg dtyp) :
    @prog_refines IP IPT M (strip_file_info_mcfg M).
  Proof using.
    apply lift_cfg_pass.
    - exact strip_file_info_cfg_block_addresses.
    - intros c va; apply denote_cfg_strip_gen.
      symmetry; apply strip_file_info_cfg_idem.
  Qed.

  Theorem strip_file_info_mcfg_refines_bwd (M : CFG.mcfg dtyp) :
    @prog_refines IP IPT (strip_file_info_mcfg M) M.
  Proof using.
    apply module_defs_ruttc_refines.
    - unfold strip_file_info_mcfg, build_global_environment.
      rewrite map_mcfg_cfg_prototypes,
              (map_mcfg_cfg_block_addresses strip_file_info_cfg M strip_file_info_cfg_block_addresses).
      reflexivity.
    - reflexivity.
    - unfold strip_file_info_mcfg, map_mcfg_cfg; cbn [m_definitions].
      induction (m_definitions M) as [| d rest IH]; [constructor |].
      cbn [List.map map_defn_cfg]; constructor; [| exact IH].
      refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros va; apply denote_cfg_strip_gen, strip_file_info_cfg_idem.
  Qed.

  Theorem check_module_merge_parsed_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge_parsed m_orig m_merged verified_slices = true)
    (Hslices :
       Forall slice_body_refines
         (List.map
            (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
            verified_slices)) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    eapply prog_refines_trans; [apply strip_file_info_mcfg_refines_fwd |].
    eapply prog_refines_trans;
      [exact (check_module_merge_refines _ _ _ Hchk Hslices)
      | apply strip_file_info_mcfg_refines_bwd].
  Qed.

  Corollary validate_module_merge_parsed_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hval : validate_module_merge_parsed m_orig m_merged verified_slices = inr tt)
    (Hslices :
       Forall slice_body_refines
         (List.map
            (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
            verified_slices)) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    apply (check_module_merge_parsed_refines m_orig m_merged verified_slices);
      [exact (proj1 (validate_module_merge_ok_iff _ _ _) Hval) | exact Hslices].
  Qed.

End StripFileInfoRefinement.

Theorem validate_module_merge_parsed_I2F_model_refine
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (ret_typ : dtyp) (entry : function_id)
  (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
  (s1 : @FusedS PInf) (s2 : @FusedS PFin)
  (Hval : validate_module_merge_parsed m_orig m_merged verified_slices = inr tt)
  (Hslices :
     Forall (@slice_body_refines IPZ IPZTheory)
       (List.map
          (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
          verified_slices))
  (Hargs : Forall2 I2F_dvalue args1 args2)
  (Hs : I2F_FusedS s1 s2) :
  @prog_refines IPZ IPZTheory m_orig m_merged /\
  I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
    (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 m_merged) s1)
    (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 m_merged) s2).
Proof.
  split.
  - exact (@validate_module_merge_parsed_refines IPZ IPZTheory m_orig m_merged
             verified_slices Hval Hslices).
  - exact (@I2F_toplevel.model_refine ret_typ entry args1 args2 m_merged s1 s2 Hargs Hs).
Qed.

(** * 7. Surface-Syntax [toplevel_entities] CLI Entrypoint *)

Definition mm_strip_leading_at (s : string) : string :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 64%nat then rest else s
  | EmptyString => EmptyString
  end.

Definition mm_tle_to_dtyp_mcfg
  (tle : toplevel_entities typ (block typ * list (block typ))) : CFG.mcfg dtyp :=
  convert_types (CFG.mcfg_of_tle (ModuleRefs.resolve_module_refs tle)).

Definition validate_module_merge_tle
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (verified_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : string + unit :=
  validate_module_merge_parsed
    (mm_tle_to_dtyp_mcfg orig_tle)
    (mm_tle_to_dtyp_mcfg merged_tle)
    (List.map
       (fun '(fn_str, s_tle, t_tle) =>
          (Name (mm_strip_leading_at fn_str),
           mm_tle_to_dtyp_mcfg s_tle,
           mm_tle_to_dtyp_mcfg t_tle))
       verified_slices).

Theorem validate_module_merge_tle_refines
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (verified_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (Hval : validate_module_merge_tle orig_tle merged_tle verified_slices = inr tt)
  (Hslices :
     Forall (@slice_body_refines IPZ IPZTheory)
       (List.map
          (fun '(fn_str, s_tle, t_tle) =>
             (Name (mm_strip_leading_at fn_str),
              strip_file_info_mcfg (mm_tle_to_dtyp_mcfg s_tle),
              strip_file_info_mcfg (mm_tle_to_dtyp_mcfg t_tle)))
          verified_slices)) :
  @prog_refines IPZ IPZTheory
    (mm_tle_to_dtyp_mcfg orig_tle)
    (mm_tle_to_dtyp_mcfg merged_tle).
Proof.
  unfold validate_module_merge_tle in Hval.
  apply (@validate_module_merge_parsed_refines IPZ IPZTheory _ _ _ Hval).
  clear Hval.
  induction verified_slices as [| [[fn_str s_tle] t_tle] rest IH]; cbn in *.
  - constructor.
  - inversion Hslices as [| ? ? Hhd Htl]; subst.
    constructor; [exact Hhd | exact (IH Htl)].
Qed.


(** * 9. Atomic Certified & Safe-Path [--check-merge] CLI Checker (F-64, E-22) *)

Definition mm_norm_iid (iid : instr_id) : instr_id :=
  match iid with
  | IId x => IId x
  | IVoid _ => IVoid 0%Z
  end.

Lemma mm_norm_iid_idem (iid : instr_id) :
  mm_norm_iid (mm_norm_iid iid) = mm_norm_iid iid.
Proof.
  destruct iid; reflexivity.
Qed.

Definition mm_norm_void_block (bk : block dtyp) : block dtyp :=
  {| blk_id       := blk_id bk;
     blk_phis     := blk_phis bk;
     blk_code     := List.map (fun '(iid, ins, md) => (mm_norm_iid iid, ins, md)) (blk_code bk);
     blk_term     := let '(iid, tm, md) := blk_term bk in (mm_norm_iid iid, tm, md);
     blk_comments := None |}.

Definition mm_norm_void_cfg (c : CFG.cfg dtyp) : CFG.cfg dtyp :=
  {| init := init c;
     blks := List.map mm_norm_void_block (blks c);
     args := args c |}.

Definition mm_norm_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  strip_file_info_mcfg (map_mcfg_cfg mm_norm_void_cfg M).

Lemma mm_norm_void_cfg_idem (c : CFG.cfg dtyp) :
  mm_norm_void_cfg (mm_norm_void_cfg c) = mm_norm_void_cfg c.
Proof.
  destruct c as [in0 bks0 ar0]; unfold mm_norm_void_cfg; cbn [init blks args]; f_equal.
  induction bks0 as [| [id ph cd [[ti tm] tmd] cm] rest IH]; [reflexivity |].
  cbn [List.map]; f_equal; [| exact IH].
  unfold mm_norm_void_block; cbn [blk_id blk_phis blk_code blk_term blk_comments].
  rewrite mm_norm_iid_idem; f_equal.
  induction cd as [| [[i ins] md] rc IHc]; [reflexivity |].
  cbn [List.map]; rewrite mm_norm_iid_idem, IHc; reflexivity.
Qed.

Lemma mm_norm_void_cfg_block_addresses (c : CFG.cfg dtyp) :
  flat_map block_block_addresses (blks (mm_norm_void_cfg c)) =
  flat_map block_block_addresses (blks c).
Proof.
  unfold mm_norm_void_cfg; cbn [blks].
  induction (blks c) as [| bk rest IH]; [reflexivity |]; cbn [List.map flat_map].
  rewrite IH; f_equal.
  unfold block_block_addresses, mm_norm_void_block; cbn [blk_phis blk_code blk_term].
  assert (Hcd : forall cd : code dtyp,
            flat_map (fun '(_, i, _) => instr_block_addresses i)
              (List.map (fun '(iid, ins, md) => (mm_norm_iid iid, ins, md)) cd) =
            flat_map (fun '(_, i, _) => instr_block_addresses i) cd).
  { induction cd as [| [[iid ins] md] rc IHc]; [reflexivity | cbn; rewrite IHc; reflexivity]. }
  rewrite Hcd; destruct (blk_term bk) as [[iid tm] md]; reflexivity.
Qed.

Section NormVoidRefinement.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).

  Lemma denote_instr_norm_iid
    (iid : instr_id) (ins : instr dtyp) (md : list (metadata dtyp))
    (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    @denote_instr PaV (mm_norm_iid iid, ins, md) va =
    @denote_instr PaV (iid, ins, md) va.
  Proof using.
    unfold denote_instr; cbv zeta.
    destruct iid as [id | vid], ins as
      [ msg
      | op
      | [dt f] cargs anns obs
      | dt anns
      | dt [du ptr_e] anns
      | [dt val_e] [du ptr_e] anns
      | ss ord
      | cpx
      | armw
      | [t va_e] argty
      | rty clp cs ]; reflexivity.
  Qed.

  Lemma denote_term_norm_iid
    (iid : instr_id) (tm : terminator dtyp) (md : list (metadata dtyp)) :
    @denote_terminator PaV (mm_norm_iid iid, tm, md) =
    @denote_terminator PaV (iid, tm, md).
  Proof using.
    unfold denote_terminator; cbv zeta.
    destruct iid as [id | vid], tm as
      [ [dt op]
      |
      | [dt op] br1 br2
      | br
      | [dt e] def_br dests
      | [dt addr] brs fn
      | [dt expr]
      | [dt fn_e] cargs to_lbl uw_lbl anns obs
      | ]; reflexivity.
  Qed.

  Lemma denote_code_norm_void_eq
    (cd1 cd2 : code dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (Heq : List.map (fun '(iid, ins, md) => (mm_norm_iid iid, ins, md)) cd1 =
           List.map (fun '(iid, ins, md) => (mm_norm_iid iid, ins, md)) cd2) :
    @refine_cfg PaV unit unit Logic.eq (denote_code cd1 va) (denote_code cd2 va).
  Proof using.
    revert cd2 Heq; induction cd1 as [| [[iid1 ins1] md1] r1 IH];
      intros [| [[iid2 ins2] md2] r2] Heq;
      cbn [List.map] in Heq; try discriminate Heq; cbn [denote_code loop_monad].
    - apply ruttc_ret; reflexivity.
    - injection Heq as Hiid <- <- Htl.
      eapply ruttc_bind.
      + rewrite <- (denote_instr_norm_iid iid1 ins1 md1 va),
                <- (denote_instr_norm_iid iid2 ins1 md1 va), Hiid.
        apply refine_cfg_refl.
      + intros [] _ _; exact (IH r2 Htl).
  Qed.

  Lemma denote_cfg_norm_void_gen
    (c1 c2 : CFG.cfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (Hnorm : mm_norm_void_cfg c1 = mm_norm_void_cfg c2) :
    @refine_cfg PaV _ _ Logic.eq (denote_cfg c1 va) (denote_cfg c2 va).
  Proof using.
    unfold mm_norm_void_cfg in Hnorm; injection Hnorm as Hinit Hbks _.
    unfold denote_cfg, denote_cfg_map; rewrite Hinit.
    eapply ruttc_bind.
    - unfold denote_ocfg_map, refine_cfg.
      eapply ruttc_iter with (II := Logic.eq); [| reflexivity].
      intros [from src] _ <-; cbv beta iota.
      rewrite !ScopeTheory.ocfg_map_find_block.
      assert (Hfb :
        option_map mm_norm_void_block (find_block (blks c1) src) =
        option_map mm_norm_void_block (find_block (blks c2) src)).
      { rewrite <- !(@ScopeTheory.find_block_map _ mm_norm_void_block _ src)
          by (intros ?; reflexivity).
        rewrite Hbks; reflexivity. }
      destruct (find_block (blks c1) src) as [bk1 |],
               (find_block (blks c2) src) as [bk2 |];
        cbn [option_map] in Hfb; try discriminate Hfb.
      + unfold mm_norm_void_block in Hfb.
        injection Hfb as _ Hph Hcd Htm.
        destruct (blk_term bk1) as [[ti1 tm1] tmd1] eqn:Et1,
                 (blk_term bk2) as [[ti2 tm2] tmd2] eqn:Et2.
        injection Htm as Hti <- <-.
        eapply ruttc_bind.
        * unfold denote_block; rewrite Et1, Et2, Hph.
          eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ _].
          eapply ruttc_bind; [exact (denote_code_norm_void_eq _ _ va Hcd) | intros [] _ _].
          rewrite <- (denote_term_norm_iid ti1 tm1 tmd1),
                  <- (denote_term_norm_iid ti2 tm1 tmd1), Hti.
          apply refine_cfg_refl.
        * intros [tgt | dv] _ <-; cbv beta iota; apply ruttc_ret; constructor; reflexivity.
      + apply ruttc_ret; constructor; reflexivity.
    - intros [bid | uv] _ <-; cbv beta iota;
        [apply refine_cfg_raise_any | apply ruttc_ret; reflexivity].
  Qed.

  Lemma mm_norm_void_mcfg_refines_fwd (M : CFG.mcfg dtyp) :
    @prog_refines IP IPT M (map_mcfg_cfg mm_norm_void_cfg M).
  Proof using.
    apply lift_cfg_pass.
    - exact mm_norm_void_cfg_block_addresses.
    - intros c va; apply denote_cfg_norm_void_gen.
      symmetry; apply mm_norm_void_cfg_idem.
  Qed.

  Lemma mm_norm_void_mcfg_refines_bwd (M : CFG.mcfg dtyp) :
    @prog_refines IP IPT (map_mcfg_cfg mm_norm_void_cfg M) M.
  Proof using.
    apply module_defs_ruttc_refines.
    - unfold build_global_environment.
      rewrite map_mcfg_cfg_prototypes,
              (map_mcfg_cfg_block_addresses mm_norm_void_cfg M mm_norm_void_cfg_block_addresses).
      reflexivity.
    - reflexivity.
    - unfold map_mcfg_cfg; cbn [m_definitions].
      induction (m_definitions M) as [| d rest IH]; [constructor |].
      cbn [List.map map_defn_cfg]; constructor; [| exact IH].
      refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros va; apply denote_cfg_norm_void_gen, mm_norm_void_cfg_idem.
  Qed.

  Theorem mm_norm_mcfg_refines_fwd (M : CFG.mcfg dtyp) :
    @prog_refines IP IPT M (mm_norm_mcfg M).
  Proof using.
    unfold mm_norm_mcfg.
    eapply prog_refines_trans;
      [apply mm_norm_void_mcfg_refines_fwd | apply strip_file_info_mcfg_refines_fwd].
  Qed.

  Theorem mm_norm_mcfg_refines_bwd (M : CFG.mcfg dtyp) :
    @prog_refines IP IPT (mm_norm_mcfg M) M.
  Proof using.
    unfold mm_norm_mcfg.
    eapply prog_refines_trans;
      [apply strip_file_info_mcfg_refines_bwd | apply mm_norm_void_mcfg_refines_bwd].
  Qed.

End NormVoidRefinement.

Definition mm_mcfg_sem_eqb (m1 m2 : CFG.mcfg dtyp) : bool :=
  let n1 := mm_norm_mcfg m1 in
  let n2 := mm_norm_mcfg m2 in
  mm_list_eqb mm_global_eqb (m_globals n1) (m_globals n2) &&
  mm_list_eqb mm_declaration_eqb (m_declarations n1) (m_declarations n2) &&
  mm_list_eqb mm_definition_eqb (m_definitions n1) (m_definitions n2).

Lemma mm_exact_core_eq_refines
  {IP : IPtr} {IPT : @IPtrTheory IP}
  (n1 n2 : CFG.mcfg dtyp)
  (Hg : m_globals n2 = m_globals n1)
  (Hd : m_declarations n2 = m_declarations n1)
  (Hdf : m_definitions n2 = m_definitions n1) :
  @prog_refines IP IPT n1 n2.
Proof.
  apply module_defs_ruttc_refines.
  - unfold build_global_environment, mcfg_block_addresses.
    rewrite Hd, Hdf, Hg; reflexivity.
  - exact Hd.
  - rewrite Hdf; clear Hdf.
    induction (m_definitions n1) as [| d rest IH]; [constructor |].
    constructor; [| exact IH].
    refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
    intros va; apply refine_cfg_refl.
Qed.

Theorem mm_mcfg_sem_eqb_refines
  {IP : IPtr} {IPT : @IPtrTheory IP}
  (m1 m2 : CFG.mcfg dtyp)
  (Heqb : mm_mcfg_sem_eqb m1 m2 = true) :
  @prog_refines IP IPT m1 m2 /\ @prog_refines IP IPT m2 m1.
Proof.
  unfold mm_mcfg_sem_eqb in Heqb; cbv zeta in Heqb.
  rewrite !Bool.andb_true_iff in Heqb.
  destruct Heqb as [[Hg Hd] Hdf].
  apply (mm_list_eqb_eq _ mm_global_eqb_eq) in Hg.
  apply (mm_list_eqb_eq _ mm_declaration_eqb_eq) in Hd.
  apply (mm_list_eqb_eq _ mm_definition_eqb_eq) in Hdf.
  split.
  - eapply prog_refines_trans; [apply mm_norm_mcfg_refines_fwd |].
    eapply prog_refines_trans;
      [exact (mm_exact_core_eq_refines _ _ (eq_sym Hg) (eq_sym Hd) (eq_sym Hdf))
      | apply mm_norm_mcfg_refines_bwd].
  - eapply prog_refines_trans; [apply mm_norm_mcfg_refines_fwd |].
    eapply prog_refines_trans;
      [exact (mm_exact_core_eq_refines _ _ Hg Hd Hdf)
      | apply mm_norm_mcfg_refines_bwd].
Qed.

(** Replay the verified Safe-Path pipeline ([Pipeline.optimize_mcfg_typ] +
    [McfgExport.export_mcfg_with_tle]) on [src_tle]. *)
Definition mm_safe_export_mcfg
  (src_tle : toplevel_entities typ (block typ * list (block typ)))
  : option (CFG.mcfg dtyp) :=
  let r_tle := McfgExport.resolve_for_opt_tle src_tle in
  match McfgExport.export_mcfg_with_tle r_tle
          (Pipeline.optimize_mcfg_typ (CFG.mcfg_of_tle r_tle)) with
  | inl _ => None
  | inr exp_tle => Some (mm_tle_to_dtyp_mcfg exp_tle)
  end.

(** Authenticate a [--slice-safe <fn> <src.ll> <opt_safe.ll>] witness inside
    Rocq by re-executing the Safe-Path pipeline on [src_tle] and checking
    semantic AST equivalence against [opt_safe_tle] ([F-64]). *)
Definition check_safe_slice_tle
  (src_tle opt_safe_tle : toplevel_entities typ (block typ * list (block typ))) : bool :=
  match mm_safe_export_mcfg src_tle with
  | None => false
  | Some m_exp => mm_mcfg_sem_eqb m_exp (mm_tle_to_dtyp_mcfg opt_safe_tle)
  end.

Theorem check_safe_slice_tle_sound
  {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
  (src_tle opt_safe_tle : toplevel_entities typ (block typ * list (block typ)))
  (Hsafe : check_safe_slice_tle src_tle opt_safe_tle = true)
  (Hexp_sound :
     forall r_tle M_opt exp_tle,
       r_tle = McfgExport.resolve_for_opt_tle src_tle ->
       M_opt = Pipeline.optimize_mcfg_typ (CFG.mcfg_of_tle r_tle) ->
       McfgExport.export_mcfg_with_tle r_tle M_opt = inr exp_tle ->
       @prog_refines IP IPT M_opt (mm_tle_to_dtyp_mcfg exp_tle)) :
  @prog_refines IP IPT
    (convert_types (CFG.mcfg_of_tle (McfgExport.resolve_for_opt_tle src_tle)))
    (mm_tle_to_dtyp_mcfg opt_safe_tle).
Proof.
  unfold check_safe_slice_tle, mm_safe_export_mcfg in Hsafe; cbv zeta in Hsafe.
  set (r_tle := McfgExport.resolve_for_opt_tle src_tle) in *.
  set (M_opt := Pipeline.optimize_mcfg_typ (CFG.mcfg_of_tle r_tle)) in *.
  destruct (McfgExport.export_mcfg_with_tle r_tle M_opt) as [err | exp_tle] eqn:Eexp;
    [discriminate Hsafe |].
  eapply prog_refines_trans.
  - exact (@Pipeline.optimize_mcfg_refines IP IPT IPWB (convert_types (CFG.mcfg_of_tle r_tle))).
  - eapply prog_refines_trans.
    + exact (Hexp_sound r_tle M_opt exp_tle Logic.eq_refl Logic.eq_refl Eexp).
    + exact (proj1 (mm_mcfg_sem_eqb_refines _ _ Hsafe)).
Qed.

Fixpoint check_all_safe_slices_tle
  (safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)))) : bool :=
  match safe_slices with
  | [] => true
  | (_, s_tle, t_tle) :: rest =>
      check_safe_slice_tle s_tle t_tle && check_all_safe_slices_tle rest
  end.

Fixpoint validate_all_safe_slices_tle
  (safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)))) : string + unit :=
  match safe_slices with
  | [] => inr tt
  | (fn_str, s_tle, t_tle) :: rest =>
      if negb (check_safe_slice_tle s_tle t_tle) then
        inl ("validate_module_merge_certified_tle: --slice-safe failed Safe-Path replay on @" ++
             mm_strip_leading_at fn_str)%string
      else
        validate_all_safe_slices_tle rest
  end.

Lemma validate_all_safe_slices_tle_ok_iff
  (safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)))) :
  validate_all_safe_slices_tle safe_slices = inr tt <->
  check_all_safe_slices_tle safe_slices = true.
Proof.
  induction safe_slices as [| [[fn_str s_tle] t_tle] rest IH];
    cbn [validate_all_safe_slices_tle check_all_safe_slices_tle].
  - split; intros _; reflexivity.
  - destruct (check_safe_slice_tle s_tle t_tle); cbn [negb andb];
      [exact IH | split; intros H; discriminate H].
Qed.

Lemma check_all_safe_slices_tle_Forall
  (safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)))) :
  check_all_safe_slices_tle safe_slices = true <->
  Forall (fun '(_, s_tle, t_tle) => check_safe_slice_tle s_tle t_tle = true) safe_slices.
Proof.
  induction safe_slices as [| [[fn_str s_tle] t_tle] rest IH];
    cbn [check_all_safe_slices_tle].
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite Bool.andb_true_iff, IH; split.
    + intros [Hhd Htl]; constructor; assumption.
    + intros H; inversion H as [| ? ? Hhd Htl]; subst; exact (conj Hhd Htl).
Qed.

Fixpoint validate_flex_defs_merge
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (defs_orig defs_merged : list (definition dtyp (CFG.cfg dtyp)))
  : string + unit :=
  match defs_orig, defs_merged with
  | [], [] => inr tt
  | [], _ :: _ =>
      inl "validate_module_merge_certified_tle: extra function definition in m_merged"%string
  | _ :: _, [] =>
      inl "validate_module_merge_certified_tle: missing function definition in m_merged"%string
  | df_orig :: r1, df_merged :: r2 =>
      let fname := show_raw_id (dc_name (df_prototype df_orig)) in
      if negb (mm_declaration_eqb (df_prototype df_merged) (df_prototype df_orig)) then
        inl ("validate_module_merge_certified_tle: prototype/attribute desync on @" ++ fname)%string
      else if negb (Nat.eqb (List.length (df_args df_merged)) (List.length (df_args df_orig))) then
        inl ("validate_module_merge_certified_tle: formal parameter count desync on @" ++ fname)%string
      else if negb (mm_definition_eqb df_merged df_orig ||
                    existsb (check_slice_matches_defn df_orig df_merged) verified_slices) then
        inl ("validate_module_merge_certified_tle: unverified body modification on @" ++ fname)%string
      else
        validate_flex_defs_merge verified_slices r1 r2
  end.

Definition validate_flex_module_merge
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  : string + unit :=
  if negb (mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig)) then
    inl "validate_module_merge_certified_tle: m_globals layout or alignment mismatch"%string
  else if negb (forallb global_no_extern_weak (m_globals m_orig)) then
    inl "validate_module_merge_certified_tle: extern_weak global linkage is unsupported"%string
  else if negb (mm_list_eqb mm_declaration_eqb
                  (non_intrinsic_decls (m_declarations m_merged))
                  (non_intrinsic_decls (m_declarations m_orig))) then
    inl "validate_module_merge_certified_tle: m_declarations symbol table mismatch"%string
  else if negb (forallb decl_no_extern_weak (m_declarations m_orig)) then
    inl "validate_module_merge_certified_tle: extern_weak declaration linkage is unsupported"%string
  else if negb (forallb decl_no_extern_weak (m_declarations m_merged)) then
    inl "validate_module_merge_certified_tle: extern_weak synthesized declaration linkage is unsupported"%string
  else if negb (forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig)) then
    inl "validate_module_merge_certified_tle: extern_weak definition linkage is unsupported"%string
  else if negb (mm_nodup_raw_ids
                  (List.map dc_name
                     (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig)))) then
    inl "validate_module_merge_certified_tle: duplicate function symbol in declarations/definitions"%string
  else if negb (mm_nodup_raw_ids
                  (List.map dc_name
                     (m_declarations m_merged ++ List.map df_prototype (m_definitions m_merged)))) then
    inl "validate_module_merge_certified_tle: duplicate function symbol in merged declarations/definitions"%string
  else if negb (mm_list_eqb mm_block_addr_eqb
                  (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
                  (nodup block_address_eq_dec (mcfg_block_addresses m_orig))) then
    inl "validate_module_merge_certified_tle: module blockaddress table mismatch"%string
  else
    validate_flex_defs_merge verified_slices (m_definitions m_orig) (m_definitions m_merged).

Lemma validate_flex_defs_merge_ok_iff
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  forall defs_orig defs_merged,
    validate_flex_defs_merge verified_slices defs_orig defs_merged = inr tt <->
    check_flex_defs_merge verified_slices defs_orig defs_merged = true.
Proof.
  induction defs_orig as [| d1 r1 IH]; intros [| d2 r2];
    cbn [validate_flex_defs_merge check_flex_defs_merge].
  - split; intros _; reflexivity.
  - split; intros H; discriminate H.
  - split; intros H; discriminate H.
  - unfold check_flex_defn_pair; cbv zeta.
    destruct (mm_declaration_eqb (df_prototype d2) (df_prototype d1)); cbn [negb andb];
      [| split; intros H; discriminate H].
    destruct (Nat.eqb (List.length (df_args d2)) (List.length (df_args d1))); cbn [negb andb];
      [| split; intros H; discriminate H].
    destruct (mm_definition_eqb d2 d1 ||
              existsb (check_slice_matches_defn d1 d2) verified_slices);
      cbn [negb andb]; [exact (IH r2) | split; intros H; discriminate H].
Qed.

Theorem validate_flex_module_merge_ok_iff
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  validate_flex_module_merge m_orig m_merged verified_slices = inr tt <->
  check_flex_module_merge m_orig m_merged verified_slices = true.
Proof.
  unfold validate_flex_module_merge, check_flex_module_merge.
  destruct (mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig));
    cbn [negb andb]; [| split; intros H; discriminate H].
  destruct (forallb global_no_extern_weak (m_globals m_orig));
    cbn [negb andb]; [| split; intros H; discriminate H].
  destruct (mm_list_eqb mm_declaration_eqb
              (non_intrinsic_decls (m_declarations m_merged))
              (non_intrinsic_decls (m_declarations m_orig)));
    cbn [negb andb]; [| split; intros H; discriminate H].
  destruct (forallb decl_no_extern_weak (m_declarations m_orig));
    cbn [negb andb]; [| split; intros H; discriminate H].
  destruct (forallb decl_no_extern_weak (m_declarations m_merged));
    cbn [negb andb]; [| split; intros H; discriminate H].
  destruct (forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig));
    cbn [negb andb]; [| split; intros H; discriminate H].
  destruct (mm_nodup_raw_ids
              (List.map dc_name
                 (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig))));
    cbn [negb andb]; [| split; intros H; discriminate H].
  destruct (mm_nodup_raw_ids
              (List.map dc_name
                 (m_declarations m_merged ++ List.map df_prototype (m_definitions m_merged))));
    cbn [negb andb]; [| split; intros H; discriminate H].
  destruct (mm_list_eqb mm_block_addr_eqb
              (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
              (nodup block_address_eq_dec (mcfg_block_addresses m_orig)));
    cbn [negb andb]; [| split; intros H; discriminate H].
  apply validate_flex_defs_merge_ok_iff.
Qed.

Definition mm_single_def_mcfg
  (base : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp)) : CFG.mcfg dtyp :=
  {| m_name         := m_name base;
     m_target       := m_target base;
     m_datalayout   := m_datalayout base;
     m_type_defs    := m_type_defs base;
     m_globals      := m_globals base;
     m_declarations := m_declarations base;
     m_definitions  := [df] |}.

Fixpoint mm_zip_safe_defs
  (n_orig n_exp : CFG.mcfg dtyp)
  (defs_orig defs_exp : list (definition dtyp (CFG.cfg dtyp)))
  : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) :=
  match defs_orig, defs_exp with
  | d1 :: r1, d2 :: r2 =>
      (dc_name (df_prototype d1),
       mm_single_def_mcfg n_orig d1,
       mm_single_def_mcfg n_exp d2) ::
      mm_zip_safe_defs n_orig n_exp r1 r2
  | _, _ => []
  end.

Definition mm_tle_slice_to_norm_dtyp
  (entry :
    string *
    toplevel_entities typ (block typ * list (block typ)) *
    toplevel_entities typ (block typ * list (block typ)))
  : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp :=
  let '(fn_str, s_tle, t_tle) := entry in
  (Name (mm_strip_leading_at fn_str),
   mm_norm_mcfg (mm_tle_to_dtyp_mcfg s_tle),
   mm_norm_mcfg (mm_tle_to_dtyp_mcfg t_tle)).

Definition mm_is_empty_list {A : Type} (xs : list A) : bool :=
  match xs with
  | [] => true
  | _ :: _ => false
  end.

Lemma mm_is_empty_list_spec {A : Type} (xs : list A) :
  mm_is_empty_list xs = true <-> xs = [].
Proof.
  destruct xs; cbn [mm_is_empty_list]; split; intros H;
    try reflexivity; discriminate H.
Qed.

Definition mm_mcfg_no_extern_weak (m : CFG.mcfg dtyp) : bool :=
  forallb global_no_extern_weak (m_globals m) &&
  forallb decl_no_extern_weak (m_declarations m) &&
  forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m).

(** Certified & Safe-Path [--check-merge] boolean checker ([F-64], [E-22]):
    1. Authenticates every [--slice-safe] pair inside Rocq via [check_safe_slice_tle].
    2. Verifies whole-module global/declaration/prototype/blockaddress invariants
       and per-definition provenance against Fast-Path [cert_slices] (already
       authenticated by [CertValidator.validate_tle_pair_with_cert_str]),
       Safe-Path [safe_slices], unchanged pass-through definitions, or lazy
       whole-module Safe-Path pass-through on [orig_tle]. *)
Definition check_module_merge_certified_tle
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : bool :=
  check_all_safe_slices_tle safe_slices &&
  let n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle) in
  let n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle) in
  let explicit_slices :=
    List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices)
  in
  if check_flex_module_merge n_orig n_merged explicit_slices then
    true
  else if mm_mcfg_no_extern_weak n_orig &&
          mm_mcfg_no_extern_weak n_merged &&
          mm_is_empty_list cert_slices &&
          mm_is_empty_list safe_slices &&
          check_safe_slice_tle orig_tle merged_tle then
    true
  else
    match mm_safe_export_mcfg orig_tle with
    | None => false
    | Some m_exp_orig =>
        let n_exp := mm_norm_mcfg m_exp_orig in
        let wm_slices :=
          mm_zip_safe_defs n_orig n_exp (m_definitions n_orig) (m_definitions n_exp)
        in
        check_flex_module_merge n_orig n_merged (explicit_slices ++ wm_slices)
    end.

(** Diagnostic CLI entrypoint extracted to OCaml ([Extract.v], [cert_validator.ml]). *)
Definition validate_module_merge_certified_tle
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : string + unit :=
  match validate_all_safe_slices_tle safe_slices with
  | inl err => inl err
  | inr tt =>
      let n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle) in
      let n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle) in
      let explicit_slices :=
        List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices)
      in
      match validate_flex_module_merge n_orig n_merged explicit_slices with
      | inr tt => inr tt
      | inl err_explicit =>
          if mm_mcfg_no_extern_weak n_orig &&
             mm_mcfg_no_extern_weak n_merged &&
             mm_is_empty_list cert_slices &&
             mm_is_empty_list safe_slices &&
             check_safe_slice_tle orig_tle merged_tle then
            inr tt
          else
            match mm_safe_export_mcfg orig_tle with
            | None => inl err_explicit
            | Some m_exp_orig =>
                let n_exp := mm_norm_mcfg m_exp_orig in
                let wm_slices :=
                  mm_zip_safe_defs n_orig n_exp (m_definitions n_orig) (m_definitions n_exp)
                in
                validate_flex_module_merge n_orig n_merged (explicit_slices ++ wm_slices)
            end
      end
  end.

Theorem validate_module_merge_certified_tle_ok_iff
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)))) :
  validate_module_merge_certified_tle orig_tle merged_tle cert_slices safe_slices = inr tt <->
  check_module_merge_certified_tle orig_tle merged_tle cert_slices safe_slices = true.
Proof.
  unfold validate_module_merge_certified_tle, check_module_merge_certified_tle; cbv zeta.
  set (n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)).
  set (n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle)).
  set (explicit_slices := List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices)).
  destruct (validate_all_safe_slices_tle safe_slices) as [err | []] eqn:Esafe.
  - assert (Hsf : check_all_safe_slices_tle safe_slices = false).
    { destruct (check_all_safe_slices_tle safe_slices) eqn:Ec; [| reflexivity].
      apply validate_all_safe_slices_tle_ok_iff in Ec; congruence. }
    rewrite Hsf; cbn [andb]; split; intros H; discriminate H.
  - assert (Hst : check_all_safe_slices_tle safe_slices = true)
      by (apply validate_all_safe_slices_tle_ok_iff, Esafe).
    rewrite Hst; cbn [andb].
    destruct (validate_flex_module_merge n_orig n_merged explicit_slices)
      as [err_ex | []] eqn:Eflex.
    + assert (Hff : check_flex_module_merge n_orig n_merged explicit_slices = false).
      { destruct (check_flex_module_merge n_orig n_merged explicit_slices) eqn:Ec; [| reflexivity].
        apply validate_flex_module_merge_ok_iff in Ec; congruence. }
      rewrite Hff.
      destruct (mm_mcfg_no_extern_weak n_orig &&
                mm_mcfg_no_extern_weak n_merged &&
                mm_is_empty_list cert_slices &&
                mm_is_empty_list safe_slices &&
                check_safe_slice_tle orig_tle merged_tle);
        [split; intros _; reflexivity |].
      destruct (mm_safe_export_mcfg orig_tle) as [m_exp_orig |];
        [apply validate_flex_module_merge_ok_iff | split; intros H; discriminate H].
    + assert (Hft : check_flex_module_merge n_orig n_merged explicit_slices = true)
        by (apply validate_flex_module_merge_ok_iff, Eflex).
      rewrite Hft; split; intros _; reflexivity.
Qed.

Lemma mm_Forall_app {A : Type} (P : A -> Prop) (xs ys : list A) :
  Forall P xs -> Forall P ys -> Forall P (xs ++ ys).
Proof.
  intros Hx Hy; induction Hx as [| x l Hpx _ IH]; cbn [app];
    [exact Hy | constructor; [exact Hpx | exact IH]].
Qed.

(** Provenance inversion theorem for [validate_module_merge_certified_tle = inr tt]:
    every [--slice-safe] entry passes [check_safe_slice_tle], and [merged_tle]
    satisfies one of the three verified provenance modes ([F-64], [E-22]). *)
Theorem validate_module_merge_certified_tle_cases
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (Hval : validate_module_merge_certified_tle orig_tle merged_tle cert_slices safe_slices = inr tt) :
  let n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle) in
  let n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle) in
  let explicit_slices :=
    List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices)
  in
  Forall (fun '(_, s_tle, t_tle) => check_safe_slice_tle s_tle t_tle = true) safe_slices /\
  (check_flex_module_merge n_orig n_merged explicit_slices = true \/
   (cert_slices = [] /\ safe_slices = [] /\ check_safe_slice_tle orig_tle merged_tle = true) \/
   exists m_exp_orig,
     mm_safe_export_mcfg orig_tle = Some m_exp_orig /\
     check_flex_module_merge n_orig n_merged
       (explicit_slices ++
        mm_zip_safe_defs n_orig (mm_norm_mcfg m_exp_orig)
          (m_definitions n_orig) (m_definitions (mm_norm_mcfg m_exp_orig))) = true).
Proof.
  cbv zeta.
  apply validate_module_merge_certified_tle_ok_iff in Hval.
  unfold check_module_merge_certified_tle in Hval; cbv zeta in Hval.
  apply Bool.andb_true_iff in Hval as [Hsafes Hrest].
  split; [apply check_all_safe_slices_tle_Forall, Hsafes |].
  set (n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)) in *.
  set (n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle)) in *.
  set (explicit_slices := List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices)) in *.
  destruct (check_flex_module_merge n_orig n_merged explicit_slices) eqn:Eex;
    [left; reflexivity |].
  destruct (mm_mcfg_no_extern_weak n_orig &&
            mm_mcfg_no_extern_weak n_merged &&
            mm_is_empty_list cert_slices &&
            mm_is_empty_list safe_slices &&
            check_safe_slice_tle orig_tle merged_tle) eqn:Ewm.
  - right; left.
    rewrite !Bool.andb_true_iff in Ewm.
    destruct Ewm as [[[[_ _] Hc] Hs] Hsafe_wm].
    apply mm_is_empty_list_spec in Hc; apply mm_is_empty_list_spec in Hs.
    exact (conj Hc (conj Hs Hsafe_wm)).
  - right; right.
    destruct (mm_safe_export_mcfg orig_tle) as [m_exp_orig |]; [| discriminate Hrest].
    exists m_exp_orig; exact (conj Logic.eq_refl Hrest).
Qed.

(** Master End-to-End Soundness Theorem for Certified & Safe-Path [--check-merge]
    ([F-59], [F-64], [E-22]): lifts authenticated Fast-Path [cert_slices] and
    Safe-Path [safe_slices] (plus whole-module Safe-Path pass-through) to
    whole-module value- & [DrawE]-refinement ([prog_value_draw_refines]) or
    whole-module Safe-Path [@prog_refines]. *)
Theorem validate_module_merge_certified_tle_refines
  {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (Hval : validate_module_merge_certified_tle orig_tle merged_tle cert_slices safe_slices = inr tt)
  (Hcert :
     Forall (@slice_value_refines IP IPT)
       (List.map mm_tle_slice_to_norm_dtyp cert_slices))
  (Hsafe_slices :
     forall fn_str s_tle t_tle,
       In (fn_str, s_tle, t_tle) safe_slices ->
       check_safe_slice_tle s_tle t_tle = true ->
       @slice_value_refines IP IPT (mm_tle_slice_to_norm_dtyp (fn_str, s_tle, t_tle)))
  (Hwm_slices :
     forall m_exp_orig,
       mm_safe_export_mcfg orig_tle = Some m_exp_orig ->
       Forall (@slice_value_refines IP IPT)
         (mm_zip_safe_defs
            (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle))
            (mm_norm_mcfg m_exp_orig)
            (m_definitions (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)))
            (m_definitions (mm_norm_mcfg m_exp_orig))))
  (Hexp_orig_sound :
     forall r_tle M_opt exp_tle,
       r_tle = McfgExport.resolve_for_opt_tle orig_tle ->
       M_opt = Pipeline.optimize_mcfg_typ (CFG.mcfg_of_tle r_tle) ->
       McfgExport.export_mcfg_with_tle r_tle M_opt = inr exp_tle ->
       @prog_refines IP IPT M_opt (mm_tle_to_dtyp_mcfg exp_tle)) :
  (@prog_refines IP IPT (mm_tle_to_dtyp_mcfg orig_tle)
     (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)) /\
   @prog_value_draw_refines IP IPT
     (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle))
     (mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle)) /\
   @prog_refines IP IPT
     (mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle))
     (mm_tle_to_dtyp_mcfg merged_tle))
  \/
  (cert_slices = [] /\
   safe_slices = [] /\
   @prog_refines IP IPT
     (convert_types (CFG.mcfg_of_tle (McfgExport.resolve_for_opt_tle orig_tle)))
     (mm_tle_to_dtyp_mcfg merged_tle)).
Proof.
  destruct (validate_module_merge_certified_tle_cases
              orig_tle merged_tle cert_slices safe_slices Hval)
    as [Hsafes Hmode].
  assert (Hsafe_list :
    Forall (@slice_value_refines IP IPT)
      (List.map mm_tle_slice_to_norm_dtyp safe_slices)).
  { rewrite Forall_forall in Hsafes |- *.
    intros entry Hin.
    apply in_map_iff in Hin as [[[fn_str s_tle] t_tle] [<- Hin_s]].
    pose proof (Hsafes (fn_str, s_tle, t_tle) Hin_s) as Hchk_s.
    exact (Hsafe_slices fn_str s_tle t_tle Hin_s Hchk_s). }
  assert (Hexplicit :
    Forall (@slice_value_refines IP IPT)
      (List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices))).
  { rewrite map_app; exact (mm_Forall_app _ _ _ Hcert Hsafe_list). }
  destruct Hmode as [Hex | [(-> & -> & Hwm_direct) | (m_exp_orig & Hexp_eq & Hwm_flex)]].
  - left; split; [apply mm_norm_mcfg_refines_fwd | split; [| apply mm_norm_mcfg_refines_bwd]].
    exact (@check_flex_module_merge_value_refines IP IPT _ _ _ Hex Hexplicit).
  - right; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
    exact (@check_safe_slice_tle_sound IP IPT IPWB orig_tle merged_tle Hwm_direct Hexp_orig_sound).
  - left; split; [apply mm_norm_mcfg_refines_fwd | split; [| apply mm_norm_mcfg_refines_bwd]].
    exact (@check_flex_module_merge_value_refines IP IPT _ _ _ Hwm_flex
             (mm_Forall_app _ _ _ Hexplicit (Hwm_slices m_exp_orig Hexp_eq))).
Qed.

(** Call-free leaf specialization of [validate_module_merge_certified_tle_refines]
    lifting [Poison -> Concrete] and [freeze] ([DrawE]) slices WITHOUT requiring
    [noundef] on function prototypes ([F-59], [F-64]). *)
Corollary validate_module_merge_certified_tle_leaf_refines
  {IP : IPtr} {IPT : @IPtrTheory IP}
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (Hchk_ex :
     check_flex_module_merge
       (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle))
       (mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle))
       (List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices)) = true)
  (Hval : validate_module_merge_certified_tle orig_tle merged_tle cert_slices safe_slices = inr tt)
  (Hunchanged_leaf :
     forall df,
       In df (m_definitions (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle))) ->
       forall fvs va,
         List.length fvs = List.length (df_args df) ->
         @cfg_local_vdraw_leaf_sim IP IPT _ _ (fun _ _ r1 r2 => mm_ret_dvalue_refines r1 r2)
           (init_local_env (List.combine (df_args df) fvs))
           (init_local_env (List.combine (df_args df) fvs))
           (denote_cfg (df_instrs df) va)
           (denote_cfg (df_instrs df) va))
  (Hcert_leaf :
     Forall (@slice_leaf_value_refines IP IPT)
       (List.map mm_tle_slice_to_norm_dtyp cert_slices))
  (Hsafe_leaf :
     forall fn_str s_tle t_tle,
       In (fn_str, s_tle, t_tle) safe_slices ->
       check_safe_slice_tle s_tle t_tle = true ->
       @slice_leaf_value_refines IP IPT (mm_tle_slice_to_norm_dtyp (fn_str, s_tle, t_tle))) :
  @prog_value_draw_refines IP IPT
    (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle))
    (mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle)).
Proof.
  destruct (validate_module_merge_certified_tle_cases
              orig_tle merged_tle cert_slices safe_slices Hval)
    as [Hsafes _].
  assert (Hsafe_list :
    Forall (@slice_leaf_value_refines IP IPT)
      (List.map mm_tle_slice_to_norm_dtyp safe_slices)).
  { rewrite Forall_forall in Hsafes |- *.
    intros entry Hin.
    apply in_map_iff in Hin as [[[fn_str s_tle] t_tle] [<- Hin_s]].
    pose proof (Hsafes (fn_str, s_tle, t_tle) Hin_s) as Hchk_s.
    exact (Hsafe_leaf fn_str s_tle t_tle Hin_s Hchk_s). }
  apply (@check_flex_module_merge_leaf_value_refines IP IPT _ _ _ Hchk_ex Hunchanged_leaf).
  rewrite map_app; exact (mm_Forall_app _ _ _ Hcert_leaf Hsafe_list).
Qed.


(** * 10. Composed Safe-Path -> Fast-Path [--slice-safe-cert] Verification *)

Fixpoint mm_lookup_composed_mid_def
  (fid : function_id)
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : option (definition dtyp (CFG.cfg dtyp)) :=
  match safe_cert_slices with
  | [] => None
  | (fn_str, _, m_tle, _) :: rest =>
      if raw_id_eqb (Name (mm_strip_leading_at fn_str)) fid then
        match m_definitions (mm_norm_mcfg (mm_tle_to_dtyp_mcfg m_tle)) with
        | [df_mid] => Some df_mid
        | _ => None
        end
      else
        mm_lookup_composed_mid_def fid rest
  end.

Definition mm_build_mid_defs
  (defs_orig : list (definition dtyp (CFG.cfg dtyp)))
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : list (definition dtyp (CFG.cfg dtyp)) :=
  List.map
    (fun df_orig =>
       match mm_lookup_composed_mid_def (dc_name (df_prototype df_orig)) safe_cert_slices with
       | Some df_mid =>
           {| df_prototype := df_prototype df_orig;
              df_args      := df_args df_mid;
              df_instrs    := df_instrs df_mid |}
       | None => df_orig
       end)
    defs_orig.

Definition mm_build_mid_mcfg
  (n_orig : CFG.mcfg dtyp)
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : CFG.mcfg dtyp :=
  {| m_name         := m_name n_orig;
     m_target       := m_target n_orig;
     m_datalayout   := m_datalayout n_orig;
     m_type_defs    := m_type_defs n_orig;
     m_globals      := m_globals n_orig;
     m_declarations := m_declarations n_orig;
     m_definitions  := mm_build_mid_defs (m_definitions n_orig) safe_cert_slices |}.

Definition mm_composed_stage1_slices
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))) :=
  List.map (fun '(fn_str, s_tle, m_tle, _) => (fn_str, s_tle, m_tle)) safe_cert_slices.

Definition mm_composed_stage2_slices
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))) :=
  List.map (fun '(fn_str, _, m_tle, f_tle) => (fn_str, m_tle, f_tle)) safe_cert_slices.

(** Two-stage Safe-Path -> Fast-Path composed [--check-merge] boolean checker
    handling [--slice-cert], [--slice-safe], and [--slice-safe-cert] uniformly. *)
Definition check_module_merge_certified_tle_composed
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : bool :=
  match safe_cert_slices with
  | [] => check_module_merge_certified_tle orig_tle merged_tle cert_slices safe_slices
  | _ :: _ =>
      let stage1_only := mm_composed_stage1_slices safe_cert_slices in
      let stage2_fast := mm_composed_stage2_slices safe_cert_slices in
      let all_safe := safe_slices ++ stage1_only in
      let n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle) in
      let n_mid := mm_build_mid_mcfg n_orig safe_cert_slices in
      let n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle) in
      let s1_dtyp := List.map mm_tle_slice_to_norm_dtyp stage1_only in
      let s2_dtyp :=
        List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices ++ stage2_fast)
      in
      check_all_safe_slices_tle all_safe &&
      check_flex_module_merge n_orig n_mid s1_dtyp &&
      if check_flex_module_merge n_mid n_merged s2_dtyp then
        true
      else
        match mm_safe_export_mcfg orig_tle with
        | None => false
        | Some m_exp_orig =>
            let n_exp := mm_norm_mcfg m_exp_orig in
            let wm_slices :=
              mm_zip_safe_defs n_orig n_exp (m_definitions n_orig) (m_definitions n_exp)
            in
            check_flex_module_merge n_mid n_merged (s2_dtyp ++ wm_slices)
        end
  end.

(** Diagnostic CLI entrypoint extracted to OCaml ([Extract.v], [cert_validator.ml]). *)
Definition validate_module_merge_certified_tle_composed
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : string + unit :=
  match safe_cert_slices with
  | [] => validate_module_merge_certified_tle orig_tle merged_tle cert_slices safe_slices
  | _ :: _ =>
      let stage1_only := mm_composed_stage1_slices safe_cert_slices in
      let stage2_fast := mm_composed_stage2_slices safe_cert_slices in
      let all_safe := safe_slices ++ stage1_only in
      match validate_all_safe_slices_tle all_safe with
      | inl err => inl err
      | inr tt =>
          let n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle) in
          let n_mid := mm_build_mid_mcfg n_orig safe_cert_slices in
          let n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle) in
          let s1_dtyp := List.map mm_tle_slice_to_norm_dtyp stage1_only in
          let s2_dtyp :=
            List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices ++ stage2_fast)
          in
          match validate_flex_module_merge n_orig n_mid s1_dtyp with
          | inl err1 => inl err1
          | inr tt =>
              match validate_flex_module_merge n_mid n_merged s2_dtyp with
              | inr tt => inr tt
              | inl err2 =>
                  match mm_safe_export_mcfg orig_tle with
                  | None => inl err2
                  | Some m_exp_orig =>
                      let n_exp := mm_norm_mcfg m_exp_orig in
                      let wm_slices :=
                        mm_zip_safe_defs n_orig n_exp (m_definitions n_orig) (m_definitions n_exp)
                      in
                      validate_flex_module_merge n_mid n_merged (s2_dtyp ++ wm_slices)
                  end
              end
          end
      end
  end.

Theorem validate_module_merge_certified_tle_composed_ok_iff
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)))) :
  validate_module_merge_certified_tle_composed
    orig_tle merged_tle cert_slices safe_slices safe_cert_slices = inr tt <->
  check_module_merge_certified_tle_composed
    orig_tle merged_tle cert_slices safe_slices safe_cert_slices = true.
Proof.
  destruct safe_cert_slices as [| p rest];
    [exact (validate_module_merge_certified_tle_ok_iff orig_tle merged_tle cert_slices safe_slices) |].
  unfold validate_module_merge_certified_tle_composed, check_module_merge_certified_tle_composed;
    cbv zeta.
  set (stage1_only := mm_composed_stage1_slices (p :: rest)).
  set (stage2_fast := mm_composed_stage2_slices (p :: rest)).
  set (all_safe := safe_slices ++ stage1_only).
  set (n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)).
  set (n_mid := mm_build_mid_mcfg n_orig (p :: rest)).
  set (n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle)).
  set (s1_dtyp := List.map mm_tle_slice_to_norm_dtyp stage1_only).
  set (s2_dtyp := List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices ++ stage2_fast)).
  destruct (validate_all_safe_slices_tle all_safe) as [err | []] eqn:Esafe.
  - assert (Hsf : check_all_safe_slices_tle all_safe = false).
    { destruct (check_all_safe_slices_tle all_safe) eqn:Ec; [| reflexivity].
      apply validate_all_safe_slices_tle_ok_iff in Ec; congruence. }
    rewrite Hsf; cbn [andb]; split; intros H; discriminate H.
  - assert (Hst : check_all_safe_slices_tle all_safe = true)
      by (apply validate_all_safe_slices_tle_ok_iff, Esafe).
    rewrite Hst; cbn [andb].
    destruct (validate_flex_module_merge n_orig n_mid s1_dtyp) as [err1 | []] eqn:E1.
    + assert (H1f : check_flex_module_merge n_orig n_mid s1_dtyp = false).
      { destruct (check_flex_module_merge n_orig n_mid s1_dtyp) eqn:Ec; [| reflexivity].
        apply validate_flex_module_merge_ok_iff in Ec; congruence. }
      rewrite H1f; cbn [andb]; split; intros H; discriminate H.
    + assert (H1t : check_flex_module_merge n_orig n_mid s1_dtyp = true)
        by (apply validate_flex_module_merge_ok_iff, E1).
      rewrite H1t; cbn [andb].
      destruct (validate_flex_module_merge n_mid n_merged s2_dtyp) as [err2 | []] eqn:E2.
      * assert (H2f : check_flex_module_merge n_mid n_merged s2_dtyp = false).
        { destruct (check_flex_module_merge n_mid n_merged s2_dtyp) eqn:Ec; [| reflexivity].
          apply validate_flex_module_merge_ok_iff in Ec; congruence. }
        rewrite H2f.
        destruct (mm_safe_export_mcfg orig_tle) as [m_exp_orig |];
          [apply validate_flex_module_merge_ok_iff | split; intros H; discriminate H].
      * assert (H2t : check_flex_module_merge n_mid n_merged s2_dtyp = true)
          by (apply validate_flex_module_merge_ok_iff, E2).
        rewrite H2t; split; intros _; reflexivity.
Qed.

(** End-to-End Soundness Theorem for Composed [--slice-safe-cert] Module Merging. *)
Theorem validate_module_merge_certified_tle_composed_refines
  {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_slices safe_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (safe_cert_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (Hval :
     validate_module_merge_certified_tle_composed
       orig_tle merged_tle cert_slices safe_slices safe_cert_slices = inr tt)
  (Hcert :
     Forall (@slice_value_refines IP IPT)
       (List.map mm_tle_slice_to_norm_dtyp cert_slices))
  (Hsafe_slices :
     forall fn_str s_tle t_tle,
       (In (fn_str, s_tle, t_tle) safe_slices \/
        exists f_tle, In (fn_str, s_tle, t_tle, f_tle) safe_cert_slices) ->
       check_safe_slice_tle s_tle t_tle = true ->
       @slice_value_refines IP IPT (mm_tle_slice_to_norm_dtyp (fn_str, s_tle, t_tle)))
  (Hstage2_cert :
     Forall (@slice_value_refines IP IPT)
       (List.map mm_tle_slice_to_norm_dtyp (mm_composed_stage2_slices safe_cert_slices)))
  (Hwm_slices :
     forall m_exp_orig,
       mm_safe_export_mcfg orig_tle = Some m_exp_orig ->
       Forall (@slice_value_refines IP IPT)
         (mm_zip_safe_defs
            (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle))
            (mm_norm_mcfg m_exp_orig)
            (m_definitions (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)))
            (m_definitions (mm_norm_mcfg m_exp_orig))))
  (Hexp_orig_sound :
     forall r_tle M_opt exp_tle,
       r_tle = McfgExport.resolve_for_opt_tle orig_tle ->
       M_opt = Pipeline.optimize_mcfg_typ (CFG.mcfg_of_tle r_tle) ->
       McfgExport.export_mcfg_with_tle r_tle M_opt = inr exp_tle ->
       @prog_refines IP IPT M_opt (mm_tle_to_dtyp_mcfg exp_tle)) :
  (@prog_refines IP IPT (mm_tle_to_dtyp_mcfg orig_tle)
     (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)) /\
   (exists n_mid,
      @prog_value_draw_refines IP IPT
        (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)) n_mid /\
      @prog_value_draw_refines IP IPT
        n_mid (mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle))) /\
   @prog_refines IP IPT
     (mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle))
     (mm_tle_to_dtyp_mcfg merged_tle))
  \/
  (cert_slices = [] /\
   safe_slices = [] /\
   safe_cert_slices = [] /\
   @prog_refines IP IPT
     (convert_types (CFG.mcfg_of_tle (McfgExport.resolve_for_opt_tle orig_tle)))
     (mm_tle_to_dtyp_mcfg merged_tle)).
Proof.
  destruct safe_cert_slices as [| p rest].
  - cbn [validate_module_merge_certified_tle_composed] in Hval.
    assert (Hsafe0 :
      forall fn_str s_tle t_tle,
        In (fn_str, s_tle, t_tle) safe_slices ->
        check_safe_slice_tle s_tle t_tle = true ->
        @slice_value_refines IP IPT (mm_tle_slice_to_norm_dtyp (fn_str, s_tle, t_tle)))
      by (intros fn s t Hin; exact (Hsafe_slices fn s t (or_introl Hin))).
    destruct (@validate_module_merge_certified_tle_refines IP IPT IPWB
                orig_tle merged_tle cert_slices safe_slices
                Hval Hcert Hsafe0 Hwm_slices Hexp_orig_sound)
      as [(Hfwd & Hvd & Hbwd) | (Hc & Hs & Hwm)].
    + left; refine (conj Hfwd (conj _ Hbwd)).
      exists (mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)).
      split; [apply prog_value_draw_refines_refl | exact Hvd].
    + right; exact (conj Hc (conj Hs (conj Logic.eq_refl Hwm))).
  - apply validate_module_merge_certified_tle_composed_ok_iff in Hval.
    unfold check_module_merge_certified_tle_composed in Hval; cbv zeta in Hval.
    apply Bool.andb_true_iff in Hval as [Hband Hstage2].
    apply Bool.andb_true_iff in Hband as [Hall_safe Hstage1].
    apply check_all_safe_slices_tle_Forall in Hall_safe.
    set (stage1_only := mm_composed_stage1_slices (p :: rest)) in *.
    set (stage2_fast := mm_composed_stage2_slices (p :: rest)) in *.
    set (n_orig := mm_norm_mcfg (mm_tle_to_dtyp_mcfg orig_tle)) in *.
    set (n_mid := mm_build_mid_mcfg n_orig (p :: rest)) in *.
    set (n_merged := mm_norm_mcfg (mm_tle_to_dtyp_mcfg merged_tle)) in *.
    assert (Hsafes_all :
      Forall (@slice_value_refines IP IPT)
        (List.map mm_tle_slice_to_norm_dtyp (safe_slices ++ stage1_only))).
    { rewrite Forall_forall in Hall_safe |- *.
      intros entry Hin.
      apply in_map_iff in Hin as [[[fn_str s_tle] t_tle] [<- Hin_s]].
      pose proof (Hall_safe (fn_str, s_tle, t_tle) Hin_s) as Hchk_s.
      apply in_app_iff in Hin_s as [Hin_sf | Hin_st1].
      - exact (Hsafe_slices fn_str s_tle t_tle (or_introl Hin_sf) Hchk_s).
      - unfold stage1_only, mm_composed_stage1_slices in Hin_st1.
        apply in_map_iff in Hin_st1 as [[[[fn0 s0] m0] f0] [Heq Hin_p]].
        inversion Heq; subst fn0 s0 m0.
        exact (Hsafe_slices fn_str s_tle t_tle (or_intror (ex_intro _ f0 Hin_p)) Hchk_s). }
    rewrite map_app, Forall_app in Hsafes_all.
    destruct Hsafes_all as [Hsafes_s Hsafes_st1].
    pose proof (@check_flex_module_merge_value_refines IP IPT
                  n_orig n_mid (List.map mm_tle_slice_to_norm_dtyp stage1_only)
                  Hstage1 Hsafes_st1) as Hmid1.
    assert (Hs2 :
      Forall (@slice_value_refines IP IPT)
        (List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices ++ stage2_fast))).
    { rewrite !map_app; apply mm_Forall_app;
        [exact Hcert | apply mm_Forall_app; [exact Hsafes_s | exact Hstage2_cert]]. }
    destruct (check_flex_module_merge n_mid n_merged
                (List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices ++ stage2_fast)))
      eqn:E2.
    + pose proof (@check_flex_module_merge_value_refines IP IPT
                    n_mid n_merged
                    (List.map mm_tle_slice_to_norm_dtyp (cert_slices ++ safe_slices ++ stage2_fast))
                    E2 Hs2) as Hmid2.
      left; split; [apply mm_norm_mcfg_refines_fwd | split; [exists n_mid; exact (conj Hmid1 Hmid2) | apply mm_norm_mcfg_refines_bwd]].
    + destruct (mm_safe_export_mcfg orig_tle) as [m_exp_orig |]; [| discriminate Hstage2].
      pose proof (@check_flex_module_merge_value_refines IP IPT
                    n_mid n_merged _ Hstage2
                    (mm_Forall_app _ _ _ Hs2 (Hwm_slices m_exp_orig Logic.eq_refl))) as Hmid2.
      left; split; [apply mm_norm_mcfg_refines_fwd | split; [exists n_mid; exact (conj Hmid1 Hmid2) | apply mm_norm_mcfg_refines_bwd]].
Qed.


