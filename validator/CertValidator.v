(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Top-Level Verified CFG Translation Validator ([F-44] Relational [DrawE] & [F-33] Open-World [CallE])

    Implements:
    1. Open-world per-function event interpretation ([run_cfg_locals],
       [eval_cfg_open]) keeping [CallE], [ExternalCallE], [IntrinsicE],
       [GlobalE], [StackE], [MemoryE], and [DrawE] uninterpreted ([F-33]).
    2. Relational [DrawE] refinement ([ow_itree_refines], [F-44]) over
       well-formed [Draw] strategies ([valid_draw_value]), proving reflexivity,
       transitivity, source existential / universal [Draw] introduction,
       target universal [Draw] inversion, refutation of target-invented
       [0 -> freeze poison], and soundness of [or(freeze x, 1) -> -1] (on [i1])
       and [or(freeze x, -1) -> -1] (at arbitrary width [sz : positive]).
    3. Small-step/big-step operational stepping ([mcfg_steps_to_ret],
       [mcfg_steps_to_ub], [cfg_steps_to_ret], [cfg_steps_to_ub]) bridging
       Vellvm's [denote_cfg] to [det_ref] with zero dependent-equality axioms.
    4. Reflexive and transitive per-function open-world refinement
       [validator_cfg_refines].
    5. Computable bounded-DAG SSA reification, distinct target [freeze]-key
       checking, source-verified UB assumption discharge, [cert-v1] block &
       return obligation checking ([check_cert_cfg_with_lrat], [check_cert_cfg],
       [check_cert_defn]), and [check_cert_cfg_sound] ([0 Admitted]).
    6. Extraction-ready module and string-level entrypoints
       ([validate_mcfg_with_cert], [validate_tle_pair_with_cert],
       [validate_tle_pair_with_cert_str]) and [validate_tle_pair_with_cert_str_sound]. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
  Ascii
  List
  Bool
  Lia
  PeanoNat
  Numbers.DecimalString.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  Utils
  Utils.ITreeUtil
  Utils.Assoc
  Utils.ListUtil
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.DynamicTypes
  Syntax.CFG
  Syntax.TypToDtyp
  Syntax.RawIdMaps
  Syntax.ModuleRefs
  Syntax.Traversal
  Numeric.Integers
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.LLVMEvents
  Semantics.Attributes
  Semantics.Denotation
  Semantics.IntrinsicsDefinitions
  Semantics.MemoryBytes
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select
  Semantics.Operations.Freeze
  Semantics.Operations.Gep
  Theory.MemoryBytesFacts.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  CertFormat
  AigLrat
  AlgRules.

From CertValidator Require Export
  CfgDag
  CertValOpenWorld
  CertValExpReify
  CertValCfgDag
  CertValCfgSum
  CertValUbCheck
  CertValPathCheck
  CertValLoop
  CertValProto.

Import ListNotations.
Import Sum.
Import Subevent.
Import Logic.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.eqb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments Z.eqb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
#[local] Arguments Z.gtb _ _ : simpl nomatch.
#[local] Arguments Z.geb _ _ : simpl nomatch.
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments String.eqb _ _ : simpl nomatch.
#[local] Arguments Integers.modulus : simpl never.
#[local] Arguments Integers.half_modulus : simpl never.
#[local] Arguments Integers.max_unsigned : simpl never.
#[local] Arguments Integers.max_signed : simpl never.
#[local] Arguments Integers.min_signed : simpl never.
#[local] Arguments Integers.unsigned : simpl never.
#[local] Arguments Integers.signed : simpl never.
#[local] Arguments Integers.repr : simpl never.
#[local] Arguments Integers.zero : simpl never.
#[local] Arguments Integers.one : simpl never.
#[local] Arguments Integers.mone : simpl never.
#[local] Arguments Integers.iwordsize : simpl never.
#[local] Arguments Integers.eq : simpl never.
#[local] Arguments Integers.lt : simpl never.
#[local] Arguments Integers.ltu : simpl never.
#[local] Arguments Integers.neg : simpl never.
#[local] Arguments Integers.add : simpl never.
#[local] Arguments Integers.sub : simpl never.
#[local] Arguments Integers.mul : simpl never.
#[local] Arguments Integers.divs : simpl never.
#[local] Arguments Integers.mods : simpl never.
#[local] Arguments Integers.divu : simpl never.
#[local] Arguments Integers.modu : simpl never.
#[local] Arguments Integers.and : simpl never.
#[local] Arguments Integers.or : simpl never.
#[local] Arguments Integers.xor : simpl never.
#[local] Arguments Integers.not : simpl never.
#[local] Arguments Integers.shl : simpl never.
#[local] Arguments Integers.shru : simpl never.
#[local] Arguments Integers.shr : simpl never.
#[local] Arguments Integers.rol : simpl never.
#[local] Arguments Integers.ror : simpl never.
#[local] Arguments Integers.rolm : simpl never.
#[local] Arguments Integers.negative : simpl never.
#[local] Arguments Integers.add_carry : simpl never.
#[local] Arguments Integers.add_overflow : simpl never.
#[local] Arguments Integers.sub_borrow : simpl never.
#[local] Arguments Integers.sub_overflow : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition check_cert_cfg_with_proto_lrat
  (opt_proto : option (list dtyp * list (list param_attr)))
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : bool :=
  let src_pnames := List.map cert_reg_name (args src_cfg) in
  let proto_seed :=
    match opt_proto with
    | None => ([], [])
    | Some (p_dtys, s_pattrs) => seed_proto_param_ctx src_pnames p_dtys s_pattrs
    end in
  let allowed := used_src_param_vars src_cfg ++ fst proto_seed in
  let init_ctx := snd proto_seed in
  let src_uses := param_idx_uses_cfg src_cfg in
  let tgt_uses := param_idx_uses_cfg tgt_cfg in
  let src_slots := cfg_alloca_slot_names src_cfg in
  let tgt_slots := cfg_alloca_slot_names tgt_cfg in
  let known_src_slots := src_slots ++ cert_promoted_slot_names cert in
  let blk_uas := fun bid => block_uas_for (init src_cfg) (pc_blocks cert) bid in
  wf_proof_certificate cert &&
  check_validator_syntax_gates src_cfg tgt_cfg &&
  list_empty_b src_slots &&
  list_empty_b tgt_slots &&
  forallb (check_alias_witness_valid known_src_slots) (pc_alias_witnesses cert) &&
  check_ro_vars_subset allowed (pc_return_obligation cert) &&
  bmap_varargs_irrel (ocfg_map (blks src_cfg)) &&
  bmap_varargs_irrel (ocfg_map (blks tgt_cfg)) &&
  Nat.eqb (List.length (args src_cfg)) (List.length (args tgt_cfg)) &&
  no_dup_raw_ids (args src_cfg) &&
  no_dup_raw_ids (args tgt_cfg) &&
  no_dup_strings src_pnames &&
  forallb (fun u => param_use_in u src_uses) tgt_uses &&
  match pc_loop_invariants cert with
  | [] =>
      forallb (fun bc =>
        forallb (check_memory_invariant_valid allowed (bc_ub_assumptions bc ++ init_ctx))
          (bc_memory_invariants bc))
        (pc_blocks cert) &&
      match summarize_cfg_dag_with_uas blk_uas false src_cfg src_pnames,
            summarize_cfg_dag true tgt_cfg src_pnames with
      | Some d_src, Some d_tgt =>
          let fuel := S (dag_node_count d_src + dag_node_count d_tgt) in
          check_dag_refines_cert fuel allowed init_ctx (pc_return_obligation cert) opt_pf
            (spine_src_evals d_src) (spine_branch_conds d_src) d_src d_tgt
      | _, _ => false
      end
  | [lci] =>
      check_loop_cutpoint_cfg allowed init_ctx src_cfg tgt_cfg cert lci opt_pf
  | _ :: _ :: _ => false
  end.

Definition check_cert_cfg_with_lrat
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : bool :=
  check_cert_cfg_with_proto_lrat None src_cfg tgt_cfg cert opt_pf.

Definition check_cert_cfg
  (src_cfg tgt_cfg : CFG.cfg dtyp) (cert : proof_certificate) : bool :=
  check_cert_cfg_with_lrat src_cfg tgt_cfg cert None.

Definition strip_leading_at (s : string) : string :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 64%nat then rest else s
  | EmptyString => EmptyString
  end.

Definition cert_fn_matches_raw_id (fn_name : string) (rid : raw_id) : bool :=
  String.eqb (strip_leading_at fn_name) (cert_raw_id_bare rid).

Definition check_cert_defn_with_lrat
  (src_tenv tgt_tenv : list (ident * typ))
  (src_defn tgt_defn : definition typ (CFG.cfg typ))
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : bool :=
  let src_cfg := convert_typ src_tenv (df_instrs src_defn) in
  let tgt_cfg := convert_typ tgt_tenv (df_instrs tgt_defn) in
  let arg_dtys := defn_arg_dtys src_tenv src_defn in
  let s_pattrs := snd (dc_param_attrs (df_prototype src_defn)) in
  cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) &&
  check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) &&
  proto_deref_preserved_b (df_prototype src_defn) (df_prototype tgt_defn) &&
  forallb2 attr_preserves_dtyp_b arg_dtys s_pattrs &&
  forallb2 raw_id_eqb (df_args src_defn) (args src_cfg) &&
  forallb2 raw_id_eqb (df_args tgt_defn) (args tgt_cfg) &&
  Nat.eqb (List.length arg_dtys) (List.length (args src_cfg)) &&
  cfg_param_dtyp_compatible src_cfg arg_dtys &&
  check_cert_cfg_with_proto_lrat (Some (arg_dtys, s_pattrs)) src_cfg tgt_cfg cert opt_pf.

Definition check_cert_defn
  (src_tenv tgt_tenv : list (ident * typ))
  (src_defn tgt_defn : definition typ (CFG.cfg typ))
  (cert : proof_certificate) : bool :=
  check_cert_defn_with_lrat src_tenv tgt_tenv src_defn tgt_defn cert (pc_lrat_proof cert).


(** *** 5.7 Top-Level Per-Function Translation Validator Soundness ([0 Admitted]) *)

Theorem check_cert_cfg_proto_core_sound :
  forall {Pa : Params}
         (opt_proto : option (list dtyp * list (list param_attr)))
         (src_cfg tgt_cfg : CFG.cfg dtyp)
         (cert : proof_certificate)
         (opt_pf : option (list lrat_step)),
    check_cert_cfg_with_proto_lrat opt_proto src_cfg tgt_cfg cert opt_pf = true ->
    List.length (args src_cfg) = List.length (args tgt_cfg) /\
    bmap_varargs_irrel (ocfg_map (blks src_cfg)) = true /\
    bmap_varargs_irrel (ocfg_map (blks tgt_cfg)) = true /\
    forall arg_dtys,
      List.length arg_dtys = List.length (args src_cfg) ->
      cfg_param_dtyp_compatible src_cfg arg_dtys = true ->
      cfg_param_dtyp_compatible tgt_cfg arg_dtys = true /\
      forall (vs : list (@dvalue Pa)),
        Forall2 dvalue_has_dtyp vs arg_dtys ->
        match opt_proto with
        | None => True
        | Some (p_dtys, s_pattrs) =>
            p_dtys = arg_dtys /\
            Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                    s_pattrs vs
        end ->
        forall sigma_tgt,
          wf_draw_strat sigma_tgt ->
          exists sigma_src,
            wf_draw_strat sigma_src /\
            det_ref dvalue_refines
              (run_draws sigma_src (eval_cfg_open src_cfg vs))
              (run_draws sigma_tgt (eval_cfg_open tgt_cfg vs)) /\
            no_stack_det (run_draws sigma_src (eval_cfg_open src_cfg vs)).
Proof.
  intros Pa opt_proto src_cfg tgt_cfg cert opt_pf Hchk.
  unfold check_cert_cfg_with_proto_lrat in Hchk; cbn zeta in Hchk.
  set (src_pnames := List.map cert_reg_name (args src_cfg)) in *.
  set (proto_seed :=
         match opt_proto with
         | None => ([], [])
         | Some (p_dtys, s_pattrs) => seed_proto_param_ctx src_pnames p_dtys s_pattrs
         end) in *.
  set (allowed := used_src_param_vars src_cfg ++ fst proto_seed) in *.
  set (init_ctx := snd proto_seed) in *.
  set (src_uses := param_idx_uses_cfg src_cfg) in *.
  set (tgt_uses := param_idx_uses_cfg tgt_cfg) in *.
  set (blk_uas := fun bid => block_uas_for (init src_cfg) (pc_blocks cert) bid) in *.
  apply andb_true_iff in Hchk as [Hchk Hbody].
  apply andb_true_iff in Hchk as [Hchk Huses_sub].
  apply andb_true_iff in Hchk as [Hchk Hnd_sp].
  apply andb_true_iff in Hchk as [Hchk Hnd_ta].
  apply andb_true_iff in Hchk as [Hchk Hnd_sa].
  apply andb_true_iff in Hchk as [Hchk Hlen_st].
  apply andb_true_iff in Hchk as [Hchk Hbm_t].
  apply andb_true_iff in Hchk as [_ Hbm_s].
  apply Nat.eqb_eq in Hlen_st.
  apply no_dup_raw_ids_spec in Hnd_sa.
  apply no_dup_raw_ids_spec in Hnd_ta.
  apply no_dup_strings_spec in Hnd_sp.
  assert (Hpu_src : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) src_uses ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) allowed).
  { intros idx w0 pnm Hin Hpnm; unfold allowed; apply in_app_iff; left.
    unfold used_src_param_vars; apply in_flat_map.
    exists (idx, DTYPE_Base (DTYPE_I w0)).
    split; [exact Hin | fold src_pnames; rewrite Hpnm; left; reflexivity]. }
  assert (Hpu_tgt : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) tgt_uses ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) allowed).
  { intros idx w0 pnm Hin Hpnm.
    rewrite forallb_forall in Huses_sub.
    pose proof (Huses_sub (idx, DTYPE_Base (DTYPE_I w0)) Hin) as Hin_s.
    apply param_use_in_spec in Hin_s; exact (Hpu_src idx w0 pnm Hin_s Hpnm). }
  split; [exact Hlen_st | split; [exact Hbm_s | split; [exact Hbm_t |]]].
  intros arg_dtys Hlen_da Hcomp_s.
  assert (Hcomp_t : cfg_param_dtyp_compatible tgt_cfg arg_dtys = true).
  { unfold cfg_param_dtyp_compatible in Hcomp_s |- *.
    rewrite forallb_forall in Hcomp_s, Huses_sub |- *.
    intros u Hu; apply Hcomp_s; apply param_use_in_spec; exact (Huses_sub u Hu). }
  split; [exact Hcomp_t |].
  intros vs Hvs Hproto_vs sigma_tgt Hwfsig_t.
  pose proof (List.Forall2_length Hvs) as Hlen_vs.
  assert (Hlen_sp_s : List.length src_pnames = List.length (args src_cfg))
    by (unfold src_pnames; apply List.length_map).
  assert (Hlen_sp_t : List.length src_pnames = List.length (args tgt_cfg)) by lia.
  assert (Hlen_da_t : List.length arg_dtys = List.length (args tgt_cfg)) by lia.
  assert (Hlen_sp_vs : List.length src_pnames = List.length vs) by lia.
  set (penv := build_param_env src_pnames vs) in *.
  pose proof (used_src_param_vars_wf src_cfg arg_dtys vs Hnd_sp Hlen_da Hcomp_s Hvs) as Hpenv_used.
  fold src_pnames penv in Hpenv_used.
  assert (Hseed_wf :
    wf_param_env_for (fst proto_seed) penv /\
    (forall fo : freeze_oracle, ub_ctx_holds penv fo init_ctx)).
  { unfold init_ctx, proto_seed.
    destruct opt_proto as [[p_dtys s_pattrs] |].
    - destruct Hproto_vs as [-> Hnu].
      split.
      + exact (proj1 (seed_proto_param_ctx_sound src_pnames arg_dtys s_pattrs vs
                        dummy_freeze_oracle Hnd_sp Hlen_sp_vs Hvs Hnu)).
      + intros fo.
        exact (proj2 (seed_proto_param_ctx_sound src_pnames arg_dtys s_pattrs vs
                        fo Hnd_sp Hlen_sp_vs Hvs Hnu)).
    - split; [intros ? ? [] | intros fo; constructor]. }
  destruct Hseed_wf as [Hpenv_extra Hinit_ctx_any].
  assert (Hpenv_wf : wf_param_env_for allowed penv).
  { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | He];
      [exact (Hpenv_used nm w Hu) | exact (Hpenv_extra nm w He)]. }
  destruct (pc_loop_invariants cert) as [| lci [| ? ?]].
  - apply andb_true_iff in Hbody as [_ Hrest].
    destruct (summarize_cfg_dag_with_uas blk_uas false src_cfg src_pnames)
      as [d_src |] eqn:Esum_s; [| discriminate Hrest].
    destruct (summarize_cfg_dag true tgt_cfg src_pnames)
      as [d_tgt |] eqn:Esum_t; [| discriminate Hrest].
    pose proof (summarize_cfg_dag_with_uas_wf blk_uas false src_cfg src_pnames allowed d_src
                  Hpu_src Esum_s) as Hwfd_s.
    pose proof (summarize_cfg_dag_wf true tgt_cfg src_pnames allowed d_tgt
                  Hpu_tgt Esum_t) as Hwfd_t.
    destruct (summarize_tgt_dag_sound tgt_cfg src_pnames arg_dtys vs sigma_tgt d_tgt
                Hnd_ta Hnd_sp Hlen_sp_t Hlen_da_t Hcomp_t Hvs Hwfsig_t Esum_t)
      as [fmap_tgt Htgt_out].
    set (foracle := oracle_of_fmap fmap_tgt) in *.
    destruct (summarize_src_dag_with_uas_sound blk_uas src_cfg src_pnames arg_dtys vs foracle d_src
                Hnd_sa Hnd_sp Hlen_sp_s Hlen_da Hcomp_s Hvs Esum_s)
      as [sigma_src [Hwfsig_s Hsrc_out]].
    exists sigma_src; split; [exact Hwfsig_s |].
    destruct Hsrc_out as [[Hst_ub_s _] | (sigma_src' & env_out_s & dv_src & Hev_ds & Hst_ret_s)].
    + split.
      * exact (cfg_steps_ub_det_ref dvalue_refines sigma_src
                 (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None)
                 (run_draws sigma_tgt (eval_cfg_open tgt_cfg vs)) Hst_ub_s).
      * exact (cfg_steps_ub_no_stack_det sigma_src
                 (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None) Hst_ub_s).
    + destruct (check_dag_refines_cert_sound
                  (S (dag_node_count d_src + dag_node_count d_tgt))
                  allowed init_ctx (pc_return_obligation cert) opt_pf
                  (spine_src_evals d_src) (spine_branch_conds d_src)
                  d_src d_tgt penv foracle dv_src
                  Hwfd_s Hwfd_t Hpenv_wf (Hinit_ctx_any foracle)
                  (fun big H => spine_src_evals_wf allowed d_src big Hwfd_s H)
                  (fun big H => spine_src_evals_ret penv foracle d_src dv_src big Hev_ds H)
                  (fun c H => spine_branch_conds_ret penv foracle d_src dv_src c Hev_ds H)
                  Hrest Hev_ds)
        as [dv_tgt [Hev_dt Href_dv]].
      unfold penv in Hev_dt.
      destruct Htgt_out as [Hev_dt_ub | (sigma_tgt' & env_out_t & dv_tgt' & Hev_dt' & Hst_ret_t)].
      * rewrite Hev_dt in Hev_dt_ub; discriminate Hev_dt_ub.
      * rewrite Hev_dt in Hev_dt'; injection Hev_dt' as <-.
        split.
        -- exact (cfg_steps_ret_det_ref dvalue_refines
                    sigma_src (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None)
                    sigma_src' env_out_s dv_src
                    sigma_tgt (init_cfg_locals (args tgt_cfg) vs) (denote_cfg tgt_cfg None)
                    sigma_tgt' env_out_t dv_tgt
                    Hst_ret_s Hst_ret_t Href_dv).
        -- exact (cfg_steps_ret_no_stack_det sigma_src
                    (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None)
                    sigma_src' env_out_s dv_src Hst_ret_s).
  - destruct (check_loop_cutpoint_cfg_open_sound
                allowed init_ctx src_cfg tgt_cfg cert lci opt_pf arg_dtys vs
                Hnd_sa Hnd_ta Hnd_sp Hlen_st Hlen_da Hcomp_s Hcomp_t Hvs
                Hpu_src Hpu_tgt Hpenv_wf (Hinit_ctx_any dummy_freeze_oracle)
                Hbody sigma_tgt Hwfsig_t)
      as [sigma_src [Hwfsig_s Hdr_loop]].
    exists sigma_src; split; [exact Hwfsig_s | split; [exact Hdr_loop |]].
    exact (check_loop_cutpoint_cfg_no_stack_det
             allowed init_ctx src_cfg tgt_cfg cert lci opt_pf arg_dtys vs
             Hnd_sa Hnd_sp Hlen_da Hcomp_s Hvs Hpu_src Hbody sigma_src).
  - discriminate Hbody.
Qed.

Theorem check_cert_cfg_with_lrat_sound :
  forall {Pa : Params} (src_cfg tgt_cfg : CFG.cfg dtyp)
         (cert : proof_certificate) (opt_pf : option (list lrat_step)),
    check_cert_cfg_with_lrat src_cfg tgt_cfg cert opt_pf = true ->
    @validator_cfg_refines Pa src_cfg tgt_cfg.
Proof.
  intros Pa src_cfg tgt_cfg cert opt_pf Hchk.
  destruct (@check_cert_cfg_proto_core_sound Pa None src_cfg tgt_cfg cert opt_pf Hchk)
    as (Hlen_st & _ & _ & Hrest).
  split; [exact Hlen_st |].
  intros arg_dtys Hlen_da Hcomp_s.
  destruct (Hrest arg_dtys Hlen_da Hcomp_s) as [Hcomp_t Hgo].
  split; [exact Hcomp_t |].
  intros vs Hvs sigma_tgt Hwfsig_t.
  destruct (Hgo vs Hvs I sigma_tgt Hwfsig_t) as (sigma_src & Hwfsig_s & Hdr & _).
  exists sigma_src; exact (conj Hwfsig_s Hdr).
Qed.

Theorem check_cert_cfg_sound :
  forall {Pa : Params} (src_cfg tgt_cfg : CFG.cfg dtyp) (cert : proof_certificate),
    check_cert_cfg src_cfg tgt_cfg cert = true ->
    @validator_cfg_refines Pa src_cfg tgt_cfg.
Proof.
  intros Pa src_cfg tgt_cfg cert Hchk.
  exact (check_cert_cfg_with_lrat_sound src_cfg tgt_cfg cert None Hchk).
Qed.

Theorem check_cert_defn_with_lrat_sound :
  forall {Pa : Params} (src_tenv tgt_tenv : list (ident * typ))
         (src_defn tgt_defn : definition typ (CFG.cfg typ))
         (cert : proof_certificate)
         (opt_pf : option (list lrat_step)),
    check_cert_defn_with_lrat src_tenv tgt_tenv src_defn tgt_defn cert opt_pf = true ->
    cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
    dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
    check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
    @validator_defn_refines Pa
      (defn_arg_dtys src_tenv src_defn)
      (tfmap (typ_to_dtyp src_tenv) src_defn)
      (tfmap (typ_to_dtyp tgt_tenv) tgt_defn).
Proof.
  intros Pa src_tenv tgt_tenv src_defn tgt_defn cert opt_pf Hchk.
  unfold check_cert_defn_with_lrat in Hchk; cbn zeta in Hchk.
  set (src_cfg := convert_typ src_tenv (df_instrs src_defn)) in *.
  set (tgt_cfg := convert_typ tgt_tenv (df_instrs tgt_defn)) in *.
  set (arg_dtys := defn_arg_dtys src_tenv src_defn) in *.
  set (s_pattrs := snd (dc_param_attrs (df_prototype src_defn))) in *.
  apply andb_true_iff in Hchk as [Hchk Hcfg].
  apply andb_true_iff in Hchk as [Hchk Hcomp_s].
  apply andb_true_iff in Hchk as [Hchk Hlen_ad].
  apply andb_true_iff in Hchk as [Hchk Hdfa_t].
  apply andb_true_iff in Hchk as [Hchk Hdfa_s].
  apply andb_true_iff in Hchk as [Hchk Hpres].
  apply andb_true_iff in Hchk as [Hchk Hderef].
  apply andb_true_iff in Hchk as [Hfn Hproto].
  apply Nat.eqb_eq in Hlen_ad.
  apply forallb2_raw_id_eqb_eq in Hdfa_s.
  apply forallb2_raw_id_eqb_eq in Hdfa_t.
  destruct (check_prototype_contract_inv _ _ Hproto) as [Hdcnm _].
  destruct (@check_cert_cfg_proto_core_sound Pa (Some (arg_dtys, s_pattrs))
              src_cfg tgt_cfg cert opt_pf Hcfg)
    as (Hlen_st & Hbm_s & Hbm_t & Hcore).
  destruct (Hcore arg_dtys Hlen_ad Hcomp_s) as [_ Hgo].
  repeat split; [exact Hfn | exact Hdcnm | exact Hproto |].
  exact (proto_cfg_to_defn_refines src_tenv tgt_tenv src_defn tgt_defn
           Hproto Hderef Hpres Hdfa_s Hdfa_t Hlen_ad Hlen_st Hbm_s Hbm_t
           (fun vs' Hty' Hnu' => Hgo vs' Hty' (conj eq_refl Hnu'))).
Qed.

Theorem check_cert_defn_sound :
  forall {Pa : Params} (src_tenv tgt_tenv : list (ident * typ))
         (src_defn tgt_defn : definition typ (CFG.cfg typ))
         (cert : proof_certificate),
    check_cert_defn src_tenv tgt_tenv src_defn tgt_defn cert = true ->
    cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
    dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
    check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
    @validator_defn_refines Pa
      (defn_arg_dtys src_tenv src_defn)
      (tfmap (typ_to_dtyp src_tenv) src_defn)
      (tfmap (typ_to_dtyp tgt_tenv) tgt_defn).
Proof.
  intros Pa src_tenv tgt_tenv src_defn tgt_defn cert Hchk.
  exact (check_cert_defn_with_lrat_sound src_tenv tgt_tenv src_defn tgt_defn cert (pc_lrat_proof cert) Hchk).
Qed.


(** ** 6. Extraction-Ready Module & String-Level CLI Entrypoints *)

Fixpoint find_unique_defn_by_name_tr
  (fn_name : string)
  (found : option (definition typ (CFG.cfg typ)))
  (ds : list (definition typ (CFG.cfg typ)))
  {struct ds} : option (definition typ (CFG.cfg typ)) :=
  match ds with
  | [] => found
  | d :: rest =>
      if cert_fn_matches_raw_id fn_name (dc_name (df_prototype d)) then
        match found with
        | None => find_unique_defn_by_name_tr fn_name (Some d) rest
        | Some _ => None
        end
      else find_unique_defn_by_name_tr fn_name found rest
  end.

Definition find_unique_defn_by_name
  (fn_name : string)
  (ds : list (definition typ (CFG.cfg typ)))
  : option (definition typ (CFG.cfg typ)) :=
  find_unique_defn_by_name_tr fn_name None ds.

Lemma find_unique_defn_by_name_tr_in :
  forall fn_name ds found d,
    find_unique_defn_by_name_tr fn_name found ds = Some d ->
    (match found with
     | Some f => f = d
     | None => In d ds /\ cert_fn_matches_raw_id fn_name (dc_name (df_prototype d)) = true
     end).
Proof.
  intros fn_name ds; induction ds as [| d0 rest IH]; intros [f |] d H;
    cbn [find_unique_defn_by_name_tr] in H.
  - inversion H; subst; reflexivity.
  - discriminate H.
  - destruct (cert_fn_matches_raw_id fn_name (dc_name (df_prototype d0))); [discriminate H |].
    exact (IH (Some f) d H).
  - destruct (cert_fn_matches_raw_id fn_name (dc_name (df_prototype d0))) eqn:Em.
    + specialize (IH (Some d0) d H); cbn in IH; subst d0; split; [left; reflexivity | exact Em].
    + destruct (IH None d H) as [Hin Hmatch]; split; [right; exact Hin | exact Hmatch].
Qed.

Lemma find_unique_defn_by_name_in :
  forall fn_name ds d,
    find_unique_defn_by_name fn_name ds = Some d ->
    In d ds /\ cert_fn_matches_raw_id fn_name (dc_name (df_prototype d)) = true.
Proof.
  intros fn_name ds d H.
  exact (find_unique_defn_by_name_tr_in fn_name ds None d H).
Qed.

Definition find_unique_defn_by_name_diag
  (side fn_name : string)
  (ds : list (definition typ (CFG.cfg typ)))
  : string + definition typ (CFG.cfg typ) :=
  match find_unique_diag (fun d => cert_fn_matches_raw_id fn_name (dc_name (df_prototype d))) ds with
  | UM_Missing =>
      inl (diag "ir-fn-lookup" (side ++ " function '" ++ fn_name ++ "' not found in module"))
  | UM_Duplicate _ _ =>
      inl (diag "ir-fn-lookup" (side ++ " function '" ++ fn_name ++ "' is defined multiple times in module"))
  | UM_Unique d => inr d
  end.

Lemma find_unique_defn_by_name_diag_in :
  forall side fn_name ds d,
    find_unique_defn_by_name_diag side fn_name ds = inr d ->
    In d ds /\ cert_fn_matches_raw_id fn_name (dc_name (df_prototype d)) = true.
Proof.
  intros side fn_name ds d H; unfold find_unique_defn_by_name_diag in H.
  destruct (find_unique_diag (fun d0 => cert_fn_matches_raw_id fn_name (dc_name (df_prototype d0))) ds)
    as [| d0 | d1 d2] eqn:Eu; try discriminate H.
  inversion H; subst d0.
  destruct (find_unique_diag_spec _ _ _ Eu) as [Hin [Hm _]].
  exact (conj Hin Hm).
Qed.

Definition check_alias_witness_valid_diag
  (idx : nat) (src_alloca_slots : list string) (aw : alias_witness) : string + unit :=
  let pfx : string := ("alias witness #" ++ diag_nat_dec idx ++ ": ")%string in
  bind_err
    (guard_err (wf_alias_witness aw)
      (fun _ => diag "cert-mem" (pfx ++ "malformed alias witness")))
    (fun _ =>
  match aw_kind aw with
  | ARK_MustAlias =>
      guard_err (String.eqb (aw_lhs_ptr aw) (aw_rhs_ptr aw))
        (fun _ => diag "cert-mem"
          (pfx ++ "must-alias pointer mismatch '" ++ aw_lhs_ptr aw ++ "' vs '" ++ aw_rhs_ptr aw ++ "'"))
  | ARK_NoAlias =>
      bind_err
        (guard_err (negb (String.eqb (aw_lhs_ptr aw) (aw_rhs_ptr aw)))
          (fun _ => diag "cert-mem" (pfx ++ "no-alias pointers cannot be identical ('" ++ aw_lhs_ptr aw ++ "')")))
        (fun _ =>
      bind_err
        (guard_err (string_in_list (aw_lhs_ptr aw) src_alloca_slots)
          (fun _ => diag "cert-mem" (pfx ++ "unknown lhs alloca slot '" ++ aw_lhs_ptr aw ++ "'")))
        (fun _ =>
      guard_err (string_in_list (aw_rhs_ptr aw) src_alloca_slots)
        (fun _ => diag "cert-mem" (pfx ++ "unknown rhs alloca slot '" ++ aw_rhs_ptr aw ++ "'"))))
  end).

Lemma check_alias_witness_valid_diag_sound :
  forall idx slots aw,
    check_alias_witness_valid_diag idx slots aw = inr tt ->
    check_alias_witness_valid slots aw = true.
Proof.
  intros idx slots aw H; unfold check_alias_witness_valid_diag in H; unfold check_alias_witness_valid.
  destruct (wf_alias_witness aw); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (aw_kind aw); repeat match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  | guard_err ?c _ = inr tt =>
      destruct c; cbn [guard_err] in H; [| discriminate H]
  end; reflexivity.
Qed.

Definition check_memory_invariant_valid_diag
  (blk_name : string) (idx : nat) (allowed : list (string * positive))
  (ctx : ub_ctx) (mi : memory_invariant) : string + unit :=
  let pfx : string := ("block '" ++ blk_name ++ "' mem-invariant #" ++ diag_nat_dec idx ++ ": ")%string in
  bind_err
    (guard_err (wf_memory_invariant mi)
      (fun _ => diag "cert-mem" (pfx ++ "malformed memory invariant")))
    (fun _ =>
  match mi with
  | MI_AllocaPromoted slot _ pe =>
      bind_err
        (guard_err (vars_subset_b (collect_free_vars [] pe) allowed)
          (fun _ => diag "cert-mem" (pfx ++ "free variable outside allowed scope for promoted slot '" ++ slot ++ "'")))
        (fun _ =>
      guard_err (check_expr_refines ctx pe pe)
        (fun _ => diag "cert-mem" (pfx ++ "self-refinement check failed for promoted slot '" ++ slot ++ "'")))
  | MI_SlotRefines slot _ _ se te =>
      bind_err
        (guard_err (vars_subset_b (collect_free_vars [] se) allowed)
          (fun _ => diag "cert-mem" (pfx ++ "source free variable outside allowed scope for slot '" ++ slot ++ "'")))
        (fun _ =>
      bind_err
        (guard_err (vars_subset_b (collect_free_vars [] te) allowed)
          (fun _ => diag "cert-mem" (pfx ++ "target free variable outside allowed scope for slot '" ++ slot ++ "'")))
        (fun _ =>
      guard_err (check_expr_refines ctx se te)
        (fun _ => diag "cert-mem" (pfx ++ "slot refinement obligation failed for slot '" ++ slot ++ "'"))))
  end).

Lemma check_memory_invariant_valid_diag_sound :
  forall blk_name idx allowed ctx mi,
    check_memory_invariant_valid_diag blk_name idx allowed ctx mi = inr tt ->
    check_memory_invariant_valid allowed ctx mi = true.
Proof.
  intros blk_name idx allowed ctx mi H; unfold check_memory_invariant_valid_diag in H; unfold check_memory_invariant_valid.
  destruct (wf_memory_invariant mi); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct mi; repeat match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  | guard_err ?c _ = inr tt =>
      destruct c; cbn [guard_err] in H; [| discriminate H]
  end; reflexivity.
Qed.

Fixpoint cv_find_reify_code_err_idx
  (uf : bool) (params : list raw_id) (src_pnames : list string) (defs : list raw_id)
  (smap : rmap (positive * cert_expr)) (seen : list freeze_key)
  (idx : nat) (c : code dtyp) {struct c} : nat :=
  match c with
  | [] => idx
  | i1 :: rest1 =>
      match reify_code_step uf params src_pnames defs smap seen i1 with
      | None => idx
      | Some (_, smap1, seen1) =>
          cv_find_reify_code_err_idx uf params src_pnames defs smap1 seen1 (S idx) rest1
      end
  end.

Fixpoint summarize_ocfg_dag_diag
  (side : string)
  (fuel : nat)
  (blk_uas : block_id -> list ub_assumption)
  (uf : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (bmap : rmap (block dtyp))
  (is_entry : bool)
  (bid_from bid_cur : block_id)
  (smap : rmap (positive * cert_expr))
  (seen : list freeze_key)
  {struct fuel} : string + cfg_dag :=
  let loc (_ : unit) : string :=
    (side ++ " block '" ++ cert_raw_id_bare bid_cur ++ "'")%string
  in
  match fuel with
  | O => inl (diag "ir-reify" ("CFG summarization fuel exhausted at " ++ loc tt))
  | S fuel' =>
      match RM.find bid_cur bmap with
      | None => inl (diag "ir-reify" (loc tt ++ " not found in CFG"))
      | Some b =>
          if is_entry && negb (list_empty_b (blk_phis b)) then
            inl (diag "ir-reify" ("disallowed phi node in entry " ++ loc tt))
          else
            match reify_phi_evals uf params src_pnames defs smap bid_from seen (blk_phis b) with
            | None => inl (diag "ir-reify" ("failed to reify phi node in " ++ loc tt))
            | Some (pevals, seen_p) =>
                let smap_p := apply_phi_smap smap pevals in
                match reify_code uf params src_pnames defs smap_p seen_p (blk_code b) with
                | None =>
                    let err_i :=
                      cv_find_reify_code_err_idx uf params src_pnames defs smap_p seen_p 0 (blk_code b) in
                    inl (diag "ir-reify"
                      ("failed to reify instruction #" ++ diag_nat_dec err_i ++ " in " ++ loc tt))
                | Some (cevals, smap_c, seen_c) =>
                    let d_term_res :=
                      match blk_term b with
                      | (_, TERM_Unreachable, _) =>
                          inr CD_Unreachable
                      | (_, TERM_Ret_void, _) =>
                          inr CD_RetVoid
                      | (_, TERM_Ret (DTYPE_Base (DTYPE_I w), op), _) =>
                          match reify_exp uf params src_pnames defs smap_c seen_c
                                  (Some (DTYPE_Base (DTYPE_I w))) op with
                          | Some (_, ce_ret, _) =>
                              inr (CD_RetScalar w ce_ret)
                          | None =>
                              inl (diag "ir-reify" ("failed to reify return expression in " ++ loc tt))
                          end
                      | (_, TERM_Ret _, _) =>
                          inl (diag "ir-reify" ("unsupported non-integer return type in " ++ loc tt))
                      | (_, TERM_Br_1 br, _) =>
                          summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap
                            false bid_cur br smap_c seen_c
                      | (_, TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2, _) =>
                          match reify_exp uf params src_pnames defs smap_c seen_c
                                  (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
                          | Some (_, ce_cond, seen_br) =>
                              match try_const_i1 ce_cond with
                              | Some true =>
                                  match summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br1 smap_c seen_br with
                                  | inr d_t => inr (CD_Eval 1%positive ce_cond d_t)
                                  | inl err => inl err
                                  end
                              | Some false =>
                                  match summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br2 smap_c seen_br with
                                  | inr d_f => inr (CD_Eval 1%positive ce_cond d_f)
                                  | inl err => inl err
                                  end
                              | None =>
                                  match summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br1 smap_c seen_br with
                                  | inl err => inl err
                                  | inr d_t =>
                                      match summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap
                                              false bid_cur br2 smap_c seen_br with
                                      | inl err => inl err
                                      | inr d_f => inr (CD_Branch ce_cond d_t d_f)
                                      end
                                  end
                              end
                          | None =>
                              inl (diag "ir-reify" ("failed to reify branch condition in " ++ loc tt))
                          end
                      | _ => inl (diag "ir-reify" ("unsupported terminator in " ++ loc tt))
                      end in
                    match d_term_res with
                    | inr d_term =>
                        inr (CD_BlockAssume (blk_uas bid_cur)
                               (wrap_phi_evals pevals (wrap_evals cevals d_term)))
                    | inl err => inl err
                    end
                end
            end
      end
  end.

Definition summarize_cfg_dag_with_uas_diag
  (side : string) (blk_uas : block_id -> list ub_assumption)
  (uf : bool) (G : CFG.cfg dtyp) (src_pnames : list string) : string + cfg_dag :=
  summarize_ocfg_dag_diag side (default_cfg_dag_fuel G) blk_uas uf (args G) src_pnames
    (defined_ids_of_cfg G) (ocfg_map (blks G)) true (init G) (init G) (RM.empty _) [].

Lemma summarize_ocfg_dag_diag_sound :
  forall side fuel blk_uas uf params src_pnames defs bmap is_entry bid_from bid_cur smap seen d,
    summarize_ocfg_dag_diag side fuel blk_uas uf params src_pnames defs bmap is_entry bid_from bid_cur smap seen = inr d ->
    summarize_ocfg_dag fuel blk_uas uf params src_pnames defs bmap is_entry bid_from bid_cur smap seen = Some d.
Proof.
  intros side fuel; induction fuel as [| fuel' IH];
    intros blk_uas uf params src_pnames defs bmap is_entry bid_from bid_cur smap seen d H;
    cbn [summarize_ocfg_dag_diag summarize_ocfg_dag] in *; [discriminate H |].
  destruct (RM.find bid_cur bmap) as [b |]; [| discriminate H].
  destruct (is_entry && negb (list_empty_b (blk_phis b))); [discriminate H |].
  destruct (reify_phi_evals uf params src_pnames defs smap bid_from seen (blk_phis b))
    as [[pevals seen_p] |]; [| discriminate H].
  destruct (reify_code uf params src_pnames defs (apply_phi_smap smap pevals) seen_p (blk_code b))
    as [[[cevals smap_c] seen_c] |]; [| discriminate H].
  set (d_term_res :=
    match blk_term b with
    | (_, TERM_Unreachable, _) => inr CD_Unreachable
    | (_, TERM_Ret_void, _) => inr CD_RetVoid
    | (_, TERM_Ret (DTYPE_Base (DTYPE_I w), op), _) =>
        match reify_exp uf params src_pnames defs smap_c seen_c (Some (DTYPE_Base (DTYPE_I w))) op with
        | Some (_, ce_ret, _) => inr (CD_RetScalar w ce_ret)
        | None => inl _
        end
    | (_, TERM_Ret _, _) => inl _
    | (_, TERM_Br_1 br, _) =>
        summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br smap_c seen_c
    | (_, TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2, _) =>
        match reify_exp uf params src_pnames defs smap_c seen_c (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
        | Some (_, ce_cond, seen_br) =>
            match try_const_i1 ce_cond with
            | Some true =>
                match summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br1 smap_c seen_br with
                | inr d_t => inr (CD_Eval 1%positive ce_cond d_t)
                | inl err => inl err
                end
            | Some false =>
                match summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br2 smap_c seen_br with
                | inr d_f => inr (CD_Eval 1%positive ce_cond d_f)
                | inl err => inl err
                end
            | None =>
                match summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br1 smap_c seen_br with
                | inl err => inl err
                | inr d_t =>
                    match summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br2 smap_c seen_br with
                    | inl err => inl err
                    | inr d_f => inr (CD_Branch ce_cond d_t d_f)
                    end
                end
            end
        | None => inl _
        end
    | _ => inl _
    end) in *.
  destruct (blk_term b) as [[? tm] ?];
    destruct tm as [ [dt_r op_r] | | [dt_b op_b] br1 br2 | br1 | | | | | ];
    try discriminate H.
  - destruct dt_r as [[w_r | | | | | | | | | |] | |]; try discriminate H.
    destruct (reify_exp uf params src_pnames defs smap_c seen_c (Some (DTYPE_Base (DTYPE_I w_r))) op_r)
      as [[[? ce_ret] ?] |]; [| discriminate H].
    subst d_term_res; cbn in H; injection H as <-; reflexivity.
  - subst d_term_res; cbn in H; injection H as <-; reflexivity.
  - destruct dt_b as [[w_b | | | | | | | | | |] | |]; try discriminate H.
    destruct w_b as [| |]; try discriminate H.
    destruct (reify_exp uf params src_pnames defs smap_c seen_c (Some (DTYPE_Base (DTYPE_I 1%positive))) op_b)
      as [[[? ce_cond] seen_br] |]; [| discriminate H].
    destruct (try_const_i1 ce_cond) as [[|] |].
    + destruct (summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br1 smap_c seen_br)
        as [| dt] eqn:Et; [discriminate H |].
      rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ Et).
      subst d_term_res; cbn in H; injection H as <-; reflexivity.
    + destruct (summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br2 smap_c seen_br)
        as [| df] eqn:Ef; [discriminate H |].
      rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ Ef).
      subst d_term_res; cbn in H; injection H as <-; reflexivity.
    + destruct (summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br1 smap_c seen_br)
        as [| dt] eqn:Et; [discriminate H |].
      destruct (summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br2 smap_c seen_br)
        as [| df] eqn:Ef; [discriminate H |].
      rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ Et), (IH _ _ _ _ _ _ _ _ _ _ _ _ Ef).
      subst d_term_res; cbn in H; injection H as <-; reflexivity.
  - destruct (summarize_ocfg_dag_diag side fuel' blk_uas uf params src_pnames defs bmap false bid_cur br1 smap_c seen_c)
      as [| d1] eqn:E1; [discriminate H |].
    rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ E1).
    subst d_term_res; cbn in H; injection H as <-; reflexivity.
  - subst d_term_res; cbn in H; injection H as <-; reflexivity.
Qed.

Lemma summarize_cfg_dag_with_uas_diag_sound :
  forall side blk_uas uf G src_pnames d,
    summarize_cfg_dag_with_uas_diag side blk_uas uf G src_pnames = inr d ->
    summarize_cfg_dag_with_uas blk_uas uf G src_pnames = Some d.
Proof.
  intros side blk_uas uf G src_pnames d H.
  exact (summarize_ocfg_dag_diag_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Fixpoint check_dag_refines_cert_path_diag
  (fuel : nat)
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (path_ctx : list (cert_expr * bool))
  (ro : return_obligation)
  (opt_pf : option (list lrat_step))
  (src_evals src_br_conds : list cert_expr)
  (d_src d_tgt : cfg_dag) {struct fuel} : string + unit :=
  let refine_fail_msg (_ : unit) : string :=
    match opt_pf with
    | Some pf =>
        diag "lrat-check"
          ("LRAT proof (" ++ diag_nat_dec (length_tr pf) ++
           " step(s)) failed to discharge IR scalar refinement obligation")
    | None =>
        diag "ir-refine"
          "IR scalar refinement obligation failed (algebraic + bounded SAT; no LRAT proof provided)"
    end
  in
  match fuel with
  | O => inl (diag "ir-refine" "DAG refinement fuel exhausted")
  | S fuel' =>
      if spine_is_unreachable d_src || ctx_has_unreachable ctx then inr tt
      else
        match as_block_assume d_src with
        | Some (uas, next_s) =>
            match check_ub_assumptions_list allowed src_evals src_br_conds next_s ctx uas with
            | Some ctx' =>
                check_dag_refines_cert_path_diag fuel' allowed ctx' path_ctx ro opt_pf
                  src_evals src_br_conds next_s d_tgt
            | None =>
                inl (diag "ir-ub" "block UB assumptions in certificate could not be justified by prior source evaluations")
            end
        | None =>
            match as_block_assume d_tgt with
            | Some (uas_t, next_t) =>
                match uas_t with
                | [] =>
                    check_dag_refines_cert_path_diag fuel' allowed ctx path_ctx ro opt_pf
                      src_evals src_br_conds d_src next_t
                | _ :: _ => inl (diag "ir-ub" "unexpected UB assumptions attached to target DAG")
                end
            | None =>
                if check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
                then inr tt
                else
                  let opt_known_tgt_step :=
                    match d_tgt with
                    | CD_Branch ct tb ft =>
                        match lookup_path_bool ctx path_ctx (simplify_expr_with_path ctx path_ctx ct) with
                        | Some b => Some (if b then tb else ft)
                        | None => None
                        end
                    | _ => None
                    end in
                  match opt_known_tgt_step with
                  | Some next_tgt =>
                      check_dag_refines_cert_path_diag fuel' allowed ctx path_ctx ro opt_pf
                        src_evals src_br_conds d_src next_tgt
                  | None =>
                      match d_src with
                      | CD_Unreachable => inr tt
                      | CD_BlockAssume _ _ => inl (diag "ir-ub" "unwrapped CD_BlockAssume in source DAG")
                      | CD_Eval _ se next_s =>
                          check_dag_refines_cert_path_diag fuel' allowed ctx path_ctx ro opt_pf
                            (se :: src_evals) src_br_conds next_s d_tgt
                      | CD_Branch cs ts fs =>
                          let ctx_t := extract_branch_cond_assumptions true cs ++ ctx in
                          let ctx_f := extract_branch_cond_assumptions false cs ++ ctx in
                          if spine_is_unreachable fs then
                            check_dag_refines_cert_path_diag fuel' allowed ctx_t ((cs, true) :: path_ctx) ro opt_pf
                              (cs :: src_evals) (cs :: src_br_conds) ts d_tgt
                          else if spine_is_unreachable ts then
                            check_dag_refines_cert_path_diag fuel' allowed ctx_f ((cs, false) :: path_ctx) ro opt_pf
                              (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
                          else
                            match d_tgt with
                            | CD_Eval _ te next_t =>
                                if expr_safe_under_src ctx src_evals te then
                                  check_dag_refines_cert_path_diag fuel' allowed ctx path_ctx ro opt_pf
                                    src_evals src_br_conds d_src next_t
                                else
                                  inl (diag "ir-ub" "target evaluation may introduce UB/poison not present in source")
                            | CD_Branch ct tb ft =>
                                let ct_s := simplify_expr_with_path ctx path_ctx ct in
                                let aligned_ok :=
                                  if check_expr_refines ctx cs ct_s then
                                    match check_dag_refines_cert_path_diag fuel' allowed ctx_t ((cs, true) :: path_ctx)
                                            ro opt_pf (cs :: src_evals) (cs :: src_br_conds) ts tb with
                                    | inr tt =>
                                        match check_dag_refines_cert_path_diag fuel' allowed ctx_f ((cs, false) :: path_ctx)
                                                ro opt_pf (cs :: src_evals) (cs :: src_br_conds) fs ft with
                                        | inr tt => true
                                        | inl _ => false
                                        end
                                    | inl _ => false
                                    end
                                  else false
                                in
                                if aligned_ok then inr tt
                                else
                                  bind_err
                                    (check_dag_refines_cert_path_diag fuel' allowed ctx_t ((cs, true) :: path_ctx) ro opt_pf
                                       (cs :: src_evals) (cs :: src_br_conds) ts d_tgt)
                                    (fun _ =>
                                      check_dag_refines_cert_path_diag fuel' allowed ctx_f ((cs, false) :: path_ctx) ro opt_pf
                                        (cs :: src_evals) (cs :: src_br_conds) fs d_tgt)
                            | CD_RetScalar _ _ | CD_RetVoid =>
                                bind_err
                                  (check_dag_refines_cert_path_diag fuel' allowed ctx_t ((cs, true) :: path_ctx) ro opt_pf
                                     (cs :: src_evals) (cs :: src_br_conds) ts d_tgt)
                                  (fun _ =>
                                    check_dag_refines_cert_path_diag fuel' allowed ctx_f ((cs, false) :: path_ctx) ro opt_pf
                                      (cs :: src_evals) (cs :: src_br_conds) fs d_tgt)
                            | _ =>
                                inl (diag "ir-refine" "incompatible source branch and target CFG DAG shape")
                            end
                      | CD_RetVoid =>
                          match ro with
                          | RO_VoidEquiv =>
                              guard_err (tgt_dag_void_safe ctx src_evals src_br_conds d_tgt)
                                (fun _ => diag "ir-refine" "target void-return DAG may introduce UB/poison not present in source")
                          | _ =>
                              inl (diag "ir-refine" "certificate return obligation is not void-equiv for ret void function")
                          end
                      | CD_RetScalar ws es =>
                          match d_tgt with
                          | CD_Eval _ te next_t =>
                              if expr_safe_under_src ctx src_evals te then
                                check_dag_refines_cert_path_diag fuel' allowed ctx path_ctx ro opt_pf
                                  src_evals src_br_conds d_src next_t
                              else
                                inl (diag "ir-ub" "target evaluation before return may introduce UB/poison not present in source")
                          | CD_RetScalar wt et =>
                              match ro with
                              | RO_ScalarRefines w _ _ _ =>
                                  bind_err
                                    (guard_err (Pos.eqb ws w)
                                      (fun _ => diag "ir-refine"
                                        ("source return width i" ++ diag_pos_dec ws ++
                                         " disagrees with certificate scalar-refines width i" ++ diag_pos_dec w)))
                                    (fun _ =>
                                  bind_err
                                    (guard_err (Pos.eqb wt w)
                                      (fun _ => diag "ir-refine"
                                        ("target return width i" ++ diag_pos_dec wt ++
                                         " disagrees with certificate scalar-refines width i" ++ diag_pos_dec w)))
                                    (fun _ =>
                                  guard_err (check_expr_refines_with_lrat ctx es (simplify_expr_with_path ctx path_ctx et) opt_pf)
                                    refine_fail_msg))
                              | _ =>
                                  inl (diag "ir-refine" "certificate return obligation is void-equiv for non-void scalar function")
                              end
                          | _ =>
                              inl (diag "ir-refine" "incompatible source return and target CFG DAG shape")
                          end
                      end
                  end
            end
        end
  end.

Lemma check_dag_refines_cert_path_diag_sound :
  forall fuel allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src d_tgt,
    check_dag_refines_cert_path_diag fuel allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src d_tgt = inr tt ->
    check_dag_refines_cert_path fuel allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src d_tgt = true.
Proof.
  intros fuel; induction fuel as [| fuel' IH];
    intros allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src d_tgt H;
    cbn [check_dag_refines_cert_path_diag check_dag_refines_cert_path] in *;
    [discriminate H |].
  destruct (spine_is_unreachable d_src || ctx_has_unreachable ctx); [reflexivity |].
  destruct (as_block_assume d_src) as [[uas next_s] |].
  { destruct (check_ub_assumptions_list allowed src_evals src_br_conds next_s ctx uas) as [ctx' |];
      [exact (IH _ _ _ _ _ _ _ _ _ H) | discriminate H]. }
  destruct (as_block_assume d_tgt) as [[uas_t next_t] |].
  { destruct uas_t; [exact (IH _ _ _ _ _ _ _ _ _ H) | discriminate H]. }
  destruct (check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt); [reflexivity |].
  cbn zeta in *.
  set (opt_known_tgt_step :=
    match d_tgt with
    | CD_Branch ct tb ft =>
        match lookup_path_bool ctx path_ctx (simplify_expr_with_path ctx path_ctx ct) with
        | Some b => Some (if b then tb else ft)
        | None => None
        end
    | _ => None
    end) in *.
  destruct opt_known_tgt_step as [next_tgt |]; [exact (IH _ _ _ _ _ _ _ _ _ H) |].
  destruct d_src as [| | ws es | wse se next_s | | cs ts fs]; try discriminate H.
  - reflexivity.
  - destruct ro; [exact (guard_err_inr _ _ H) | discriminate H].
  - destruct d_tgt as [| | wt et | wte te next_t | | ct tb ft]; try discriminate H.
    + destruct ro as [| w ? ? ?]; [discriminate H |].
      destruct (Pos.eqb ws w); cbn [guard_err bind_err] in H; [| discriminate H].
      destruct (Pos.eqb wt w); cbn [guard_err bind_err] in H; [| discriminate H].
      exact (guard_err_inr _ _ H).
    + destruct (expr_safe_under_src ctx src_evals te); [exact (IH _ _ _ _ _ _ _ _ _ H) | discriminate H].
  - exact (IH _ _ _ _ _ _ _ _ _ H).
  - destruct (spine_is_unreachable fs); [exact (IH _ _ _ _ _ _ _ _ _ H) |].
    destruct (spine_is_unreachable ts); [exact (IH _ _ _ _ _ _ _ _ _ H) |].
    destruct d_tgt as [| | wt et | wte te next_t | | ct tb ft]; try discriminate H.
    + destruct (check_dag_refines_cert_path_diag fuel' allowed _ _ _ _ _ _ ts CD_RetVoid) as [| []] eqn:E1;
        cbn [bind_err] in H; [discriminate H |].
      rewrite (IH _ _ _ _ _ _ _ _ _ E1), (IH _ _ _ _ _ _ _ _ _ H); reflexivity.
    + destruct (check_dag_refines_cert_path_diag fuel' allowed _ _ _ _ _ _ ts (CD_RetScalar wt et)) as [| []] eqn:E1;
        cbn [bind_err] in H; [discriminate H |].
      rewrite (IH _ _ _ _ _ _ _ _ _ E1), (IH _ _ _ _ _ _ _ _ _ H); reflexivity.
    + destruct (expr_safe_under_src ctx src_evals te); [exact (IH _ _ _ _ _ _ _ _ _ H) | discriminate H].
    + cbv zeta in H.
      destruct (if check_expr_refines ctx cs (simplify_expr_with_path ctx path_ctx ct) then _ else false) eqn:Eal.
      * destruct (check_expr_refines ctx cs (simplify_expr_with_path ctx path_ctx ct)); [| discriminate Eal].
        destruct (check_dag_refines_cert_path_diag fuel' allowed (extract_branch_cond_assumptions true cs ++ ctx)
                    ((cs, true) :: path_ctx) ro opt_pf (cs :: src_evals) (cs :: src_br_conds) ts tb) as [| []] eqn:Etb;
          [discriminate Eal |].
        destruct (check_dag_refines_cert_path_diag fuel' allowed (extract_branch_cond_assumptions false cs ++ ctx)
                    ((cs, false) :: path_ctx) ro opt_pf (cs :: src_evals) (cs :: src_br_conds) fs ft) as [| []] eqn:Eft;
          [discriminate Eal |].
        rewrite (IH _ _ _ _ _ _ _ _ _ Etb), (IH _ _ _ _ _ _ _ _ _ Eft); cbn [andb]; reflexivity.
      * destruct (check_dag_refines_cert_path_diag fuel' allowed (extract_branch_cond_assumptions true cs ++ ctx)
                    ((cs, true) :: path_ctx) ro opt_pf (cs :: src_evals) (cs :: src_br_conds) ts (CD_Branch ct tb ft))
          as [| []] eqn:E1; cbn [bind_err] in H; [discriminate H |].
        rewrite (IH _ _ _ _ _ _ _ _ _ E1), (IH _ _ _ _ _ _ _ _ _ H); cbn [andb].
        destruct (_ && _); reflexivity.
Qed.

Definition check_loop_cutpoint_cfg_diag
  (allowed : list (string * positive))
  (init_ctx : ub_ctx)
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (lci : loop_cutpoint_invariant)
  (opt_pf : option (list lrat_step)) : string + unit :=
  let src_pnames := List.map cert_reg_name (args src_cfg) in
  let src_uses := param_idx_uses_cfg src_cfg in
  let tgt_uses := param_idx_uses_cfg tgt_cfg in
  let proof_err (tag ctx_desc : string) : unit -> string :=
    fun _ =>
      match opt_pf with
      | Some pf =>
          diag "lrat-check"
            ("LRAT proof (" ++ diag_nat_dec (length_tr pf) ++ " step(s)) failed on " ++ ctx_desc)
      | None => diag tag (ctx_desc ++ " failed (algebraic + bounded SAT; no LRAT proof provided)")
      end
  in
  bind_err
    (guard_err (forallb (fun '(nm, _) => string_in_list nm src_pnames) allowed)
      (fun _ => diag "ir-loop" "allowed parameter environment includes non-parameter variable"))
    (fun _ =>
  let lmap0_s := init_param_lmap (args src_cfg) src_pnames src_uses in
  let lmap0_t := init_param_lmap (args tgt_cfg) src_pnames tgt_uses in
  match reify_natural_loop src_cfg (lci_src_header lci) lmap0_s (overlay_hspecs_s 0%nat) with
  | None =>
      inl (diag "ir-loop" ("failed to reify source natural loop at header '" ++ lci_src_header lci ++ "'"))
  | Some (hspecs_s, s_s) =>
      match reify_natural_loop tgt_cfg (lci_tgt_header lci) lmap0_t (overlay_hspecs_t 0%nat) with
      | None =>
          inl (diag "ir-loop" ("failed to reify target natural loop at header '" ++ lci_tgt_header lci ++ "'"))
      | Some (hspecs_t, s_t) =>
          match pair_phi_specs hspecs_s hspecs_t with
          | None => inl (diag "ir-loop" "source and target loop header phis could not be paired")
          | Some pspecs =>
              let cut_allowed := allowed ++ cut_vars_from 0%nat pspecs in
              bind_err
                (guard_err (no_dup_strings (src_pnames ++ cut_names_from 0%nat pspecs))
                  (fun _ => diag "ir-loop" "duplicate cutpoint variable names in loop invariant"))
                (fun _ =>
              match fold_ub_assumptions allowed (nls_evals_entry s_s) [] init_ctx
                      (block_uas_for (init src_cfg) (pc_blocks cert) (init src_cfg)) with
              | None => inl (diag "ir-ub" "entry block UB assumptions could not be justified")
              | Some ctx_ent =>
                  bind_err
                    (guard_err (forallb (expr_safe_under_src ctx_ent (nls_evals_entry s_s)) (nls_evals_entry s_t))
                      (fun _ => diag "ir-ub" "target loop preheader evaluation may introduce UB/poison"))
                    (fun _ =>
                  bind_err
                    (guard_err
                      (forallb (expr_safe_under_src ctx_ent
                                 (nls_evals_entry s_s ++ peval_exprs (nls_init_pevals s_s)))
                              (peval_exprs (nls_init_pevals s_t)))
                      (fun _ => diag "ir-ub" "target loop initial phi value may introduce UB/poison"))
                    (fun _ =>
                  bind_err
                    (guard_err (check_pevals_refine ctx_ent opt_pf pspecs (nls_init_pevals s_s) (nls_init_pevals s_t))
                      (proof_err "ir-loop" "loop entry phi refinement"))
                    (fun _ =>
                  let base_loop_ctx := filter_param_ub_ctx src_pnames ctx_ent in
                  match fold_ub_assumptions cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
                          base_loop_ctx (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_hdr s_s)) with
                  | None => inl (diag "ir-ub" "loop header UB assumptions could not be justified")
                  | Some ctx_hdr =>
                      let eff_s := eff_loop_cond (nls_latch_on_true s_s) (nls_ce_cond s_s) in
                      let eff_t := eff_loop_cond (nls_latch_on_true s_t) (nls_ce_cond s_t) in
                      bind_err
                        (guard_err
                          (forallb (expr_safe_under_src ctx_hdr (nls_evals_hdr s_s))
                            (nls_ce_cond s_t :: nls_evals_hdr s_t))
                          (fun _ => diag "ir-ub" "target loop header evaluation/condition may introduce UB/poison"))
                        (fun _ =>
                      bind_err
                        (guard_err (check_expr_refines_with_lrat ctx_hdr eff_s eff_t opt_pf)
                          (proof_err "ir-loop" "loop condition equivalence"))
                        (fun _ =>
                      let ctx_cont_0 :=
                        extract_branch_cond_assumptions (nls_latch_on_true s_s) (nls_ce_cond s_s) ++ ctx_hdr in
                      let latch_uas :=
                        if raw_id_eqb (nls_bid_latch_entry s_s) (nls_bid_hdr s_s) then []
                        else block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_latch_entry s_s) in
                      match fold_ub_assumptions cut_allowed
                              (nls_evals_hdr s_s ++ nls_evals_body s_s) [nls_ce_cond s_s]
                              ctx_cont_0 latch_uas with
                      | None => inl (diag "ir-ub" "loop latch/body UB assumptions could not be justified")
                      | Some ctx_cont =>
                          bind_err
                            (guard_err
                              (forallb (expr_safe_under_src ctx_cont
                                         (nls_evals_hdr s_s ++ nls_evals_body s_s))
                                      (nls_evals_body s_t))
                              (fun _ => diag "ir-ub" "target loop body evaluation may introduce UB/poison"))
                            (fun _ =>
                          bind_err
                            (guard_err
                              (forallb (expr_safe_under_src ctx_cont
                                         ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++
                                          peval_exprs (nls_next_pevals s_s)))
                                      (peval_exprs (nls_next_pevals s_t)))
                              (fun _ => diag "ir-ub" "target loop backedge phi value may introduce UB/poison"))
                            (fun _ =>
                          bind_err
                            (guard_err (check_pevals_refine ctx_cont opt_pf pspecs (nls_next_pevals s_s) (nls_next_pevals s_t))
                              (proof_err "ir-loop" "loop backedge phi step preservation"))
                            (fun _ =>
                          let ctx_exit_0 :=
                            extract_branch_cond_assumptions
                              (negb (nls_latch_on_true s_s)) (nls_ce_cond s_s) ++ ctx_hdr in
                          match fold_ub_assumptions cut_allowed
                                  (nls_evals_hdr s_s ++ nls_evals_exit s_s) [nls_ce_cond s_s]
                                  ctx_exit_0 (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_exit s_s)) with
                          | None => inl (diag "ir-ub" "loop exit block UB assumptions could not be justified")
                          | Some ctx_exit =>
                              match pc_return_obligation cert with
                              | RO_VoidEquiv =>
                                  inl (diag "ir-loop" "void return obligation is unsupported in loop cutpoint mode")
                              | RO_ScalarRefines w _ _ _ =>
                                  bind_err
                                    (guard_err (Pos.eqb w (nls_w_ret s_s))
                                      (fun _ => diag "ir-loop"
                                        ("loop source return width i" ++ diag_pos_dec (nls_w_ret s_s) ++
                                         " disagrees with scalar-refines width i" ++ diag_pos_dec w)))
                                    (fun _ =>
                                  bind_err
                                    (guard_err (Pos.eqb w (nls_w_ret s_t))
                                      (fun _ => diag "ir-loop"
                                        ("loop target return width i" ++ diag_pos_dec (nls_w_ret s_t) ++
                                         " disagrees with scalar-refines width i" ++ diag_pos_dec w)))
                                    (fun _ =>
                                  bind_err
                                    (guard_err
                                      (forallb (expr_safe_under_src ctx_exit
                                                 (nls_evals_hdr s_s ++ nls_evals_exit s_s))
                                              (nls_ce_ret s_t :: nls_evals_exit s_t))
                                      (fun _ => diag "ir-ub" "target loop exit evaluation may introduce UB/poison"))
                                    (fun _ =>
                                  guard_err (check_expr_refines_with_lrat ctx_exit (nls_ce_ret s_s) (nls_ce_ret s_t) opt_pf)
                                    (proof_err "ir-loop" "loop exit return refinement"))))
                              end
                          end)))
                      end))
                  end)))
              end)
          end
      end
  end).

Lemma check_loop_cutpoint_cfg_diag_sound :
  forall allowed init_ctx src_cfg tgt_cfg cert lci opt_pf,
    check_loop_cutpoint_cfg_diag allowed init_ctx src_cfg tgt_cfg cert lci opt_pf = inr tt ->
    check_loop_cutpoint_cfg allowed init_ctx src_cfg tgt_cfg cert lci opt_pf = true.
Proof.
  intros allowed init_ctx src_cfg tgt_cfg cert lci opt_pf H.
  unfold check_loop_cutpoint_cfg_diag in H; unfold check_loop_cutpoint_cfg.
  cbn zeta in *.
  destruct (forallb _ allowed); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (reify_natural_loop src_cfg _ _ _) as [[hspecs_s s_s] |]; [| discriminate H].
  destruct (reify_natural_loop tgt_cfg _ _ _) as [[hspecs_t s_t] |]; [| discriminate H].
  destruct (pair_phi_specs hspecs_s hspecs_t) as [pspecs |]; [| discriminate H].
  destruct (no_dup_strings _); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (fold_ub_assumptions allowed _ _ _ _) as [ctx_ent |]; [| discriminate H].
  destruct (forallb _ (nls_evals_entry s_t)); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (forallb _ (peval_exprs (nls_init_pevals s_t))); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (check_pevals_refine ctx_ent _ _ _ _); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (fold_ub_assumptions _ _ _ _ _) as [ctx_hdr |]; [| discriminate H].
  destruct (forallb _ (nls_ce_cond s_t :: nls_evals_hdr s_t)); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (check_expr_refines_with_lrat ctx_hdr _ _ _); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (fold_ub_assumptions _ _ _ _ _) as [ctx_cont |]; [| discriminate H].
  destruct (forallb _ (nls_evals_body s_t)); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (forallb _ (peval_exprs (nls_next_pevals s_t))); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (check_pevals_refine ctx_cont _ _ _ _); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (fold_ub_assumptions _ _ _ _ _) as [ctx_exit |]; [| discriminate H].
  destruct (pc_return_obligation cert); [discriminate H |].
  repeat match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  | guard_err ?c _ = inr tt =>
      destruct c; cbn [guard_err] in H; [| discriminate H]
  end.
  reflexivity.
Qed.

Definition check_cert_cfg_with_proto_lrat_diag
  (opt_proto : option (list dtyp * list (list param_attr)))
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : string + unit :=
  let src_pnames := List.map cert_reg_name (args src_cfg) in
  let proto_seed :=
    match opt_proto with
    | None => ([], [])
    | Some (p_dtys, s_pattrs) => seed_proto_param_ctx src_pnames p_dtys s_pattrs
    end in
  let allowed := used_src_param_vars src_cfg ++ fst proto_seed in
  let init_ctx := snd proto_seed in
  let src_uses := param_idx_uses_cfg src_cfg in
  let tgt_uses := param_idx_uses_cfg tgt_cfg in
  let src_slots := cfg_alloca_slot_names src_cfg in
  let tgt_slots := cfg_alloca_slot_names tgt_cfg in
  let known_src_slots := src_slots ++ cert_promoted_slot_names cert in
  let blk_uas := fun bid => block_uas_for (init src_cfg) (pc_blocks cert) bid in
  bind_err (check_wf_proof_certificate_diag cert) (fun _ =>
  bind_err (check_validator_syntax_gates_diag src_cfg tgt_cfg) (fun _ =>
  bind_err
    (guard_err (list_empty_b src_slots)
      (fun _ => diag "ir-syntax-F19" "unpromoted stack alloca remains in source IR"))
    (fun _ =>
  bind_err
    (guard_err (list_empty_b tgt_slots)
      (fun _ => diag "ir-syntax-F19" "unpromoted stack alloca remains in target IR"))
    (fun _ =>
  bind_err
    (cf_check_idx_diag_acc (fun idx aw => check_alias_witness_valid_diag idx known_src_slots aw)
       0 (pc_alias_witnesses cert))
    (fun _ =>
  bind_err
    (guard_err (check_ro_vars_subset allowed (pc_return_obligation cert))
      (fun _ => diag "cert-wf" "return obligation references variable outside allowed parameter scope"))
    (fun _ =>
  bind_err
    (guard_err (bmap_varargs_irrel (ocfg_map (blks src_cfg)))
      (fun _ => diag "ir-syntax-F31" "unsupported varargs/bmap metadata in source CFG"))
    (fun _ =>
  bind_err
    (guard_err (bmap_varargs_irrel (ocfg_map (blks tgt_cfg)))
      (fun _ => diag "ir-syntax-F31" "unsupported varargs/bmap metadata in target CFG"))
    (fun _ =>
  bind_err
    (guard_err (Nat.eqb (List.length (args src_cfg)) (List.length (args tgt_cfg)))
      (fun _ => diag "ir-proto" "source and target CFG argument counts differ"))
    (fun _ =>
  bind_err
    (guard_err (no_dup_raw_ids (args src_cfg))
      (fun _ => diag "ir-proto" "duplicate raw parameter IDs in source CFG"))
    (fun _ =>
  bind_err
    (guard_err (no_dup_raw_ids (args tgt_cfg))
      (fun _ => diag "ir-proto" "duplicate raw parameter IDs in target CFG"))
    (fun _ =>
  bind_err
    (guard_err (no_dup_strings src_pnames)
      (fun _ => diag "ir-proto" "duplicate formatted parameter names in source CFG"))
    (fun _ =>
  bind_err
    (guard_err (forallb (fun u => param_use_in u src_uses) tgt_uses)
      (fun _ => diag "ir-proto" "target CFG uses parameter with type incompatible with source CFG"))
    (fun _ =>
  match pc_loop_invariants cert with
  | [] =>
      bind_err
        (cf_check_idx_diag_acc
          (fun _ bc =>
            cf_check_idx_diag_acc
              (fun idx mi =>
                check_memory_invariant_valid_diag (bc_src_block bc) idx allowed (bc_ub_assumptions bc ++ init_ctx) mi)
              0 (bc_memory_invariants bc))
          0 (pc_blocks cert))
        (fun _ =>
      match summarize_cfg_dag_with_uas_diag "source" blk_uas false src_cfg src_pnames with
      | inl err => inl err
      | inr d_src =>
          match summarize_ocfg_dag_diag "target" (default_cfg_dag_fuel tgt_cfg) (fun _ => []) true (args tgt_cfg) src_pnames
                  (defined_ids_of_cfg tgt_cfg) (ocfg_map (blks tgt_cfg)) true (init tgt_cfg) (init tgt_cfg) (RM.empty _) []
          with
          | inl err => inl err
          | inr d_tgt =>
              let fuel := S (dag_node_count d_src + dag_node_count d_tgt) in
              check_dag_refines_cert_path_diag fuel allowed init_ctx [] (pc_return_obligation cert) opt_pf
                (spine_src_evals d_src) (spine_branch_conds d_src) d_src d_tgt
          end
      end)
  | [lci] =>
      check_loop_cutpoint_cfg_diag allowed init_ctx src_cfg tgt_cfg cert lci opt_pf
  | _ :: _ :: _ =>
      inl (diag "ir-loop" "multiple loop invariants in one cert-v1 certificate are not supported")
  end))))))))))))).

Lemma check_cert_cfg_with_proto_lrat_diag_sound :
  forall opt_proto src_cfg tgt_cfg cert opt_pf,
    check_cert_cfg_with_proto_lrat_diag opt_proto src_cfg tgt_cfg cert opt_pf = inr tt ->
    check_cert_cfg_with_proto_lrat opt_proto src_cfg tgt_cfg cert opt_pf = true.
Proof.
  intros opt_proto src_cfg tgt_cfg cert opt_pf H.
  unfold check_cert_cfg_with_proto_lrat_diag in H; unfold check_cert_cfg_with_proto_lrat.
  cbn zeta in *.
  destruct (check_wf_proof_certificate_diag cert) as [| []] eqn:Ewf;
    cbn [bind_err] in H; [discriminate H | rewrite (check_wf_proof_certificate_diag_sound _ Ewf)].
  destruct (check_validator_syntax_gates_diag src_cfg tgt_cfg) as [| []] eqn:Esyn;
    cbn [bind_err] in H; [discriminate H | rewrite (check_validator_syntax_gates_diag_sound _ _ Esyn)].
  do 2 (match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  end).
  match type of H with
  | bind_err (cf_check_idx_diag_acc ?f ?acc ?xs) _ = inr tt =>
      destruct (cf_check_idx_diag_acc f acc xs) as [| []] eqn:Eaw;
        cbn [bind_err] in H; [discriminate H |]
  end.
  rewrite (cf_check_idx_diag_acc_sound _
             (check_alias_witness_valid (cfg_alloca_slot_names src_cfg ++ cert_promoted_slot_names cert))
             _ _
             (fun idx aw Haw => check_alias_witness_valid_diag_sound idx _ aw Haw)
             Eaw).
  repeat match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  end.
  destruct (pc_loop_invariants cert) as [| lci [| ? ?]].
  - match type of H with
    | bind_err (cf_check_idx_diag_acc ?f ?acc ?xs) _ = inr tt =>
        destruct (cf_check_idx_diag_acc f acc xs) as [| []] eqn:Ebm;
          cbn [bind_err] in H; [discriminate H |]
    end.
    pose proof (cf_check_idx_diag_acc_sound _
                  (fun bc =>
                    forallb
                      (check_memory_invariant_valid
                         (used_src_param_vars src_cfg ++
                          fst match opt_proto with
                              | Some (p_dtys, s_pattrs) => seed_proto_param_ctx (List.map cert_reg_name (args src_cfg)) p_dtys s_pattrs
                              | None => ([], [])
                              end)
                         (bc_ub_assumptions bc ++
                          snd match opt_proto with
                              | Some (p_dtys, s_pattrs) => seed_proto_param_ctx (List.map cert_reg_name (args src_cfg)) p_dtys s_pattrs
                              | None => ([], [])
                              end))
                      (bc_memory_invariants bc))
                  _ _
                  (fun _ bc Hbc =>
                    cf_check_idx_diag_acc_sound _
                      (check_memory_invariant_valid _ (bc_ub_assumptions bc ++ _))
                      _ _
                      (fun idx mi Hmi => check_memory_invariant_valid_diag_sound (bc_src_block bc) idx _ _ mi Hmi) Hbc)
                  Ebm) as Hbm.
    rewrite Hbm.
    match type of H with
    | match summarize_cfg_dag_with_uas_diag ?s ?bu ?uf ?g ?sp with _ => _ end = inr tt =>
        destruct (summarize_cfg_dag_with_uas_diag s bu uf g sp) as [| d_src] eqn:Es; [discriminate H |]
    end.
    match type of H with
    | match summarize_ocfg_dag_diag ?s ?fl ?bu ?uf ?pa ?sp ?df ?bm ?ie ?bf ?bc ?sm ?se with _ => _ end = inr tt =>
        destruct (summarize_ocfg_dag_diag s fl bu uf pa sp df bm ie bf bc sm se) as [| d_tgt] eqn:Et; [discriminate H |]
    end.
    unfold summarize_cfg_dag, check_dag_refines_cert.
    rewrite (summarize_cfg_dag_with_uas_diag_sound _ _ _ _ _ _ Es).
    unfold summarize_cfg_dag_with_uas.
    rewrite (summarize_ocfg_dag_diag_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ Et).
    exact (check_dag_refines_cert_path_diag_sound _ _ _ _ _ _ _ _ _ _ H).
  - exact (check_loop_cutpoint_cfg_diag_sound _ _ _ _ _ _ _ H).
  - discriminate H.
Qed.

Definition check_cert_defn_with_lrat_diag
  (src_tenv tgt_tenv : list (ident * typ))
  (src_defn tgt_defn : definition typ (CFG.cfg typ))
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : string + unit :=
  let src_cfg := convert_typ src_tenv (df_instrs src_defn) in
  let tgt_cfg := convert_typ tgt_tenv (df_instrs tgt_defn) in
  let arg_dtys := defn_arg_dtys src_tenv src_defn in
  let s_pattrs := snd (dc_param_attrs (df_prototype src_defn)) in
  bind_err
    (guard_err (cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)))
      (fun _ => diag "cert-fn-name"
        ("certificate function name '" ++ pc_function_name cert ++
         "' does not match IR function '" ++ cert_raw_id_bare (dc_name (df_prototype src_defn)) ++ "'")))
    (fun _ =>
  bind_err (check_prototype_contract_diag (df_prototype src_defn) (df_prototype tgt_defn)) (fun _ =>
  bind_err
    (guard_err (proto_deref_preserved_b (df_prototype src_defn) (df_prototype tgt_defn))
      (fun _ => diag "ir-proto"
        ("dereferenceable attribute contract failed on '" ++ pc_function_name cert ++ "'")))
    (fun _ =>
  bind_err
    (guard_err (forallb2 attr_preserves_dtyp_b arg_dtys s_pattrs)
      (fun _ => diag "ir-proto"
        ("parameter attribute type-preservation failed on '" ++ pc_function_name cert ++ "'")))
    (fun _ =>
  bind_err
    (guard_err (forallb2 raw_id_eqb (df_args src_defn) (args src_cfg))
      (fun _ => diag "ir-proto"
        ("source definition vs CFG parameter ID mismatch on '" ++ pc_function_name cert ++ "'")))
    (fun _ =>
  bind_err
    (guard_err (forallb2 raw_id_eqb (df_args tgt_defn) (args tgt_cfg))
      (fun _ => diag "ir-proto"
        ("target definition vs CFG parameter ID mismatch on '" ++ pc_function_name cert ++ "'")))
    (fun _ =>
  bind_err
    (guard_err (Nat.eqb (List.length arg_dtys) (List.length (args src_cfg)))
      (fun _ => diag "ir-proto"
        ("source prototype vs CFG argument count mismatch on '" ++ pc_function_name cert ++ "'")))
    (fun _ =>
  bind_err
    (guard_err (cfg_param_dtyp_compatible src_cfg arg_dtys)
      (fun _ => diag "ir-proto"
        ("source CFG parameter uses disagree with declared types on '" ++ pc_function_name cert ++ "'")))
    (fun _ => check_cert_cfg_with_proto_lrat_diag (Some (arg_dtys, s_pattrs)) src_cfg tgt_cfg cert opt_pf)))))))).

Lemma check_cert_defn_with_lrat_diag_sound :
  forall src_tenv tgt_tenv src_defn tgt_defn cert opt_pf,
    check_cert_defn_with_lrat_diag src_tenv tgt_tenv src_defn tgt_defn cert opt_pf = inr tt ->
    check_cert_defn_with_lrat src_tenv tgt_tenv src_defn tgt_defn cert opt_pf = true.
Proof.
  intros src_tenv tgt_tenv src_defn tgt_defn cert opt_pf H.
  unfold check_cert_defn_with_lrat_diag in H; unfold check_cert_defn_with_lrat; cbn zeta in *.
  destruct (cert_fn_matches_raw_id _ _); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (check_prototype_contract_diag _ _) as [| []] eqn:Ep;
    cbn [bind_err] in H; [discriminate H | rewrite (check_prototype_contract_diag_sound _ _ Ep)].
  repeat match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  end.
  exact (check_cert_cfg_with_proto_lrat_diag_sound _ _ _ _ _ H).
Qed.

Definition validate_mcfg_with_cert_lrat
  (src_m tgt_m : CFG.mcfg typ)
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : string + unit :=
  match find_unique_defn_by_name_diag "source" (pc_function_name cert) (m_definitions src_m) with
  | inl err => inl err
  | inr src_defn =>
      match find_unique_defn_by_name_diag "target" (pc_function_name cert) (m_definitions tgt_m) with
      | inl err => inl err
      | inr tgt_defn =>
          match check_mcfg_identified_typs_defined_diag "source" src_m with
          | inl err => inl err
          | inr tt =>
              match check_mcfg_identified_typs_defined_diag "target" tgt_m with
              | inl err => inl err
              | inr tt =>
                  check_cert_defn_with_lrat_diag
                    (m_type_defs src_m) (m_type_defs tgt_m) src_defn tgt_defn cert opt_pf
              end
          end
      end
  end.

Definition validate_mcfg_with_cert
  (src_m tgt_m : CFG.mcfg typ)
  (cert : proof_certificate) : string + unit :=
  validate_mcfg_with_cert_lrat src_m tgt_m cert (pc_lrat_proof cert).

Definition validate_tle_pair_with_cert
  (src_tle tgt_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert : proof_certificate) : string + unit :=
  validate_mcfg_with_cert
    (mcfg_of_tle (resolve_module_refs src_tle))
    (mcfg_of_tle (resolve_module_refs tgt_tle))
    cert.

Definition validate_tle_pair_with_cert_str
  (src_tle tgt_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_str : string) : string + unit :=
  match parse_cert cert_str with
  | inl err => inl err
  | inr cert => validate_tle_pair_with_cert src_tle tgt_tle cert
  end.

Theorem validate_mcfg_with_cert_lrat_sound :
  forall {Pa : Params} (src_m tgt_m : CFG.mcfg typ)
         (cert : proof_certificate) (opt_pf : option (list lrat_step)),
    validate_mcfg_with_cert_lrat src_m tgt_m cert opt_pf = inr tt ->
    exists src_defn tgt_defn,
      In src_defn (m_definitions src_m) /\
      In tgt_defn (m_definitions tgt_m) /\
      cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
      dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
      check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
      @validator_defn_refines Pa
        (defn_arg_dtys (m_type_defs src_m) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs src_m)) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs tgt_m)) tgt_defn).
Proof.
  intros Pa src_m tgt_m cert opt_pf Hval.
  unfold validate_mcfg_with_cert_lrat in Hval.
  destruct (find_unique_defn_by_name_diag "source" (pc_function_name cert) (m_definitions src_m))
    as [| src_defn] eqn:Hfs; [discriminate Hval |].
  destruct (find_unique_defn_by_name_diag "target" (pc_function_name cert) (m_definitions tgt_m))
    as [| tgt_defn] eqn:Hft; [discriminate Hval |].
  destruct (check_mcfg_identified_typs_defined_diag "source" src_m) as [| []]; [discriminate Hval |].
  destruct (check_mcfg_identified_typs_defined_diag "target" tgt_m) as [| []]; [discriminate Hval |].
  pose proof (check_cert_defn_with_lrat_diag_sound _ _ _ _ _ _ Hval) as Hchk.
  destruct (find_unique_defn_by_name_diag_in _ _ _ _ Hfs) as [Hin_s _].
  destruct (find_unique_defn_by_name_diag_in _ _ _ _ Hft) as [Hin_t _].
  destruct (@check_cert_defn_with_lrat_sound Pa (m_type_defs src_m) (m_type_defs tgt_m)
              src_defn tgt_defn cert opt_pf Hchk)
    as (Hfn & Hdcnm & Hproto & Href).
  exists src_defn, tgt_defn.
  repeat split; assumption.
Qed.

Theorem validate_mcfg_with_cert_sound :
  forall {Pa : Params} (src_m tgt_m : CFG.mcfg typ) (cert : proof_certificate),
    validate_mcfg_with_cert src_m tgt_m cert = inr tt ->
    exists src_defn tgt_defn,
      In src_defn (m_definitions src_m) /\
      In tgt_defn (m_definitions tgt_m) /\
      cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
      dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
      check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
      @validator_defn_refines Pa
        (defn_arg_dtys (m_type_defs src_m) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs src_m)) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs tgt_m)) tgt_defn).
Proof.
  intros Pa src_m tgt_m cert Hval.
  exact (validate_mcfg_with_cert_lrat_sound src_m tgt_m cert (pc_lrat_proof cert) Hval).
Qed.

Theorem validate_tle_pair_with_cert_str_sound :
  forall {Pa : Params}
         (src_tle tgt_tle : toplevel_entities typ (block typ * list (block typ)))
         (cert_str : string),
    validate_tle_pair_with_cert_str src_tle tgt_tle cert_str = inr tt ->
    let src_m := mcfg_of_tle (resolve_module_refs src_tle) in
    let tgt_m := mcfg_of_tle (resolve_module_refs tgt_tle) in
    exists cert src_defn tgt_defn,
      parse_cert cert_str = inr cert /\
      wf_proof_certificate cert = true /\
      In src_defn (m_definitions src_m) /\
      In tgt_defn (m_definitions tgt_m) /\
      cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
      dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
      check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
      @validator_defn_refines Pa
        (defn_arg_dtys (m_type_defs src_m) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs src_m)) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs tgt_m)) tgt_defn).
Proof.
  intros Pa src_tle tgt_tle cert_str Hval src_m tgt_m.
  unfold validate_tle_pair_with_cert_str in Hval.
  destruct (parse_cert cert_str) as [| cert] eqn:Ep; [discriminate Hval |].
  unfold validate_tle_pair_with_cert in Hval; fold src_m tgt_m in Hval.
  pose proof (parse_cert_wf cert_str cert Ep) as Hwf_cert.
  destruct (@validate_mcfg_with_cert_sound Pa src_m tgt_m cert Hval)
    as (src_defn & tgt_defn & Hin_s & Hin_t & Hfn & Hdcnm & Hproto & Href).
  exists cert, src_defn, tgt_defn.
  repeat split; assumption.
Qed.
