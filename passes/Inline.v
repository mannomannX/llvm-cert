(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Interprocedural Function Inlining Pass ([CertPasses.Inline])

    Purpose:
      Re-exports the [Inline*] stack, builds the 7-state coinductive caller
      inline-loop invariant ([r_caller]) for [denote_function_caller_sim],
      lifts standard-library simulations, and proves [inline_one_site_refines]
      and [inline_mcfg_refines].

    Trust Contract & Fail-Closed Boundary:
      Proof-only top-level theorem module (extraction targets
      [InlineSpec.inline_mcfg] and [InlineSpec.inline_mcfg_typ] in [Extract.v]);
      runtime execution fails closed via [InlineSpec.inline_one_site_mcfg] when
      hygiene or eligibility checks fail.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.PassCommon],
      [CertPasses.common.ItreeTactics], and
      [CertPasses.Inline{Spec,SyntaxProof,FrameGenv,Sim,CalleeProof,CallerProof}];
      zero custom axioms.

    Section Outline:
      7-state [CallerInlineLoop] ([r_caller]) & [denote_function_caller_sim];
      (10C) Library simulations; (10D) Whole-program [inline_mcfg_refines]. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
  Strings.Ascii
  List
  Bool
  Morphisms
  RelationClasses
  Lia.
Import ListNotations.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Events.State
  Events.StateFacts
  Eq.Eqit
  Basics.HeterogeneousRelations
  Interp.Recursion
  Interp.TranslateFacts
  Interp.InterpFacts.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  ScopeTheory
  Theory.Equational
  Theory.MemoryBytesFacts
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.Provenance
  Semantics.Implementations.Pointer
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.

From CertPasses Require Import PassCommon.
From CertPasses.common Require Import ItreeTactics.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.

From CertPasses Require Export
  InlineSpec InlineSyntaxProof InlineFrameGenv InlineSim InlineCalleeProof InlineCallerProof.

Section InliningSemantics.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.
  #[local] Hint Resolve refine_prov__mon : paco.
  #[local] Hint Resolve gen_inline_sim__mon : paco.

  #[local] Ltac try_cfg_raise_h Hact :=
    lazymatch goal with
    | |- cfg_inline_sim _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise, Hact
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise, Hact
    | _ => idtac
    end.

  #[local] Ltac try_cfg_raise :=
    lazymatch goal with
    | |- cfg_inline_sim _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise; reflexivity
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise; reflexivity
    | _ => idtac
    end.

  #[local] Ltac try_cfg_raise_ub_h Hact :=
    lazymatch goal with
    | |- cfg_inline_sim _ _ _ _ _ (@raiseUB _ _ _ _) _ => apply cfg_inline_sim_raiseUB
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raiseUB _ _ _ _) _ => apply cfg_inline_sim_raiseUB
    | |- cfg_inline_sim _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise, Hact
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise, Hact
    | _ => idtac
    end.

  #[local] Ltac try_cfg_raise_ub :=
    lazymatch goal with
    | |- cfg_inline_sim _ _ _ _ _ (@raiseUB _ _ _ _) _ => apply cfg_inline_sim_raiseUB
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raiseUB _ _ _ _) _ => apply cfg_inline_sim_raiseUB
    | |- cfg_inline_sim _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise; reflexivity
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise; reflexivity
    | _ => idtac
    end.

  #[local] Ltac try_mcfg_raise :=
    lazymatch goal with
    | |- mcfg_inline_sim _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply mcfg_inline_sim_raise; reflexivity
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply mcfg_inline_sim_raise; reflexivity
    | _ => idtac
    end.

  (** *** 7-State Coinductive Invariant for Single-Call-Site Inlining *)

  Section CallerInlineLoop.
    Variable g0 : global_env.
    Variable p_callee : @ptr (@PROV PaV) (@PTR PaV).
    Variable caller_df callee_df : definition dtyp (CFG.cfg dtyp).
    Variable pre_blks post_blks : ocfg dtyp.
    Variable b_call : block dtyp.
    Variable pre_cd post_cd : code dtyp.
    Variable call_iid : instr_id.
    Variable call_md : list (metadata dtyp).
    Variable ret_dt : dtyp.
    Variable call_args : list (texp dtyp * list param_attr).
    Variable call_anns : list (annotation dtyp).
    Variable caller_va : option (@ptr (@PROV PaV) (@PTR PaV)).
    Variable stk : env_stack.

    Let caller_cfg := df_instrs caller_df.
    Let callee_cfg := df_instrs callee_df.
    Let callee_gid := dc_name (df_prototype callee_df).
    Let call_bid := blk_id b_call.
    Let opt_ret_dt := match call_iid with IId _ => Some ret_dt | IVoid _ => None end.
    Let caller_df' :=
      inline_site_in_caller caller_df callee_df pre_blks post_blks
        b_call pre_cd post_cd call_iid ret_dt call_args.
    Let caller_cfg' := df_instrs caller_df'.
    Let used_ids := defn_all_ids caller_df ++ defn_all_ids callee_df.
    Let l_origs := callee_local_ids callee_df.
    Let b_origs := callee_block_ids callee_df.
    Let n_loc := List.length l_origs.
    Let n_blk := List.length b_origs.
    Let n_ret := List.length (blks callee_cfg).
    Let all_fresh := fresh_names "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids.
    Let post_bid := hd (Name "inl_post"%string) all_fresh.
    Let va_tmp_id := hd (Name "inl_va"%string) (skipn 1 all_fresh).
    Let l_fresh := firstn n_loc (skipn 2 all_fresh).
    Let b_fresh := firstn n_blk (skipn (2 + n_loc)%nat all_fresh).
    Let ret_tmps := firstn n_ret (skipn (2 + n_loc + n_blk)%nat all_fresh).
    Let ren_l := lookup_ren (combine l_origs l_fresh).
    Let ren_b := lookup_ren (combine b_origs b_fresh).
    Let bk_rtmps := combine (blks callee_cfg) ret_tmps.
    Let in_map := compute_def_map (df_args callee_df) callee_cfg.
    Let opt_c := callee_opt_call p_callee (denote_function callee_df).

    Hypothesis Hg_callee :
      Maps.lookup callee_gid g0 = Some (DVALUE_Base (DVALUE_Pointer p_callee)).
    Hypothesis Hcaller_ok : is_inlinable_caller caller_df = true.
    Hypothesis Hcaller_split : blks caller_cfg = pre_blks ++ b_call :: post_blks.
    Hypothesis Hcd_split :
      blk_code b_call =
        pre_cd ++
        (call_iid,
         INSTR_Call (ret_dt, EXP_Ident (ID_Global callee_gid)) call_args call_anns [],
         call_md) :: post_cd.
    Hypothesis Harg_len : List.length call_args = List.length (df_args callee_df).
    Hypothesis Hpattrs_nil : forall te pattrs, In (te, pattrs) call_args -> pattrs = [].
    Hypothesis Hcc_eq :
      cconv_eqb (anns_cconv call_anns)
        (anns_cconv (dc_annotations (df_prototype callee_df))) = true.
    Hypothesis Hcall_rattrs : ann_ret_attributes call_anns = [].
    Hypothesis Hcall_fattrs : forallb is_safe_fn_attr (ann_fun_attributes call_anns) = true.
    Hypothesis Hcall_range : metadata_range call_md = None.
    Hypothesis Hcallee_ok : is_inlinable_callee opt_ret_dt callee_df = true.

    Let tree_at1 (b_from bid : block_id) : @CFGtop PaV (@dvalue PaV) :=
      ITree.bind (denote_ocfg_map (ocfg_map (blks caller_cfg)) caller_va (b_from, bid)) finish_cfg.

    Let tree_at2 (b_from bid : block_id) : @CFGtop PaV (@dvalue PaV) :=
      ITree.bind (denote_ocfg_map (ocfg_map (blks caller_cfg')) caller_va (b_from, bid)) finish_cfg.

    Let tree_callee1 (b_from bid : block_id) (varg : @ptr (@PROV PaV) (@PTR PaV)) : @CFGtop PaV (@dvalue PaV) :=
      ITree.bind (denote_ocfg_map (ocfg_map (blks callee_cfg)) (Some varg) (b_from, bid)) finish_cfg.

    Let call_loc : string :=
      (set_loc (get_file_info call_md) ++ location_error_string call_md)%string.

    Let write_call_res (dv : @dvalue PaV) : @CFGtop PaV unit :=
      match call_iid with
      | IVoid _ => Ret tt
      | IId id => lwrite id dv
      end.

    Let post_call_u1 : @CFGtop PaV (@dvalue PaV) :=
      ITree.bind
        (ITree.bind (denote_code post_cd caller_va)
           (fun _ => denote_terminator (blk_term b_call)))
        (step_bd_cont (blks caller_cfg) caller_va call_bid).

    Let call_after_ret_k1 (vs : list (@dvalue PaV)) (rv : @exc PaV + @dvalue PaV)
      : @CFGtop PaV (@dvalue PaV) :=
      ITree.bind
        (check_call_return (ann_fun_attributes call_anns) (ann_ret_attributes call_anns)
           (metadata_range call_md) (call_loc ++ ": Call")%string vs rv)
        (fun res =>
           ITree.bind
             (match res with
              | inl ex => raiseLLVM ex
              | inr dv => Ret dv
              end)
             (fun returned_value =>
                ITree.bind (write_call_res returned_value) (fun _ => post_call_u1))).

    Let call_after_args_k1 (vs : list (@dvalue PaV)) : @CFGtop PaV (@dvalue PaV) :=
      ITree.bind
        (ITree.bind (denote_exp' None (EXP_Ident (ID_Global callee_gid)))
           (fun fv => call ret_dt (anns_cconv call_anns) fv vs))
        (call_after_ret_k1 vs).

    Let pre_after_args_k2 (_ : unit) : @CFGtop PaV (@dvalue PaV) :=
      ITree.bind (alloca (DTYPE_Struct true []) 1%N None)
        (fun v =>
           ITree.bind (lwrite va_tmp_id v)
             (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg))))).

    Let callee_outer_k1 (vs : list (@dvalue PaV)) (rv : @exc PaV + @dvalue PaV)
      : @CFGtop PaV (@exc PaV + @dvalue PaV) :=
      Tau (run_exc (call_after_ret_k1 vs rv)).

    Let callee_epilogue_k1 (vs : list (@dvalue PaV)) (rv : @exc PaV + @dvalue PaV)
      : @CFGtop PaV (@exc PaV + @dvalue PaV) :=
      ITree.bind pop_call_frame
        (fun _ =>
           ITree.bind
             (check_call_return (dc_attrs (df_prototype callee_df))
                (fst (dc_param_attrs (df_prototype callee_df))) None
                (show_raw_id callee_gid) vs rv)
             (callee_outer_k1 vs)).

    Let out_rel : inline_ctx -> @exc PaV + @dvalue PaV -> @exc PaV + @dvalue PaV -> Prop :=
      fun ic' rv1 rv2 =>
        exists e1' e2',
          ic' = IC_Synced stk e1' e2' /\
          rv1 = rv2.

    Let sync_bd_rel : inline_ctx -> block_id + @dvalue PaV -> block_id + @dvalue PaV -> Prop :=
      fun ic' bd1 bd2 =>
        bd1 = bd2 /\
        (forall succ_bid,
           bd1 = inl succ_bid ->
           succ_bid <> post_bid /\ ~ In succ_bid b_fresh) /\
        exists e1' e2',
          ic' = IC_Synced stk e1' e2' /\
          env_agree_outside all_fresh e1' e2'.

    Let call_pre_rel : inline_ctx -> list (@dvalue PaV) -> unit -> Prop :=
      fun ic' vs r2 =>
        r2 = tt /\
        List.length vs = List.length (df_args callee_df) /\
        exists ce1 e2_args,
          ic' = IC_Synced stk ce1 e2_args /\
          env_agree_outside all_fresh ce1 e2_args /\
          (forall p v,
             In (p, v) (combine (df_args callee_df) vs) ->
             Maps.lookup (ren_l p) e2_args = Some v).

    Let callee_bd_rel (bk_cur : block dtyp) (rtmp_cur : raw_id) (ce1 : @local_env PaV)
      : inline_ctx -> block_id + @dvalue PaV -> block_id + @dvalue PaV -> Prop :=
      fun ic' bd1 bd2 =>
        (exists succ_bid d_out e1' e2',
           bd1 = inl succ_bid /\
           bd2 = inl (ren_b succ_bid) /\
           In succ_bid (term_succ_bids (snd (fst (blk_term bk_cur)))) /\
           check_succ_edge (blks callee_cfg) in_map (blk_id bk_cur) d_out succ_bid = true /\
           incl d_out l_origs /\
           ic' = IC_Inlined stk ce1 e1' e2' /\
           callee_defs_bound ren_l d_out e1' e2' /\
           env_agree_outside all_fresh ce1 e2') \/
        (exists dv e1' e2',
           bd1 = inr dv /\
           bd2 = inl post_bid /\
           ic' = IC_Inlined stk ce1 e1' e2' /\
           env_agree_outside all_fresh ce1 e2' /\
           match opt_ret_dt with
           | None => True
           | Some _ =>
               (exists rpair, snd (fst (blk_term bk_cur)) = TERM_Ret rpair) /\
               Maps.lookup rtmp_cur e2' = Some dv
           end).

    Inductive r_caller
      : inline_ctx ->
        @CFGtop PaV (@exc PaV + @dvalue PaV) ->
        @CFGtop PaV (@exc PaV + @dvalue PaV) -> Prop :=
    | RC_CallerAt (b_from1 b_from2 bid_cur : block_id) (e1 e2 : @local_env PaV) :
        env_agree_outside all_fresh e1 e2 ->
        bid_cur <> post_bid ->
        ~ In bid_cur b_fresh ->
        ((bid_cur = init caller_cfg /\ b_from1 = init caller_cfg /\ b_from2 = init caller_cfg) \/
         (b_from1 <> post_bid /\ b_from2 = remap_pred_id call_bid post_bid b_from1)) ->
        r_caller (IC_Synced stk e1 e2)
          (run_exc (tree_at1 b_from1 bid_cur))
          (run_exc (tree_at2 b_from2 bid_cur))
    | RC_SyncStep (src1 src2 : block_id) (ic0 : inline_ctx)
        (u1 u2 : @CFGtop PaV (block_id + @dvalue PaV)) :
        src1 <> post_bid ->
        src2 = remap_pred_id call_bid post_bid src1 ->
        ic_synced_stk stk ic0 ->
        cfg_inline_sim opt_c g0 false sync_bd_rel ic0 u1 u2 ->
        r_caller ic0
          (run_exc (ITree.bind u1 (step_bd_cont (blks caller_cfg) caller_va src1)))
          (run_exc (ITree.bind u2 (step_bd_cont (blks caller_cfg') caller_va src2)))
    | RC_CallPre (ic0 : inline_ctx)
        (u1 : @CFGtop PaV (list (@dvalue PaV)))
        (u2 : @CFGtop PaV unit) :
        ic_synced_stk stk ic0 ->
        cfg_inline_sim opt_c g0 false call_pre_rel ic0 u1 u2 ->
        r_caller ic0
          (run_exc (ITree.bind u1 call_after_args_k1))
          (run_exc (ITree.bind u2 pre_after_args_k2))
    | RC_VaFinish (ce1 e1_c0 e2_args : @local_env PaV)
        (vs : list (@dvalue PaV)) (varg : @ptr (@PROV PaV) (@PTR PaV)) :
        e1_c0 = init_local_env (combine (df_args callee_df) vs) ->
        List.length vs = List.length (df_args callee_df) ->
        env_agree_outside all_fresh ce1 e2_args ->
        (forall p v,
           In (p, v) (combine (df_args callee_df) vs) ->
           Maps.lookup (ren_l p) e2_args = Some v) ->
        r_caller (IC_Inlined stk ce1 e1_c0 e2_args)
          (ITree.bind
             (store (DTYPE_Struct true [])
                (DVALUE_Base (DVALUE_Pointer varg))
                (DVALUE_Struct true []))
             (fun _ =>
                ITree.bind (run_exc (tree_callee1 (init callee_cfg) (init callee_cfg) varg))
                  (callee_epilogue_k1 vs)))
          (run_exc
             (ITree.bind (lwrite va_tmp_id (DVALUE_Base (DVALUE_Pointer varg)))
                (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg))))))
    | RC_CalleeAt (b_from1 b_from2 b_cur : block_id) (d_in : list raw_id)
        (ce1 e1_c e2_c : @local_env PaV)
        (vs : list (@dvalue PaV)) (varg : @ptr (@PROV PaV) (@PTR PaV)) :
        List.length vs = List.length (df_args callee_df) ->
        incl d_in l_origs ->
        incl (lookup_def_set in_map b_cur) d_in ->
        callee_defs_bound ren_l d_in e1_c e2_c ->
        env_agree_outside all_fresh ce1 e2_c ->
        (exists bk_cur,
           find_block (blks callee_cfg) b_cur = Some bk_cur /\
           (blk_phis bk_cur = [] \/
            (b_from2 = ren_b b_from1 /\
             In b_from1 b_origs /\
             Forall
               (fun '(_, Phi _ _ pargs, md) =>
                  exists op,
                    assoc b_from1 pargs = Some op /\
                    incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_in)
               (blk_phis bk_cur)))) ->
        r_caller (IC_Inlined stk ce1 e1_c e2_c)
          (ITree.bind (run_exc (tree_callee1 b_from1 b_cur varg)) (callee_epilogue_k1 vs))
          (run_exc (tree_at2 b_from2 (ren_b b_cur)))
    | RC_CalleeStep (ce1 : @local_env PaV) (vs : list (@dvalue PaV)) (varg : @ptr (@PROV PaV) (@PTR PaV))
        (b_cur : block_id) (bk_cur : block dtyp) (rtmp_cur : raw_id)
        (ic0 : inline_ctx)
        (u1 u2 : @CFGtop PaV (block_id + @dvalue PaV)) :
        is_ic_inlined ic0 = true ->
        List.length vs = List.length (df_args callee_df) ->
        b_cur = blk_id bk_cur ->
        In (bk_cur, rtmp_cur) bk_rtmps ->
        cfg_inline_sim opt_c g0 false (callee_bd_rel bk_cur rtmp_cur ce1) ic0 u1 u2 ->
        r_caller ic0
          (ITree.bind
             (run_exc (ITree.bind u1 (step_bd_cont (blks callee_cfg) (Some varg) b_cur)))
             (callee_epilogue_k1 vs))
          (run_exc (ITree.bind u2 (step_bd_cont (blks caller_cfg') caller_va (ren_b b_cur))))
    | RC_PostAt (b_ret rtmp_ret : raw_id) (bk_ret : block dtyp)
        (dv : @dvalue PaV) (ce1 e2' : @local_env PaV) (vs : list (@dvalue PaV)) :
        b_ret = blk_id bk_ret ->
        In (bk_ret, rtmp_ret) bk_rtmps ->
        env_agree_outside all_fresh ce1 e2' ->
        match opt_ret_dt with
        | None => True
        | Some _ =>
            (exists rpair, snd (fst (blk_term bk_ret)) = TERM_Ret rpair) /\
            Maps.lookup rtmp_ret e2' = Some dv
        end ->
        r_caller (IC_Synced stk ce1 e2')
          (run_exc (call_after_ret_k1 vs (inr dv)))
          (run_exc (tree_at2 (ren_b b_ret) post_bid)).

    Lemma denote_run_exc_cfg_caller_inline_sim (e1 e2 : @local_env PaV)
      (Hagree0 : env_agree_outside all_fresh e1 e2) :
      cfg_inline_sim opt_c g0 true out_rel
        (IC_Synced stk e1 e2)
        (run_exc (denote_cfg_map (ocfg_map (blks caller_cfg)) caller_cfg caller_va))
        (run_exc (denote_cfg_map (ocfg_map (blks caller_cfg')) caller_cfg' caller_va)).
    Proof using Hg_callee Hcaller_ok Hcaller_split Hcd_split Harg_len
                Hpattrs_nil Hcc_eq Hcall_rattrs Hcall_fattrs Hcall_range Hcallee_ok.
      (* Unpack caller & callee eligibility guards and fresh-ID partition *)
      pose proof Hcaller_ok as Hc1.
      unfold is_inlinable_caller in Hc1; cbn zeta in Hc1; fold caller_cfg in Hc1.
      apply andb_prop in Hc1 as [Hc1 _].
      apply andb_prop in Hc1 as [Hcaller_nd Hcaller_entry].
      apply nodup_raw_ids_spec in Hcaller_nd.

      pose proof Hcallee_ok as Hce.
      unfold is_inlinable_callee in Hce; cbn zeta in Hce; fold callee_gid callee_cfg in Hce.
      apply andb_prop in Hce as [Hce Hvmap].
      unfold check_cfg_def_before_use in Hvmap; fold in_map in Hvmap.
      apply andb_prop in Hce as [Hce _].
      apply andb_prop in Hce as [Hce Hcallee_leaf_b].
      rewrite forallb_forall in Hcallee_leaf_b.
      apply andb_prop in Hce as [Hce _].
      apply andb_prop in Hce as [Hce Hcallee_entry].
      apply andb_prop in Hce as [Hce Hcallee_nd].
      apply nodup_raw_ids_spec in Hcallee_nd.
      apply andb_prop in Hce as [Hce Hcallee_args_nd].
      apply nodup_raw_ids_spec in Hcallee_args_nd.
      apply andb_prop in Hce as [Hce Hproto_fattrs].
      apply andb_prop in Hce as [Hce Hproto_pattrs].
      apply andb_prop in Hce as [Hce Hproto_rattrs].
      apply is_empty_list_spec in Hproto_rattrs.
      apply andb_prop in Hce as [Hce _].
      apply andb_prop in Hce as [Hce _].
      apply andb_prop in Hce as [Hce _].
      apply andb_prop in Hce as [Hintr_b _].
      assert (Hintr_none : lookup_intrinsic_declaration callee_gid = None).
      { destruct (lookup_intrinsic_declaration callee_gid); [discriminate Hintr_b | reflexivity]. }

      pose proof (all_fresh_partition used_ids n_loc n_blk n_ret)
        as (Eaf & Hlen_l & Hlen_b & Hlen_r & Hnd_af & Hdisj_used).
      fold all_fresh post_bid va_tmp_id l_fresh b_fresh ret_tmps in
        Eaf, Hlen_l, Hlen_b, Hlen_r, Hnd_af, Hdisj_used.
      assert (Hpb_af : In post_bid all_fresh) by (rewrite Eaf; left; reflexivity).
      assert (Hva_af : In va_tmp_id all_fresh) by (rewrite Eaf; right; left; reflexivity).
      assert (Hlf_af : forall x, In x l_fresh -> In x all_fresh).
      { intros x Hx; rewrite Eaf; right; right; apply in_or_app; left; exact Hx. }
      assert (Hbf_af : forall x, In x b_fresh -> In x all_fresh).
      { intros x Hx; rewrite Eaf; right; right; apply in_or_app; right; apply in_or_app; left; exact Hx. }
      assert (Hrt_af : forall x, In x ret_tmps -> In x all_fresh).
      { intros x Hx; rewrite Eaf; right; right; apply in_or_app; right; apply in_or_app; right; exact Hx. }
      pose proof Hnd_af as Hnd_af0; rewrite Eaf in Hnd_af0.
      inversion Hnd_af0 as [| ? ? _ Hnd_af1]; subst.
      inversion Hnd_af1 as [| ? ? Hnin_va Hnd_lbr]; subst.
      assert (Hva_not_lf : ~ In va_tmp_id l_fresh).
      { intros Hin; apply Hnin_va, in_or_app; left; exact Hin. }
      pose proof (inl_nodup_app_l _ _ Hnd_lbr) as Hnd_lf.
      pose proof (inl_nodup_app_r _ _ Hnd_lbr) as Hnd_br.
      pose proof (inl_nodup_app_l _ _ Hnd_br) as Hnd_bf.
      assert (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2).
      { apply lookup_ren_inj_on; [symmetry; exact Hlen_l | exact Hnd_lf]. }
      assert (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh).
      { intros x Hx; apply Hlf_af, lookup_ren_in_dom; [symmetry; exact Hlen_l | exact Hx]. }
      assert (Hinj_b : forall b1 b2, In b1 b_origs -> In b2 b_origs -> ren_b b1 = ren_b b2 -> b1 = b2).
      { apply lookup_ren_inj_on; [symmetry; exact Hlen_b | exact Hnd_bf]. }
      assert (Hren_b_bf : forall b, In b b_origs -> In (ren_b b) b_fresh).
      { intros b Hb; apply lookup_ren_in_dom; [symmetry; exact Hlen_b | exact Hb]. }
      assert (Hcaller_not_af : forall x, In x (defn_all_ids caller_df) -> ~ In x all_fresh).
      { intros x Hx Haf; eapply Hdisj_used; [exact Haf | unfold used_ids; apply in_or_app; left; exact Hx]. }
      assert (Hbcall_in : In b_call (blks caller_cfg)).
      { rewrite Hcaller_split; apply in_or_app; right; left; reflexivity. }
      assert (Hcall_ne_post : call_bid <> post_bid).
      { intros Heq; eapply Hcaller_not_af;
          [apply defn_all_ids_blk_id, Hbcall_in | unfold call_bid in Heq; rewrite Heq; exact Hpb_af]. }
      assert (Hcaller_lbl_safe :
        forall bk b,
          In bk (blks caller_cfg) ->
          In b (block_all_label_ids bk) ->
          b <> post_bid /\ ~ In b b_fresh).
      { intros bk b Hbk Hb.
        pose proof (Hcaller_not_af b (defn_all_ids_label_ids caller_df bk b Hbk Hb)) as Hnaf.
        split; [intros Heq; rewrite Heq in Hnaf; exact (Hnaf Hpb_af) | intros Hbf; exact (Hnaf (Hbf_af b Hbf))]. }
      assert (Hcaller_use_safe :
        forall bk x,
          In bk (blks caller_cfg) ->
          In x (full_block_uses bk) ->
          ~ In x all_fresh).
      { intros bk x Hbk Hx; apply Hcaller_not_af, (defn_all_ids_block_uses caller_df bk x Hbk Hx). }
      assert (Hexc_out : forall ea1 ea2 ex, out_rel (IC_Synced stk ea1 ea2) (inl ex) (inl ex)).
      { intros ea1 ea2 ex; exists ea1, ea2; auto. }

      (* 1. [RC_SyncStep]: step caller non-call / post-call block body to [RC_CallerAt] or return *)
      assert (Hsync_step :
        forall src1 src2 ic0 u1 u2,
          src1 <> post_bid ->
          src2 = remap_pred_id call_bid post_bid src1 ->
          ic_synced_stk stk ic0 ->
          cfg_inline_sim opt_c g0 false sync_bd_rel ic0 u1 u2 ->
          gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller ic0
            (run_exc (ITree.bind u1 (step_bd_cont (blks caller_cfg) caller_va src1)))
            (run_exc (ITree.bind u2 (step_bd_cont (blks caller_cfg') caller_va src2)))).
      { intros src1 src2 ic0 u1 u2 Hsrc1 Hsrc2 Hic0 Hu.
        eapply (run_exc_bind_step_sync opt_c g0 true stk sync_bd_rel out_rel r_caller
                  (step_bd_cont (blks caller_cfg) caller_va src1)
                  (step_bd_cont (blks caller_cfg') caller_va src2)
                  Hexc_out);
          [| | exact Hic0 | exact Hu].
        - intros ic' m1 m2 Hic' Hm; eapply RC_SyncStep; eassumption.
        - intros ic' bd1 bd2 _ (<- & Hsucc & e1' & e2' & -> & Hag').
          destruct bd1 as [succ_bid | dv]; cbn [step_bd_cont].
          + eapply gen_inline_sim__obs_eq;
              [symmetry; apply run_exc_tau_eq; reflexivity
              | symmetry; apply run_exc_tau_eq; reflexivity |].
            apply GIS_Step; cbn [gis_step_body observe].
            exists (run_exc (tree_at1 src1 succ_bid)),
                   (run_exc (tree_at2 src2 succ_bid)).
            split; [apply ITS_Refl | split; [apply ITS_Refl |]].
            destruct (Hsucc succ_bid Logic.eq_refl) as [Hs_post Hs_bf].
            apply RC_CallerAt; [exact Hag' | exact Hs_post | exact Hs_bf | right; split; assumption].
          + eapply gen_inline_sim__obs_eq;
              [symmetry; apply run_exc_ret_eq; reflexivity
              | symmetry; apply run_exc_ret_eq; reflexivity |].
            apply GIS_Step; cbn [gis_step_body observe]; exists e1', e2'; auto. }

      (* 2. [RC_CalleeStep]: step inlined callee block body to [RC_CalleeAt] or [RC_PostAt] *)
      assert (Hcallee_step :
        forall ce1 vs varg b_cur bk_cur rtmp_cur ic0 u1 u2,
          is_ic_inlined ic0 = true ->
          List.length vs = List.length (df_args callee_df) ->
          b_cur = blk_id bk_cur ->
          In (bk_cur, rtmp_cur) bk_rtmps ->
          cfg_inline_sim opt_c g0 false (callee_bd_rel bk_cur rtmp_cur ce1) ic0 u1 u2 ->
          gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller ic0
            (ITree.bind
               (run_exc (ITree.bind u1 (step_bd_cont (blks callee_cfg) (Some varg) b_cur)))
               (callee_epilogue_k1 vs))
            (run_exc (ITree.bind u2 (step_bd_cont (blks caller_cfg') caller_va (ren_b b_cur))))).
      { intros ce1 vs varg b_cur bk_cur rtmp_cur ic0 u1 u2 Hic0 Hvs_len Hbcur Hbk_rtmp Hu.
        eapply (run_exc_bind_step_inlined opt_c g0 true
                  (callee_bd_rel bk_cur rtmp_cur ce1) out_rel r_caller
                  (step_bd_cont (blks callee_cfg) (Some varg) b_cur)
                  (callee_epilogue_k1 vs)
                  (step_bd_cont (blks caller_cfg') caller_va (ren_b b_cur)));
          [| | exact Hic0 | exact Hu].
        - intros ic' m1 m2 Hic' Hm; eapply RC_CalleeStep; eassumption.
        - intros ic' bd1 bd2 _ Hbd.
          destruct Hbd as [(succ_bid & d_out & e1' & e2' & -> & -> & _ & Hedge & Hdout_dom & -> & Hbound & Hag')
                          | (dv & e1' & e2' & -> & -> & -> & Hag' & Hret_info)];
            cbn [step_bd_cont].
          + eapply gen_inline_sim__obs_eq;
              [symmetry; erewrite run_exc_tau_eq; [rewrite Eqit.bind_tau; reflexivity | reflexivity]
              | symmetry; apply run_exc_tau_eq; reflexivity |].
            apply GIS_Step; cbn [gis_step_body observe].
            exists (ITree.bind (run_exc (tree_callee1 b_cur succ_bid varg)) (callee_epilogue_k1 vs)),
                   (run_exc (tree_at2 (ren_b b_cur) (ren_b succ_bid))).
            split; [apply ITS_Refl | split; [apply ITS_Refl |]].
            rewrite <- Hbcur in Hedge.
            apply check_succ_edge_inv in Hedge as (b_succ & Hfb_succ & Hd_succ & Hphis_succ).
            assert (Hbcur_orig : In b_cur b_origs).
            { rewrite Hbcur; apply callee_block_ids_blk_id; eapply in_combine_l, Hbk_rtmp. }
            eapply RC_CalleeAt with (d_in := d_out);
              [exact Hvs_len | exact Hdout_dom | exact Hd_succ | exact Hbound | exact Hag' |].
            exists b_succ; split; [exact Hfb_succ | right; auto].
          + assert (El_pop :
              ITree.bind (run_exc (Ret dv)) (callee_epilogue_k1 vs) ≅
              ITree.bind (ITree.trigger (subevent _ StackPop))
                (fun _ =>
                   ITree.bind (ITree.trigger (subevent _ MemPop))
                     (fun _ => Tau (run_exc (call_after_ret_k1 vs (inr dv)))))).
            { rewrite (run_exc_ret_eq (Ret dv) dv Logic.eq_refl), Eqit.bind_ret_l.
              unfold callee_epilogue_k1, pop_call_frame, stack_pop, mem_pop.
              try unfold trigger; norm_subevent.
              cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
              rewrite Eqit.bind_bind.
              apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
              apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
              rewrite Hproto_rattrs.
              rewrite (check_call_return_safe_inr_eq _ _ _ _ Hproto_fattrs), Eqit.bind_ret_l.
              reflexivity. }
            eapply GIS_StackPopL; [reflexivity | exact El_pop |].
            eapply GIS_MemPopL; [reflexivity | reflexivity |].
            eapply gen_inline_sim__obs_eq;
              [reflexivity | symmetry; apply run_exc_tau_eq; reflexivity |].
            apply GIS_Step; cbn [gis_step_body observe].
            exists (run_exc (call_after_ret_k1 vs (inr dv))),
                   (run_exc (tree_at2 (ren_b b_cur) post_bid)).
            split; [apply ITS_Refl | split; [apply ITS_Refl |]].
            eapply RC_PostAt; eassumption. }

      (* 3. [RC_CalleeAt]: unfold callee block and delegate to [Hcallee_step] *)
      assert (Hcallee_at :
        forall b_from1 b_from2 b_cur d_in ce1 e1_c e2_c vs varg,
          List.length vs = List.length (df_args callee_df) ->
          incl d_in l_origs ->
          incl (lookup_def_set in_map b_cur) d_in ->
          callee_defs_bound ren_l d_in e1_c e2_c ->
          env_agree_outside all_fresh ce1 e2_c ->
          (exists bk_cur,
             find_block (blks callee_cfg) b_cur = Some bk_cur /\
             (blk_phis bk_cur = [] \/
              (b_from2 = ren_b b_from1 /\
               In b_from1 b_origs /\
               Forall
                 (fun '(_, Phi _ _ pargs, md) =>
                    exists op,
                      assoc b_from1 pargs = Some op /\
                      incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_in)
                 (blk_phis bk_cur)))) ->
          gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller (IC_Inlined stk ce1 e1_c e2_c)
            (ITree.bind (run_exc (tree_callee1 b_from1 b_cur varg)) (callee_epilogue_k1 vs))
            (run_exc (tree_at2 b_from2 (ren_b b_cur)))).
      { intros b_from1 b_from2 b_cur d_in ce1 e1_c e2_c vs varg
          Hvs_len Hdin_dom Hd0_in Hbound Hagree (bk_cur & Hfb_cur & Hentry_or_pred).
        pose proof (find_block_has_id _ _ Hfb_cur) as Hbcur_id.
        pose proof (find_block_In' _ _ Hfb_cur) as Hbk_in.
        destruct (in_combine_same_length (blks callee_cfg) ret_tmps Hlen_r bk_cur Hbk_in)
          as [rtmp_cur Hbk_rtmp].
        assert (Hrtmp_af : In rtmp_cur all_fresh).
        { apply Hrt_af; eapply in_combine_r, Hbk_rtmp. }
        pose proof (find_block_new_callee caller_df callee_df pre_blks post_blks
                      b_call pre_cd post_cd call_iid ret_dt call_args bk_cur rtmp_cur
                      Hcaller_nd Hcaller_split Hcallee_nd Hbk_rtmp) as Hfb_new.
        fold caller_df' caller_cfg' used_ids l_origs b_origs n_loc n_blk n_ret
             all_fresh post_bid l_fresh b_fresh ret_tmps ren_l ren_b in Hfb_new.
        rewrite <- Hbcur_id in Hfb_new.
        assert (El_u :
          ITree.bind (run_exc (tree_callee1 b_from1 b_cur varg)) (callee_epilogue_k1 vs) ≅
          ITree.bind
            (run_exc (ITree.bind (denote_block bk_cur b_from1 (Some varg))
                        (step_bd_cont (blks callee_cfg) (Some varg) b_cur)))
            (callee_epilogue_k1 vs)).
        { apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
          apply run_exc_proper; unfold tree_callee1; apply ocfg_bind_finish_some_eq, Hfb_cur. }
        assert (Er_u :
          run_exc (tree_at2 b_from2 (ren_b b_cur)) ≅
          run_exc
            (ITree.bind
               (denote_block (transform_callee_block ren_l ren_b post_bid (bk_cur, rtmp_cur))
                  b_from2 caller_va)
               (step_bd_cont (blks caller_cfg') caller_va (ren_b b_cur)))).
        { apply run_exc_proper; unfold tree_at2; apply ocfg_bind_finish_some_eq, Hfb_new. }
        eapply gen_inline_sim__obs_eq; [symmetry; exact El_u | symmetry; exact Er_u |].
        eapply (Hcallee_step ce1 vs varg b_cur bk_cur rtmp_cur
                  (IC_Inlined stk ce1 e1_c e2_c));
          [reflexivity | exact Hvs_len | exact Hbcur_id | exact Hbk_rtmp |].
        apply (denote_block_callee_sim opt_c g0 opt_ret_dt l_origs b_origs all_fresh d_in
                 in_map (blks callee_cfg) ren_l ren_b post_bid (Some varg) caller_va
                 stk ce1 e1_c e2_c b_from1 b_from2 bk_cur rtmp_cur
                 Hinj_l Hfresh_l Hinj_b Hrtmp_af).
        - apply Hcallee_leaf_b, Hbk_in.
        - apply (verify_def_map_block _ _ _ _ Hvmap Hbk_in).
        - exact Hdin_dom.
        - rewrite <- Hbcur_id; exact Hd0_in.
        - intros x Hx; eapply callee_local_ids_defs; eassumption.
        - intros b Hb; eapply callee_block_ids_label; eassumption.
        - exact Hbound.
        - exact Hagree.
        - exact Hentry_or_pred. }

      (* 4. [RC_VaFinish]: finish 0-byte varargs store / local write and enter [Hcallee_at] *)
      assert (Hva_finish :
        forall ce1 e1_c0 e2_args vs varg,
          e1_c0 = init_local_env (combine (df_args callee_df) vs) ->
          List.length vs = List.length (df_args callee_df) ->
          env_agree_outside all_fresh ce1 e2_args ->
          (forall p v,
             In (p, v) (combine (df_args callee_df) vs) ->
             Maps.lookup (ren_l p) e2_args = Some v) ->
          gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller (IC_Inlined stk ce1 e1_c0 e2_args)
            (ITree.bind
               (store (DTYPE_Struct true [])
                  (DVALUE_Base (DVALUE_Pointer varg))
                  (DVALUE_Struct true []))
               (fun _ =>
                  ITree.bind (run_exc (tree_callee1 (init callee_cfg) (init callee_cfg) varg))
                    (callee_epilogue_k1 vs)))
            (run_exc
               (ITree.bind (lwrite va_tmp_id (DVALUE_Base (DVALUE_Pointer varg)))
                  (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg))))))).
      { intros ce1 e1_c0 e2_args vs varg He1_c0 Hvs_len Hagree Hparams.
        set (dv_va := DVALUE_Base (DVALUE_Pointer varg)).
        eapply GIS_ZeroStoreL; [unfold store, dv_va; norm_subevent; reflexivity |].
        assert (Er_va :
          run_exc (ITree.bind (lwrite va_tmp_id dv_va)
                     (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg))))) ≅
          ITree.bind (ITree.trigger (subevent _ (LocalWrite va_tmp_id dv_va)))
            (fun _ => Tau (run_exc (Tau (tree_at2 call_bid (ren_b (init callee_cfg))))))).
        { unfold lwrite; norm_subevent.
          rewrite run_exc_bind_trigger_none_eq by reflexivity;
            reflexivity. }
        eapply GIS_WriteR with (ic' := IC_Inlined stk ce1 e1_c0 (Maps.add va_tmp_id dv_va e2_args));
          [reflexivity | exact Er_va |].
        eapply GIS_TauR; [reflexivity |].
        eapply gen_inline_sim__obs_eq;
          [reflexivity | symmetry; apply run_exc_tau_eq; reflexivity |].
        eapply GIS_TauR; [reflexivity |].
        assert (Hbound0 : callee_defs_bound ren_l (df_args callee_df) e1_c0 e2_args).
        { intros x Hx.
          destruct (in_combine_same_length (df_args callee_df) vs Hvs_len x Hx) as [v Hxv].
          exists v; split.
          - rewrite He1_c0; apply init_local_env_nodup_lookup;
              [exact Hcallee_args_nd | symmetry; exact Hvs_len | exact Hxv].
          - apply Hparams, Hxv. }
        eapply (Hcallee_at (init callee_cfg) call_bid (init callee_cfg) (df_args callee_df)
                  ce1 e1_c0 (Maps.add va_tmp_id dv_va e2_args) vs varg).
        - exact Hvs_len.
        - intros x Hx; apply callee_local_ids_arg, Hx.
        - apply (verify_def_map_init _ _ _ Hvmap).
        - apply callee_defs_bound_add_other_r; [| exact Hbound0].
          intros x Hx Heq; apply Hva_not_lf; rewrite <- Heq.
          apply lookup_ren_in_dom; [symmetry; exact Hlen_l | apply callee_local_ids_arg, Hx].
        - apply env_agree_outside_add_fresh_r; [exact Hva_af | exact Hagree].
        - destruct (cfg_entry_has_no_phis_inv _ Hcallee_entry) as (bk0 & Hfb0 & Hphis0).
          exists bk0; split; [exact Hfb0 | left; exact Hphis0]. }

      (* 5. [RC_CallPre]: step call-pre prefix, inline [Call], push frame, sync 0-byte [Alloca] *)
      assert (Hcallpre_step :
        forall ic0 u1 u2,
          ic_synced_stk stk ic0 ->
          cfg_inline_sim opt_c g0 false call_pre_rel ic0 u1 u2 ->
          gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller ic0
            (run_exc (ITree.bind u1 call_after_args_k1))
            (run_exc (ITree.bind u2 pre_after_args_k2))).
      { intros ic0 u1 u2 Hic0 Hu.
        eapply (run_exc_bind_step_sync opt_c g0 true stk call_pre_rel out_rel r_caller
                  call_after_args_k1 pre_after_args_k2 Hexc_out);
          [| | exact Hic0 | exact Hu].
        - intros ic' m1 m2 Hic' Hm; eapply RC_CallPre; eassumption.
        - intros ic' vs r2 _ (-> & Hvs_len & ce1 & e2_args & -> & Hagree & Hparams).
          assert (El_gr :
            run_exc (call_after_args_k1 vs) ≅
            ITree.bind (ITree.trigger (subevent _ (GlobalRead callee_gid)))
              (fun fv =>
                 Tau (run_exc (ITree.bind (call ret_dt (anns_cconv call_anns) fv vs)
                                 (call_after_ret_k1 vs))))).
          { assert (Eb : call_after_args_k1 vs ≅
                         ITree.bind (ITree.trigger (subevent _ (GlobalRead callee_gid)))
                           (fun fv => ITree.bind (call ret_dt (anns_cconv call_anns) fv vs)
                                        (call_after_ret_k1 vs))).
            { unfold call_after_args_k1; rewrite Eqit.bind_bind.
              apply eq_itree_clo_bind with (UU := Logic.eq);
                [apply denote_exp'_global_eq | intros fv _ <-; reflexivity]. }
            rewrite (run_exc_proper _ _ Eb).
            rewrite run_exc_bind_trigger_none_eq by reflexivity;
              reflexivity. }
          eapply GIS_GReadL; [exact El_gr | exact Hg_callee |].
          eapply GIS_TauL; [reflexivity |].
          set (ce_call :=
            @subevent (@CallE PaV) (@CFGEtop PaV) _ _
              (Call ret_dt (anns_cconv call_anns) (DVALUE_Base (DVALUE_Pointer p_callee)) vs)).
          assert (El_call :
            run_exc (ITree.bind (call ret_dt (anns_cconv call_anns)
                                   (DVALUE_Base (DVALUE_Pointer p_callee)) vs)
                       (call_after_ret_k1 vs)) ≅
            ITree.bind (ITree.trigger ce_call) (callee_outer_k1 vs)).
          { unfold call, ce_call, callee_outer_k1; norm_subevent.
            rewrite run_exc_bind_trigger_none_eq by reflexivity;
              reflexivity. }
          assert (Hopt_eq : opt_c _ ce_call = Some (denote_function callee_df (anns_cconv call_anns) vs)).
          { unfold opt_c, callee_opt_call, ce_call; norm_subevent.
            rewrite Z.eqb_refl; reflexivity. }
          eapply GIS_InlCallL; [reflexivity | exact El_call | exact Hopt_eq |].
          set (bs_c := combine (df_args callee_df) vs).
          assert (El_dfn :
            ITree.bind (denote_function callee_df (anns_cconv call_anns) vs) (callee_outer_k1 vs) ≅
            ITree.bind (ITree.trigger (subevent _ MemPush))
              (fun _ =>
                 ITree.bind (ITree.trigger (subevent _ (StackPush bs_c)))
                   (fun _ =>
                      ITree.bind (ITree.trigger (subevent _ (Alloca (DTYPE_Struct true []) 1%N None)))
                        (fun varargs =>
                           ITree.bind
                             (store (DTYPE_Struct true []) varargs (DVALUE_Struct true []))
                             (fun _ =>
                                ITree.bind
                                  (match varargs with
                                   | DVALUE_Base (DVALUE_Pointer varg) => Ret varg
                                   | _ => raise "Non-address returned from alloca of varargs"%string
                                   end)
                                  (fun varg =>
                                     ITree.bind (run_exc (tree_callee1 (init callee_cfg) (init callee_cfg) varg))
                                       (callee_epilogue_k1 vs))))))).
          { pose proof Hproto_rattrs as Hpr; pose proof Hproto_pattrs as Hpp.
            assert (Edcpa :
              exists args_attrs,
                dc_param_attrs (df_prototype callee_df) = ([], args_attrs) /\
                forallb is_empty_list args_attrs = true).
            { clear - Hpr Hpp.
              destruct (dc_param_attrs (df_prototype callee_df)) as [ra aa];
                cbn [fst snd] in *; subst ra; exists aa; split; [reflexivity | exact Hpp]. }
            destruct Edcpa as (args_attrs & Edcpa & Hpp').
            unfold denote_function, push_call_frame, mem_push, stack_push, alloca;
              norm_subevent.
            fold callee_gid callee_cfg.
            rewrite Edcpa.
            rewrite (check_cconv_eq_true _ _ _ Hcc_eq).
            cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
            rewrite Eqit.bind_ret_l, Eqit.bind_bind.
            rewrite (apply_args_attrs_all_nil_eq _ _ _ Hpp'), Eqit.bind_ret_l.
            rewrite (combine_lists_varargs_exact (df_args callee_df) vs (eq_sym Hvs_len)).
            cbn [EOU_to_itree map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_itree]; fold bs_c.
            rewrite !Eqit.bind_ret_l, !Eqit.bind_bind.
            cbn [EOU_to_itree map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_itree].
            rewrite !Eqit.bind_ret_l, !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros varargs _ <-].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros varg _ <-].
            rewrite !Eqit.bind_bind.
            unfold callee_epilogue_k1; rewrite Edcpa; cbn [fst].
            apply eq_itree_clo_bind with (UU := Logic.eq);
              [unfold denote_cfg_map, tree_callee1, finish_cfg; reflexivity | intros rv _ <-].
            rewrite Eqit.bind_bind; reflexivity. }
          eapply GIS_MemPushL; [reflexivity | exact El_dfn |].
          eapply GIS_StackPushL; [reflexivity | reflexivity |].
          set (ev_va := @subevent (@MemoryE PaV) (@CFGEtop PaV) _ _
                          (Alloca (DTYPE_Struct true []) 1%N None)).
          assert (Er_al :
            run_exc (pre_after_args_k2 tt) ≅
            Vis ev_va
              (fun v =>
                 Tau (run_exc (ITree.bind (lwrite va_tmp_id v)
                                 (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg)))))))).
          { unfold pre_after_args_k2, alloca, ev_va; norm_subevent.
            rewrite run_exc_bind_trigger_none_eq by reflexivity; rewrite bind_trigger.
            reflexivity. }
          eapply gen_inline_sim__obs_eq;
            [symmetry; apply bind_trigger | symmetry; exact Er_al |].
          apply GIS_Step; cbn [gis_step_body observe]; right; left.
          split; [reflexivity | split; [apply EqE_CFG_refl |]].
          intros a1 a2 Ha Hp.
          apply EqA_CFG_eq in Ha; subst a2.
          destruct Hp as [varg ->].
          exists (ITree.bind
                    (store (DTYPE_Struct true [])
                       (DVALUE_Base (DVALUE_Pointer varg))
                       (DVALUE_Struct true []))
                    (fun _ =>
                       ITree.bind (run_exc (tree_callee1 (init callee_cfg) (init callee_cfg) varg))
                         (callee_epilogue_k1 vs))),
                 (run_exc
                    (ITree.bind (lwrite va_tmp_id (DVALUE_Base (DVALUE_Pointer varg)))
                       (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg)))))).
          split.
          + eapply ITS_Eq; [| apply ITS_Refl].
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite Eqit.bind_ret_l; reflexivity.
          + split; [apply ITS_Tau, ITS_Refl |].
            eapply RC_VaFinish; [reflexivity | exact Hvs_len | exact Hagree | exact Hparams]. }

      (* 6. [RC_PostAt]: step return-value phi/write + [post_cd] + terminator via [Hsync_step] *)
      assert (Hpost_at :
        forall b_ret rtmp_ret bk_ret dv ce1 e2' vs,
          b_ret = blk_id bk_ret ->
          In (bk_ret, rtmp_ret) bk_rtmps ->
          env_agree_outside all_fresh ce1 e2' ->
          match opt_ret_dt with
          | None => True
          | Some _ =>
              (exists rpair, snd (fst (blk_term bk_ret)) = TERM_Ret rpair) /\
              Maps.lookup rtmp_ret e2' = Some dv
          end ->
          gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller (IC_Synced stk ce1 e2')
            (run_exc (call_after_ret_k1 vs (inr dv)))
            (run_exc (tree_at2 (ren_b b_ret) post_bid))).
      { intros b_ret rtmp_ret bk_ret dv ce1 e2' vs Hb_ret Hbk_rtmp Hagree Hret_info.
        pose proof (find_block_new_post_bid caller_df callee_df pre_blks post_blks
                      b_call pre_cd post_cd call_iid ret_dt call_args
                      Hcaller_nd Hcaller_split Hcallee_nd) as Hfb_post.
        cbn zeta in Hfb_post.
        fold callee_cfg used_ids l_origs b_origs n_loc n_blk n_ret
             all_fresh post_bid b_fresh ret_tmps ren_b bk_rtmps caller_df' caller_cfg' in Hfb_post.
        set (post_phis :=
          match call_iid with
          | IId res_id => [(res_id, Phi [] ret_dt (collect_ret_phi_incoming ren_b bk_rtmps), @nil (metadata dtyp))]
          | IVoid _ => []
          end).
        assert (El_post :
          call_after_ret_k1 vs (inr dv) ≅
          ITree.bind
            (ITree.bind (write_call_res dv)
               (fun _ => ITree.bind (denote_code post_cd caller_va)
                           (fun _ => denote_terminator (blk_term b_call))))
            (step_bd_cont (blks caller_cfg) caller_va call_bid)).
        { unfold call_after_ret_k1, post_call_u1.
          rewrite Hcall_rattrs, Hcall_range.
          rewrite (check_call_return_safe_inr_eq _ _ _ _ Hcall_fattrs).
          rewrite Eqit.bind_ret_l, Eqit.bind_ret_l.
          symmetry; apply Eqit.bind_bind. }
        assert (Er_post :
          tree_at2 (ren_b b_ret) post_bid ≅
          ITree.bind
            (ITree.bind (denote_phis (ren_b b_ret) post_phis)
               (fun _ => ITree.bind (denote_code post_cd caller_va)
                           (fun _ => denote_terminator (blk_term b_call))))
            (step_bd_cont (blks caller_cfg') caller_va post_bid)).
        { unfold tree_at2, post_phis; rewrite (ocfg_bind_finish_some_eq _ _ _ _ _ Hfb_post).
          unfold denote_block;
            cbn [blk_phis blk_code blk_term ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
          reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; apply run_exc_proper, El_post
          | symmetry; apply run_exc_proper, Er_post |].
        assert (Hremap_call : post_bid = remap_pred_id call_bid post_bid call_bid).
        { unfold remap_pred_id; rewrite raw_id_eqb_refl; reflexivity. }
        eapply (Hsync_step call_bid post_bid (IC_Synced stk ce1 e2'));
          [exact Hcall_ne_post | exact Hremap_call | exists ce1, e2'; reflexivity |].
        eapply gen_inline_sim_bind with
          (RA := fun ic' _ _ =>
                   exists ea1 ea2,
                     ic' = IC_Synced stk ea1 ea2 /\
                     env_agree_outside all_fresh ea1 ea2).
        - unfold write_call_res, post_phis.
          destruct ((fun c : instr_id =>
                       match c return (c = call_iid -> (exists r, call_iid = IId r) \/ (exists v, call_iid = IVoid v)) with
                       | IId r => fun E => or_introl (ex_intro _ r (eq_sym E))
                       | IVoid v => fun E => or_intror (ex_intro _ v (eq_sym E))
                       end) call_iid Logic.eq_refl)
            as [[res_id Hiid] | [vn Hiid]]; rewrite Hiid.
          + unfold opt_ret_dt in Hret_info; rewrite Hiid in Hret_info; cbv iota in Hret_info.
            destruct Hret_info as ([rpair Hrpair] & Hlk_rtmp).
            assert (Hbks_dom : incl (List.map blk_id (blks callee_cfg)) b_origs).
            { intros z Hz; apply in_map_iff in Hz as [bk [<- Hbk]].
              apply callee_block_ids_blk_id, Hbk. }
            pose proof (assoc_collect_ret_phi_incoming ren_b b_origs (blks callee_cfg) ret_tmps
                          bk_ret rtmp_ret rpair Hcallee_nd Hinj_b Hbks_dom Hbk_rtmp Hrpair)
              as Hassoc_ret.
            rewrite <- Hb_ret in Hassoc_ret.
            assert (Ephi_post :
              denote_phis (ren_b b_ret)
                [(res_id, Phi [] ret_dt (collect_ret_phi_incoming ren_b bk_rtmps), [])] ≅
              ITree.bind (ITree.trigger (subevent _ (LocalRead rtmp_ret)))
                (fun uv => lwrite res_id uv)).
            { cbn [denote_phis map_monad denote_phi ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
              first [rewrite Hassoc_ret
                    | lazymatch goal with
                      | |- context [@Assoc.assoc ?A ?B ?RD ?k ?xs] =>
                          let t := constr:(@Assoc.assoc A B RD k xs) in
                          assert (Hassoc : t = Some (EXP_Ident (ID_Local rtmp_ret))) by exact Hassoc_ret;
                          rewrite Hassoc; clear Hassoc
                      end].
              rewrite !Eqit.bind_bind.
              apply eq_itree_clo_bind with (UU := Logic.eq);
                [apply denote_exp'_local_eq | intros uv _ <-].
              rewrite !Eqit.bind_ret_l; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
              rewrite !Eqit.bind_bind.
              etransitivity; [| apply Eqit.bind_ret_r].
              apply eq_itree_clo_bind with (UU := Logic.eq);
                [reflexivity | intros [] [] _; rewrite !Eqit.bind_ret_l; reflexivity]. }
            eapply gen_inline_sim_obs_eq; [reflexivity | symmetry; exact Ephi_post |].
            assert (Hlw :
              cfg_inline_sim opt_c g0 false
                (fun ic' _ _ =>
                   exists ea1 ea2,
                     ic' = IC_Synced stk ea1 ea2 /\
                     env_agree_outside all_fresh ea1 ea2)
                (IC_Synced stk ce1 e2')
                (lwrite res_id dv) (lwrite res_id dv)).
            { eapply gen_inline_sim_weaken;
                [| apply (cfg_inline_sim_lwrite_lr opt_c g0 false
                            (IC_Synced stk ce1 e2')
                            (IC_Synced stk (Maps.add res_id dv ce1) e2')
                            (IC_Synced stk (Maps.add res_id dv ce1) (Maps.add res_id dv e2'))
                            res_id res_id dv Logic.eq_refl Logic.eq_refl)].
              intros ? [] [] (-> & _ & _).
              eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree]. }
            pstep; eapply GIS_ReadR; [reflexivity | reflexivity | exact Hlk_rtmp |].
            punfold Hlw; exact Hlw.
          + eapply gen_inline_sim_obs_eq;
              [reflexivity
              | cbn [denote_phis map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
                symmetry; rewrite !Eqit.bind_ret_l; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; rewrite !Eqit.bind_ret_l; reflexivity |].
            apply gen_inline_sim_ret; exists ce1, e2'; auto.
        - intros ? _ _ (ea1 & ea2 & -> & Hag_a).
          eapply gen_inline_sim_bind.
          + apply (denote_code_caller_sim opt_c g0 all_fresh stk caller_va post_cd ea1 ea2);
              [| exact Hag_a].
            intros x Hx; apply (Hcaller_use_safe b_call x Hbcall_in).
            unfold full_block_uses; apply in_or_app; right; apply in_or_app; left.
            rewrite Hcd_split, flat_map_app; apply in_or_app; right; cbn [flat_map];
              apply in_or_app; right; exact Hx.
          + intros ? [] [] (_ & _ & eb1 & eb2 & -> & Hag_b).
            set (tiid := fst (fst (blk_term b_call)));
            set (tm := snd (fst (blk_term b_call)));
            set (tmd := snd (blk_term b_call)).
            assert (Ebt_call : blk_term b_call = (tiid, tm, tmd))
              by (unfold tiid, tm, tmd; rewrite <- !surjective_pairing; reflexivity).
            rewrite Ebt_call.
            eapply gen_inline_sim_weaken;
              [| apply (denote_terminator_caller_sim opt_c g0 all_fresh stk eb1 eb2 tiid tm tmd);
                 [| exact Hag_b]].
            * intros ? bd1 bd2 (<- & Hsucc & ec1 & ec2 & -> & Hag_c).
              split; [reflexivity | split; [| exists ec1, ec2; auto]].
              intros succ_bid Hbd.
              apply (Hcaller_lbl_safe b_call succ_bid Hbcall_in).
              unfold block_all_label_ids; rewrite Ebt_call; cbn [fst snd].
              right; apply in_or_app; right; apply Hsucc, Hbd.
            * intros x Hx; apply (Hcaller_use_safe b_call x Hbcall_in).
              unfold full_block_uses; rewrite Ebt_call.
              apply in_or_app; right; apply in_or_app; right; exact Hx. }

      (* 7. [RC_CallerAt]: dispatch [call_bid] to [Hcallpre_step] and other blocks to [Hsync_step] *)
      assert (Hcaller_at :
        forall b_from1 b_from2 bid_cur ea1 ea2,
          env_agree_outside all_fresh ea1 ea2 ->
          bid_cur <> post_bid ->
          ~ In bid_cur b_fresh ->
          ((bid_cur = init caller_cfg /\ b_from1 = init caller_cfg /\ b_from2 = init caller_cfg) \/
           (b_from1 <> post_bid /\ b_from2 = remap_pred_id call_bid post_bid b_from1)) ->
          gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller (IC_Synced stk ea1 ea2)
            (run_exc (tree_at1 b_from1 bid_cur))
            (run_exc (tree_at2 b_from2 bid_cur))).
      { intros b_from1 b_from2 bid_cur ea1 ea2 Hagree Hcur_post Hcur_bf Hpred.
        destruct (RawIDOrd.eq_dec bid_cur call_bid) as [-> | Hne_call].
        - (* Call-site block [b_call] vs [b_pre] *)
          pose proof (inl_find_block_nodup_in _ _ Hcaller_nd Hbcall_in) as Hfb1;
            fold call_bid in Hfb1.
          pose proof (find_block_new_call_bid caller_df callee_df pre_blks post_blks
                        b_call pre_cd post_cd call_iid ret_dt call_args
                        Hcaller_nd Hcaller_split Hcallee_nd) as Hfb2.
          cbn zeta in Hfb2.
          fold callee_cfg used_ids l_origs b_origs n_loc n_blk n_ret
               all_fresh post_bid va_tmp_id l_fresh b_fresh ren_l ren_b
               caller_df' caller_cfg' call_bid in Hfb2.
          assert (Hphis_cond :
            blk_phis b_call = [] \/
            (call_bid <> post_bid /\
             b_from1 <> post_bid /\
             b_from2 = remap_pred_id call_bid post_bid b_from1 /\
             ~ In post_bid (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) (blk_phis b_call)))).
          { destruct Hpred as [(Hinit_eq & _ & _) | (Hbf1 & Hbf2_eq)].
            - left; destruct (cfg_entry_has_no_phis_inv _ Hcaller_entry) as (b0 & Hfb0 & Hb0_phis).
              rewrite <- Hinit_eq, Hfb1 in Hfb0; injection Hfb0 as Hb0_eq;
                rewrite <- Hb0_eq in Hb0_phis; exact Hb0_phis.
            - right; split; [exact Hcall_ne_post | split; [exact Hbf1 | split; [exact Hbf2_eq |]]].
              intros Hin; eapply (proj1 (Hcaller_lbl_safe b_call post_bid Hbcall_in
                ltac:(unfold block_all_label_ids; right; apply in_or_app; left; exact Hin))); reflexivity. }
          assert (El_call_bk :
            tree_at1 b_from1 call_bid ≅
            ITree.bind
              (ITree.bind (denote_phis b_from1 (blk_phis b_call))
                 (fun _ =>
                    ITree.bind (denote_code pre_cd caller_va)
                      (fun _ =>
                         denote_call_args call_args
                           (call_loc ++ ": Call argument violates noundef.")%string)))
              call_after_args_k1).
          { unfold tree_at1; rewrite (ocfg_bind_finish_some_eq _ _ _ _ _ Hfb1).
            unfold denote_block;
              cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
            rewrite Hcd_split.
            unfold call_after_args_k1, call_after_ret_k1, write_call_res, post_call_u1.
            rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite denote_code_app_eq; rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] [] _].
            unfold denote_code at 1; cbn [loop_monad]; fold (denote_code post_cd caller_va).
            destruct ((fun c : instr_id =>
                         match c return (c = call_iid -> (exists r, call_iid = IId r) \/ (exists v, call_iid = IVoid v)) with
                         | IId r => fun E => or_introl (ex_intro _ r (eq_sym E))
                         | IVoid v => fun E => or_intror (ex_intro _ v (eq_sym E))
                         end) call_iid Logic.eq_refl)
              as [[res_id Hiid] | [vn Hiid]]; rewrite Hiid;
              (cbn [denote_instr ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; fold call_loc;
               rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry;
               apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros vs _ <-];
               rewrite denote_operand_bundles_nil_eq, (intrinsic_exp_global_none _ Hintr_none), Eqit.bind_ret_l;
               rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry;
               apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros fv _ <-];
               rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry;
               apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros rv _ <-];
               rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry;
               apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros res _ <-];
               rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry;
               apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros retv _ <-];
               rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry;
               apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _];
               rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry; reflexivity). }
          assert (Er_call_bk :
            tree_at2 b_from2 call_bid ≅
            ITree.bind
              (ITree.bind (denote_phis b_from2 (remap_phis_pred call_bid post_bid (blk_phis b_call)))
                 (fun _ =>
                    ITree.bind (denote_code pre_cd caller_va)
                      (fun _ =>
                         denote_code (build_param_copies ren_l (df_args callee_df) call_args) caller_va)))
              pre_after_args_k2).
          { unfold tree_at2; rewrite (ocfg_bind_finish_some_eq _ _ _ _ _ Hfb2).
            unfold denote_block;
              cbn [blk_phis blk_code blk_term ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
            rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite denote_code_app_eq; rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] [] _].
            rewrite denote_code_app_eq; rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] [] _].
            unfold denote_code at 1.
            cbn [loop_monad denote_instr explicit_alignment find_option denote_terminator
                 step_bd_cont ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
            unfold pre_after_args_k2, tree_at2.
            rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros v _ <-].
            rewrite ?Eqit.bind_bind; symmetry; rewrite ?Eqit.bind_bind; symmetry.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_ret_l; reflexivity. }
          eapply gen_inline_sim__obs_eq;
            [symmetry; apply run_exc_proper, El_call_bk
            | symmetry; apply run_exc_proper, Er_call_bk |].
          eapply (Hcallpre_step (IC_Synced stk ea1 ea2));
            [exists ea1, ea2; reflexivity |].
          eapply gen_inline_sim_bind.
          + apply (denote_phis_caller_sim opt_c g0 all_fresh call_bid post_bid b_from1 b_from2
                     stk ea1 ea2 (blk_phis b_call));
              [| exact Hagree | exact Hphis_cond].
            intros x Hx; apply (Hcaller_use_safe b_call x Hbcall_in).
            unfold full_block_uses; apply in_or_app; left; exact Hx.
          + intros ? [] [] (_ & _ & e1_p & e2_p & -> & Hag_p).
            eapply gen_inline_sim_bind.
            * apply (denote_code_caller_sim opt_c g0 all_fresh stk caller_va pre_cd e1_p e2_p);
                [| exact Hag_p].
              intros x Hx; apply (Hcaller_use_safe b_call x Hbcall_in).
              unfold full_block_uses; apply in_or_app; right; apply in_or_app; left.
              rewrite Hcd_split, flat_map_app; apply in_or_app; left; exact Hx.
            * intros ? [] [] (_ & _ & ce1 & e2_c & -> & Hag_c).
              assert (Harg_use_safe :
                forall (te : texp dtyp) (pattrs : list param_attr) (x : raw_id),
                  In (te, pattrs) call_args -> In x (full_texp_uses te) -> ~ In x all_fresh).
              { intros te pattrs x Hin_arg Hx_use.
                apply (Hcaller_use_safe b_call x Hbcall_in).
                unfold full_block_uses; apply in_or_app; right; apply in_or_app; left.
                rewrite Hcd_split, flat_map_app; apply in_or_app; right; cbn [flat_map].
                apply in_or_app; left; apply in_or_app; left; cbn [full_instr_uses].
                apply in_or_app; right; apply in_or_app; left.
                apply in_flat_map; exists (te, pattrs); split; assumption. }
              eapply gen_inline_sim_weaken;
                [| apply (denote_call_args_param_copies_sim opt_c g0 l_origs all_fresh ren_l
                            (call_loc ++ ": Call argument violates noundef.")%string
                            caller_va stk ce1 Hinj_l Hfresh_l
                            (df_args callee_df) call_args e2_c
                            Harg_len Hcallee_args_nd
                            (fun p Hp => callee_local_ids_arg callee_df p Hp)
                            Hpattrs_nil Harg_use_safe Hag_c)].
              -- intros ? vs [] (_ & Hvs_len & e2_args & -> & Hag_args & _ & Hparams).
                 split; [reflexivity | split; [exact Hvs_len | exists ce1, e2_args; auto]].
        - (* Non-call caller block [bid_cur <> call_bid] *)
          pose proof (find_block_new_caller_other caller_df callee_df pre_blks post_blks
                        b_call pre_cd post_cd call_iid ret_dt call_args bid_cur
                        Hcaller_nd Hcaller_split Hcallee_nd
                        Hne_call Hcur_post Hcur_bf) as Hfb_other.
          cbn zeta in Hfb_other.
          fold caller_cfg callee_cfg used_ids l_origs b_origs n_loc n_blk n_ret
               all_fresh post_bid b_fresh caller_df' caller_cfg' call_bid in Hfb_other.
          destruct (find_block (blks caller_cfg) bid_cur) as [bk |] eqn:Efb1;
            cbn [option_map] in Hfb_other.
          + pose proof (find_block_In' _ _ Efb1) as Hbk_in.
            assert (Hphis_cond :
              blk_phis bk = [] \/
              (call_bid <> post_bid /\
               b_from1 <> post_bid /\
               b_from2 = remap_pred_id call_bid post_bid b_from1 /\
               ~ In post_bid (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) (blk_phis bk)))).
            { destruct Hpred as [(Hinit_eq & _ & _) | (Hbf1 & Hbf2_eq)].
              - left; destruct (cfg_entry_has_no_phis_inv _ Hcaller_entry) as (b0 & Hfb0 & Hb0_phis).
                rewrite <- Hinit_eq, Efb1 in Hfb0; injection Hfb0 as ->; exact Hb0_phis.
              - right; split; [exact Hcall_ne_post | split; [exact Hbf1 | split; [exact Hbf2_eq |]]].
                intros Hin; eapply (proj1 (Hcaller_lbl_safe bk post_bid Hbk_in
                  ltac:(unfold block_all_label_ids; right; apply in_or_app; left; exact Hin))); reflexivity. }
            assert (Hremap_cur : bid_cur = remap_pred_id call_bid post_bid bid_cur).
            { unfold remap_pred_id.
              destruct (raw_id_eqb bid_cur call_bid) eqn:Eeq;
                [apply raw_id_eqb_spec in Eeq; contradiction | reflexivity]. }
            eapply gen_inline_sim__obs_eq;
              [symmetry; apply run_exc_proper; unfold tree_at1; apply (ocfg_bind_finish_some_eq _ _ _ _ _ Efb1)
              | symmetry; apply run_exc_proper; unfold tree_at2; apply (ocfg_bind_finish_some_eq _ _ _ _ _ Hfb_other) |].
            eapply (Hsync_step bid_cur bid_cur (IC_Synced stk ea1 ea2));
              [exact Hcur_post | exact Hremap_cur | exists ea1, ea2; reflexivity |].
            unfold denote_block, remap_block_phis;
              cbn [blk_phis blk_code blk_term ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
            eapply gen_inline_sim_bind.
            * apply (denote_phis_caller_sim opt_c g0 all_fresh call_bid post_bid b_from1 b_from2
                       stk ea1 ea2 (blk_phis bk));
                [| exact Hagree | exact Hphis_cond].
              intros x Hx; apply (Hcaller_use_safe bk x Hbk_in).
              unfold full_block_uses; apply in_or_app; left; exact Hx.
            * intros ? [] [] (_ & _ & e1_p & e2_p & -> & Hag_p).
              eapply gen_inline_sim_bind.
              -- apply (denote_code_caller_sim opt_c g0 all_fresh stk caller_va (blk_code bk) e1_p e2_p);
                   [| exact Hag_p].
                 intros x Hx; apply (Hcaller_use_safe bk x Hbk_in).
                 unfold full_block_uses; apply in_or_app; right; apply in_or_app; left; exact Hx.
              -- intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hag_c).
                 destruct (blk_term bk) as [[tiid tm] tmd] eqn:Ebt_bk.
                 eapply gen_inline_sim_weaken;
                   [| apply (denote_terminator_caller_sim opt_c g0 all_fresh stk e1_c e2_c tiid tm tmd);
                      [| exact Hag_c]].
                 ++ intros ? bd1 bd2 (<- & Hsucc & ec1 & ec2 & -> & Hag_ec).
                    split; [reflexivity | split; [| exists ec1, ec2; auto]].
                    intros succ_bid Hbd.
                    apply (Hcaller_lbl_safe bk succ_bid Hbk_in).
                    unfold block_all_label_ids; rewrite Ebt_bk; cbn [fst snd].
                    right; apply in_or_app; right; apply Hsucc, Hbd.
                 ++ intros x Hx; apply (Hcaller_use_safe bk x Hbk_in).
                    unfold full_block_uses; rewrite Ebt_bk.
                    apply in_or_app; right; apply in_or_app; right; exact Hx.
          + eapply gen_inline_sim__obs_eq;
              [symmetry; apply run_exc_proper; unfold tree_at1; apply (ocfg_bind_finish_none_eq _ _ _ _ Efb1)
              | symmetry; apply run_exc_proper; unfold tree_at2; apply (ocfg_bind_finish_none_eq _ _ _ _ Hfb_other) |].
            apply gen_inline_sim__run_exc_raise; reflexivity. }

      (* Tie the 7-state coinductive knot *)
      assert (Hr_all :
        forall ic0 t1 t2,
          r_caller ic0 t1 t2 ->
          cfg_inline_sim opt_c g0 true out_rel ic0 t1 t2).
      { pcofix CIH.
        intros ic0 t1 t2 Hrc; pstep.
        eapply gen_inline_sim__mon with (r := r_caller);
          [| intros ic1 a1 a2 Hr; right; apply CIH, Hr].
        destruct Hrc.
        - eapply Hcaller_at; eassumption.
        - eapply Hsync_step; eassumption.
        - eapply Hcallpre_step; eassumption.
        - eapply Hva_finish; eassumption.
        - eapply Hcallee_at; eassumption.
        - eapply Hcallee_step; eassumption.
        - eapply Hpost_at; eassumption. }

      pose proof (Hcaller_not_af (init caller_cfg) (defn_all_ids_init caller_df)) as Hinit_naf.
      change (denote_cfg_map (ocfg_map (blks caller_cfg)) caller_cfg caller_va)
        with (tree_at1 (init caller_cfg) (init caller_cfg)).
      change (denote_cfg_map (ocfg_map (blks caller_cfg')) caller_cfg' caller_va)
        with (tree_at2 (init caller_cfg) (init caller_cfg)).
      apply Hr_all, RC_CallerAt.
      - exact Hagree0.
      - intros Heq; apply Hinit_naf; rewrite Heq; exact Hpb_af.
      - intros Hbf; apply Hinit_naf, Hbf_af, Hbf.
      - left; repeat split; reflexivity.
    Qed.

  End CallerInlineLoop.

  Lemma denote_function_caller_sim
    (g0 : global_env)
    (p_callee : @ptr (@PROV PaV) (@PTR PaV))
    (caller_df callee_df : definition dtyp (CFG.cfg dtyp))
    (pre_blks post_blks : ocfg dtyp)
    (b_call : block dtyp)
    (pre_cd post_cd : code dtyp)
    (call_iid : instr_id)
    (call_md : list (metadata dtyp))
    (ret_dt : dtyp)
    (call_args : list (texp dtyp * list param_attr))
    (call_anns : list (annotation dtyp))
    (Hg_callee :
       Maps.lookup (dc_name (df_prototype callee_df)) g0 =
         Some (DVALUE_Base (DVALUE_Pointer p_callee)))
    (Hcaller_ok : is_inlinable_caller caller_df = true)
    (Hcaller_split : blks (df_instrs caller_df) = pre_blks ++ b_call :: post_blks)
    (Hcd_split :
       blk_code b_call =
         pre_cd ++
         (call_iid,
          INSTR_Call (ret_dt, EXP_Ident (ID_Global (dc_name (df_prototype callee_df))))
            call_args call_anns [],
          call_md) :: post_cd)
    (Harg_len : List.length call_args = List.length (df_args callee_df))
    (Hpattrs_nil : forall te pattrs, In (te, pattrs) call_args -> pattrs = [])
    (Hcc_eq :
       cconv_eqb (anns_cconv call_anns)
         (anns_cconv (dc_annotations (df_prototype callee_df))) = true)
    (Hcall_rattrs : ann_ret_attributes call_anns = [])
    (Hcall_fattrs : forallb is_safe_fn_attr (ann_fun_attributes call_anns) = true)
    (Hcall_range : metadata_range call_md = None)
    (Hcallee_ok :
       is_inlinable_callee
         (match call_iid with IId _ => Some ret_dt | IVoid _ => None end)
         callee_df = true) :
    forall stk e1 e2 cc args,
      cfg_inline_sim (callee_opt_call p_callee (denote_function callee_df)) g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
        (IC_Synced stk e1 e2)
        (denote_function caller_df cc args)
        (denote_function
           (inline_site_in_caller caller_df callee_df pre_blks post_blks
              b_call pre_cd post_cd call_iid ret_dt call_args)
           cc args).
  Proof using.
    apply (denote_function_from_run_exc_sim
             (callee_opt_call p_callee (denote_function callee_df)) g0
             caller_df
             (inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_cd post_cd call_iid ret_dt call_args)
             Logic.eq_refl Logic.eq_refl).
    intros stk0 e0 varg.
    exact (denote_run_exc_cfg_caller_inline_sim
             g0 p_callee caller_df callee_df pre_blks post_blks b_call pre_cd post_cd
             call_iid call_md ret_dt call_args call_anns (Some varg) stk0
             Hg_callee Hcaller_ok Hcaller_split Hcd_split Harg_len Hpattrs_nil
             Hcc_eq Hcall_rattrs Hcall_fattrs Hcall_range Hcallee_ok
             e0 e0 (env_agree_outside_refl _ e0)).
  Qed.

  (** ** 10C. Standard Library Function Simulations ([Libraries.v]) *)

  Lemma cfg_inline_sim_iter
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    {I1 I2 R1 R2 : Type}
    (RI : inline_ctx -> I1 -> I2 -> Prop)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (step1 : I1 -> @CFGtop PaV (I1 + R1))
    (step2 : I2 -> @CFGtop PaV (I2 + R2))
    (Hstep : forall ic i1 i2,
               RI ic i1 i2 ->
               cfg_inline_sim opt_call1 g0 false
                 (fun ic' lr1 lr2 =>
                    match lr1, lr2 with
                    | inl j1, inl j2 => RI ic' j1 j2
                    | inr r1, inr r2 => RR ic' r1 r2
                    | _, _ => False
                    end)
                 ic (step1 i1) (step2 i2)) :
    forall ic i1 i2,
      RI ic i1 i2 ->
      cfg_inline_sim opt_call1 g0 bf RR ic (ITree.iter step1 i1) (ITree.iter step2 i2).
  Proof using.
    set (step_rel :=
      fun ic' (lr1 : I1 + R1) (lr2 : I2 + R2) =>
        match lr1, lr2 with
        | inl j1, inl j2 => RI ic' j1 j2
        | inr r1, inr r2 => RR ic' r1 r2
        | _, _ => False
        end).
    set (iter_k1 :=
      fun (lr : I1 + R1) =>
        match lr with
        | inl j => Tau (ITree.iter step1 j)
        | inr v => Ret v
        end).
    set (iter_k2 :=
      fun (lr : I2 + R2) =>
        match lr with
        | inl j => Tau (ITree.iter step2 j)
        | inr v => Ret v
        end).
    set (r_iter :=
      fun ic0 (a1 : @CFGtop PaV R1) (a2 : @CFGtop PaV R2) =>
        exists u1 u2,
          a1 = ITree.bind u1 iter_k1 /\
          a2 = ITree.bind u2 iter_k2 /\
          cfg_inline_sim opt_call1 g0 false step_rel ic0 u1 u2).
    assert (Hlift_cont :
      forall ic0 w1 w2,
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false step_rel) bot3)
          ic0 w1 w2 ->
        gis_cont r_iter ic0 (ITree.bind w1 iter_k1) (ITree.bind w2 iter_k2)).
    { intros ic0 w1 w2 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (ITree.bind m1 iter_k1), (ITree.bind m2 iter_k2).
      split; [apply itree_tau_star_bind, Hs1 |].
      split; [apply itree_tau_star_bind, Hs2 |].
      exists m1, m2; auto. }
    assert (Hone :
      forall ic0 u1 u2,
        cfg_inline_sim opt_call1 g0 false step_rel ic0 u1 u2 ->
        gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
          (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
          opt_call1 g0 bf RR r_iter
          ic0 (ITree.bind u1 iter_k1) (ITree.bind u2 iter_k2)).
    { intros ic0 u1 u2 Hu; punfold Hu.
      induction Hu as [ic0 u1 u2 Hst
                       | ic0 u1 mu1 u2 Hu1 _ IH
                       | ic0 u1 u2 mu2 Hu2 _ IH
                       | ic0 env1 u1 x v ku1 u2 He1 Hu1 Hlk _ IH
                       | ic0 env2 u1 u2 x v ku2 He2 Hu2 Hlk _ IH
                       | ic0 ic' u1 x v ku1 u2 Hw1 Hu1 _ IH
                       | ic0 ic' u1 u2 x v ku2 Hw2 Hu2 _ IH
                       | ic0 u1 k v ku1 u2 Hu1 Hlk _ IH
                       | stk0 ce1 ea1 ea2 u1 varg ku1 u2 Hu1 _ IH
                       | ? ? ? ? ? ? Hfr
                       | ? ? ? ? ? ? ? Hfr
                       | ? ? ? ? ? ? ? Hfr
                       | ? ? ? ? ? ? Hfr
                       | ? ? ? ? ? ? ? ? ? Hfr];
        try discriminate Hfr.
      - unfold gis_step_body in Hst.
        destruct (observe u1) as [lr1 | m1 | X1 ev1 k1] eqn:Hou1.
        + destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct lr1 as [next1 | r1], lr2 as [next2 | r2]; cbn in Hst; try contradiction.
          * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2; cbn [observe iter_k1 iter_k2].
            exists (ITree.bind (step1 next1) iter_k1), (ITree.bind (step2 next2) iter_k2).
            split; [eapply ITS_Eq; [apply unfold_iter | apply ITS_Refl] |].
            split; [eapply ITS_Eq; [apply unfold_iter | apply ITS_Refl] |].
            exists (step1 next1), (step2 next2); split; [reflexivity | split; [reflexivity |]].
            apply (Hstep ic0 next1 next2 Hst).
          * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2; cbn [observe iter_k1 iter_k2].
            exact Hst.
        + destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2.
          apply Hlift_cont, Hst.
        + apply GIS_Step; unfold gis_step_body; rewrite (observe_bind u1 iter_k1), Hou1.
          destruct Hst as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          rewrite (observe_bind u2 iter_k2), Hou2.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; apply Hlift_cont, (HA a1 a2 Ha Hp).
          * right; destruct ic0 as [stk0 env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [Hfr_s _]]; [| discriminate Hfr_s].
            left; destruct (as_local_cfg ev1) as [le1 |], (as_local_cfg ev2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
               apply Hlift_cont, Hr.
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; apply Hlift_cont, Hrd, Hv.
      - eapply GIS_TauL; [rewrite (observe_bind u1 iter_k1), Hu1; reflexivity | exact IH].
      - eapply GIS_TauR; [rewrite (observe_bind u2 iter_k2), Hu2; reflexivity | exact IH].
      - eapply GIS_ReadL; [exact He1 | rewrite Hu1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_ReadR; [exact He2 | rewrite Hu2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_WriteL; [exact Hw1 | rewrite Hu1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_WriteR; [exact Hw2 | rewrite Hu2, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_GReadL; [rewrite Hu1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_ZeroStoreL; [rewrite Hu1, Eqit.bind_bind; reflexivity | exact IH]. }
    assert (Hmain :
      forall ic0 t1 t2,
        r_iter ic0 t1 t2 ->
        cfg_inline_sim opt_call1 g0 bf RR ic0 t1 t2).
    { pcofix CIH.
      intros ic0 t1 t2 (u1 & u2 & -> & -> & Hu); pstep.
      eapply gen_inline_sim__mon with (r := r_iter);
        [apply Hone, Hu | intros ic1 a1 a2 Hr; right; apply CIH, Hr]. }
    intros ic i1 i2 Hi.
    eapply gen_inline_sim_obs_eq;
      [symmetry; apply unfold_iter | symmetry; apply unfold_iter |].
    apply Hmain; exists (step1 i1), (step2 i2).
    split; [reflexivity | split; [reflexivity | apply Hstep, Hi]].
  Qed.

  Lemma i8_str_index_inline_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    stk e1 e2 (strptr : @ptr (@PROV PaV) (@PTR PaV)) (index : Z) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
      (IC_Synced stk e1 e2)
      (i8_str_index strptr index)
      (i8_str_index strptr index).
  Proof using.
    unfold i8_str_index.
    eapply gen_inline_sim_bind;
      [apply cfg_inline_sim_EOU; reflexivity | intros ? iptr _ [-> <-]].
    eapply gen_inline_sim_bind;
      [apply cfg_inline_sim_EOU; reflexivity | intros ? addr _ [-> <-]].
    eapply gen_inline_sim_bind.
    - unfold load, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity.
    - intros ? d_byte _ [-> <-].
      assert (Herr :
        forall msg,
          cfg_inline_sim opt_call1 g0 bf
            (fun ic' (r1 r2 : @Integers.bit_int 8) => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
            (IC_Synced stk e1 e2) (raise msg) (raise msg)).
      { intros msg; apply cfg_inline_sim_raise; reflexivity. }
      destruct d_byte as [[| sz b | | | | | |] | |]; cbv beta iota zeta;
        try apply Herr.
      destruct sz as [p | p |];
        cbv beta iota zeta;
        first
          [ apply Herr
          | destruct p as [p | p |];
            cbv beta iota zeta;
            first
              [ apply Herr
              | destruct p as [p | p |];
                cbv beta iota zeta;
                first
                  [ apply Herr
                  | destruct p as [p | p |];
                    cbv beta iota zeta;
                    try apply Herr ] ] ].
      apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma putchar_denotation_inline_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) :
    forall stk e1 e2 cc args,
      cfg_inline_sim opt_call1 g0 bf
        (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
        (IC_Synced stk e1 e2)
        (putchar_denotation cc args)
        (putchar_denotation cc args).
  Proof using.
    intros stk e1 e2 cc args; unfold putchar_denotation.
    destruct args as [| ch [| ? ?]]; cbv beta iota zeta;
      try_cfg_raise.
    cbn [Functor.fmap Functor_itree ITree.map].
    eapply gen_inline_sim_bind with
      (RA := fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2);
      [| intros ? dv _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    destruct ch as [[| sz x32 | | | | | |] | |]; cbv beta iota zeta;
      try_cfg_raise_ub.
    destruct (Pos.eq_dec 32 sz) as [<- | _];
      [| apply cfg_inline_sim_raiseUB].
    eapply gen_inline_sim_bind.
    - unfold io_stdout, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity.
    - intros ? [] _ [-> _]; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma puts_denotation_inline_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) :
    forall stk e1 e2 cc args,
      cfg_inline_sim opt_call1 g0 bf
        (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
        (IC_Synced stk e1 e2)
        (puts_denotation cc args)
        (puts_denotation cc args).
  Proof using.
    intros stk e1 e2 cc args; unfold puts_denotation.
    destruct args as [| u_strptr [| ? ?]]; cbv beta iota zeta;
      try_cfg_raise.
    cbn [Functor.fmap Functor_itree ITree.map].
    eapply gen_inline_sim_bind with
      (RA := fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2);
      [| intros ? dv _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    destruct u_strptr as [[strptr | | | | | | |] | |]; cbv beta iota zeta;
      try_cfg_raise_ub.
    eapply gen_inline_sim_bind;
      [apply i8_str_index_inline_sim | intros ? ch _ [-> <-]].
    eapply gen_inline_sim_bind.
    - eapply (cfg_inline_sim_iter opt_call1 g0 bf
                (fun ic' s1 s2 => ic' = IC_Synced stk e1 e2 /\ s1 = s2)
                (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2));
        [| split; reflexivity].
      intros ? [[c bytes] offset] _ [-> <-].
      destruct (@Integers.eq 8 c (@Integers.zero 8)).
      + apply gen_inline_sim_ret; cbn; split; reflexivity.
      + eapply gen_inline_sim_bind;
          [apply i8_str_index_inline_sim |].
        intros ? next_char _ [-> <-].
        apply gen_inline_sim_ret; cbn; split; reflexivity.
    - intros ? bytes _ [-> <-].
      eapply gen_inline_sim_bind.
      + unfold io_stdout, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity.
      + intros ? [] _ [-> _]; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma library_functions_inline_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (decls : list (declaration dtyp)) :
    Forall
      (fun '(_, den) =>
         forall stk e1 e2 cc args,
           cfg_inline_sim opt_call1 g0 true
             (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
             (IC_Synced stk e1 e2) (den cc args) (den cc args))
      (library_functions decls).
  Proof using.
    unfold library_functions, _LIBRARIES; cbn [List.filter].
    repeat match goal with |- context [existsb ?f ?l] => destruct (existsb f l) end;
      repeat (apply Forall_cons;
              [intros stk e1 e2 cc args;
               first [apply puts_denotation_inline_sim | apply putchar_denotation_inline_sim] |]);
      try apply Forall_nil.
  Qed.

  (** ** 10D. Whole-Program Refinement ([TopLevel.v]) *)

  Lemma find_defn_by_gid_split (gid : function_id)
    (defs : list (definition dtyp (CFG.cfg dtyp)))
    (callee_df : definition dtyp (CFG.cfg dtyp)) :
    find_defn_by_gid gid defs = Some callee_df ->
    exists defs_pre defs_post,
      defs = defs_pre ++ callee_df :: defs_post /\
      dc_name (df_prototype callee_df) = gid /\
      ~ In gid (List.map (fun d => dc_name (df_prototype d)) defs_pre).
  Proof using.
    induction defs as [| d rest IH]; cbn [find_defn_by_gid]; [discriminate |].
    destruct (raw_id_eqb (dc_name (df_prototype d)) gid) eqn:E.
    - intros H; injection H as <-; apply raw_id_eqb_spec in E.
      exists [], rest; split; [reflexivity | split; [exact E | intros []]].
    - intros H; apply raw_id_eqb_neq in E.
      destruct (IH H) as (dpre & dpost & -> & Hnm & Hnin).
      exists (d :: dpre), dpost; split; [reflexivity | split; [exact Hnm |]].
      cbn [List.map In]; intros [Heq | Hin]; [exact (E Heq) | exact (Hnin Hin)].
  Qed.

  Lemma is_inlinable_callee_no_intrinsic (opt_ret_dt : option dtyp)
    (callee_df : definition dtyp (CFG.cfg dtyp)) :
    is_inlinable_callee opt_ret_dt callee_df = true ->
    lookup_intrinsic_declaration (dc_name (df_prototype callee_df)) = None.
  Proof using.
    unfold is_inlinable_callee.
    repeat match goal with
           | |- (_ && _)%bool = true -> _ =>
               let H := fresh in intros H; apply andb_prop in H as [H _]; revert H
           end.
    destruct (lookup_intrinsic_declaration (dc_name (df_prototype callee_df)));
      [discriminate | intros _; reflexivity].
  Qed.

  Lemma inl_Forall2_app_inv_l {A B : Type} (R : A -> B -> Prop)
    (l1 l2 : list A) (ys : list B) :
    Forall2 R (l1 ++ l2) ys ->
    exists ys1 ys2,
      ys = ys1 ++ ys2 /\
      Forall2 R l1 ys1 /\
      Forall2 R l2 ys2.
  Proof using.
    revert ys; induction l1 as [| x xs IH]; intros ys H; cbn [app] in H.
    - exists [], ys; split; [reflexivity | split; [constructor | exact H]].
    - inversion H as [| ? y ? ys' Hxy Hrest]; subst.
      destruct (IH ys' Hrest) as (ys1 & ys2 & -> & H1 & H2).
      exists (y :: ys1), ys2; split; [reflexivity | split; [constructor; assumption | exact H2]].
  Qed.

  Lemma inl_Forall2_in_r {A B : Type} (R : A -> B -> Prop)
    (xs : list A) (ys : list B) (y : B) :
    Forall2 R xs ys ->
    In y ys ->
    exists x, In x xs /\ R x y.
  Proof using.
    intros H; induction H as [| x0 y0 xs' ys' Hr _ IH]; cbn [In]; [intros [] |].
    intros [-> | Hin].
    - exists x0; split; [left; reflexivity | exact Hr].
    - destruct (IH Hin) as (x & Hx & Hrx).
      exists x; split; [right; exact Hx | exact Hrx].
  Qed.

  Lemma of_list_lookup_split {V : Type}
    (l_pre l_post : list (Z * V)) (k0 : Z) (v0 : V)
    (Hnin : ~ In k0 (List.map fst l_pre)) :
    lookup k0 (IntMaps.IP.of_list (l_pre ++ (k0, v0) :: l_post)) = Some v0.
  Proof using.
    induction l_pre as [| [k v] rest IH]; cbn [List.map fst In app] in *.
    - cbn [IntMaps.IP.of_list fold_right]; unfold IntMaps.IP.uncurry, lookup; cbn [fst snd].
      apply IntMaps.IP.F.add_eq_o; reflexivity.
    - assert (Hne : k <> k0) by (intros ->; apply Hnin; left; reflexivity).
      assert (Hnin' : ~ In k0 (List.map fst rest)) by (intros H; apply Hnin; right; exact H).
      cbn [IntMaps.IP.of_list fold_right]; unfold IntMaps.IP.uncurry, lookup; cbn [fst snd].
      rewrite IntMaps.IP.F.add_neq_o by exact Hne.
      apply (IH Hnin').
  Qed.

  Lemma of_list_fn_ctx_inline_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l1 l2 : list (Z * @function_denotation PaV))
    (Hl : Forall2
            (fun '(k1, f1) '(k2, f2) =>
               k1 = k2 /\
               forall stk e1 e2 cc args,
                 cfg_inline_sim opt_call1 g0 true
                   (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                   (IC_Synced stk e1 e2) (f1 cc args) (f2 cc args))
            l1 l2) :
    forall k,
      option_rel
        (fun f1 f2 =>
           forall stk e1 e2 cc args,
             cfg_inline_sim opt_call1 g0 true
               (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
               (IC_Synced stk e1 e2) (f1 cc args) (f2 cc args))
        (lookup k (IntMaps.IP.of_list l1))
        (lookup k (IntMaps.IP.of_list l2)).
  Proof using.
    induction Hl as [| [k1 f1] [k2 f2] l1' l2' [<- Hf] _ IH]; intros k.
    - cbn; constructor.
    - cbn [IntMaps.IP.of_list fold_right]; unfold IntMaps.IP.uncurry, lookup; cbn [fst snd].
      destruct (Z.eq_dec k1 k) as [<- | Hne].
      + rewrite !IntMaps.IP.F.add_eq_o by reflexivity; constructor; exact Hf.
      + rewrite !IntMaps.IP.F.add_neq_o by exact Hne; apply IH.
  Qed.

  Lemma mcfg_inline_sim_raiseLLVM {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    stk e1 e2 (ex : @exc PaV) :
    mcfg_inline_sim g0 bf RR (IC_Synced stk e1 e2) (raiseLLVM ex) (raiseLLVM ex).
  Proof using.
    unfold raiseLLVM, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn.
    right; left; split; [reflexivity | split; [reflexivity | intros [] [] _ _]].
  Qed.

  Lemma model_hoare_gread_exact (s0 : FusedS) (k : raw_id) :
    model_hoare (fun s => s = s0) (gread k)
      (fun s' v => s' = s0 /\ Maps.lookup k (snd (snd s0)) = Some v).
  Proof using.
    intros s U ->; unfold gread, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity
      | symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity |].
    norm_subevent;
      cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
      norm_subevent.
    destruct (Maps.lookup k (snd (snd s0))) as [v |] eqn:Elk.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite (fused_global_prov_read_some k v s0 Elk), Eqit.bind_ret_l; reflexivity
        | symmetry; rewrite (fused_global_prov_read_some k v s0 Elk), Eqit.bind_ret_l; reflexivity |].
      apply refine_prov_tau2_ret; repeat split; exact Elk.
    - destruct (fused_global_prov_read_none k s0 Elk) as (u & kf & Ef).
      eapply refine_prov_obs_eq;
        [symmetry; rewrite Ef, Eqit.bind_vis; reflexivity
        | symmetry; rewrite Ef, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma interp_address_one_function_inline
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (s0 : FusedS) (U : list N)
    (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (Hg0 : snd (snd s0) = g0)
    (Hproto : df_prototype df1 = df_prototype df2)
    (Hfn : forall stk e1 e2 cc args,
             cfg_inline_sim opt_call1 g0 true
               (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
               (IC_Synced stk e1 e2)
               (denote_function df1 cc args)
               (denote_function df2 cc args)) :
    refine_prov
      (fun _ '(s1', (k1, fn1)) '(s2', (k2, fn2)) =>
         s1' = s0 /\ s2' = s0 /\
         (exists p : @ptr (@PROV PaV) (@PTR PaV),
            k1 = ptr_to_int p /\
            Maps.lookup (dc_name (df_prototype df1)) g0 =
              Some (DVALUE_Base (DVALUE_Pointer p)) /\
            fn1 = denote_function df1) /\
         k1 = k2 /\
         forall stk e1 e2 cc args,
           cfg_inline_sim opt_call1 g0 true
             (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
             (IC_Synced stk e1 e2) (fn1 cc args) (fn2 cc args))
      U
      (interp_mcfg_model (address_one_function df1) s0)
      (interp_mcfg_model (address_one_function df2) s0).
  Proof using.
    unfold address_one_function; rewrite <- Hproto.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq
      | symmetry; apply interp_mcfg_model_bind_eq |].
    eapply refine_prov_bind;
      [apply (model_hoare_gread_exact s0 (dc_name (df_prototype df1)) s0 U Logic.eq_refl) |].
    intros U' [s1 fv1] [s2 fv2] _ (Hs12 & <- & -> & Hlk).
    subst s2; rewrite Hg0 in Hlk.
    assert (Herr :
      forall msg,
        refine_prov
          (fun _ '(s1', (k1, fn1)) '(s2', (k2, fn2)) =>
             s1' = s0 /\ s2' = s0 /\
             (exists p : @ptr (@PROV PaV) (@PTR PaV),
                k1 = ptr_to_int p /\
                Maps.lookup (dc_name (df_prototype df1)) g0 =
                  Some (DVALUE_Base (DVALUE_Pointer p)) /\
                fn1 = denote_function df1) /\
             k1 = k2 /\
             forall stk e1 e2 cc args,
               cfg_inline_sim opt_call1 g0 true
                 (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                 (IC_Synced stk e1 e2) (fn1 cc args) (fn2 cc args))
          U'
          (interp_mcfg_model (raise msg) s0)
          (interp_mcfg_model (raise msg) s0)).
    { intros msg.
      eapply refine_prov_antitone;
        [| apply incl_refl
         | apply (model_hoare_raise (fun _ => True) (fun _ _ => False) msg s0 U' I)].
      intros _ _ [? [? ?]] [? [? ?]] _ (_ & _ & []). }
    destruct fv1 as [[p | | | | | | |] | |]; cbv beta iota zeta;
      try apply Herr.
    cbn [ExtLib.Structures.Monad.ret Monad_itree].
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_ret_eq
      | symmetry; apply interp_mcfg_model_ret_eq |].
    pstep; apply RP_Step; cbn [rp_step_body observe].
    split; [reflexivity | split; [reflexivity |]].
    split; [exists p; split; [reflexivity | split; [exact Hlk | reflexivity]] |].
    split; [reflexivity | exact Hfn].
  Qed.

  Lemma interp_map_address_functions_inline
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (defs1 defs2 : list (definition dtyp (CFG.cfg dtyp)))
    (Hdefs : Forall2
               (fun df1 df2 =>
                  df_prototype df1 = df_prototype df2 /\
                  forall stk e1 e2 cc args,
                    cfg_inline_sim opt_call1 g0 true
                      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                      (IC_Synced stk e1 e2)
                      (denote_function df1 cc args)
                      (denote_function df2 cc args))
               defs1 defs2) :
    forall (s0 : FusedS) (U : list N),
      snd (snd s0) = g0 ->
      refine_prov
        (fun _ '(s1', l1) '(s2', l2) =>
           s1' = s0 /\ s2' = s0 /\
           Forall2
             (fun df1 '(k1, fn1) =>
                exists p : @ptr (@PROV PaV) (@PTR PaV),
                  k1 = ptr_to_int p /\
                  Maps.lookup (dc_name (df_prototype df1)) g0 =
                    Some (DVALUE_Base (DVALUE_Pointer p)) /\
                  fn1 = denote_function df1)
             defs1 l1 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall stk e1 e2 cc args,
                  cfg_inline_sim opt_call1 g0 true
                    (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                    (IC_Synced stk e1 e2) (fn1 cc args) (fn2 cc args))
             l1 l2)
        U
        (interp_mcfg_model (map_monad address_one_function defs1) s0)
        (interp_mcfg_model (map_monad address_one_function defs2) s0).
  Proof using.
    induction Hdefs as [| df1 df2 rest1 rest2 [Hproto Hfn] _ IH];
      intros s0 U Hg0; cbn [map_monad].
    - cbn [ExtLib.Structures.Monad.ret Monad_itree].
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret_eq
        | symmetry; apply interp_mcfg_model_ret_eq |].
      pstep; apply RP_Step; cbn [rp_step_body observe].
      split; [reflexivity | split; [reflexivity | split; constructor]].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_bind_eq
        | symmetry; apply interp_mcfg_model_bind_eq |].
      eapply refine_prov_bind;
        [apply (interp_address_one_function_inline opt_call1 g0 s0 U df1 df2 Hg0 Hproto Hfn) |].
      intros U1 [s1 [k1 fn1]] [s2 [k2 fn2]] _ (-> & -> & Hsrc_hd & Hk_eq & Hfn_hd).
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_bind_eq
        | symmetry; apply interp_mcfg_model_bind_eq |].
      eapply refine_prov_bind; [apply (IH s0 U1 Hg0) |].
      intros U2 [s1' tl1] [s2' tl2] _ (-> & -> & Hsrc_tl & Hrel_tl).
      cbn [ExtLib.Structures.Monad.ret Monad_itree].
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret_eq
        | symmetry; apply interp_mcfg_model_ret_eq |].
      pstep; apply RP_Step; cbn [rp_step_body observe].
      split; [reflexivity | split; [reflexivity | split]].
      + constructor; [exact Hsrc_hd | exact Hsrc_tl].
      + constructor; [split; [exact Hk_eq | exact Hfn_hd] | exact Hrel_tl].
  Qed.

  Lemma map_monad_address_library_inline_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (libs : list (function_id * @function_denotation PaV))
    (Hlibs : Forall
               (fun '(_, den) =>
                  forall stk e1 e2 cc args,
                    cfg_inline_sim opt_call1 g0 true
                      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                      (IC_Synced stk e1 e2) (den cc args) (den cc args))
               libs) :
    forall stk env1 env2,
      mcfg_inline_sim g0 true
        (fun ic' l1 l2 =>
           ic' = IC_Synced stk env1 env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_inline_sim opt_call1 g0 true
                    (fun ic'' r1 r2 => ic'' = IC_Synced s0 a1 a2 /\ r1 = r2)
                    (IC_Synced s0 a1 a2) (fn1 cc args) (fn2 cc args))
             l1 l2)
        (IC_Synced stk env1 env2)
        (map_monad address_one_library_function libs)
        (map_monad address_one_library_function libs).
  Proof using.
    induction Hlibs as [| [fid den] rest Hden _ IH]; intros stk env1 env2; cbn [map_monad].
    - apply gen_inline_sim_ret; split; [reflexivity | constructor].
    - eapply gen_inline_sim_bind with
        (RA := fun ic' p1 p2 =>
                 ic' = IC_Synced stk env1 env2 /\
                 let '(k1, fn1) := p1 in
                 let '(k2, fn2) := p2 in
                 k1 = k2 /\
                 forall s0 a1 a2 cc args,
                   cfg_inline_sim opt_call1 g0 true
                     (fun ic'' r1 r2 => ic'' = IC_Synced s0 a1 a2 /\ r1 = r2)
                     (IC_Synced s0 a1 a2) (fn1 cc args) (fn2 cc args)).
      + unfold address_one_library_function.
        eapply gen_inline_sim_bind.
        * unfold gread, trigger_cast; apply mcfg_inline_sim_trigger_refl; reflexivity.
        * intros ? fv _ [-> <-].
          destruct fv as [[p | | | | | | |] | |]; cbv beta iota zeta;
            try_mcfg_raise.
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exact Hden]].
      + intros ? [k1 fn1] [k2 fn2] [-> Hhd].
        eapply gen_inline_sim_bind; [apply IH |].
        intros ? tl1 tl2 [-> Htl].
        apply gen_inline_sim_ret; split; [reflexivity | constructor; assumption].
  Qed.

  Lemma inline_one_site_refines_in_section (M : CFG.mcfg dtyp) :
    prog_refines M (inline_one_site_mcfg M).
  Proof using.
    intros ret_typ entry args U.
    pose proof (@inline_one_site_build_global_env PaV M) as Hbg.
    unfold inline_one_site_mcfg in *.
    destruct (is_hygienic_module M) eqn:Ehyg;
      [| apply refine_prov_refl; intros; reflexivity].
    destruct (inline_first_in_defs (m_definitions M) (m_definitions M)) as [defs' |] eqn:Efind;
      [| apply refine_prov_refl; intros; reflexivity].
    destruct (inline_first_in_defs_inv _ _ _ Efind)
      as (pre_defs & caller_df & post_defs &
          pre_blks & b_call & post_blks &
          pre_cd & call_iid & ins & call_md & post_cd &
          callee_df & ret_dt & call_args & call_anns &
          Edefs & Edefs' & Hcaller_ok & Hcaller_split & Hcd_split & Hmatch).
    destruct (match_inlinable_call_instr_inv _ _ _ _ _ _ _ _ _ Hmatch)
      as (callee_gid & -> & Hself_ne & Hfind_callee & Hret_nv &
          Harg_len & Hpattrs_nil & Hcc_eq & Hcall_rattrs &
          Hcall_fattrs & Hcall_range & Hcallee_ok).
    destruct (find_defn_by_gid_split _ _ _ Hfind_callee)
      as (cpre & cpost & Ec_split & Hcallee_nm & Hcpre_nin).
    subst callee_gid.
    pose proof (is_inlinable_callee_no_intrinsic _ _ Hcallee_ok) as Hintr_none.
    unfold run_mcfg_model, denote_vellvm.
    rewrite Hbg; cbn [m_definitions m_declarations].
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq
      | symmetry; apply interp_mcfg_model_bind_eq |].
    eapply refine_prov_bind;
      [apply (build_global_environment_inline_post M Ehyg init_fused_state U Logic.eq_refl) |].
    intros U1 [s_bg []] [s_bg2 []] _ (Hs_eq & _ & Hpost).
    subst s_bg2.
    set (all_decls := m_declarations M ++ List.map df_prototype (m_definitions M)) in *.
    destruct s_bg as [m_bg [[sf_bg fstk_bg] g0]].
    destruct Hpost as (Hsf_vars & Hsf_exc & Hsf_loc & -> &
                       seen & Hincl_seen & Hall_seen & Hok_seen & Hdom_seen & Hdisj_seen).
    assert (Hcallee_in_defs : In callee_df (m_definitions M)).
    { rewrite Ec_split; apply in_or_app; right; left; reflexivity. }
    assert (Hproto_in_decls : In (df_prototype callee_df) all_decls).
    { unfold all_decls; apply in_or_app; right; apply in_map, Hcallee_in_defs. }
    destruct (Hall_seen (df_prototype callee_df) Hproto_in_decls Hintr_none)
      as [z_callee Hz_callee_seen].
    destruct (Hok_seen _ _ Hz_callee_seen)
      as (Hz_callee_ge1 & p_callee & Hp_callee_z & Hg_callee).
    set (opt_c := callee_opt_call p_callee (denote_function callee_df)).
    assert (Hdefs_pair :
      Forall2
        (fun df1 df2 =>
           df_prototype df1 = df_prototype df2 /\
           forall stk e1 e2 cc fargs,
             cfg_inline_sim opt_c g0 true
               (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
               (IC_Synced stk e1 e2)
               (denote_function df1 cc fargs)
               (denote_function df2 cc fargs))
        (m_definitions M) defs').
    { rewrite Edefs, Edefs'; clear Edefs Edefs'.
      apply Forall2_app.
      - induction pre_defs as [| d ds IH];
          [constructor | constructor; [split; [reflexivity | apply denote_function_other_sim] | exact IH]].
      - constructor.
        + split; [reflexivity |].
          exact (denote_function_caller_sim
                   g0 p_callee caller_df callee_df pre_blks post_blks b_call pre_cd post_cd
                   call_iid call_md ret_dt call_args call_anns
                   Hg_callee Hcaller_ok Hcaller_split Hcd_split Harg_len Hpattrs_nil
                   Hcc_eq Hcall_rattrs Hcall_fattrs Hcall_range Hcallee_ok).
        + induction post_defs as [| d ds IH];
            [constructor | constructor; [split; [reflexivity | apply denote_function_other_sim] | exact IH]]. }
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq
      | symmetry; apply interp_mcfg_model_bind_eq |].
    eapply refine_prov_bind;
      [apply (interp_map_address_functions_inline opt_c g0
                (m_definitions M) defs' Hdefs_pair (m_bg, ((sf_bg, []), g0)) U1 Logic.eq_refl) |].
    intros U2 [s_d1 defns1] [s_d2 defns2] _ (-> & -> & Hdefns1_src & Hdefns_rel).
    rewrite Ec_split in Hdefns1_src.
    apply inl_Forall2_app_inv_l in Hdefns1_src
      as (defns1_pre & defns1_rest & Hdefns1_eq & Hsrc_pre & Hsrc_rest).
    subst defns1.
    inversion Hsrc_rest as [| ? [k_c fn_c] ? defns1_post Hc_hd Hsrc_post]; subst.
    destruct Hc_hd as (p_c & Hkc_eq & Hlk_pc & Hfnc_eq); subst k_c fn_c.
    assert (Hpc_eq : p_callee = p_c).
    { assert (Hv : Some (DVALUE_Base (DVALUE_Pointer p_callee)) =
                   Some (DVALUE_Base (DVALUE_Pointer p_c)))
        by (etransitivity; [symmetry; exact Hg_callee | exact Hlk_pc]).
      injection Hv; trivial. }
    rewrite <- Hpc_eq in Hdefns_rel |- *.
    assert (Hnin_pre : ~ In (ptr_to_int p_callee) (List.map fst defns1_pre)).
    { intros Hin_k.
      apply in_map_iff in Hin_k as ([k_d fn_d] & Hk_eq & Hin_pair).
      cbn [fst] in Hk_eq; subst k_d.
      destruct (inl_Forall2_in_r _ _ _ _ Hsrc_pre Hin_pair)
        as (d & Hd_in_cpre & p_d & Hp_d_eq & Hlk_d & _).
      assert (Hd_in_defs : In d (m_definitions M)).
      { rewrite Ec_split; apply in_or_app; left; exact Hd_in_cpre. }
      assert (Hd_in_decl_names : In (dc_name (df_prototype d)) (List.map dc_name all_decls)).
      { unfold all_decls; rewrite map_app; apply in_or_app; right.
        rewrite map_map; apply (in_map (fun df => dc_name (df_prototype df))), Hd_in_defs. }
      pose proof (Hdom_seen _ _ Hd_in_decl_names Hlk_d) as Hd_in_seen_fst.
      apply in_map_iff in Hd_in_seen_fst as ([x_d z_d] & Hxz_eq & Hxz_in).
      cbn [fst] in Hxz_eq; subst x_d.
      destruct (Hok_seen _ _ Hxz_in) as (_ & p_d0 & Hp_d0_z & Hlk_d0).
      assert (Hpd_eq : p_d = p_d0).
      { assert (Hv : Some (DVALUE_Base (DVALUE_Pointer p_d)) =
                     Some (DVALUE_Base (DVALUE_Pointer p_d0)))
          by (etransitivity; [symmetry; exact Hlk_d | exact Hlk_d0]).
        injection Hv; trivial. }
      rewrite <- Hpd_eq in Hp_d0_z.
      assert (Hne_nm : dc_name (df_prototype d) <> dc_name (df_prototype callee_df)).
      { intros Heq_nm; apply Hcpre_nin.
        rewrite <- Heq_nm; apply (in_map (fun d0 => dc_name (df_prototype d0))), Hd_in_cpre. }
      apply (Hdisj_seen _ _ _ _ Hxz_in Hz_callee_seen Hne_nm).
      assert (E1 : @ptr_to_int (@PROV PaV) (@PTR PaV) (@P2I PaV) p_d = z_d) by exact Hp_d0_z.
      assert (E3 : @ptr_to_int (@PROV PaV) (@PTR PaV) (@P2I PaV) p_callee =
                   @ptr_to_int (@PROV PaV) (@PTR PaV) (@P2I PaV) p_d \/
                   @ptr_to_int (@PROV PaV) (@PTR PaV) (@P2I PaV) p_d =
                   @ptr_to_int (@PROV PaV) (@PTR PaV) (@P2I PaV) p_callee)
        by (first [left; exact Hp_d_eq | right; exact Hp_d_eq]).
      destruct E3 as [E3 | E3]; congruence. }
    unfold interp_mcfg_model.
    eapply refine_prov_antitone with (U := U2);
      [| apply incl_refl
       | eapply (mcfg_inline_sim_to_model g0 (fun _ r1 r2 => r1 = r2)
                   U2 (IC_Synced [] Maps.empty Maps.empty))];
      [intros _ _ [s1 r1] [s2 r2] _ (_ & _ & <-); reflexivity | ..].
    { split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
      split; [repeat (first [exact Hsf_vars | reflexivity | split]) | constructor]. }
    apply mcfg_inline_sim_interp_intrinsics.
    eapply gen_inline_sim_bind;
      [apply (map_monad_address_library_inline_sim opt_c g0
                (library_functions (m_declarations M))
                (library_functions_inline_sim opt_c g0 (m_declarations M))) |].
    intros ? libs1 libs2 [-> Hlibs].
    eapply gen_inline_sim_bind.
    { unfold gread, trigger_cast; apply mcfg_inline_sim_trigger_refl; reflexivity. }
    intros ? addr _ [-> <-].
    assert (Hctx :
      forall k,
        option_rel
          (fun f1 f2 =>
             forall stk e1 e2 cc fargs,
               cfg_inline_sim opt_c g0 true
                 (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                 (IC_Synced stk e1 e2) (f1 cc fargs) (f2 cc fargs))
          (lookup k (IntMaps.IP.of_list ((defns1_pre ++ (ptr_to_int p_callee, denote_function callee_df) :: defns1_post) ++ libs1)))
          (lookup k (IntMaps.IP.of_list (defns2 ++ libs2)))).
    { apply of_list_fn_ctx_inline_sim, Forall2_app; assumption. }
    eapply gen_inline_sim_bind.
    - rewrite !denote_mcfg_eq_interp_mrec.
      eapply (cfg_to_mcfg_inline_sim_mrec p_callee (denote_function callee_df)
                (IntMaps.IP.of_list ((defns1_pre ++ (ptr_to_int p_callee, denote_function callee_df) :: defns1_post) ++ libs1))
                (IntMaps.IP.of_list (defns2 ++ libs2))
                g0).
      + exact Hz_callee_ge1.
      + rewrite <- app_assoc; cbn [app]; apply of_list_lookup_split, Hnin_pre.
      + exact Hctx.
      + unfold inl_mrec_ctx.
        eapply gen_inline_sim_bind;
          [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
        assert (Hext :
          cfg_inline_sim opt_c g0 true
            (fun ic' r1 r2 => ic' = IC_Synced [] Maps.empty Maps.empty /\ r1 = r2)
            (IC_Synced [] Maps.empty Maps.empty)
            (Functor.fmap (@inr (@exc PaV) _) (external_call ret_typ addr args))
            (Functor.fmap (@inr (@exc PaV) _) (external_call ret_typ addr args))).
        { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
          eapply gen_inline_sim_bind.
          - apply cfg_inline_sim_trigger_refl; reflexivity.
          - intros ? rv1 rv2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
        unfold lookup_defn.
        destruct addr as [[p | | | | | | |] | |]; try exact Hext.
        pose proof (Hctx (ptr_to_int p)) as Hlk.
        destruct Hlk as [| f1 f2 Hf12].
        * exact Hext.
        * apply Hf12.
    - intros ? rv _ [-> <-].
      destruct rv as [ex | v].
      + apply mcfg_inline_sim_raiseLLVM.
      + apply gen_inline_sim_ret; reflexivity.
  Qed.

End InliningSemantics.

Theorem inline_one_site_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (inline_one_site_mcfg M).
Proof.
  intros IP IPT M.
  exact (@inline_one_site_refines_in_section IP IPT M).
Qed.

Lemma inline_iter_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (fuel : nat) (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (inline_iter fuel M).
Proof.
  intros IP IPT fuel; induction fuel as [| fuel' IH]; intros M; cbn [inline_iter].
  - apply prog_refines_refl.
  - eapply prog_refines_trans; [apply inline_one_site_refines | apply IH].
Qed.

Theorem inline_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (inline_mcfg M).
Proof.
  intros IP IPT M; unfold inline_mcfg.
  apply inline_iter_refines.
Qed.
