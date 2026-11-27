(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Direct Call Summaries & Caller/Callee Composition ([CertValidator.McCall])

    Top-level entry point for Milestone M3c of Phase 8.3a for direct
    non-recursive acyclic calls on [RV64IM+RVC] and [AArch64]:
    re-exports [CertValidator.McCallSpec], [CertValidator.McCallMcWitness], and
    [CertValidator.McCallIrExec], and proves Sections 5.5-5.6 end-to-end
    call-validator soundness ([validate_mc_call_rv64_sound],
    [validate_mc_call_a64_sound]) and caller/callee composition theorems
    ([compose_rv64_caller_callee_sound], [compose_a64_caller_callee_sound]). *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.Ascii
  Strings.String
  Numbers.DecimalString
  Numbers.DecimalZ
  List
  Bool
  Lia.
Import ListNotations.

From ITree Require Import
  ITree
  ITreeFacts
  Events.Exception.

From Vellvm Require Import
  Utils
  Utils.ITreeUtil
  Utils.Assoc
  Utils.ListUtil
  Numeric.Zbits
  Numeric.Integers
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.DynamicTypes
  Syntax.TypToDtyp
  Syntax.RawIdMaps
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Attributes
  Semantics.Denotation
  Semantics.LLVMEvents
  Semantics.IntrinsicsDefinitions.

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  CertValidator
  Elf64Spec
  McFrameMem
  McIsaCommon
  Rv64Decode
  Rv64ExecSym
  Rv64DagProof
  Rv64LoopSeg
  A64Decode
  A64ExecSym
  A64DagProof
  A64LoopSeg
  McFormat
  Diag
  McOblDischarger.

From CertValidator Require Export
  McCallSpec
  McCallMcWitness
  McCallIrExec.

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
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments Nat.leb _ _ : simpl nomatch.
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
#[local] Arguments Integers.add : simpl never.
#[local] Arguments Integers.sub : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.


(** *** 5.5 Ghost Call-Variable Filling & End-to-End Call Validator Soundness *)

Lemma reify_ir_code_calls_vars_bang :
  forall cur_bid callees c cid lmap k_end t,
    (forall cid' lmap' t', k_end cid' lmap' = inr t' ->
       forall nm w, In (nm, w) (collect_ir_call_vars t') -> mc_starts_with_bang nm = true) ->
    reify_ir_code_calls cur_bid callees c cid lmap k_end = inr t ->
    forall nm w, In (nm, w) (collect_ir_call_vars t) -> mc_starts_with_bang nm = true.
Proof.
  intros cur_bid callees c; induction c as [| [[iid ins] md] rest IH];
    intros cid lmap k_end t Hk Hrc nm w Hin; cbn [reify_ir_code_calls] in Hrc.
  - exact (Hk cid lmap t Hrc nm w Hin).
  - destruct iid as [id | vid];
      [| destruct ins; try discriminate Hrc; exact (IH cid lmap k_end t Hk Hrc nm w Hin)].
    destruct ins; try discriminate Hrc.
    + destruct (reify_pure_exp lmap None op) as [[? ?] |]; [| discriminate Hrc].
      destruct (ub_free_expr _); cbn [negb] in Hrc; [| discriminate Hrc].
      destruct (expr_has_freeze _); [discriminate Hrc |].
      exact (IH cid _ k_end t Hk Hrc nm w Hin).
    + destruct fn as [dt_ret fn_e].
      destruct (match_pure_int_intrinsic_call (INSTR_Call (dt_ret, fn_e) args anns obs)) as [[op wi a0 a1 | wi a0 fl] |] eqn:Epic.
      * destruct (match metadata_range md with None => true | Some _ => false end) eqn:Emr; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wi))) a0) as [[? ?] |] eqn:Ea0; [| discriminate Hrc].
        destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wi))) a1) as [[? ?] |] eqn:Ea1; [| discriminate Hrc].
        destruct (ub_free_expr _ && ub_free_expr _) eqn:Euf; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (expr_has_freeze _ || expr_has_freeze _); [discriminate Hrc |].
        exact (IH cid _ k_end t Hk Hrc nm w Hin).
      * destruct (match metadata_range md with None => true | Some _ => false end) eqn:Emr; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wi))) a0) as [[? ?] |] eqn:Ea0; [| discriminate Hrc].
        destruct (ub_free_expr _) eqn:Euf; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (expr_has_freeze _); [discriminate Hrc |].
        exact (IH cid _ k_end t Hk Hrc nm w Hin).
      * destruct dt_ret as [bdt | |]; [destruct bdt as [rw | | | | | | | | | |] | |];
          destruct fn_e;
          try match goal with iv : ident |- _ => destruct iv as [[cname | | ] | ?] end;
          destruct obs; try discriminate Hrc.
        destruct (match @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname))) with None => true | Some _ => false end); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (cconv_eqb (anns_cconv anns) CC_Ccc); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (match metadata_range md with None => true | Some _ => false end); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (fattrs_call_ok (ann_fun_attributes anns)); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (pattrs_no_value_poison (ann_ret_attributes anns)); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (is_supported_bit_width rw); cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (find_callee_spec callees cname) as [sp |] eqn:Efc; [| discriminate Hrc].
        destruct (Pos.eqb rw (mcs_ret_width sp)) eqn:Erw; [| discriminate Hrc].
        destruct (reify_ir_call_args cname 0%nat lmap (mcs_args sp) args) as [| aes] eqn:Eaes; [discriminate Hrc |].
        destruct (reify_ir_code_calls cur_bid callees rest (S cid) _ k_end) as [| cont] eqn:Ect; [discriminate Hrc |].
        inversion Hrc; subst t; clear Hrc;
        unfold collect_ir_call_vars in Hin; cbn [collect_ir_call_vars_acc] in Hin;
        rewrite collect_ir_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [Hr | [Heq | []]];
        [exact (IH _ _ _ _ Hk Ect nm w Hr) | inversion Heq; subst; apply mc_call_ret_var_bang].
Qed.

Lemma reify_ir_call_at_vars_bang :
  forall fuel callees bmap ret_w visited is_entry bid_from cur_bid cid lmap t,
    reify_ir_call_at fuel callees bmap ret_w visited is_entry bid_from cur_bid cid lmap = inr t ->
    forall nm w, In (nm, w) (collect_ir_call_vars t) -> mc_starts_with_bang nm = true.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros callees bmap ret_w visited is_entry bid_from cur_bid cid lmap t Hrec;
    cbn [reify_ir_call_at] in Hrec;
    destruct (raw_id_in_list cur_bid visited); try discriminate Hrec.
  destruct (RM.find cur_bid bmap) as [b |]; [| discriminate Hrec].
  match type of Hrec with
  | match ?x with inl _ => _ | inr _ => _ end = _ => destruct x as [| lmap1]; [discriminate Hrec |]
  end.
  eapply reify_ir_code_calls_vars_bang; [| exact Hrec].
  intros cid' lmap' t' Ht' nm w Hin.
  destruct (fst (blk_term b)) as [_ term]; destruct term; try discriminate Ht';
    try (inversion Ht'; subst t'; contradiction Hin).
  - match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] op] end; try discriminate Ht'.
    destruct (Pos.eqb rw ret_w); [| discriminate Ht'].
    destruct (reify_pure_exp lmap' _ op) as [[? ret_e] |]; [| discriminate Ht'].
    destruct (ub_free_expr ret_e); cbn [negb] in Ht'; [| discriminate Ht'].
    destruct (expr_has_freeze ret_e); inversion Ht'; subst t'; contradiction Hin.
  - match goal with x : texp dtyp |- _ => destruct x as [[[w0 | | | | | | | | | |] | |] e_cond] end; try discriminate Ht'.
    destruct w0; try discriminate Ht'.
    destruct (reify_pure_exp lmap' _ e_cond) as [[? cond_e] |]; [| discriminate Ht'].
    destruct (ub_free_expr cond_e); cbn [negb] in Ht'; [| discriminate Ht'].
    destruct (expr_has_freeze cond_e); [discriminate Ht' |].
    destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' lmap') as [| dt1] eqn:Edt; [discriminate Ht' |].
    destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' lmap') as [| df1] eqn:Edf; [discriminate Ht' |].
    inversion Ht'; subst t';
      unfold collect_ir_call_vars in Hin; cbn [collect_ir_call_vars_acc] in Hin;
      rewrite collect_ir_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [Hin | Hin];
      [exact (IH _ _ _ _ _ _ _ _ _ _ Edf nm w Hin) | exact (IH _ _ _ _ _ _ _ _ _ _ Edt nm w Hin)].
  - exact (IH _ _ _ _ _ _ _ _ _ _ Ht' nm w Hin).
Qed.

Lemma summarize_rv64_call_at_vars_bang :
  forall fuel im callees visited pc cid sp_off vrf astk ret_w t,
    summarize_rv64_call_at fuel im callees visited pc cid sp_off vrf astk ret_w = inr t ->
    forall nm w, In (nm, w) (collect_mc_call_vars t) -> mc_starts_with_bang nm = true.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros im callees visited pc cid sp_off vrf astk ret_w t Hsum nm w Hin;
    cbn [summarize_rv64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |]; [| discriminate Hsum].
  destruct (drci_inst dec) as [i | cname].
  - destruct (rv_sym_step_one (mk_decoded_rv (drci_off dec) (drci_len dec) i) pc sp_off vrf astk ret_w)
      as [[npc sp' vrf' astk' | cond tpc npc | ret_e] |] eqn:Est; try discriminate Hsum.
    + exact (IH _ _ _ _ _ _ _ _ _ _ Hsum nm w Hin).
    + destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk ret_w) as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk ret_w) as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t;
        unfold collect_mc_call_vars in Hin; cbn [collect_mc_call_vars_acc] in Hin;
        rewrite collect_mc_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [H | H];
        [exact (IH _ _ _ _ _ _ _ _ _ _ Hdf nm w H) | exact (IH _ _ _ _ _ _ _ _ _ _ Hdt nm w H)].
    + inversion Hsum; subst t; contradiction Hin.
  - destruct (mc_sp_aligned16 sp_off); cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |]; [| discriminate Hsum].
    destruct (rv_sym_read_call_args_from pc cname 10%N (List.length (mcs_args c)) vrf); [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) (pc + drci_len dec)%N (S cid) sp_off (rv_post_call_vrf cid c vrf) astk ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t;
      unfold collect_mc_call_vars in Hin; cbn [collect_mc_call_vars_acc] in Hin;
      rewrite collect_mc_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [Hr | Hh];
      [exact (IH _ _ _ _ _ _ _ _ _ _ Ect nm w Hr) |].
    destruct opt_hi as [hn |] eqn:Eoh.
    + destruct Hh as [Heq | [Heq | []]]; inversion Heq; subst.
      * apply mc_call_ret_var_bang.
      * unfold mc_post_call_ret_expr in Epc; destruct (Pos.eqb _ 64%positive); [discriminate Epc |].
        destruct (mcs_ret_ext c); inversion Epc; apply mc_call_hi_var_bang.
    + destruct Hh as [Heq | []]; inversion Heq; subst; apply mc_call_ret_var_bang.
Qed.

Lemma summarize_a64_call_at_vars_bang :
  forall fuel im callees visited pc cid sp_off vrf astk sfl fl_def ret_w t,
    summarize_a64_call_at fuel im callees visited pc cid sp_off vrf astk sfl fl_def ret_w = inr t ->
    forall nm w, In (nm, w) (collect_mc_call_vars t) -> mc_starts_with_bang nm = true.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros im callees visited pc cid sp_off vrf astk sfl fl_def ret_w t Hsum nm w Hin;
    cbn [summarize_a64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |]; [| discriminate Hsum].
  destruct (daci_inst dec) as [i | cname].
  - destruct (a64_sym_step_one (mk_decoded_a64_inst (daci_off dec) i) pc sp_off vrf astk sfl fl_def ret_w)
      as [[npc sp' vrf' astk' sfl' fl_def' | cond tpc npc fl_def' | ret_e] |] eqn:Est; try discriminate Hsum.
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hsum nm w Hin).
    + destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk sfl fl_def' ret_w) as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk sfl fl_def' ret_w) as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t;
        unfold collect_mc_call_vars in Hin; cbn [collect_mc_call_vars_acc] in Hin;
        rewrite collect_mc_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [H | H];
        [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hdf nm w H) | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Hdt nm w H)].
    + inversion Hsum; subst t; contradiction Hin.
  - destruct (mc_sp_aligned16 sp_off); cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |]; [| discriminate Hsum].
    destruct (a64_sym_read_call_args_from pc cname 0%N (List.length (mcs_args c)) vrf); [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) (pc + 4%N)%N (S cid) sp_off (a64_post_call_vrf cid c vrf) astk sfl false ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t;
      unfold collect_mc_call_vars in Hin; cbn [collect_mc_call_vars_acc] in Hin;
      rewrite collect_mc_call_vars_acc_shift in Hin; apply in_app_iff in Hin as [Hr | Hh];
      [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ Ect nm w Hr) |].
    destruct opt_hi as [hn |] eqn:Eoh.
    + destruct Hh as [Heq | [Heq | []]]; inversion Heq; subst.
      * apply mc_call_ret_var_bang.
      * unfold mc_post_call_ret_expr in Epc; destruct (Pos.eqb _ 64%positive); [discriminate Epc |].
        destruct (mcs_ret_ext c); inversion Epc; apply mc_call_hi_var_bang.
    + destruct Hh as [Heq | []]; inversion Heq; subst; apply mc_call_ret_var_bang.
Qed.

Section CallGhostFilling.
  Context {Pa : Params}.

  Definition call_extra_binds
    (new_binds : list (string * @dvalue Pa)) (call_vars : list (string * positive))
    : list (string * @dvalue Pa) :=
    List.map
      (fun '(nm, w) => (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
      (List.filter (fun '(nm, _) => negb (existsb (String.eqb nm) (List.map fst new_binds))) call_vars).

  Lemma call_extra_binds_props :
    forall allowed0 mc_vars call_vars all_vars (penv0 : param_env Pa) new_binds,
      (forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false) ->
      (forall nm w, In (nm, w) call_vars -> mc_starts_with_bang nm = true) ->
      NoDup (List.map fst call_vars) ->
      NoDup (List.map fst all_vars) ->
      (forall nm w, In (nm, w) call_vars -> In (nm, w) all_vars) ->
      (forall nm w, In (nm, w) allowed0 -> In (nm, w) all_vars) ->
      (forall nm w, In (nm, w) all_vars -> In (nm, w) allowed0 \/ In (nm, w) call_vars) ->
      (forall nm w, In (nm, w) mc_vars -> In (nm, w) all_vars) ->
      NoDup (List.map fst new_binds) ->
      (forall nm, In nm (List.map fst new_binds) -> mc_starts_with_bang nm = true) ->
      (forall nm dv, In (nm, dv) new_binds ->
         exists w, In (nm, w) mc_vars /\ exists v : @Integers.bit_int w, dv = DVALUE_Base (@DVALUE_I Pa w v)) ->
      wf_param_env_for allowed0 penv0 ->
      (forall penv' : param_env Pa,
         (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
         ub_ctx_holds penv' dummy_freeze_oracle []) ->
      let extra_binds := call_extra_binds new_binds call_vars in
      let penv_full := overlay_penv (new_binds ++ extra_binds) penv0 in
      binds_disjoint_from allowed0 extra_binds /\
      (forall nm, In nm (List.map fst new_binds) -> ~ In nm (List.map fst extra_binds)) /\
      (forall nm, mc_starts_with_bang nm = false -> penv_full nm = penv0 nm) /\
      wf_param_env_for all_vars penv_full /\
      ub_ctx_holds penv_full dummy_freeze_oracle (List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars).
  Proof.
    intros allowed0 mc_vars call_vars all_vars penv0 new_binds
           Hnb_al Hnb_cv Hnd_cv Hnd_av Hcv_av Hal_av Hav_sp Hmv_av Hnd_nb Hnb_nb Hnb_vals Hpenv0 _ extra_binds penv_full.
    assert (Hextra_bang : forall nm, In nm (List.map fst extra_binds) -> mc_starts_with_bang nm = true).
    { intros nm Hin; unfold extra_binds, call_extra_binds in Hin.
      rewrite map_map in Hin; apply in_map_iff in Hin as [[nm0 w0] [Heq Hflt]]; cbn in Heq; subst nm0.
      apply filter_In in Hflt as [Hcv _]; exact (Hnb_cv nm w0 Hcv). }
    assert (Hdisj_eb : binds_disjoint_from allowed0 extra_binds).
    { intros nm w Hal Hin; pose proof (Hnb_al nm w Hal) as Hb0; pose proof (Hextra_bang nm Hin) as Hb1; congruence. }
    assert (Hdisj_nb_eb : forall nm, In nm (List.map fst new_binds) -> ~ In nm (List.map fst extra_binds)).
    { intros nm HinN HinE; unfold extra_binds, call_extra_binds in HinE; rewrite map_map in HinE.
      apply in_map_iff in HinE as [[nm0 w0] [Heq Hflt]]; cbn in Heq; subst nm0.
      apply filter_In in Hflt as [_ Hneg]; apply negb_true_iff in Hneg.
      assert (Hex : existsb (String.eqb nm) (List.map fst new_binds) = true)
        by (apply existsb_exists; exists nm; split; [exact HinN | apply String.eqb_refl]).
      congruence. }
    assert (Hpres_nonbang : forall nm, mc_starts_with_bang nm = false -> penv_full nm = penv0 nm).
    { intros nm Hnb; unfold penv_full; apply overlay_penv_not_in; intro Hin.
      rewrite map_app in Hin; apply in_app_iff in Hin as [Hin | Hin];
        [pose proof (Hnb_nb nm Hin) | pose proof (Hextra_bang nm Hin)]; congruence. }
    assert (Hnd_comb : NoDup (List.map fst (new_binds ++ extra_binds))).
    { rewrite map_app; apply NoDup_app; [exact Hnd_nb | |].
      - unfold extra_binds, call_extra_binds.
        assert (Hmfst : List.map fst (List.map (fun '(nm, w) => (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
                                        (List.filter (fun '(nm, _) => negb (existsb (String.eqb nm) (List.map fst new_binds))) call_vars)) =
                        List.filter (fun nm => negb (existsb (String.eqb nm) (List.map fst new_binds))) (List.map fst call_vars)).
        { clear; induction call_vars as [| [a w] r IH]; cbn; [reflexivity |].
          destruct (negb (existsb (String.eqb a) (List.map fst new_binds))); cbn; [f_equal |]; exact IH. }
        rewrite Hmfst; apply NoDup_filter; exact Hnd_cv.
      - exact Hdisj_nb_eb. }
    assert (Hcv_val : forall nm w, In (nm, w) call_vars ->
      exists v : @Integers.bit_int w, penv_full nm = Some (DVALUE_Base (@DVALUE_I Pa w v))).
    { intros nm w Hcv.
      destruct (in_dec String.string_dec nm (List.map fst new_binds)) as [HinN | HnotN].
      - apply in_map_iff in HinN as [[nm0 dv0] [Heq HinP]]; cbn in Heq; subst nm0.
        destruct (Hnb_vals nm dv0 HinP) as (w' & Hmv' & v' & ->).
        pose proof (Hcv_av nm w Hcv) as Hav1.
        pose proof (Hmv_av nm w' Hmv') as Hav2.
        assert (Hw_eq : w' = w).
        { clear -Hnd_av Hav1 Hav2; induction all_vars as [| [x wx] rest IH]; cbn in *; [contradiction |].
          inversion Hnd_av as [| ? ? Hni Hndr]; subst.
          destruct Hav1 as [H1 | H1], Hav2 as [H2 | H2].
          - inversion H1; inversion H2; congruence.
          - inversion H1; subst; exfalso; apply Hni; apply in_map_iff; exists (nm, w'); split; [reflexivity | exact H2].
          - inversion H2; subst; exfalso; apply Hni; apply in_map_iff; exists (nm, w); split; [reflexivity | exact H1].
          - exact (IH Hndr H1 H2). }
        subst w'; exists v'; unfold penv_full; apply overlay_penv_lookup_in; [exact Hnd_comb |].
        apply in_or_app; left; exact HinP.
      - assert (HinE : In (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))) extra_binds).
        { unfold extra_binds, call_extra_binds; apply in_map_iff; exists (nm, w); split; [reflexivity |].
          apply filter_In; split; [exact Hcv | apply negb_true_iff].
          destruct (existsb (String.eqb nm) (List.map fst new_binds)) eqn:Eex; [| reflexivity].
          exfalso; apply existsb_exists in Eex as [y [Hy Heqy]]; apply String.eqb_eq in Heqy; subst y; contradiction. }
        exists (@Integers.zero w); unfold penv_full; apply overlay_penv_lookup_in; [exact Hnd_comb |].
        apply in_or_app; right; exact HinE. }
    repeat split; try assumption.
    - intros nm w Hav; destruct (Hav_sp nm w Hav) as [Hal | Hcv].
      + rewrite (Hpres_nonbang nm (Hnb_al nm w Hal)); exact (Hpenv0 nm w Hal).
      + destruct (Hcv_val nm w Hcv) as [v Hv]; exists (DVALUE_Base (@DVALUE_I Pa w v)); split; [exact Hv | right; exists v; reflexivity].
    - apply Forall_forall; intros u Hu; apply in_map_iff in Hu as [[nm w] [<- Hcv]].
      destruct (Hcv_val nm w Hcv) as [v Hv]; cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hv in Hdv; inversion Hdv; discriminate.
  Qed.

End CallGhostFilling.

Lemma mc_no_dup_strings_spec : forall xs,
  mc_no_dup_strings xs = true -> NoDup xs.
Proof.
  induction xs as [| x rest IH]; intros H; [constructor |].
  cbn in H; apply andb_true_iff in H as [Hneg Hnd]; apply negb_true_iff in Hneg.
  constructor; [| exact (IH Hnd)].
  intro Hin; unfold mc_str_in_list in Hneg;
    assert (Hex : existsb (String.eqb x) rest = true) by (apply existsb_exists; exists x; split; [exact Hin | apply String.eqb_refl]);
    congruence.
Qed.

Theorem validate_mc_call_rv64_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
         (insts : list decoded_rv_call_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
         (callees : list mc_callee_spec) (opt_pf : option (list lrat_step))
         arg_dtys vs (penv0 : param_env Pa) rf0 mstk0,
    validate_mc_call_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees opt_pf = inr tt ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    cfg_param_dtyp_compatible ir_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx sp,
       nth_error arg_specs idx = Some sp ->
       nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I (ras_width sp))) /\
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some (ras_name sp)) ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (param_idx_uses_cfg ir_cfg) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed0) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv0 nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed0) ->
    mc_valid_sp0_depth 2%nat (rv_read_reg 2%N rf0) ->
    rv_rf_matches_args penv0 arg_specs rf0 ->
    rv_call_sound_spec ir_cfg insts ret_w callees vs rf0 mstk0.
Proof.
  intros ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees opt_pf
         arg_dtys vs penv0 rf0 mstk0
         Hval Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp Hty Hargs_compat Hpu Hpenv_eq Hpenv0 Hctx0 Hargs_al Hsp0 Hm.
  unfold validate_mc_call_rv64, build_mc_call_bundle_rv64 in Hval.
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hval; [| discriminate Hval].
  destruct (forallb rv_call_inst_no_word_mulh insts) eqn:Hmul; cbn [negb] in Hval; [| discriminate Hval].
  destruct (Nat.leb (List.length arg_specs) 8) eqn:Hlen_a; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) eqn:Hnb_al_b;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (forallb (fun c => rv_supported_arg_width (mcs_ret_width c) &&
                              Nat.leb (List.length (mcs_args c)) 8 &&
                              forallb rv_valid_arg_spec (mcs_args c) &&
                              mc_no_dup_strings (List.map ras_name (mcs_args c))) callees) eqn:Hcal_b;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (reify_ir_call_tree ir_cfg arg_specs callees ret_w) as [| t_ir] eqn:Eir; [discriminate Hval |].
  destruct (summarize_rv64_call_tree insts callees arg_specs ret_w) as [| t_mc] eqn:Emc; [discriminate Hval |].
  destruct (collect_call_obls EA_Riscv64 callees ret_w [] t_ir t_mc) as [| obls] eqn:Eco; [discriminate Hval |].
  set (raw_cvars := collect_ir_call_vars_acc t_ir (collect_mc_call_vars_acc t_mc [])) in *.
  set (call_vars := dedup_typed_vars raw_cvars) in *.
  set (all_vars := dedup_typed_vars_acc allowed0 call_vars) in *.
  destruct (vars_width_consistent allowed0 all_vars && vars_width_consistent raw_cvars all_vars) eqn:Evwc;
    cbn [negb] in Hval; [| discriminate Hval].
  apply andb_true_iff in Evwc as [Evwc_al Evwc_cv].
  destruct (forallb (obl_wf_exprs all_vars) obls) eqn:Ewf_o; cbn [negb] in Hval; [| discriminate Hval].
  cbn [mccb_ctx mccb_all_vars mccb_obls] in Hval.
  destruct (check_mc_loop_obls "mc-call" (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars)
              all_vars None obls opt_pf) as [| []] eqn:Hchk; [discriminate Hval |].
  clear Hval.
  assert (Hnb_al : forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false).
  { intros nm w Hin; rewrite forallb_forall in Hnb_al_b; pose proof (Hnb_al_b (nm, w) Hin) as Hn; apply negb_true_iff in Hn; exact Hn. }
  assert (Hcws : forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true).
  { intros c Hc; rewrite forallb_forall in Hcal_b; pose proof (Hcal_b c Hc) as Ht;
      rewrite !andb_true_iff in Ht; exact (proj1 (proj1 (proj1 Ht))). }
  assert (Hcs : forall c, In c callees -> forallb rv_valid_arg_spec (mcs_args c) = true /\ NoDup (List.map ras_name (mcs_args c))).
  { intros c Hc; rewrite forallb_forall in Hcal_b; pose proof (Hcal_b c Hc) as Ht;
      rewrite !andb_true_iff in Ht; destruct Ht as [[[_ _] Hva] Hnd]; split; [exact Hva | apply mc_no_dup_strings_spec; exact Hnd]. }
  assert (Hnb_cv : forall nm w, In (nm, w) call_vars -> mc_starts_with_bang nm = true).
  { intros nm w Hcv; apply dedup_typed_vars_sub in Hcv; unfold raw_cvars in Hcv;
      rewrite collect_ir_call_vars_acc_shift in Hcv; apply in_app_iff in Hcv as [H1 | H2].
    - eapply reify_ir_call_at_vars_bang; [exact Eir | exact H1].
    - eapply summarize_rv64_call_at_vars_bang; [exact Emc | exact H2]. }
  assert (Hcv_av : forall nm w, In (nm, w) call_vars -> In (nm, w) all_vars).
  { intros nm w Hcv; apply dedup_typed_vars_sub in Hcv.
    exact (vars_width_consistent_in _ _ _ _ Evwc_cv Hcv). }
  assert (Hal_av : forall nm w, In (nm, w) allowed0 -> In (nm, w) all_vars)
    by (intros nm w Hal; exact (vars_width_consistent_in _ _ _ _ Evwc_al Hal)).
  assert (Hmv_av : forall nm w, In (nm, w) (collect_mc_call_vars t_mc) -> In (nm, w) all_vars).
  { intros nm w Hmv; eapply vars_width_consistent_in; [exact Evwc_cv |].
    unfold raw_cvars; rewrite collect_ir_call_vars_acc_shift; apply in_or_app; right; exact Hmv. }
  assert (Hav_sp : forall nm w, In (nm, w) all_vars -> In (nm, w) allowed0 \/ In (nm, w) call_vars)
    by (intros nm w Hav; exact (dedup_typed_vars_acc_sub allowed0 call_vars nm w Hav)).
  intros genv O Hgenv HO; cbn [rv_call_sound_spec].
  assert (Hsp2_init : rv_val_read 2%N (rv_build_init_val_regs 10%N arg_specs) = MSV_StackPtr 0%Z)
    by (unfold rv_val_read; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity).
  assert (Hfresh0 : forall nm w, In (nm, w) allowed0 -> forall k' w', (0 <= k')%nat ->
    nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').
  { intros nm w Hal k' w' _; pose proof (Hnb_al nm w Hal) as Hnb; split; intro Heq; subst;
      [rewrite mc_call_ret_var_bang in Hnb | rewrite mc_call_hi_var_bang in Hnb]; discriminate Hnb. }
  unfold summarize_rv64_call_tree in Emc; rewrite elf_length_tr_eq in Emc.
  destruct (summarize_rv64_call_at_exec insts (pt_of_list_first drci_off insts) (pt_of_list_first_lookup_rv_call insts)
              (S (2 * List.length insts)) callees PT_Empty 0%N 0%nat 0%Z
              (rv_build_init_val_regs 10%N arg_specs) [] ret_w allowed0 t_mc O penv0 rf0 rf0 mstk0
              Hrw Hcws Hmul HO Hsp0 ltac:(unfold mc_frame_cap; lia) Hsp2_init
              (rv_init_val_regs_wf allowed0 arg_specs Hargs_al Hws) ltac:(constructor)
              Hfresh0 (rv_init_val_regs_agrees penv0 dummy_freeze_oracle arg_specs rf0 Hws Hm)
              (mc_sym_stack_agrees_empty _ _ _ _ _) Emc)
    as (tr_mc & new_binds & rf_end & mstk_end & Hnd_nb & Hdisj_nb & Hnb_form & Hnb_vals & Hexec & Hcs_mc & Hra_mc & Hmt_gen).
  assert (Hnb_nb : forall nm, In nm (List.map fst new_binds) -> mc_starts_with_bang nm = true).
  { intros nm Hin; destruct (Hnb_form nm Hin) as [k [_ [[w ->] | ->]]];
      [apply mc_call_ret_var_bang | apply mc_call_hi_var_bang]. }
  destruct (call_extra_binds_props allowed0 (collect_mc_call_vars t_mc) call_vars all_vars penv0 new_binds
              Hnb_al Hnb_cv (dedup_typed_vars_nodup _) (dedup_typed_vars_acc_nodup _ _ (dedup_typed_vars_nodup _))
              Hcv_av Hal_av Hav_sp Hmv_av Hnd_nb Hnb_nb Hnb_vals Hpenv0
              (fun _ _ => Forall_nil _))
    as (Hdisj_eb & Hdisj_nb_eb & Hpres_nb & Hwf_full & Hctx_call).
  set (extra_binds := call_extra_binds new_binds call_vars) in *.
  set (penv_full := overlay_penv (new_binds ++ extra_binds) penv0) in *.
  assert (Hctx_all : ub_ctx_holds penv_full dummy_freeze_oracle (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars))
    by (apply Forall_app; split; [exact (Hctx0 penv_full Hpres_nb) | exact Hctx_call]).
  pose proof (check_mc_loop_obls_sound _ _ _ _ _ _ penv_full dummy_freeze_oracle false Hchk Hwf_full Hctx_all) as Hobls_ok.
  assert (Hpenv_ir_eq : forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
    penv_full nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm).
  { intros nm Hin; rewrite (Hpres_nb nm), (Hpenv_eq nm Hin); [reflexivity |].
    apply in_map_iff in Hin as [id [<- _]]; unfold cert_reg_name; reflexivity. }
  assert (Hpu_as : forall idx w pnm,
    In (idx, DTYPE_Base (DTYPE_I w)) (arg_specs_uses_from 0%nat arg_specs) ->
    nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
    In (pnm, w) all_vars).
  { intros idx w pnm Hin Hpnm; apply arg_specs_uses_from_in in Hin as (k & sp & -> & Hnth & Heq_dt).
    inversion Heq_dt; subst w; destruct (Hargs_compat k sp Hnth) as [_ Hp_sp].
    cbn [Nat.add] in Hpnm; rewrite Hpnm in Hp_sp; inversion Hp_sp; subst pnm.
    exact (Hal_av _ _ (Hargs_al sp (nth_error_In _ _ Hnth))). }
  assert (Hcomp_as : forall idx dt,
    In (idx, dt) (arg_specs_uses_from 0%nat arg_specs) -> nth_error arg_dtys idx = Some dt).
  { intros idx dt Hin; apply arg_specs_uses_from_in in Hin as (k & sp & -> & Hnth & ->).
    cbn [Nat.add]; exact (proj1 (Hargs_compat k sp Hnth)). }
  assert (Hwf_ir_t : ir_call_tree_wf all_vars ret_w t_ir)
    by (exact (reify_ir_call_tree_wf ir_cfg arg_specs callees ret_w all_vars t_ir (rv_supported_to_is_supported _ Hrw) Hpu_as Eir)).
  pose proof (reify_ir_call_tree_exec genv penv_full ir_cfg arg_specs callees ret_w all_vars arg_dtys vs t_ir
                (rv_supported_to_is_supported _ Hrw) Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp_as Hty
                Hpu_as Hpenv_ir_eq Hwf_full Eir) as Hden_ir.
  pose proof (Hmt_gen extra_binds Hdisj_eb Hdisj_nb_eb) as Hmt_full.
  destruct (ir_mc_call_trees_sound EA_Riscv64 callees ret_w genv penv_full t_ir t_mc [] obls all_vars
              (init_cfg_locals (args ir_cfg) vs) (@denote_cfg Pa ir_cfg None) _ _
              Hcs (fun _ _ Hin => ltac:(contradiction Hin)) Hobls_ok Eco Hwf_ir_t Hden_ir Hmt_full)
    as [[tr_ir_pre [Hpm_pre Hub_ir]] | (tr_ir & env_out & dv_ir & Hfa_tr & Hret_ir & Href_ir)].
  - exists tr_mc, rf_end, mstk_end; repeat split; try assumption.
    left; exists default_draw_strat, tr_ir_pre;
      split; [exact default_draw_strat_wf | split; [| exact Hub_ir]].
    clear -Hpm_pre; generalize dependent tr_ir_pre; induction tr_mc as [| [[cn_m rf_c] a0_r] r_mc IH];
      intros [| [[cn_i vs_i] dv_i] r_i] Hpm; [constructor | inversion Hpm | constructor |].
    inversion Hpm as [| ? ? ? ? Hhd Htl]; subst; constructor; [| exact (IH _ Htl)].
    destruct Hhd as (Hcn & sp & Efc & Hin_sp & Hstrip & Hlen_a & Hlen_v & Hargs & Hdv).
    rewrite Efc in Hargs, Hlen_a.
    unfold rv_call_event_matches; split; [exact Hcn | exists sp; repeat split; try assumption].
    intros k sp0 Hlt Hsp0.
    assert (Evm : nth_error (List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_c) (seq 0 (List.length (mcs_args sp)))) k =
                  Some (rv_read_reg (10%N + N.of_nat k) rf_c))
      by (rewrite nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
    exact (Hargs k sp0 _ Hsp0 Evm).
  - exists tr_mc, rf_end, mstk_end; repeat split; try assumption.
    right; exists default_draw_strat, tr_ir, default_draw_strat, env_out, dv_ir;
      split; [exact default_draw_strat_wf | split; [| split; [exact Hret_ir | exact Href_ir]]].
    clear -Hfa_tr; generalize dependent tr_ir; induction tr_mc as [| [[cn_m rf_c] a0_r] r_mc IH];
      intros [| [[cn_i vs_i] dv_i] r_i] Hfa; [constructor | inversion Hfa | inversion Hfa |].
    inversion Hfa as [| ? ? ? ? Hhd Htl]; subst; constructor; [| exact (IH _ Htl)].
    destruct Hhd as (Hcn & sp & Efc & Hin_sp & Hstrip & Hlen_a & Hlen_v & Hargs & Hdv).
    rewrite Efc in Hargs, Hlen_a.
    unfold rv_call_event_matches; split; [exact Hcn | exists sp; repeat split; try assumption].
    intros k sp0 Hlt Hsp0.
    assert (Evm : nth_error (List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_c) (seq 0 (List.length (mcs_args sp)))) k =
                  Some (rv_read_reg (10%N + N.of_nat k) rf_c))
      by (rewrite nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
    exact (Hargs k sp0 _ Hsp0 Evm).
Qed.

Theorem validate_mc_call_a64_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
         (insts : list decoded_a64_call_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
         (callees : list mc_callee_spec) (opt_pf : option (list lrat_step))
         arg_dtys vs (penv0 : param_env Pa) rf0 sp0 fl0 mstk0,
    validate_mc_call_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees opt_pf = inr tt ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    cfg_param_dtyp_compatible ir_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx sp,
       nth_error arg_specs idx = Some sp ->
       nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I (ras_width sp))) /\
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some (ras_name sp)) ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (param_idx_uses_cfg ir_cfg) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed0) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv0 nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    (forall sp, In sp arg_specs ->
       penv0 (a64_hi_var_name (ras_name sp)) =
       a64_extend_penv_with_hi (build_param_env (List.map cert_reg_name (args ir_cfg)) vs) arg_specs rf0 (a64_hi_var_name (ras_name sp))) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed0) ->
    (forall nv, In nv (a64_hi_vars arg_specs) -> In nv allowed0) ->
    NoDup (List.map ras_name arg_specs) ->
    (forall sp, In sp arg_specs -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name arg_specs)) ->
    (forall sp, In sp arg_specs -> penv0 (ras_name sp) = build_param_env (List.map cert_reg_name (args ir_cfg)) vs (ras_name sp)) ->
    mc_valid_sp0_depth 2%nat sp0 ->
    a64_rf_matches_args (build_param_env (List.map cert_reg_name (args ir_cfg)) vs) arg_specs rf0 ->
    a64_call_sound_spec ir_cfg insts ret_w callees vs rf0 sp0 fl0 mstk0.
Proof.
  intros ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w callees opt_pf
         arg_dtys vs penv0 rf0 sp0 fl0 mstk0
         Hval Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp Hty Hargs_compat Hpu Hpenv_eq Hhi_eq Hpenv0 Hctx0 Hargs_al Hhi_al Hnd_sp Hdis_hi Hsp_eq Hsp0 Hm.
  unfold validate_mc_call_a64, build_mc_call_bundle_a64 in Hval.
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hval; [| discriminate Hval].
  destruct (forallb a64_call_inst_valid insts) eqn:Hvalid; cbn [negb] in Hval; [| discriminate Hval].
  destruct (Nat.leb (List.length arg_specs) 8) eqn:Hlen_a; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb a64_valid_arg_spec arg_specs) eqn:Hws; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) eqn:Hnb_al_b;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (forallb (fun c => rv_supported_arg_width (mcs_ret_width c) &&
                              Nat.leb (List.length (mcs_args c)) 8 &&
                              forallb rv_valid_arg_spec (mcs_args c) &&
                              mc_no_dup_strings (List.map ras_name (mcs_args c))) callees) eqn:Hcal_b;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (reify_ir_call_tree ir_cfg arg_specs callees ret_w) as [| t_ir] eqn:Eir; [discriminate Hval |].
  destruct (summarize_a64_call_tree insts callees arg_specs ret_w) as [| t_mc] eqn:Emc; [discriminate Hval |].
  destruct (collect_call_obls EA_AArch64 callees ret_w [] t_ir t_mc) as [| obls] eqn:Eco; [discriminate Hval |].
  set (raw_cvars := collect_ir_call_vars_acc t_ir (collect_mc_call_vars_acc t_mc [])) in *.
  set (call_vars := dedup_typed_vars raw_cvars) in *.
  set (all_vars := dedup_typed_vars_acc allowed0 call_vars) in *.
  destruct (vars_width_consistent allowed0 all_vars && vars_width_consistent raw_cvars all_vars) eqn:Evwc;
    cbn [negb] in Hval; [| discriminate Hval].
  apply andb_true_iff in Evwc as [Evwc_al Evwc_cv].
  destruct (forallb (obl_wf_exprs all_vars) obls) eqn:Ewf_o; cbn [negb] in Hval; [| discriminate Hval].
  cbn [mccb_ctx mccb_all_vars mccb_obls] in Hval.
  destruct (check_mc_loop_obls "mc-call" (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars)
              all_vars None obls opt_pf) as [| []] eqn:Hchk; [discriminate Hval |].
  clear Hval.
  assert (Hnb_al : forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false).
  { intros nm w Hin; rewrite forallb_forall in Hnb_al_b; pose proof (Hnb_al_b (nm, w) Hin) as Hn; apply negb_true_iff in Hn; exact Hn. }
  assert (Hcws : forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true /\ (List.length (mcs_args c) <= 8)%nat).
  { intros c Hc; rewrite forallb_forall in Hcal_b; pose proof (Hcal_b c Hc) as Ht;
      rewrite !andb_true_iff in Ht; destruct Ht as [[[Hrwc Hlc] _] _]; split; [exact Hrwc | apply Nat.leb_le; exact Hlc]. }
  assert (Hcs : forall c, In c callees -> forallb rv_valid_arg_spec (mcs_args c) = true /\ NoDup (List.map ras_name (mcs_args c))).
  { intros c Hc; rewrite forallb_forall in Hcal_b; pose proof (Hcal_b c Hc) as Ht;
      rewrite !andb_true_iff in Ht; destruct Ht as [[[_ _] Hva] Hnd]; split; [exact Hva | apply mc_no_dup_strings_spec; exact Hnd]. }
  assert (Hnb_cv : forall nm w, In (nm, w) call_vars -> mc_starts_with_bang nm = true).
  { intros nm w Hcv; apply dedup_typed_vars_sub in Hcv; unfold raw_cvars in Hcv;
      rewrite collect_ir_call_vars_acc_shift in Hcv; apply in_app_iff in Hcv as [H1 | H2].
    - eapply reify_ir_call_at_vars_bang; [exact Eir | exact H1].
    - eapply summarize_a64_call_at_vars_bang; [exact Emc | exact H2]. }
  assert (Hcv_av : forall nm w, In (nm, w) call_vars -> In (nm, w) all_vars)
    by (intros nm w Hcv; apply dedup_typed_vars_sub in Hcv; exact (vars_width_consistent_in _ _ _ _ Evwc_cv Hcv)).
  assert (Hal_av : forall nm w, In (nm, w) allowed0 -> In (nm, w) all_vars)
    by (intros nm w Hal; exact (vars_width_consistent_in _ _ _ _ Evwc_al Hal)).
  assert (Hmv_av : forall nm w, In (nm, w) (collect_mc_call_vars t_mc) -> In (nm, w) all_vars).
  { intros nm w Hmv; eapply vars_width_consistent_in; [exact Evwc_cv |].
    unfold raw_cvars; rewrite collect_ir_call_vars_acc_shift; apply in_or_app; right; exact Hmv. }
  assert (Hav_sp : forall nm w, In (nm, w) all_vars -> In (nm, w) allowed0 \/ In (nm, w) call_vars)
    by (intros nm w Hav; exact (dedup_typed_vars_acc_sub allowed0 call_vars nm w Hav)).
  intros genv O Hgenv HO; cbn [a64_call_sound_spec].
  assert (Hfresh0 : forall nm w, In (nm, w) allowed0 -> forall k' w', (0 <= k')%nat ->
    nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').
  { intros nm w Hal k' w' _; pose proof (Hnb_al nm w Hal) as Hnb; split; intro Heq; subst;
      [rewrite mc_call_ret_var_bang in Hnb | rewrite mc_call_hi_var_bang in Hnb]; discriminate Hnb. }
  assert (Hag_init : a64_val_regs_agrees penv0 dummy_freeze_oracle rf0 sp0 (a64_build_init_val_regs 0%N arg_specs) rf0).
  { set (penv_ir := build_param_env (List.map cert_reg_name (args ir_cfg)) vs) in *.
    pose proof (a64_init_val_regs_agrees penv_ir dummy_freeze_oracle arg_specs rf0 sp0 Hws Hnd_sp) as Hbase.
    assert (Hbase2 : a64_val_regs_agrees (a64_extend_penv_with_hi penv_ir arg_specs rf0) dummy_freeze_oracle rf0 sp0 (a64_build_init_val_regs 0%N arg_specs) rf0)
      by (apply Hbase; [exact Hdis_hi | exact Hm]).
    intro r; pose proof (Hbase2 r) as Hr; destruct (a64_val_read r (a64_build_init_val_regs 0%N arg_specs)) as [| e_arg | |] eqn:Erd; try exact Hr.
    destruct (a64_build_init_val_regs_vars 0%N arg_specs r e_arg Erd) as [Hlf Hfv].
    cbn [mc_sym_val_agrees] in *; unfold eval_closed_cert_expr in Hr |- *;
      erewrite mcc_eval_cert_expr_penv_agree; [exact Hr | exact Hlf |].
    intros nm w Hin; destruct (Hfv nm w Hin) as [sp [Hsp [[-> ->] | [_ [-> ->]]]]].
    - unfold a64_extend_penv_with_hi; rewrite a64_extend_penv_at_orig;
        [exact (Hsp_eq sp Hsp)
        | intros s Hs Heq; apply (Hdis_hi s Hs); rewrite Heq; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]].
    - exact (Hhi_eq sp Hsp). }
  assert (Hall_a64 : forall sp, In sp arg_specs ->
    In (ras_name sp, ras_width sp) allowed0 /\
    (ras_width sp <> 64%positive -> In (a64_hi_var_name (ras_name sp), 64%positive) allowed0)).
  { intros sp Hsp; split; [exact (Hargs_al sp Hsp) | intro Hne; exact (Hhi_al _ (a64_hi_vars_in_specs _ _ Hsp Hne))]. }
  unfold summarize_a64_call_tree in Emc; rewrite elf_length_tr_eq in Emc.
  destruct (summarize_a64_call_at_exec insts (pt_of_list_first daci_off insts) (pt_of_list_first_lookup_a64_call insts)
              (S (2 * List.length insts)) callees PT_Empty 0%N 0%nat 0%Z
              (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w allowed0 t_mc
              O penv0 rf0 sp0 rf0 sp0 fl0 mstk0
              Hrw Hcws Hvalid HO Hsp0 ltac:(unfold mc_frame_cap; lia) ltac:(symmetry; apply Integers.add_zero)
              (a64_init_val_regs_wf allowed0 arg_specs Hall_a64 Hws)
              ltac:(constructor) (fun C => ltac:(discriminate C))
              Hfresh0 Hag_init (mc_sym_stack_agrees_empty _ _ _ _ _) (fun C => ltac:(discriminate C)) Emc)
    as (tr_mc & new_binds & rf_end & fl_end & mstk_end & Hnd_nb & Hdisj_nb & Hnb_form & Hnb_vals & Hexec & Hcs_mc & Hmt_gen).
  assert (Hnb_nb : forall nm, In nm (List.map fst new_binds) -> mc_starts_with_bang nm = true).
  { intros nm Hin; destruct (Hnb_form nm Hin) as [k [_ [[w ->] | ->]]];
      [apply mc_call_ret_var_bang | apply mc_call_hi_var_bang]. }
  destruct (call_extra_binds_props allowed0 (collect_mc_call_vars t_mc) call_vars all_vars penv0 new_binds
              Hnb_al Hnb_cv (dedup_typed_vars_nodup _) (dedup_typed_vars_acc_nodup _ _ (dedup_typed_vars_nodup _))
              Hcv_av Hal_av Hav_sp Hmv_av Hnd_nb Hnb_nb Hnb_vals Hpenv0
              (fun _ _ => Forall_nil _))
    as (Hdisj_eb & Hdisj_nb_eb & Hpres_nb & Hwf_full & Hctx_call).
  set (extra_binds := call_extra_binds new_binds call_vars) in *.
  set (penv_full := overlay_penv (new_binds ++ extra_binds) penv0) in *.
  assert (Hctx_all : ub_ctx_holds penv_full dummy_freeze_oracle (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) call_vars))
    by (apply Forall_app; split; [exact (Hctx0 penv_full Hpres_nb) | exact Hctx_call]).
  pose proof (check_mc_loop_obls_sound _ _ _ _ _ _ penv_full dummy_freeze_oracle false Hchk Hwf_full Hctx_all) as Hobls_ok.
  assert (Hpenv_ir_eq : forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
    penv_full nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm).
  { intros nm Hin; rewrite (Hpres_nb nm), (Hpenv_eq nm Hin); [reflexivity |].
    apply in_map_iff in Hin as [id [<- _]]; unfold cert_reg_name; reflexivity. }
  assert (Hpu_as : forall idx w pnm,
    In (idx, DTYPE_Base (DTYPE_I w)) (arg_specs_uses_from 0%nat arg_specs) ->
    nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
    In (pnm, w) all_vars).
  { intros idx w pnm Hin Hpnm; apply arg_specs_uses_from_in in Hin as (k & sp & -> & Hnth & Heq_dt).
    inversion Heq_dt; subst w; destruct (Hargs_compat k sp Hnth) as [_ Hp_sp].
    cbn [Nat.add] in Hpnm; rewrite Hpnm in Hp_sp; inversion Hp_sp; subst pnm.
    exact (Hal_av _ _ (Hargs_al sp (nth_error_In _ _ Hnth))). }
  assert (Hcomp_as : forall idx dt,
    In (idx, dt) (arg_specs_uses_from 0%nat arg_specs) -> nth_error arg_dtys idx = Some dt).
  { intros idx dt Hin; apply arg_specs_uses_from_in in Hin as (k & sp & -> & Hnth & ->).
    cbn [Nat.add]; exact (proj1 (Hargs_compat k sp Hnth)). }
  assert (Hwf_ir_t : ir_call_tree_wf all_vars ret_w t_ir)
    by (exact (reify_ir_call_tree_wf ir_cfg arg_specs callees ret_w all_vars t_ir (rv_supported_to_is_supported _ Hrw) Hpu_as Eir)).
  pose proof (reify_ir_call_tree_exec genv penv_full ir_cfg arg_specs callees ret_w all_vars arg_dtys vs t_ir
                (rv_supported_to_is_supported _ Hrw) Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp_as Hty
                Hpu_as Hpenv_ir_eq Hwf_full Eir) as Hden_ir.
  pose proof (Hmt_gen extra_binds Hdisj_eb Hdisj_nb_eb) as Hmt_full.
  destruct (ir_mc_call_trees_sound EA_AArch64 callees ret_w genv penv_full t_ir t_mc [] obls all_vars
              (init_cfg_locals (args ir_cfg) vs) (@denote_cfg Pa ir_cfg None) _ _
              Hcs (fun _ _ Hin => ltac:(contradiction Hin)) Hobls_ok Eco Hwf_ir_t Hden_ir Hmt_full)
    as [[tr_ir_pre [Hpm_pre Hub_ir]] | (tr_ir & env_out & dv_ir & Hfa_tr & Hret_ir & Href_ir)].
  - exists tr_mc, rf_end, fl_end, mstk_end; repeat split; try assumption.
    left; exists default_draw_strat, tr_ir_pre;
      split; [exact default_draw_strat_wf | split; [| exact Hub_ir]].
    clear -Hpm_pre; generalize dependent tr_ir_pre; induction tr_mc as [| [[cn_m rf_c] x0_r] r_mc IH];
      intros [| [[cn_i vs_i] dv_i] r_i] Hpm; [constructor | inversion Hpm | constructor |].
    inversion Hpm as [| ? ? ? ? Hhd Htl]; subst; constructor; [| exact (IH _ Htl)].
    destruct Hhd as (Hcn & sp & Efc & Hin_sp & Hstrip & Hlen_a & Hlen_v & Hargs & Hdv).
    rewrite Efc in Hargs, Hlen_a.
    unfold a64_call_event_matches; split; [exact Hcn | exists sp; repeat split; try assumption].
    intros k sp0 Hlt Hsp0.
    assert (Evm : nth_error (List.map (fun j => a64_read_reg (N.of_nat j) rf_c) (seq 0 (List.length (mcs_args sp)))) k =
                  Some (a64_read_reg (N.of_nat k) rf_c))
      by (rewrite nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
    exact (Hargs k sp0 _ Hsp0 Evm).
  - exists tr_mc, rf_end, fl_end, mstk_end; repeat split; try assumption.
    right; exists default_draw_strat, tr_ir, default_draw_strat, env_out, dv_ir;
      split; [exact default_draw_strat_wf | split; [| split; [exact Hret_ir | exact Href_ir]]].
    clear -Hfa_tr; generalize dependent tr_ir; induction tr_mc as [| [[cn_m rf_c] x0_r] r_mc IH];
      intros [| [[cn_i vs_i] dv_i] r_i] Hfa; [constructor | inversion Hfa | inversion Hfa |].
    inversion Hfa as [| ? ? ? ? Hhd Htl]; subst; constructor; [| exact (IH _ Htl)].
    destruct Hhd as (Hcn & sp & Efc & Hin_sp & Hstrip & Hlen_a & Hlen_v & Hargs & Hdv).
    rewrite Efc in Hargs, Hlen_a.
    unfold a64_call_event_matches; split; [exact Hcn | exists sp; repeat split; try assumption].
    intros k sp0 Hlt Hsp0.
    assert (Evm : nth_error (List.map (fun j => a64_read_reg (N.of_nat j) rf_c) (seq 0 (List.length (mcs_args sp)))) k =
                  Some (a64_read_reg (N.of_nat k) rf_c))
      by (rewrite nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
    exact (Hargs k sp0 _ Hsp0 Evm).
Qed.

(** *** 5.6 Caller/Callee Concrete Oracle Composition *)

Record rv_leaf_callee {Pa : Params} : Type := mk_rv_leaf_callee {
  rlc_spec : mc_callee_spec;
  rlc_cfg : CFG.cfg dtyp;
  rlc_insts : list decoded_rv_inst;
  rlc_exec : forall rf_call mstk_call,
    mc_valid_sp0 (rv_read_reg 2%N rf_call) ->
    exists rf_ret (v_ret : @Integers.bit_int (mcs_ret_width rlc_spec)),
      rv_exec_mem (S (2 * List.length rlc_insts)) rlc_insts 0%N (rv_read_reg 2%N rf_call) rf_call mstk_call =
        Some (rf_ret, mstk_call) /\
      rv_callee_saved_preserved rf_call rf_ret /\
      rv_abi_ret_matches (mcs_ret_width rlc_spec) (mcs_ret_ext rlc_spec) v_ret (rv_read_reg 10%N rf_ret);
  rlc_ir : forall (vs : list (@dvalue Pa)) rf_call mstk_call rf_ret mstk_ret,
    rv_rf_matches_args (build_param_env (List.map ras_name (mcs_args rlc_spec)) vs) (mcs_args rlc_spec) rf_call ->
    List.length vs = List.length (mcs_args rlc_spec) ->
    rv_exec_mem (S (2 * List.length rlc_insts)) rlc_insts 0%N (rv_read_reg 2%N rf_call) rf_call mstk_call =
      Some (rf_ret, mstk_ret) ->
    exists sigma_ir,
      wf_draw_strat sigma_ir /\
      (cfg_steps_to_ub sigma_ir (init_cfg_locals (args rlc_cfg) vs) (denote_cfg rlc_cfg None) \/
       exists sigma_ir' env_out dv_ir,
         cfg_steps_to_ret sigma_ir (init_cfg_locals (args rlc_cfg) vs) (denote_cfg rlc_cfg None)
           sigma_ir' env_out dv_ir /\
         dvalue_refines dv_ir
           (DVALUE_Base (@DVALUE_I Pa (mcs_ret_width rlc_spec)
              (rv_trunc_ret_val (mcs_ret_width rlc_spec) (rv_read_reg 10%N rf_ret)))));
}.

Fixpoint find_rv_leaf_callee {Pa : Params} (cs : list (@rv_leaf_callee Pa)) (cname : string)
  : option (@rv_leaf_callee Pa) :=
  match cs with
  | [] => None
  | lc :: rest =>
      if String.eqb (mc_strip_leading_at (mcs_name (rlc_spec lc))) cname then Some lc
      else find_rv_leaf_callee rest cname
  end.

Lemma find_rv_leaf_callee_in {Pa : Params} :
  forall (cs : list (@rv_leaf_callee Pa)) lc,
    NoDup (List.map (fun x => mc_strip_leading_at (mcs_name (rlc_spec x))) cs) ->
    In lc cs ->
    find_rv_leaf_callee cs (mc_strip_leading_at (mcs_name (rlc_spec lc))) = Some lc.
Proof.
  intros cs lc Hnd Hlc; induction cs as [| x rest IH]; cbn in *; [contradiction |].
  inversion Hnd as [| ? ? Hni Hndr]; subst.
  destruct Hlc as [<- | Hr]; [rewrite String.eqb_refl; reflexivity |].
  destruct (String.eqb (mc_strip_leading_at (mcs_name (rlc_spec x))) (mc_strip_leading_at (mcs_name (rlc_spec lc)))) eqn:Eeq.
  - apply String.eqb_eq in Eeq; exfalso; apply Hni; rewrite Eeq; apply in_map_iff; exists lc; split; [reflexivity | exact Hr].
  - exact (IH Hndr Hr).
Qed.

Definition rv_leaf_oracle {Pa : Params} (cs : list (@rv_leaf_callee Pa)) : rv_call_oracle :=
  fun cname rf_call mstk_call =>
    match find_rv_leaf_callee cs cname with
    | None => None
    | Some lc =>
        rv_exec_mem (S (2 * List.length (rlc_insts lc))) (rlc_insts lc) 0%N (rv_read_reg 2%N rf_call) rf_call mstk_call
    end.

Lemma rv_leaf_oracle_wf {Pa : Params} :
  forall (cs : list (@rv_leaf_callee Pa)),
    NoDup (List.map (fun lc => mc_strip_leading_at (mcs_name (rlc_spec lc))) cs) ->
    wf_rv_call_oracle (List.map rlc_spec cs) (rv_leaf_oracle cs).
Proof.
  intros cs Hnd c rf_call mstk_call Hinc Hsp.
  apply in_map_iff in Hinc as [lc [<- Hlc]].
  unfold rv_leaf_oracle; rewrite (find_rv_leaf_callee_in cs lc Hnd Hlc).
  exact (rlc_exec lc rf_call mstk_call Hsp).
Qed.

Lemma rv_exec_with_calls_events :
  forall fuel insts O pc sp0 rf mstk tr rf_end mstk_end,
    rv_exec_with_calls fuel insts O pc sp0 rf mstk = Some (tr, rf_end, mstk_end) ->
    Forall (fun '(cn_m, rf_call, a0_ret) =>
      exists mstk_call rf_ret mstk_ret,
        O cn_m rf_call mstk_call = Some (rf_ret, mstk_ret) /\
        rv_read_reg 10%N rf_ret = a0_ret) tr.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros insts O pc sp0 rf mstk tr rf_end mstk_end Hexec;
    cbn [rv_exec_with_calls] in Hexec; [discriminate Hexec |].
  destruct (lookup_rv_call_inst insts pc) as [d |]; [| discriminate Hexec].
  destruct (drci_inst d) as [i | cname].
  - destruct i; try discriminate Hexec;
      try (destruct (rv_exec_one_nonret _ _ _ _ _) as [[[pc1 rf1] mstk1] |]; [exact (IH _ _ _ _ _ _ _ _ _ Hexec) | discriminate Hexec]).
    inversion Hexec; constructor.
  - destruct (mc_sp_aligned16 (mc_addr_to_off sp0 (rv_read_reg 2%N rf))); [| discriminate Hexec].
    destruct (O cname _ mstk) as [[rf_ret mstk_ret] |] eqn:Eo; [| discriminate Hexec].
    destruct (rv_exec_with_calls fuel' insts O _ sp0 rf_ret mstk_ret) as [[[tr' rf_e] mstk_e] |] eqn:Erec;
      [| discriminate Hexec].
    inversion Hexec; subst; clear Hexec.
    constructor; [exists mstk, rf_ret, mstk_ret; split; [exact Eo | reflexivity] | exact (IH _ _ _ _ _ _ _ _ _ Erec)].
Qed.

Theorem compose_rv64_caller_callee_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (insts : list decoded_rv_call_inst) (ret_w : positive)
         (cs : list (@rv_leaf_callee Pa)) (vs : list (@dvalue Pa))
         rf0 mstk0 genv,
    NoDup (List.map (fun lc => mc_strip_leading_at (mcs_name (rlc_spec lc))) cs) ->
    rv_call_sound_spec ir_cfg insts ret_w (List.map rlc_spec cs) vs rf0 mstk0 ->
    wf_callee_genv (List.map rlc_spec cs) genv ->
    let rv_fuel := S (2 * List.length insts) in
    exists tr_mc rf_end mstk_end,
      rv_exec_with_calls rv_fuel insts (rv_leaf_oracle cs) 0%N (rv_read_reg 2%N rf0) rf0 mstk0 =
        Some (tr_mc, rf_end, mstk_end) /\
      rv_callee_saved_preserved rf0 rf_end /\
      rf_end 1%N = rf0 1%N /\
      ((exists sigma_ir tr_ir_pre,
          wf_draw_strat sigma_ir /\
          prefix_matches (rv_call_event_matches (List.map rlc_spec cs)) tr_ir_pre tr_mc /\
          cfg_call_steps_to_ub genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
            (denote_cfg ir_cfg None) tr_ir_pre) \/
       (exists sigma_ir tr_ir sigma_ir' env_out dv_ir,
          wf_draw_strat sigma_ir /\
          Forall2
            (fun '(cn_m, rf_call, a0_ret) '(cn_i, vs_i, dv_ret) =>
               rv_call_event_matches (List.map rlc_spec cs) (cn_m, rf_call, a0_ret) (cn_i, vs_i, dv_ret) /\
               exists lc,
                 find_rv_leaf_callee cs cn_m = Some lc /\
                 exists sigma_c,
                   wf_draw_strat sigma_c /\
                   (cfg_steps_to_ub sigma_c (init_cfg_locals (args (rlc_cfg lc)) vs_i) (denote_cfg (rlc_cfg lc) None) \/
                    exists sigma_c' env_c' dv_c,
                      cfg_steps_to_ret sigma_c (init_cfg_locals (args (rlc_cfg lc)) vs_i) (denote_cfg (rlc_cfg lc) None)
                        sigma_c' env_c' dv_c /\
                      dvalue_refines dv_c dv_ret))
            tr_mc tr_ir /\
          cfg_call_steps_to_ret genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
            (denote_cfg ir_cfg None) tr_ir sigma_ir' env_out dv_ir /\
          dvalue_refines dv_ir
            (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))))).
Proof.
  intros ir_cfg insts ret_w cs vs rf0 mstk0 genv Hnd Hcaller Hgenv.
  destruct (Hcaller genv (rv_leaf_oracle cs) Hgenv (rv_leaf_oracle_wf cs Hnd))
    as (tr_mc & rf_end & mstk_end & Hexec & Hcs & Hra & [Hub | (sigma_ir & tr_ir & sigma_ir' & env_out & dv_ir & Hwf_s & Hfa & Hret & Href)]).
  - exists tr_mc, rf_end, mstk_end; repeat split; try assumption; left; exact Hub.
  - pose proof (rv_exec_with_calls_events _ _ _ _ _ _ _ _ _ _ Hexec) as Hevs.
    exists tr_mc, rf_end, mstk_end; repeat split; try assumption.
    right; exists sigma_ir, tr_ir, sigma_ir', env_out, dv_ir.
    split; [exact Hwf_s | split; [| split; [exact Hret | exact Href]]].
    clear -Hnd Hevs Hfa; generalize dependent tr_ir; induction tr_mc as [| [[cn_m rf_call] a0_ret] r_mc IH];
      intros [| [[cn_i vs_i] dv_ret] r_i] Hfa; [constructor | inversion Hfa | inversion Hfa |].
    inversion Hfa as [| ? ? ? ? Hmfa Hfa_r]; subst.
    pose proof (Forall_inv Hevs) as (mstk_call & rf_ret & mstk_ret & Ho & Ha0).
    constructor.
    + split; [exact Hmfa |].
      destruct Hmfa as [_ (c & Hinc & Hstrip & Hrf & Hlen & Hdv)].
      apply in_map_iff in Hinc as [lc [<- Hlc]].
      pose proof (find_rv_leaf_callee_in cs lc Hnd Hlc) as Hfind; rewrite Hstrip in Hfind.
      exists lc; split; [exact Hfind |].
      unfold rv_leaf_oracle in Ho; rewrite Hfind in Ho.
      destruct (rlc_ir lc vs_i rf_call mstk_call rf_ret mstk_ret Hrf Hlen Ho) as (sigma_c & Hwf_c & Hbody).
      exists sigma_c; split; [exact Hwf_c |].
      rewrite Hdv, <- Ha0; exact Hbody.
    + exact (IH (Forall_inv_tail Hevs) _ Hfa_r).
Qed.

Record a64_leaf_callee {Pa : Params} : Type := mk_a64_leaf_callee {
  alc_spec : mc_callee_spec;
  alc_cfg : CFG.cfg dtyp;
  alc_insts : list decoded_a64_inst;
  alc_exec : forall rf_call sp_call fl_call mstk_call,
    mc_valid_sp0 sp_call ->
    exists rf_ret fl_ret (v_ret : @Integers.bit_int (mcs_ret_width alc_spec)),
      a64_exec_mem (S (2 * List.length alc_insts)) alc_insts 0%N sp_call rf_call sp_call fl_call mstk_call =
        Some (rf_ret, sp_call, fl_ret, mstk_call) /\
      a64_callee_saved_preserved rf_call rf_ret /\
      rv_abi_ret_matches (mcs_ret_width alc_spec) (mcs_ret_ext alc_spec) v_ret (a64_read_reg 0%N rf_ret);
  alc_ir : forall (vs : list (@dvalue Pa)) rf_call sp_call fl_call mstk_call rf_ret sp_ret fl_ret mstk_ret,
    a64_rf_matches_args (build_param_env (List.map ras_name (mcs_args alc_spec)) vs) (mcs_args alc_spec) rf_call ->
    List.length vs = List.length (mcs_args alc_spec) ->
    a64_exec_mem (S (2 * List.length alc_insts)) alc_insts 0%N sp_call rf_call sp_call fl_call mstk_call =
      Some (rf_ret, sp_ret, fl_ret, mstk_ret) ->
    exists sigma_ir,
      wf_draw_strat sigma_ir /\
      (cfg_steps_to_ub sigma_ir (init_cfg_locals (args alc_cfg) vs) (denote_cfg alc_cfg None) \/
       exists sigma_ir' env_out dv_ir,
         cfg_steps_to_ret sigma_ir (init_cfg_locals (args alc_cfg) vs) (denote_cfg alc_cfg None)
           sigma_ir' env_out dv_ir /\
         dvalue_refines dv_ir
           (DVALUE_Base (@DVALUE_I Pa (mcs_ret_width alc_spec)
              (rv_trunc_ret_val (mcs_ret_width alc_spec) (a64_read_reg 0%N rf_ret)))));
}.

Fixpoint find_a64_leaf_callee {Pa : Params} (cs : list (@a64_leaf_callee Pa)) (cname : string)
  : option (@a64_leaf_callee Pa) :=
  match cs with
  | [] => None
  | lc :: rest =>
      if String.eqb (mc_strip_leading_at (mcs_name (alc_spec lc))) cname then Some lc
      else find_a64_leaf_callee rest cname
  end.

Lemma find_a64_leaf_callee_in {Pa : Params} :
  forall (cs : list (@a64_leaf_callee Pa)) lc,
    NoDup (List.map (fun x => mc_strip_leading_at (mcs_name (alc_spec x))) cs) ->
    In lc cs ->
    find_a64_leaf_callee cs (mc_strip_leading_at (mcs_name (alc_spec lc))) = Some lc.
Proof.
  intros cs lc Hnd Hlc; induction cs as [| x rest IH]; cbn in *; [contradiction |].
  inversion Hnd as [| ? ? Hni Hndr]; subst.
  destruct Hlc as [<- | Hr]; [rewrite String.eqb_refl; reflexivity |].
  destruct (String.eqb (mc_strip_leading_at (mcs_name (alc_spec x))) (mc_strip_leading_at (mcs_name (alc_spec lc)))) eqn:Eeq.
  - apply String.eqb_eq in Eeq; exfalso; apply Hni; rewrite Eeq; apply in_map_iff; exists lc; split; [reflexivity | exact Hr].
  - exact (IH Hndr Hr).
Qed.

Definition a64_leaf_oracle {Pa : Params} (cs : list (@a64_leaf_callee Pa)) : a64_call_oracle :=
  fun cname rf_call sp_call fl_call mstk_call =>
    match find_a64_leaf_callee cs cname with
    | None => None
    | Some lc =>
        a64_exec_mem (S (2 * List.length (alc_insts lc))) (alc_insts lc) 0%N sp_call rf_call sp_call fl_call mstk_call
    end.

Lemma a64_leaf_oracle_wf {Pa : Params} :
  forall (cs : list (@a64_leaf_callee Pa)),
    NoDup (List.map (fun lc => mc_strip_leading_at (mcs_name (alc_spec lc))) cs) ->
    wf_a64_call_oracle (List.map alc_spec cs) (a64_leaf_oracle cs).
Proof.
  intros cs Hnd c rf_call sp_call fl_call mstk_call Hinc Hsp.
  apply in_map_iff in Hinc as [lc [<- Hlc]].
  unfold a64_leaf_oracle; rewrite (find_a64_leaf_callee_in cs lc Hnd Hlc).
  exact (alc_exec lc rf_call sp_call fl_call mstk_call Hsp).
Qed.

Lemma a64_exec_with_calls_events :
  forall fuel insts O pc sp0 rf sp fl mstk tr rf_end sp_end fl_end mstk_end,
    a64_exec_with_calls fuel insts O pc sp0 rf sp fl mstk = Some (tr, rf_end, sp_end, fl_end, mstk_end) ->
    Forall (fun '(cn_m, rf_call, x0_ret) =>
      exists sp_call fl_call mstk_call rf_ret sp_ret fl_ret mstk_ret,
        O cn_m rf_call sp_call fl_call mstk_call = Some (rf_ret, sp_ret, fl_ret, mstk_ret) /\
        a64_read_reg 0%N rf_ret = x0_ret) tr.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros insts O pc sp0 rf sp fl mstk tr rf_end sp_end fl_end mstk_end Hexec;
    cbn [a64_exec_with_calls] in Hexec; [discriminate Hexec |].
  destruct (lookup_a64_call_inst insts pc) as [d |]; [| discriminate Hexec].
  destruct (daci_inst d) as [i | cname].
  - destruct i; try discriminate Hexec;
      try (destruct (a64_exec_one_nonret _ _ _ _ _ _ _) as [[[[[pc1 rf1] sp1] fl1] mstk1] |];
           [exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec) | discriminate Hexec]).
    inversion Hexec; constructor.
  - destruct (mc_sp_aligned16 (mc_addr_to_off sp0 sp)); [| discriminate Hexec].
    destruct (O cname _ sp fl mstk) as [[[[rf_ret sp_ret] fl_ret] mstk_ret] |] eqn:Eo; [| discriminate Hexec].
    destruct (a64_exec_with_calls fuel' insts O _ sp0 rf_ret sp_ret fl_ret mstk_ret)
      as [[[[[tr' rf_e] sp_e] fl_e] mstk_e] |] eqn:Erec; [| discriminate Hexec].
    inversion Hexec; subst; clear Hexec.
    constructor; [exists sp, fl, mstk, rf_ret, sp_ret, fl_ret, mstk_ret; split; [exact Eo | reflexivity]
                 | exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Erec)].
Qed.

Theorem compose_a64_caller_callee_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (insts : list decoded_a64_call_inst) (ret_w : positive)
         (cs : list (@a64_leaf_callee Pa)) (vs : list (@dvalue Pa))
         rf0 sp0 fl0 mstk0 genv,
    NoDup (List.map (fun lc => mc_strip_leading_at (mcs_name (alc_spec lc))) cs) ->
    a64_call_sound_spec ir_cfg insts ret_w (List.map alc_spec cs) vs rf0 sp0 fl0 mstk0 ->
    wf_callee_genv (List.map alc_spec cs) genv ->
    let a64_fuel := S (2 * List.length insts) in
    exists tr_mc rf_end fl_end mstk_end,
      a64_exec_with_calls a64_fuel insts (a64_leaf_oracle cs) 0%N sp0 rf0 sp0 fl0 mstk0 =
        Some (tr_mc, rf_end, sp0, fl_end, mstk_end) /\
      a64_callee_saved_preserved rf0 rf_end /\
      ((exists sigma_ir tr_ir_pre,
          wf_draw_strat sigma_ir /\
          prefix_matches (a64_call_event_matches (List.map alc_spec cs)) tr_ir_pre tr_mc /\
          cfg_call_steps_to_ub genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
            (denote_cfg ir_cfg None) tr_ir_pre) \/
       (exists sigma_ir tr_ir sigma_ir' env_out dv_ir,
          wf_draw_strat sigma_ir /\
          Forall2
            (fun '(cn_m, rf_call, x0_ret) '(cn_i, vs_i, dv_ret) =>
               a64_call_event_matches (List.map alc_spec cs) (cn_m, rf_call, x0_ret) (cn_i, vs_i, dv_ret) /\
               exists lc,
                 find_a64_leaf_callee cs cn_m = Some lc /\
                 exists sigma_c,
                   wf_draw_strat sigma_c /\
                   (cfg_steps_to_ub sigma_c (init_cfg_locals (args (alc_cfg lc)) vs_i) (denote_cfg (alc_cfg lc) None) \/
                    exists sigma_c' env_c' dv_c,
                      cfg_steps_to_ret sigma_c (init_cfg_locals (args (alc_cfg lc)) vs_i) (denote_cfg (alc_cfg lc) None)
                        sigma_c' env_c' dv_c /\
                      dvalue_refines dv_c dv_ret))
            tr_mc tr_ir /\
          cfg_call_steps_to_ret genv sigma_ir (init_cfg_locals (args ir_cfg) vs)
            (denote_cfg ir_cfg None) tr_ir sigma_ir' env_out dv_ir /\
          dvalue_refines dv_ir
            (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))).
Proof.
  intros ir_cfg insts ret_w cs vs rf0 sp0 fl0 mstk0 genv Hnd Hcaller Hgenv.
  destruct (Hcaller genv (a64_leaf_oracle cs) Hgenv (a64_leaf_oracle_wf cs Hnd))
    as (tr_mc & rf_end & fl_end & mstk_end & Hexec & Hcs & [Hub | (sigma_ir & tr_ir & sigma_ir' & env_out & dv_ir & Hwf_s & Hfa & Hret & Href)]).
  - exists tr_mc, rf_end, fl_end, mstk_end; repeat split; try assumption; left; exact Hub.
  - pose proof (a64_exec_with_calls_events _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec) as Hevs.
    exists tr_mc, rf_end, fl_end, mstk_end; repeat split; try assumption.
    right; exists sigma_ir, tr_ir, sigma_ir', env_out, dv_ir.
    split; [exact Hwf_s | split; [| split; [exact Hret | exact Href]]].
    clear -Hnd Hevs Hfa; generalize dependent tr_ir; induction tr_mc as [| [[cn_m rf_call] x0_ret] r_mc IH];
      intros [| [[cn_i vs_i] dv_ret] r_i] Hfa; [constructor | inversion Hfa | inversion Hfa |].
    inversion Hfa as [| ? ? ? ? Hmfa Hfa_r]; subst.
    pose proof (Forall_inv Hevs) as (sp_call & fl_call & mstk_call & rf_ret & sp_ret & fl_ret & mstk_ret & Ho & Hx0).
    constructor.
    + split; [exact Hmfa |].
      destruct Hmfa as [_ (c & Hinc & Hstrip & Hrf & Hlen & Hdv)].
      apply in_map_iff in Hinc as [lc [<- Hlc]].
      pose proof (find_a64_leaf_callee_in cs lc Hnd Hlc) as Hfind; rewrite Hstrip in Hfind.
      exists lc; split; [exact Hfind |].
      unfold a64_leaf_oracle in Ho; rewrite Hfind in Ho.
      destruct (alc_ir lc vs_i rf_call sp_call fl_call mstk_call rf_ret sp_ret fl_ret mstk_ret Hrf Hlen Ho)
        as (sigma_c & Hwf_c & Hbody).
      exists sigma_c; split; [exact Hwf_c |].
      rewrite Hdv, <- Hx0; exact Hbody.
    + exact (IH (Forall_inv_tail Hevs) _ Hfa_r).
Qed.
