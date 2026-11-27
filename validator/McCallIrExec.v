(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * IR Call-Tree Execution & Lockstep Soundness ([CertValidator.McCallIrExec])

    Implements Section 5.4 of Milestone M3c of Phase 8.3a: IR call-tree
    denotation ([Section IrTreeDenote]), argument obligation checking, and
    lockstep soundness on top of [CertValidator.McCallSpec]. *)

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
  McOblDischarger
  McCallSpec.

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


(** *** 5.4 IR Call-Tree Execution, Argument Obligation Checking & Lockstep Soundness *)

Lemma eou_raise_ub_cfg_call_ub {Pa : Params} {R S : Type} (genv : raw_id -> @dvalue Pa) :
  forall sigma env msg (k : R -> @CFGtop Pa S),
    cfg_call_steps_to_ub genv sigma env (ITree.bind (EOU_to_itree (E := CFGEtop) (@raise_ub R msg)) k) [].
Proof.
  intros sigma env msg k; cbn [EOU_to_itree]; apply cfg_call_steps_to_ub_bind_l.
  eapply CCSU_UB; unfold raiseUB, trigger_cast', ITree.trigger; rewrite observe_bind; reflexivity.
Qed.

Lemma apply_attrs_scalar_step {Pa : Params} (genv : raw_id -> @dvalue Pa) :
  forall sigma env pas msg w (dv : @dvalue Pa),
    pattrs_no_value_poison pas = true ->
    wf_scalar_dvalue w dv ->
    (existsb attr_is_noundef pas = true /\ dv = DVALUE_Base DVALUE_Poison ->
     cfg_call_steps_to_ub genv sigma env (apply_attrs pas msg dv) []) /\
    ((existsb attr_is_noundef pas = false \/ dvalue_well_defined dv = true) ->
     pure_cfg_steps env (apply_attrs pas msg dv) env dv).
Proof.
  intros sigma env pas msg w dv Hnp Hsc.
  assert (Hnp_ptr : forall p, dv <> DVALUE_Base (DVALUE_Pointer p))
    by (intros p Heq; destruct Hsc as [H1 | [? H1]]; rewrite H1 in Heq; discriminate Heq).
  split.
  - intros [Hn Hd]; subst dv.
    unfold apply_attrs, apply_value_attrs; rewrite (pattrs_no_value_poison_value_attrs pas _ Hnp Hnp_ptr).
    rewrite Hn; cbn [dvalue_well_defined negb andb].
    apply cfg_call_steps_to_ub_bind_l; apply cfg_call_steps_to_ub_bind_l; cbn [EOU_to_itree].
    unfold trigger, ITree.trigger; eapply CCSU_UB; cbn; reflexivity.
  - intros Hnn.
    unfold apply_attrs, apply_value_attrs; rewrite (pattrs_no_value_poison_value_attrs pas dv Hnp Hnp_ptr).
    assert (Hb : existsb attr_is_noundef pas && negb (dvalue_well_defined dv) = false)
      by (destruct Hnn as [-> | ->]; [reflexivity | apply andb_false_r]).
    rewrite Hb; cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
    eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity |].
    rewrite (pattrs_no_value_poison_deref pas dv msg Hnp_ptr).
    eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | apply PCS_Ret; reflexivity].
Qed.

Lemma eval_reified_pure_exp_no_ub {Pa : Params} :
  forall allowed (penv : param_env Pa) lmap env o top w ce,
    wf_pure_lmap allowed lmap ->
    wf_param_env_for allowed penv ->
    lmap_matches_env penv lmap env ->
    reify_pure_exp lmap top o = Some (w, ce) ->
    ub_free_expr ce = true ->
    expr_has_freeze ce = false ->
    exists dv,
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv /\
      pure_mcfg_steps env (denote_exp top o) env dv.
Proof.
  intros allowed penv lmap env o top w ce Hlmap Hpenv Henv Hre Hub Hnf.
  destruct (reify_pure_exp_typing o allowed lmap top w ce Hlmap Hre) as (_ & Hwt & Hbw & Hlf & Hfv).
  destruct (ub_free_expr_eval_ret ce [] penv [] dummy_freeze_oracle Hub Hwt wf_let_val_env_nil
              (fun nm w0 Hin => Hpenv nm w0 (Hfv _ Hin)))
    as [dv0 [Hev0 _]].
  destruct (eval_reified_pure_exp o penv lmap env top w ce Henv Hre)
    as [[_ [msg Hub_e]] | (dv & Hev & Hsc & Hst)];
    [unfold eval_closed_cert_expr in *; congruence | exists dv; repeat split; assumption].
Qed.

Lemma denote_call_args_step {Pa : Params} (genv : raw_id -> @dvalue Pa) :
  forall cname arg_idx allowed (penv : param_env Pa) lmap env specs args aes msg,
    wf_pure_lmap allowed lmap ->
    wf_param_env_for allowed penv ->
    lmap_matches_env penv lmap env ->
    reify_ir_call_args cname arg_idx lmap specs args = inr aes ->
    (forall sigma, cfg_call_steps_to_ub genv sigma env (denote_call_args args msg) []) \/
    exists dvs,
      pure_cfg_steps env (denote_call_args args msg) env dvs /\
      Forall2 (fun '(need_def, w, ce) dv =>
        eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
        wf_scalar_dvalue w dv /\
        (need_def = false -> dvalue_well_defined dv = true)) aes dvs.
Proof.
  intros cname arg_idx allowed penv lmap env specs; revert arg_idx;
    induction specs as [| sp srest IH];
    intros arg_idx [| [[aty ae] pas] arest] aes msg Hlmap Hpenv Henv Hra;
    cbn [reify_ir_call_args] in Hra; try discriminate Hra.
  - inversion Hra; subst aes; right; exists []; split; [apply PCS_Ret; reflexivity | constructor].
  - destruct (dtyp_eqb aty (DTYPE_Base (DTYPE_I (ras_width sp)))) eqn:Hdt; cbn [negb] in Hra; [| discriminate Hra].
    destruct (pattrs_no_value_poison pas) eqn:Hnp; cbn [negb] in Hra; [| discriminate Hra].
    destruct (reify_pure_exp lmap (Some aty) ae) as [[w0 ce] |] eqn:Ere; [| discriminate Hra].
    destruct (ub_free_expr ce) eqn:Hub; cbn [negb] in Hra; [| discriminate Hra].
    destruct (expr_has_freeze ce) eqn:Hnf; [discriminate Hra |].
    destruct (reify_ir_call_args cname (S arg_idx) lmap srest arest) as [| rest] eqn:Hrr; [discriminate Hra |].
    inversion Hra; subst aes; clear Hra.
    pose proof (reify_pure_exp_top_width ae lmap (Some aty) w0 ce Ere) as Htw.
    unfold dtyp_eqb in Hdt; destruct (dtyp_eq_dec aty (DTYPE_Base (DTYPE_I (ras_width sp))));
      [| discriminate Hdt].
    subst aty; cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst w0.
    destruct (eval_reified_pure_exp_no_ub allowed penv lmap env ae (Some (DTYPE_Base (DTYPE_I (ras_width sp))))
                (ras_width sp) ce Hlmap Hpenv Henv Ere Hub Hnf)
      as (dv & Hev & Hsc & Hst).
    assert (Hsc_step : cfg_steps_to_ret default_draw_strat env (denote_exp' (Some (DTYPE_Base (DTYPE_I (ras_width sp)))) ae)
                         default_draw_strat env dv)
      by (apply mcfg_to_cfg_steps_ret; exact (pure_mcfg_to_mcfg_ret _ _ _ _ _ Hst)).
    cbn [denote_call_args map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    destruct (existsb attr_is_noundef pas) eqn:Enu; destruct Hsc as [-> | [iv ->]].
    + left; intro sigma.
      apply cfg_call_steps_to_ub_bind_l; change [] with ([] ++ @nil (@mc_call_event Pa)).
      eapply cfg_call_steps_to_ub_bind_r;
        [apply pure_cfg_steps_to_call_ret; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) |].
      destruct (apply_attrs_scalar_step genv sigma env pas msg (ras_width sp) (DVALUE_Base DVALUE_Poison) Hnp (or_introl eq_refl)) as [Hub_a _].
      exact (Hub_a (conj Enu eq_refl)).
    + destruct (apply_attrs_scalar_step genv default_draw_strat env pas msg (ras_width sp)
                  (DVALUE_Base (@DVALUE_I Pa (ras_width sp) iv)) Hnp (or_intror (ex_intro _ iv eq_refl)))
        as [_ Hret_a].
      destruct (IH (S arg_idx) arest rest msg Hlmap Hpenv Henv Hrr) as [Hub_r | (dvs_r & Hst_r & Hfa_r)].
      * left; intro sigma.
        change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ub_bind_r.
        -- change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind;
             [apply pure_cfg_steps_to_call_ret; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst)
             | apply pure_cfg_steps_to_call_ret; exact (Hret_a (or_intror eq_refl))].
        -- apply cfg_call_steps_to_ub_bind_l; exact (Hub_r sigma).
      * right; exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) iv) :: dvs_r); split.
        -- eapply pure_cfg_steps_bind;
             [eapply pure_cfg_steps_bind;
                [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) | exact (Hret_a (or_intror eq_refl))] |].
           eapply pure_cfg_steps_bind; [exact Hst_r | apply PCS_Ret; reflexivity].
        -- constructor; [| exact Hfa_r].
           split; [exact Hev | split; [right; exists iv; reflexivity | intro; reflexivity]].
    + destruct (apply_attrs_scalar_step genv default_draw_strat env pas msg (ras_width sp)
                  (DVALUE_Base DVALUE_Poison) Hnp (or_introl eq_refl)) as [_ Hret_a].
      destruct (IH (S arg_idx) arest rest msg Hlmap Hpenv Henv Hrr) as [Hub_r | (dvs_r & Hst_r & Hfa_r)].
      * left; intro sigma.
        change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ub_bind_r.
        -- change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind;
             [apply pure_cfg_steps_to_call_ret; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst)
             | apply pure_cfg_steps_to_call_ret; exact (Hret_a (or_introl Enu))].
        -- apply cfg_call_steps_to_ub_bind_l; exact (Hub_r sigma).
      * right; exists (DVALUE_Base DVALUE_Poison :: dvs_r); split.
        -- eapply pure_cfg_steps_bind;
             [eapply pure_cfg_steps_bind;
                [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) | exact (Hret_a (or_introl Enu))] |].
           eapply pure_cfg_steps_bind; [exact Hst_r | apply PCS_Ret; reflexivity].
        -- constructor; [| exact Hfa_r].
           split; [exact Hev | split; [left; reflexivity | intro C; discriminate C]].
    + destruct (apply_attrs_scalar_step genv default_draw_strat env pas msg (ras_width sp)
                  (DVALUE_Base (@DVALUE_I Pa (ras_width sp) iv)) Hnp (or_intror (ex_intro _ iv eq_refl)))
        as [_ Hret_a].
      destruct (IH (S arg_idx) arest rest msg Hlmap Hpenv Henv Hrr) as [Hub_r | (dvs_r & Hst_r & Hfa_r)].
      * left; intro sigma.
        change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ub_bind_r.
        -- change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind;
             [apply pure_cfg_steps_to_call_ret; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst)
             | apply pure_cfg_steps_to_call_ret; exact (Hret_a (or_intror eq_refl))].
        -- apply cfg_call_steps_to_ub_bind_l; exact (Hub_r sigma).
      * right; exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) iv) :: dvs_r); split.
        -- eapply pure_cfg_steps_bind;
             [eapply pure_cfg_steps_bind;
                [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) | exact (Hret_a (or_intror eq_refl))] |].
           eapply pure_cfg_steps_bind; [exact Hst_r | apply PCS_Ret; reflexivity].
        -- constructor; [| exact Hfa_r].
           split; [exact Hev | split; [right; exists iv; reflexivity | intro; reflexivity]].
Qed.

Lemma check_call_return_int_step {Pa : Params} (genv : raw_id -> @dvalue Pa) :
  forall sigma env fattrs ret_attrs loc args rw (v_ret : @Integers.bit_int rw),
    fattrs_call_ok fattrs = true ->
    pattrs_no_value_poison ret_attrs = true ->
    cfg_call_steps_to_ret genv sigma env
      (check_call_return (E := CFGEtop) fattrs ret_attrs None loc args
         (inr (DVALUE_Base (@DVALUE_I Pa rw v_ret))))
      [] sigma env (inr (DVALUE_Base (@DVALUE_I Pa rw v_ret))).
Proof.
  intros sigma env fattrs ret_attrs loc args rw v_ret Hfa Hra.
  unfold check_call_return, check_call_result.
  unfold fattrs_call_ok in Hfa; apply negb_true_iff in Hfa; rewrite Hfa.
  cbn [dvalue_well_defined negb andb].
  rewrite !andb_false_r.
  cbn [EOU_to_itree value_metadata_range ExtLib.Structures.Monad.ret Monad_itree].
  change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind; [apply CCSR_Ret; reflexivity |].
  destruct (apply_attrs_scalar_step genv sigma env ret_attrs (loc ++ " return value violates noundef.")%string
              rw (DVALUE_Base (@DVALUE_I Pa rw v_ret)) Hra (or_intror (ex_intro _ v_ret eq_refl)))
    as [_ Hret].
  change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ret_bind;
    [apply pure_cfg_steps_to_call_ret; exact (Hret (or_intror eq_refl)) | apply CCSR_Ret; reflexivity].
Qed.

Lemma build_call_arg_obls_from_length :
  forall cname arg_idx arch path specs ir_args mc_args64 obls,
    build_call_arg_obls_from cname arg_idx arch path specs ir_args mc_args64 = inr obls ->
    List.length ir_args = List.length specs /\
    List.length mc_args64 = List.length specs.
Proof.
  intros cname arg_idx arch path specs; revert arg_idx;
    induction specs as [| sp sr IH];
    intros arg_idx [| [[nd w] e] ir] [| m mr] obls Hbao;
    try (cbn [build_call_arg_obls_from build_call_arg_obls_acc] in Hbao; discriminate Hbao);
    [split; reflexivity |].
  rewrite build_call_arg_obls_from_cons in Hbao.
  destruct (Pos.eqb w (ras_width sp)); [| discriminate].
  destruct (build_call_arg_cmp cname arg_idx arch path sp w e m); [discriminate |].
  destruct (build_call_arg_obls_from cname (S arg_idx) arch path sr ir mr) as [| rest] eqn:Er;
    cbn [mcc_sum_map] in Hbao; [discriminate |].
  destruct (IH _ _ _ _ Er) as [H1 H2]; cbn; split; f_equal; assumption.
Qed.

Lemma build_call_arg_obls_length :
  forall cname arch path specs ir_args mc_args64 obls,
    build_call_arg_obls cname arch path specs ir_args mc_args64 = inr obls ->
    List.length ir_args = List.length specs /\
    List.length mc_args64 = List.length specs.
Proof.
  intros cname; exact (build_call_arg_obls_from_length cname 0%nat).
Qed.

Lemma rv_supported_arg_width_lt32 : forall w,
  rv_supported_arg_width w = true ->
  (w =? 64)%positive = false ->
  (w =? 32)%positive = false ->
  (w <? 32)%positive = true.
Proof.
  intros w Hs E64 E32; unfold rv_supported_arg_width in Hs.
  do 8 (destruct w as [w | w |]; try discriminate Hs; try discriminate E64; try discriminate E32; try reflexivity).
Qed.

Lemma rv_supported_to_is_supported : forall w,
  rv_supported_arg_width w = true -> is_supported_bit_width w = true.
Proof.
  intro w; unfold rv_supported_arg_width, is_supported_bit_width.
  do 8 (destruct w as [w | w |]; try discriminate; try reflexivity).
Qed.

Lemma build_call_arg_obls_rv64_matches {Pa : Params} :
  forall cname (penv : param_env Pa) (path : list (bool * cert_expr)) specs ir_args mc_args64 obls arg_vals vs_ir rf,
    (forall (b : bool) c, In (b, c) path ->
       eval_closed_cert_expr penv dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv dummy_freeze_oracle None false) obls ->
    build_call_arg_obls cname EA_Riscv64 path specs ir_args mc_args64 = inr obls ->
    Forall rv_valid_arg_spec specs ->
    NoDup (List.map ras_name specs) ->
    Forall2 (fun '(need_def, w, ce) dv =>
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv /\
      (need_def = false -> dvalue_well_defined dv = true)) ir_args vs_ir ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv dummy_freeze_oracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))) mc_args64 arg_vals ->
    arg_vals = List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf) (seq 0 (List.length specs)) ->
    rv_rf_matches_args (build_param_env (List.map ras_name specs) vs_ir) specs rf /\
    List.length vs_ir = List.length specs.
Proof.
  intros cname penv path specs ir_args mc_args64 obls arg_vals vs_ir rf
         Hpath Hobls Hbao Hvs Hnd Hfir Hfmc Harg_eq.
  assert (Hlen : List.length vs_ir = List.length specs)
    by (destruct (build_call_arg_obls_length _ _ _ _ _ _ _ Hbao) as [Hl1 _];
        pose proof (Forall2_length Hfir); congruence).
  split; [| exact Hlen].
  assert (Hitem : forall k sp v_mc,
    nth_error specs k = Some sp ->
    nth_error arg_vals k = Some v_mc ->
    exists v : @Integers.bit_int (ras_width sp),
      nth_error vs_ir k = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      v_mc =
        (if Pos.eqb (ras_width sp) 64%positive then
           @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
         else
           match ras_ext sp with
           | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
           | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
           end)).
  { clear Hnd Hlen Harg_eq.
    unfold build_call_arg_obls in Hbao; revert Hbao; generalize 0%nat as arg_idx.
    revert ir_args mc_args64 obls arg_vals vs_ir Hobls Hvs Hfir Hfmc.
    induction specs as [| sp0 srest IH]; intros ir_args mc_args64 ob0 avs vs0 Hob0 Hvs0 Hfi0 Hfm0 arg_idx Hb0 k sp v_mc Hsp0_n Hav_n;
      try (destruct k; discriminate Hsp0_n);
      destruct ir_args as [| [[nd0 w0] e0] irest]; destruct mc_args64 as [| m0 mrest];
      try (cbn [build_call_arg_obls_from build_call_arg_obls_acc] in Hb0; discriminate Hb0).
    rewrite build_call_arg_obls_from_cons in Hb0; cbn [build_call_arg_cmp] in Hb0.
    destruct (Pos.eqb w0 (ras_width sp0)) eqn:Epw; [apply Pos.eqb_eq in Epw; subst w0 | discriminate Hb0].
    destruct (build_call_arg_obls_from cname (S arg_idx) EA_Riscv64 path srest irest mrest) as [| rest_o] eqn:Erest;
      cbn [mcc_sum_map] in Hb0; [discriminate Hb0 |].
    inversion Hb0; subst ob0; clear Hb0.
    destruct avs as [| vm0 av_r]; [inversion Hfm0 |].
    destruct vs0 as [| dv0 vs_r]; [inversion Hfi0 |].
    inversion Hvs0 as [| ? ? Hsp0_v Hvs_r]; subst.
    inversion Hfi0 as [| ? ? ? ? Hp0 Hfi_r]; subst; destruct Hp0 as [Hev0 [Hsc0 Hnd0]].
    inversion Hfm0 as [| ? ? ? ? Hm0 Hfm_r]; subst.
    rewrite Forall_app in Hob0; destruct Hob0 as [Hrest_o Hhead0].
    assert (Hc0 : mc_obl_holds penv dummy_freeze_oracle None false
                    (MLO_Refine false path 64%positive (build_rv_call_arg_expr (ras_width sp0) (ras_ext sp0) e0) m0)).
    { destruct nd0; [inversion Hhead0 as [| ? ? _ Htl]; inversion Htl; assumption | inversion Hhead0; assumption]. }
    destruct k as [| k']; cbn in Hsp0_n, Hav_n.
    - inversion Hsp0_n; subst sp0; inversion Hav_n; subst vm0; clear Hsp0_n Hav_n.
      assert (Hwd0 : dvalue_well_defined dv0 = true).
      { destruct nd0; [| exact (Hnd0 eq_refl)].
        inversion Hhead0 as [| ? ? Hd _]; subst.
        pose proof (Hd eq_refl ltac:(discriminate) Hpath) as [v Hv1].
        unfold eval_closed_cert_expr in *; rewrite Hev0 in Hv1; inversion Hv1; reflexivity. }
      destruct Hsc0 as [Hbad | [iv ->]]; [rewrite Hbad in Hwd0; discriminate Hwd0 |].
      pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href.
      unfold refine_eou_dvalue, dvalue_refines, build_rv_call_arg_expr in Href.
      exists iv; split; [reflexivity |].
      destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
      + apply Pos.eqb_eq in Ew64; generalize iv Hev0 Href; rewrite Ew64; intros iv64 Hev64 Href64.
        rewrite Hev64, Hm0 in Href64; cbn in Href64.
        destruct Href64 as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; symmetry in Heq; subst; rewrite (@Integers.repr_unsigned 64%positive); reflexivity].
      + assert (Hltb : (ras_width sp <? 64)%positive = true).
        { apply Pos.ltb_lt; unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _].
          apply rv_supported_arg_width_lt64 in Ew64; [apply Pos.ltb_lt; exact Ew64 | exact Hsup]. }
        destruct (ras_ext sp).
        * erewrite eval_ce_sext in Href by (first [exact Hltb | exact Hev0]).
          rewrite Hm0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
        * erewrite eval_ce_sext in Href by (first [exact Hltb | exact Hev0]).
          rewrite Hm0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
        * erewrite eval_ce_zext in Href by (first [exact Hltb | exact Hev0]).
          rewrite Hm0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
    - exact (IH irest mrest rest_o av_r vs_r Hrest_o Hvs_r Hfi_r Hfm_r (S arg_idx) Erest k' sp v_mc Hsp0_n Hav_n). }
  intros k sp Hkl Hsp_n.
  assert (Hnth_av : nth_error arg_vals k = Some (rv_read_reg (10%N + N.of_nat k) rf)).
  { rewrite Harg_eq, nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hkl as Hltb_k; rewrite Hltb_k; cbn [option_map Nat.add]; reflexivity. }
  destruct (Hitem k sp _ Hsp_n Hnth_av) as (v & Hvs_n & Hvmc).
  exists v; split; [| rewrite <- Hvmc; reflexivity].
  destruct (build_param_env_nth (List.map ras_name specs) vs_ir k (ras_name sp) Hnd) as [dv [Hdv Hbp]].
  - rewrite List.length_map; symmetry; exact Hlen.
  - erewrite nth_error_map, Hsp_n; reflexivity.
  - rewrite Hvs_n in Hdv; inversion Hdv; subst dv; exact Hbp.
Qed.

Lemma build_call_arg_obls_a64_matches {Pa : Params} :
  forall cname (penv : param_env Pa) (path : list (bool * cert_expr)) specs ir_args mc_args64 obls arg_vals vs_ir rf,
    (forall (b : bool) c, In (b, c) path ->
       eval_closed_cert_expr penv dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv dummy_freeze_oracle None false) obls ->
    build_call_arg_obls cname EA_AArch64 path specs ir_args mc_args64 = inr obls ->
    Forall rv_valid_arg_spec specs ->
    NoDup (List.map ras_name specs) ->
    Forall2 (fun '(need_def, w, ce) dv =>
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv /\
      (need_def = false -> dvalue_well_defined dv = true)) ir_args vs_ir ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv dummy_freeze_oracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))) mc_args64 arg_vals ->
    arg_vals = List.map (fun j => a64_read_reg (N.of_nat j) rf) (seq 0 (List.length specs)) ->
    a64_rf_matches_args (build_param_env (List.map ras_name specs) vs_ir) specs rf /\
    List.length vs_ir = List.length specs.
Proof.
  intros cname penv path specs ir_args mc_args64 obls arg_vals vs_ir rf
         Hpath Hobls Hbao Hvs Hnd Hfir Hfmc Harg_eq.
  assert (Hlen : List.length vs_ir = List.length specs)
    by (destruct (build_call_arg_obls_length _ _ _ _ _ _ _ Hbao) as [Hl1 _];
        pose proof (Forall2_length Hfir); congruence).
  split; [| exact Hlen].
  assert (Hitem : forall k sp v_mc,
    nth_error specs k = Some sp ->
    nth_error arg_vals k = Some v_mc ->
    exists v : @Integers.bit_int (ras_width sp),
      nth_error vs_ir k = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
      | true, RAE_None =>
          v_mc = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
      | false, RAE_None =>
          @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive v_mc) = v
      | false, RAE_SignExt =>
          @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
          @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
      | false, RAE_ZeroExt =>
          @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
          @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
      | _, _ => False
      end).
  { clear Hnd Hlen Harg_eq.
    unfold build_call_arg_obls in Hbao; revert Hbao; generalize 0%nat as arg_idx.
    revert ir_args mc_args64 obls arg_vals vs_ir Hobls Hvs Hfir Hfmc.
    induction specs as [| sp0 srest IH]; intros ir_args mc_args64 ob0 avs vs0 Hob0 Hvs0 Hfi0 Hfm0 arg_idx Hb0 k sp v_mc Hsp0_n Hav_n;
      try (destruct k; discriminate Hsp0_n);
      destruct ir_args as [| [[nd0 w0] e0] irest]; destruct mc_args64 as [| m0 mrest];
      try (cbn [build_call_arg_obls_from build_call_arg_obls_acc] in Hb0; discriminate Hb0).
    rewrite build_call_arg_obls_from_cons in Hb0; cbn [build_call_arg_cmp] in Hb0.
    destruct (Pos.eqb w0 (ras_width sp0)) eqn:Epw; [apply Pos.eqb_eq in Epw; subst w0 | discriminate Hb0].
    match type of Hb0 with
    | context [match ?x with inl _ => _ | inr _ => _ end] => destruct x as [| cmp0] eqn:Ecmp0; [discriminate Hb0 |]
    end.
    destruct (build_call_arg_obls_from cname (S arg_idx) EA_AArch64 path srest irest mrest) as [| rest_o] eqn:Erest;
      cbn [mcc_sum_map] in Hb0; [discriminate Hb0 |].
    inversion Hb0; subst ob0; clear Hb0.
    destruct avs as [| vm0 av_r]; [inversion Hfm0 |].
    destruct vs0 as [| dv0 vs_r]; [inversion Hfi0 |].
    inversion Hvs0 as [| ? ? Hsp0_v Hvs_r]; subst.
    inversion Hfi0 as [| ? ? ? ? Hp0 Hfi_r]; subst; destruct Hp0 as [Hev0 [Hsc0 Hnd0]].
    inversion Hfm0 as [| ? ? ? ? Hm0 Hfm_r]; subst.
    rewrite Forall_app in Hob0; destruct Hob0 as [Hrest_o Hhead0].
    assert (Hcmp0 : Forall (mc_obl_holds penv dummy_freeze_oracle None false) [cmp0])
      by (destruct nd0; [inversion Hhead0; assumption | exact Hhead0]).
    destruct k as [| k']; cbn in Hsp0_n, Hav_n.
    - inversion Hsp0_n; subst sp0; inversion Hav_n; subst vm0; clear Hsp0_n Hav_n.
      assert (Hwd0 : dvalue_well_defined dv0 = true).
      { destruct nd0; [| exact (Hnd0 eq_refl)].
        inversion Hhead0 as [| ? ? Hd _]; subst.
        pose proof (Hd eq_refl ltac:(discriminate) Hpath) as [v Hv1].
        unfold eval_closed_cert_expr in *; rewrite Hev0 in Hv1; inversion Hv1; reflexivity. }
      destruct Hsc0 as [Hbad | [iv ->]]; [rewrite Hbad in Hwd0; discriminate Hwd0 |].
      exists iv; split; [reflexivity |].
      destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
      + destruct (ras_ext sp); inversion Ecmp0; subst cmp0; clear Ecmp0.
        inversion Hcmp0 as [| ? ? Hc0 _]; subst.
        pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href.
        unfold refine_eou_dvalue, dvalue_refines in Href.
        apply Pos.eqb_eq in Ew64; generalize iv Hev0 Href; rewrite Ew64; intros iv64 Hev64 Href64; rewrite Hev64, Hm0 in Href64.
        cbn in Href64; destruct Href64 as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; symmetry in Heq; subst].
        rewrite (@Integers.repr_unsigned 64%positive); reflexivity.
      + assert (Hltb : (ras_width sp <? 64)%positive = true).
        { apply Pos.ltb_lt; unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _].
          apply rv_supported_arg_width_lt64 in Ew64; [apply Pos.ltb_lt; exact Ew64 | exact Hsup]. }
        destruct (ras_ext sp) eqn:Eext; inversion Ecmp0; subst cmp0; clear Ecmp0;
          inversion Hcmp0 as [| ? ? Hc0 _]; subst;
          pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href;
          unfold refine_eou_dvalue, dvalue_refines in Href.
        * erewrite eval_ce_trunc in Href by (first [exact Hltb | exact Hm0]).
          rewrite Hev0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
        * erewrite eval_ce_trunc in Href by (first [reflexivity | exact Hm0]).
          destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
          -- apply Pos.eqb_eq in Ew32; generalize iv Href Hev0; rewrite Ew32; intros iv' Href' Hev0'.
             rewrite Hev0' in Href'; cbn in Href'; destruct Href' as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; subst iv'].
             rewrite (@Integers.repr_signed 32%positive); reflexivity.
          -- assert (Hlt32 : (ras_width sp <? 32)%positive = true)
               by (unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _];
                   exact (rv_supported_arg_width_lt32 _ Hsup Ew64 Ew32)).
             erewrite eval_ce_sext in Href by (first [exact Hlt32 | exact Hev0]).
             cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
        * erewrite eval_ce_trunc in Href by (first [reflexivity | exact Hm0]).
          destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
          -- apply Pos.eqb_eq in Ew32; generalize iv Href Hev0; rewrite Ew32; intros iv' Href' Hev0'.
             rewrite Hev0' in Href'; cbn in Href'; destruct Href' as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; subst iv'].
             rewrite (@Integers.repr_unsigned 32%positive); reflexivity.
          -- assert (Hlt32 : (ras_width sp <? 32)%positive = true)
               by (unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _];
                   exact (rv_supported_arg_width_lt32 _ Hsup Ew64 Ew32)).
             erewrite eval_ce_zext in Href by (first [exact Hlt32 | exact Hev0]).
             cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
    - exact (IH irest mrest rest_o av_r vs_r Hrest_o Hvs_r Hfi_r Hfm_r (S arg_idx) Erest k' sp v_mc Hsp0_n Hav_n). }
  intros k sp Hkl Hsp_n.
  assert (Hnth_av : nth_error arg_vals k = Some (a64_read_reg (N.of_nat k) rf)).
  { rewrite Harg_eq, nth_error_map, nth_error_seq; apply Nat.ltb_lt in Hkl as Hltb_k; rewrite Hltb_k; cbn [option_map Nat.add]; reflexivity. }
  destruct (Hitem k sp _ Hsp_n Hnth_av) as (v & Hvs_n & Hvmc).
  exists v; split; [| exact Hvmc].
  destruct (build_param_env_nth (List.map ras_name specs) vs_ir k (ras_name sp) Hnd) as [dv [Hdv Hbp]].
  - rewrite List.length_map; symmetry; exact Hlen.
  - erewrite nth_error_map, Hsp_n; reflexivity.
  - rewrite Hvs_n in Hdv; inversion Hdv; subst dv; exact Hbp.
Qed.

Section IrTreeDenote.
  Context {Pa : Params}.

  Fixpoint ir_tree_denotes
    (genv : raw_id -> @dvalue Pa) (penv : param_env Pa) (ret_w : positive)
    (env : rmap (@dvalue Pa)) (it_prog : @CFGtop Pa (@dvalue Pa)) (t : ir_call_tree)
    {struct t} : Prop :=
    match t with
    | ICT_UB =>
        forall sigma, cfg_call_steps_to_ub genv sigma env it_prog []
    | ICT_Ret rw ret_e =>
        rw = ret_w /\
        exists env_out dv_ir,
          eval_closed_cert_expr penv dummy_freeze_oracle ret_e = raise_ret dv_ir /\
          wf_scalar_dvalue ret_w dv_ir /\
          forall sigma, cfg_call_steps_to_ret genv sigma env it_prog [] sigma env_out dv_ir
    | ICT_Branch cond dt df =>
        (eval_closed_cert_expr penv dummy_freeze_oracle cond = raise_ret (DVALUE_Base DVALUE_Poison) /\
         forall sigma, cfg_call_steps_to_ub genv sigma env it_prog []) \/
        (exists b : bool,
           eval_closed_cert_expr penv dummy_freeze_oracle cond =
             raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
           ir_tree_denotes genv penv ret_w env it_prog (if b then dt else df))
    | ICT_Call cname arg_es rw rv cont =>
        (forall sigma, cfg_call_steps_to_ub genv sigma env it_prog []) \/
        exists dvs,
          Forall2 (fun '(nd, w, ce) dv =>
            eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
            wf_scalar_dvalue w dv /\
            (nd = false -> dvalue_well_defined dv = true)) arg_es dvs /\
          forall (v_ret : @Integers.bit_int rw),
            penv rv = Some (DVALUE_Base (@DVALUE_I Pa rw v_ret)) ->
            let dv_ret := DVALUE_Base (@DVALUE_I Pa rw v_ret) in
            exists env1 t1,
              (forall sigma tr_r s' env' r,
                 cfg_call_steps_to_ret genv sigma env1 t1 tr_r s' env' r ->
                 cfg_call_steps_to_ret genv sigma env it_prog ((cname, dvs, dv_ret) :: tr_r) s' env' r) /\
              (forall sigma tr_r,
                 cfg_call_steps_to_ub genv sigma env1 t1 tr_r ->
                 cfg_call_steps_to_ub genv sigma env it_prog ((cname, dvs, dv_ret) :: tr_r)) /\
              ir_tree_denotes genv penv ret_w env1 t1 cont
    end.

  Lemma ir_tree_denotes_prepend_tau_pure :
    forall genv penv ret_w t env0 env1 t0 t1,
      (forall sigma tr s' env' r,
         cfg_call_steps_to_ret genv sigma env1 t1 tr s' env' r ->
         cfg_call_steps_to_ret genv sigma env0 t0 tr s' env' r) ->
      (forall sigma tr,
         cfg_call_steps_to_ub genv sigma env1 t1 tr ->
         cfg_call_steps_to_ub genv sigma env0 t0 tr) ->
      ir_tree_denotes genv penv ret_w env1 t1 t ->
      ir_tree_denotes genv penv ret_w env0 t0 t.
  Proof.
    intros genv penv ret_w t; induction t as [rw ret_e | | cond dt IHt df IHf | cname aes rw rv cont IH];
      intros env0 env1 t0 t1 Hret Hub Hd; cbn [ir_tree_denotes] in *.
    - destruct Hd as [-> (env_out & dv & Hev & Hsc & Hst)]; split; [reflexivity |].
      exists env_out, dv; repeat split; try assumption; intro sigma; exact (Hret _ _ _ _ _ (Hst sigma)).
    - intro sigma; exact (Hub sigma [] (Hd sigma)).
    - destruct Hd as [[Hp Hubc] | [b [Hev Hb]]].
      + left; split; [exact Hp | intro sigma; exact (Hub sigma [] (Hubc sigma))].
      + right; exists b; split; [exact Hev |].
        destruct b; [exact (IHt _ _ _ _ Hret Hub Hb) | exact (IHf _ _ _ _ Hret Hub Hb)].
    - destruct Hd as [Hubc | (dvs & Hfa & Hk)].
      + left; intro sigma; exact (Hub sigma [] (Hubc sigma)).
      + right; exists dvs; split; [exact Hfa |].
        intros v_ret Hrv; destruct (Hk v_ret Hrv) as (env2 & t2 & Hret2 & Hub2 & Hd2).
        exists env2, t2; repeat split; try assumption.
        * intros sigma tr_r s' env' r Hs; exact (Hret _ _ _ _ _ (Hret2 _ _ _ _ _ Hs)).
        * intros sigma tr_r Hs; exact (Hub _ _ (Hub2 _ _ Hs)).
  Qed.

  Lemma pure_cfg_steps_prepend_bind {R S : Type} :
    forall genv env0 env1 (p : @CFGtop Pa R) (k : R -> @CFGtop Pa S) x,
      pure_cfg_steps env0 p env1 x ->
      (forall sigma tr s' env' r,
         cfg_call_steps_to_ret genv sigma env1 (k x) tr s' env' r ->
         cfg_call_steps_to_ret genv sigma env0 (ITree.bind p k) tr s' env' r) /\
      (forall sigma tr,
         cfg_call_steps_to_ub genv sigma env1 (k x) tr ->
         cfg_call_steps_to_ub genv sigma env0 (ITree.bind p k) tr).
  Proof.
    intros genv env0 env1 p k x Hp; split.
    - intros sigma tr s' env' r Hs; change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_bind;
        [exact (pure_cfg_steps_to_call_ret genv sigma _ _ _ _ Hp) | exact Hs].
    - intros sigma tr Hs; change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_bind_r;
        [exact (pure_cfg_steps_to_call_ret genv sigma _ _ _ _ Hp) | exact Hs].
  Qed.

  Inductive cfg_bind_ctxt : Type -> Type -> Type :=
  | CBC_Id {A : Type} : cfg_bind_ctxt A A
  | CBC_Bind {A B C : Type} : (A -> @CFGtop Pa B) -> cfg_bind_ctxt B C -> cfg_bind_ctxt A C.

  Fixpoint apply_cfg_ctxt {A B : Type} (ctx : cfg_bind_ctxt A B) (t : @CFGtop Pa A) : @CFGtop Pa B :=
    match ctx in cfg_bind_ctxt X Y return @CFGtop Pa X -> @CFGtop Pa Y with
    | @CBC_Id _ => fun t0 => t0
    | @CBC_Bind _ _ _ k rest => fun t0 => apply_cfg_ctxt rest (ITree.bind t0 k)
    end t.

  Lemma apply_cfg_ctxt_obs :
    forall A B (ctx : cfg_bind_ctxt A B) (t1 t2 : @CFGtop Pa A),
      observe t1 = observe t2 ->
      observe (apply_cfg_ctxt ctx t1) = observe (apply_cfg_ctxt ctx t2).
  Proof.
    intros A B ctx; induction ctx as [A | A B C k rest IH]; intros t1 t2 Hobs; cbn [apply_cfg_ctxt].
    - exact Hobs.
    - apply IH; rewrite !observe_bind, Hobs; reflexivity.
  Qed.

  Lemma apply_cfg_ctxt_tau :
    forall A B (ctx : cfg_bind_ctxt A B) (p p' : @CFGtop Pa A),
      observe p = TauF p' ->
      observe (apply_cfg_ctxt ctx p) = TauF (apply_cfg_ctxt ctx p').
  Proof.
    intros A B ctx; induction ctx as [A | A B C k rest IH]; intros p p' H; cbn [apply_cfg_ctxt];
      [exact H | apply IH; rewrite observe_bind, H; reflexivity].
  Qed.

  Lemma apply_cfg_ctxt_vis :
    forall A B X (ctx : cfg_bind_ctxt A B) (p : @CFGtop Pa A) (e : CFGEtop X) (k : X -> @CFGtop Pa A),
      observe p = VisF e k ->
      observe (apply_cfg_ctxt ctx p) = VisF e (fun a => apply_cfg_ctxt ctx (k a)).
  Proof.
    intros A B X ctx; revert X; induction ctx as [A | A B C k0 rest IH]; intros X p e k H; cbn [apply_cfg_ctxt];
      [exact H | apply IH; rewrite observe_bind, H; reflexivity].
  Qed.

  Lemma cfg_call_steps_to_ret_ctxt_bind {R S T : Type} (genv : raw_id -> @dvalue Pa) :
    forall (ctx : cfg_bind_ctxt S T) s0 env0 (p : @CFGtop Pa R) tr0 s1 env1 x
           (k : R -> @CFGtop Pa S) tr1 s2 env2 z,
      cfg_call_steps_to_ret genv s0 env0 p tr0 s1 env1 x ->
      cfg_call_steps_to_ret genv s1 env1 (apply_cfg_ctxt ctx (k x)) tr1 s2 env2 z ->
      cfg_call_steps_to_ret genv s0 env0 (apply_cfg_ctxt ctx (ITree.bind p k)) (tr0 ++ tr1) s2 env2 z.
  Proof.
    intros ctx s0 env0 p tr0 s1 env1 x k tr1 s2 env2 z Hp; revert tr1 s2 env2 z;
      induction Hp; intros tr1 s2' env2' z Hcont; cbn [app] in *.
    - eapply cfg_call_steps_to_ret_obs;
        [symmetry; apply apply_cfg_ctxt_obs; rewrite observe_bind, H; reflexivity | exact Hcont].
    - eapply CCSR_Tau;
        [apply apply_cfg_ctxt_tau; rewrite observe_bind, H; reflexivity | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_LocalRead;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_LocalWrite;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_Draw;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_PureIntrinsic;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact H1 | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_GlobalRead;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact (IHHp _ _ _ _ Hcont)].
    - eapply CCSR_Call;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ _ _ _ Hcont)].
  Qed.

  Lemma cfg_call_steps_to_ub_ctxt_bind_r {R S T : Type} (genv : raw_id -> @dvalue Pa) :
    forall (ctx : cfg_bind_ctxt S T) s0 env0 (p : @CFGtop Pa R) tr0 s1 env1 x
           (k : R -> @CFGtop Pa S) tr1,
      cfg_call_steps_to_ret genv s0 env0 p tr0 s1 env1 x ->
      cfg_call_steps_to_ub genv s1 env1 (apply_cfg_ctxt ctx (k x)) tr1 ->
      cfg_call_steps_to_ub genv s0 env0 (apply_cfg_ctxt ctx (ITree.bind p k)) (tr0 ++ tr1).
  Proof.
    intros ctx s0 env0 p tr0 s1 env1 x k tr1 Hp; revert tr1;
      induction Hp; intros tr1 Hcont; cbn [app] in *.
    - eapply cfg_call_steps_to_ub_obs;
        [symmetry; apply apply_cfg_ctxt_obs; rewrite observe_bind, H; reflexivity | exact Hcont].
    - eapply CCSU_Tau;
        [apply apply_cfg_ctxt_tau; rewrite observe_bind, H; reflexivity | exact (IHHp _ Hcont)].
    - eapply CCSU_LocalRead;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ Hcont)].
    - eapply CCSU_LocalWrite;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact (IHHp _ Hcont)].
    - eapply CCSU_Draw;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ Hcont)].
    - eapply CCSU_PureIntrinsic;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact H1 | exact (IHHp _ Hcont)].
    - eapply CCSU_GlobalRead;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact (IHHp _ Hcont)].
    - eapply CCSU_Call;
        [apply apply_cfg_ctxt_vis; rewrite observe_bind, H; reflexivity | exact H0 | exact (IHHp _ Hcont)].
  Qed.

  Lemma cfg_call_steps_to_ub_ctxt {R T : Type} (genv : raw_id -> @dvalue Pa) :
    forall (ctx : cfg_bind_ctxt R T) s0 env0 (p : @CFGtop Pa R) tr,
      cfg_call_steps_to_ub genv s0 env0 p tr ->
      cfg_call_steps_to_ub genv s0 env0 (apply_cfg_ctxt ctx p) tr.
  Proof.
    intros ctx s0 env0 p tr Hub; induction Hub.
    - eapply CCSU_UB; apply apply_cfg_ctxt_vis; exact H.
    - eapply CCSU_Tau; [apply apply_cfg_ctxt_tau; exact H | exact IHHub].
    - eapply CCSU_LocalRead; [apply apply_cfg_ctxt_vis; exact H | exact H0 | exact IHHub].
    - eapply CCSU_LocalWrite; [apply apply_cfg_ctxt_vis; exact H | exact IHHub].
    - eapply CCSU_Draw; [apply apply_cfg_ctxt_vis; exact H | exact H0 | exact IHHub].
    - eapply CCSU_PureIntrinsic; [apply apply_cfg_ctxt_vis; exact H | exact H0 | exact H1 | exact IHHub].
    - eapply CCSU_GlobalRead; [apply apply_cfg_ctxt_vis; exact H | exact IHHub].
    - eapply CCSU_Call; [apply apply_cfg_ctxt_vis; exact H | exact H0 | exact IHHub].
  Qed.

End IrTreeDenote.

Lemma reify_ir_code_calls_exec {Pa : Params} :
  forall cur_bid (genv : raw_id -> @dvalue Pa) (penv : param_env Pa)
         callees c cid allowed lmap env ret_w k_end t
         (ctx : cfg_bind_ctxt unit (@dvalue Pa)),
    wf_pure_lmap allowed lmap ->
    wf_param_env_for allowed penv ->
    lmap_matches_env penv lmap env ->
    (forall cid' allowed' lmap' env' t',
       incl allowed allowed' ->
       wf_pure_lmap allowed' lmap' ->
       wf_param_env_for allowed' penv ->
       lmap_matches_env penv lmap' env' ->
       k_end cid' lmap' = inr t' ->
       ir_tree_denotes genv penv ret_w env' (apply_cfg_ctxt ctx (Ret tt)) t') ->
    reify_ir_code_calls cur_bid callees c cid lmap k_end = inr t ->
    ir_tree_denotes genv penv ret_w env (apply_cfg_ctxt ctx (denote_code c None)) t.
Proof.
  intros cur_bid genv penv callees c; induction c as [| [[iid ins] md] rest IH];
    intros cid allowed lmap env ret_w k_end t ctx Hlmap Hpenv Henv Hk Hrc;
    cbn [reify_ir_code_calls] in Hrc.
  - eapply ir_tree_denotes_prepend_tau_pure with (env1 := env) (t1 := apply_cfg_ctxt ctx (Ret tt)).
    + intros sigma tr s' env' r Hs; unfold denote_code; cbn; eapply cfg_call_steps_to_ret_obs;
        [symmetry; apply apply_cfg_ctxt_obs; reflexivity | exact Hs].
    + intros sigma tr Hs; unfold denote_code; cbn; eapply cfg_call_steps_to_ub_obs;
        [symmetry; apply apply_cfg_ctxt_obs; reflexivity | exact Hs].
    + exact (Hk cid allowed lmap env t (incl_refl _) Hlmap Hpenv Henv Hrc).
  - destruct iid as [id | vid].
    + destruct ins; try discriminate Hrc.
      * destruct (reify_pure_exp lmap None op) as [[w ce] |] eqn:Ere; [| discriminate Hrc].
        destruct (ub_free_expr ce) eqn:Hub; cbn [negb] in Hrc; [| discriminate Hrc].
        destruct (expr_has_freeze ce) eqn:Hnf; [discriminate Hrc |].
        destruct (reify_pure_exp_typing op allowed lmap None w ce Hlmap Ere) as (_ & Hwt & Hbw & Hlf & Hfv).
        destruct (eval_reified_pure_exp_no_ub allowed penv lmap env op None w ce Hlmap Hpenv Henv Ere Hub Hnf)
          as (dv & Hev & Hsc & Hst).
        pose proof (lmap_matches_env_add penv lmap env id w ce dv Henv Hev Hsc) as Henv1.
        pose proof (wf_pure_lmap_add allowed lmap id w ce Hlmap Hwt Hbw Hlf Hfv) as Hlmap1.
        specialize (IH cid allowed (RM.add id (w, ce) lmap) (RM.add id dv env) ret_w k_end t ctx
                      Hlmap1 Hpenv Henv1 Hk Hrc).
        assert (Hpref : pure_cfg_steps env (denote_instr (IId id, INSTR_Op op, md) None) (RM.add id dv env) tt).
        { cbn [denote_instr]; unfold denote_exp'.
          eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst) |].
          eapply pure_cfg_steps_bind; [apply pure_cfg_steps_lwrite | apply PCS_Ret; reflexivity]. }
        eapply ir_tree_denotes_prepend_tau_pure with (env1 := RM.add id dv env)
          (t1 := apply_cfg_ctxt ctx (denote_code rest None)); [| | exact IH].
        -- intros sigma tr s' env' r Hs; unfold denote_code; cbn [loop_monad].
           change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind;
             [apply pure_cfg_steps_to_call_ret; exact Hpref | exact Hs].
        -- intros sigma tr Hs; unfold denote_code; cbn [loop_monad].
           change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r;
             [apply pure_cfg_steps_to_call_ret; exact Hpref | exact Hs].
      * destruct (match_pure_int_intrinsic_call (INSTR_Call fn args anns obs)) as [pic |] eqn:Epic.
        -- pose proof (match_pure_int_intrinsic_call_inv _ _ Epic) as Hinv.
           destruct pic as [op w a0 a1 | w a0 flag]; destruct fn as [dt_fn fn_e].
           ++ destruct (match metadata_range md with None => true | Some _ => false end) eqn:Emr; cbn [negb] in Hrc; [| discriminate Hrc].
              assert (Hmr_none : metadata_range md = None) by (destruct (metadata_range md); [discriminate | reflexivity]).
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a0) as [[wa ca] |] eqn:Ea0; [| discriminate Hrc].
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a1) as [[wb cb] |] eqn:Ea1; [| discriminate Hrc].
              destruct (ub_free_expr ca && ub_free_expr cb) eqn:Eub; cbn [negb] in Hrc; [| discriminate Hrc].
              destruct (expr_has_freeze ca || expr_has_freeze cb) eqn:Efr; [discriminate Hrc |].
              apply andb_true_iff in Eub as [Huba Hubb].
              apply orb_false_iff in Efr as [Hnfa Hnfb].
              destruct (reify_pure_exp_typing a0 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Hlmap Ea0)
                as (_ & Hwt0 & Hbw0 & Hlf0 & Hfv0).
              pose proof (reify_pure_exp_top_width a0 lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Ea0) as Htw0.
              cbn [check_opt_int_width] in Htw0; apply Pos.eqb_eq in Htw0; subst wa; rewrite Htw0 in Ea0.
              destruct (reify_pure_exp_typing a1 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wb cb Hlmap Ea1)
                as (_ & Hwt1 & Hbw1 & Hlf1 & Hfv1).
              pose proof (reify_pure_exp_top_width a1 lmap (Some (DTYPE_Base (DTYPE_I w))) wb cb Ea1) as Htw1.
              cbn [check_opt_int_width] in Htw1; apply Pos.eqb_eq in Htw1; subst wb; rewrite Htw1 in Ea1.
              destruct (eval_reified_pure_exp_no_ub allowed penv lmap env a0 (Some (DTYPE_Base (DTYPE_I w))) w ca Hlmap Hpenv Henv Ea0 Huba Hnfa)
                as (dv0 & Hev0 & Hsc0 & Hst0).
              destruct (eval_reified_pure_exp_no_ub allowed penv lmap env a1 (Some (DTYPE_Base (DTYPE_I w))) w cb Hlmap Hpenv Henv Ea1 Hubb Hnfb)
                as (dv1 & Hev1 & Hsc1 & Hst1).
              destruct fn_e; try contradiction Hinv; destruct id0 as [[fname | | ] | ?]; try contradiction Hinv;
                destruct obs; try contradiction Hinv;
                destruct Hinv as (Hdt & Hpars & Hnop & Hargs & Hfa & Hra).
              destruct (pure_int_intrinsic_binop_eval_helpers op w ca cb penv dummy_freeze_oracle dv0 dv1 Hnop Hsc0 Hsc1 Hev0 Hev1)
                as (dv_out & Hpi & Hev_out & Hsc_out).
              destruct (lower_pure_int_intrinsic_binop_typing op w ca cb
                          Hwt0 Htw0 Hlf0 (expr_has_freeze_false_collect_keys _ Hnfa)
                          Hwt1 Htw1 Hlf1 (expr_has_freeze_false_collect_keys _ Hnfb))
                as (Hwt & Hbw & Hlf & _ & Hfv_sub).
              assert (Hfv : incl (collect_free_vars [] (lower_pure_int_intrinsic_binop op w ca cb)) allowed)
                by (intros x Hx; apply Hfv_sub, in_app_iff in Hx as [Hx | Hx]; [exact (Hfv0 _ Hx) | exact (Hfv1 _ Hx)]).
              pose proof (wf_pure_lmap_add allowed lmap id w (lower_pure_int_intrinsic_binop op w ca cb) Hlmap Hwt Hbw Hlf Hfv) as Hlmap1.
              pose proof (lmap_matches_env_add penv lmap env id w (lower_pure_int_intrinsic_binop op w ca cb) dv_out Henv Hev_out Hsc_out) as Henv1.
              specialize (IH cid allowed (RM.add id (w, lower_pure_int_intrinsic_binop op w ca cb) lmap)
                            (RM.add id dv_out env) ret_w k_end t ctx Hlmap1 Hpenv Henv1 Hk Hrc).
              eapply ir_tree_denotes_prepend_tau_pure with (env1 := RM.add id dv_out env)
                (t1 := apply_cfg_ctxt ctx (denote_code rest None)); [| | exact IH].
               ** intros sigma tr s' env' r Hs; unfold denote_code; cbn [loop_monad].
                  change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind;
                    [apply cfg_steps_to_call_ret;
                     exact (@cfg_steps_pure_int_intrinsic_binop_ret Pa sigma sigma sigma
                              env id dt_fn (EXP_Ident (ID_Global (Name fname))) args anns md fname op w a0 a1 dv0 dv1 dv_out None
                              eq_refl Hpars Hargs Hfa Hra Hmr_none
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst0)
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1)
                              Hpi)
                    | exact Hs].
               ** intros sigma tr Hs; unfold denote_code; cbn [loop_monad].
                  change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r;
                    [apply cfg_steps_to_call_ret;
                     exact (@cfg_steps_pure_int_intrinsic_binop_ret Pa sigma sigma sigma
                              env id dt_fn (EXP_Ident (ID_Global (Name fname))) args anns md fname op w a0 a1 dv0 dv1 dv_out None
                              eq_refl Hpars Hargs Hfa Hra Hmr_none
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst0)
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1)
                              Hpi)
                    | exact Hs].
           ++ destruct (match metadata_range md with None => true | Some _ => false end) eqn:Emr; cbn [negb] in Hrc; [| discriminate Hrc].
              assert (Hmr_none : metadata_range md = None) by (destruct (metadata_range md); [discriminate | reflexivity]).
              destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) a0) as [[wa ca] |] eqn:Ea0; [| discriminate Hrc].
              destruct (ub_free_expr ca) eqn:Huba; cbn [negb] in Hrc; [| discriminate Hrc].
              destruct (expr_has_freeze ca) eqn:Hnfa; [discriminate Hrc |].
              destruct (reify_pure_exp_typing a0 allowed lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Hlmap Ea0)
                as (_ & Hwt0 & Hbw0 & Hlf0 & Hfv0).
              pose proof (reify_pure_exp_top_width a0 lmap (Some (DTYPE_Base (DTYPE_I w))) wa ca Ea0) as Htw0.
              cbn [check_opt_int_width] in Htw0; apply Pos.eqb_eq in Htw0; subst wa; rewrite Htw0 in Ea0.
              destruct (eval_reified_pure_exp_no_ub allowed penv lmap env a0 (Some (DTYPE_Base (DTYPE_I w))) w ca Hlmap Hpenv Henv Ea0 Huba Hnfa)
                as (dv0 & Hev0 & Hsc0 & Hst0).
              destruct fn_e; try contradiction Hinv; destruct id0 as [[fname | | ] | ?]; try contradiction Hinv;
                destruct obs; try contradiction Hinv;
                destruct Hinv as (Hdt & Hpars & a1 & Hargs & Hbool & Hfa & Hra).
              destruct (pure_int_intrinsic_abs_eval_helper w ca flag penv dummy_freeze_oracle dv0 Hsc0 Hev0)
                as (dv_out & Hpi & Hev_out & Hsc_out).
              destruct (lower_pure_int_intrinsic_abs_typing w ca flag
                          Hwt0 Htw0 Hlf0 (expr_has_freeze_false_collect_keys _ Hnfa))
                as (Hwt & Hbw & Hlf & _ & Hfv_sub).
              assert (Hfv : incl (collect_free_vars [] (lower_pure_int_intrinsic_abs w ca flag)) allowed)
                by (intros x Hx; exact (Hfv0 _ (Hfv_sub _ Hx))).
              pose proof (wf_pure_lmap_add allowed lmap id w (lower_pure_int_intrinsic_abs w ca flag) Hlmap Hwt Hbw Hlf Hfv) as Hlmap1.
              pose proof (lmap_matches_env_add penv lmap env id w (lower_pure_int_intrinsic_abs w ca flag) dv_out Henv Hev_out Hsc_out) as Henv1.
              specialize (IH cid allowed (RM.add id (w, lower_pure_int_intrinsic_abs w ca flag) lmap)
                            (RM.add id dv_out env) ret_w k_end t ctx Hlmap1 Hpenv Henv1 Hk Hrc).
              eapply ir_tree_denotes_prepend_tau_pure with (env1 := RM.add id dv_out env)
                (t1 := apply_cfg_ctxt ctx (denote_code rest None)); [| | exact IH].
               ** intros sigma tr s' env' r Hs; unfold denote_code; cbn [loop_monad].
                  change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind;
                    [apply cfg_steps_to_call_ret;
                     exact (@cfg_steps_pure_int_intrinsic_abs_ret Pa sigma sigma
                              env id dt_fn (EXP_Ident (ID_Global (Name fname))) args anns md fname w a0 a1 flag dv0 dv_out None
                              eq_refl Hpars Hargs Hbool Hfa Hra Hmr_none
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst0)
                              Hpi)
                    | exact Hs].
               ** intros sigma tr Hs; unfold denote_code; cbn [loop_monad].
                  change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r;
                    [apply cfg_steps_to_call_ret;
                     exact (@cfg_steps_pure_int_intrinsic_abs_ret Pa sigma sigma
                              env id dt_fn (EXP_Ident (ID_Global (Name fname))) args anns md fname w a0 a1 flag dv0 dv_out None
                              eq_refl Hpars Hargs Hbool Hfa Hra Hmr_none
                              (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst0)
                              Hpi)
                    | exact Hs].
        -- destruct fn as [dt_ret fn_e].
           destruct dt_ret as [bdt | |]; [destruct bdt as [rw | | | | | | | | | |] | |];
             destruct fn_e;
             try match goal with iv : ident |- _ => destruct iv as [[cname | | ] | ?] end;
             destruct obs; try discriminate Hrc.
           destruct (match @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname))) with None => true | Some _ => false end) eqn:Hintr; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (cconv_eqb (anns_cconv anns) CC_Ccc) eqn:Hcc; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (match metadata_range md with None => true | Some _ => false end) eqn:Hmr_b; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (fattrs_call_ok (ann_fun_attributes anns)) eqn:Hfa; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (pattrs_no_value_poison (ann_ret_attributes anns)) eqn:Hra; cbn [negb] in Hrc; [| discriminate Hrc].
           destruct (is_supported_bit_width rw) eqn:Hsup; cbn [negb] in Hrc; [| discriminate Hrc].
           assert (Hintr_none : @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname))) = None)
             by (destruct (@intrinsic_exp dtyp (EXP_Ident (ID_Global (Name cname)))); [discriminate | reflexivity]).
           assert (Hmr_none : metadata_range md = None)
             by (destruct (metadata_range md); [discriminate | reflexivity]).
           destruct (find_callee_spec callees cname) as [sp |]; [| discriminate Hrc].
           destruct (Pos.eqb rw (mcs_ret_width sp)); [| discriminate Hrc].
           destruct (reify_ir_call_args cname 0%nat lmap (mcs_args sp) args) as [| aes] eqn:Eaes; [discriminate Hrc |].
           destruct (reify_ir_code_calls cur_bid callees rest (S cid)
                       (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap) k_end)
             as [| cont] eqn:Ect; [discriminate Hrc |].
           inversion Hrc; subst t; clear Hrc;
           cbn [ir_tree_denotes];
             destruct (denote_call_args_step genv cname 0%nat allowed penv lmap env (mcs_args sp) args aes
                         ((set_loc (get_file_info md) ++ location_error_string md) ++ ": Call argument violates noundef.")%string
                         Hlmap Hpenv Henv Eaes) as [Hub_a | (dvs & Hst_a & Hfa_a)];
             [left; intro sigma;
              unfold denote_code; cbn [loop_monad denote_instr];
              eapply cfg_call_steps_to_ub_ctxt with (ctx := CBC_Bind _ ctx);
              apply cfg_call_steps_to_ub_bind_l; exact (Hub_a sigma)
             | right; exists dvs; split; [exact Hfa_a |];
               intros v_ret Hrv_p;
               set (dv_ret := DVALUE_Base (@DVALUE_I Pa rw v_ret));
               assert (Hpenv' : wf_param_env_for ((mc_call_ret_var cid rw, rw) :: allowed) penv) by
                 (intros nm0 w0 [Heq0 | Hal0]; [inversion Heq0; subst nm0 w0; exists dv_ret; split; [exact Hrv_p | right; exists v_ret; reflexivity] | exact (Hpenv nm0 w0 Hal0)]);
               assert (Hlmap' : wf_pure_lmap ((mc_call_ret_var cid rw, rw) :: allowed)
                                  (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap)) by
                 (apply wf_pure_lmap_add;
                   [exact (wf_pure_lmap_mono allowed ((mc_call_ret_var cid rw, rw) :: allowed) lmap (fun x Hx => or_intror Hx) Hlmap)
                   | reflexivity | reflexivity | reflexivity | intros [? ?] [? | []]; inversion H; left; reflexivity]);
               assert (Henv' : lmap_matches_env penv
                                 (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap)
                                 (RM.add id dv_ret env)) by
                 (apply lmap_matches_env_add; [exact Henv | | right; exists v_ret; reflexivity];
                  unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hrv_p;
                  cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity);
               specialize (IH (S cid) ((mc_call_ret_var cid rw, rw) :: allowed)
                             (RM.add id (rw, CE_Var (mc_call_ret_var cid rw) rw) lmap)
                             (RM.add id dv_ret env) ret_w k_end cont ctx
                             Hlmap' Hpenv' Henv'
                             (fun c' a' l' e' t' Hinc => Hk c' a' l' e' t' (fun x Hx => Hinc x (or_intror Hx)))
                             Ect);
               exists (RM.add id dv_ret env), (apply_cfg_ctxt ctx (denote_code rest None));
               assert (Hcall_step : forall sigma,
                 cfg_call_steps_to_ret genv sigma env
                   (denote_instr (IId id, INSTR_Call (DTYPE_Base (DTYPE_I rw), EXP_Ident (ID_Global (Name cname))) args anns [], md) None)
                   [(cname, dvs, dv_ret)] sigma (RM.add id dv_ret env) tt) by
                 (intro sigma; cbn [denote_instr];
                  change [(cname, dvs, dv_ret)] with ([] ++ [(cname, dvs, dv_ret)]);
                  eapply cfg_call_steps_to_ret_bind; [apply pure_cfg_steps_to_call_ret; exact Hst_a |];
                  change [(cname, dvs, dv_ret)] with ([] ++ [(cname, dvs, dv_ret)]);
                  eapply cfg_call_steps_to_ret_bind; [apply cfg_steps_to_call_ret, denote_operand_bundles_nil_cfg_steps |];
                  change [(cname, dvs, dv_ret)] with ([(cname, dvs, dv_ret)] ++ []);
                  eapply cfg_call_steps_to_ret_bind;
                  [rewrite Hintr_none;
                   change [(cname, dvs, dv_ret)] with ([] ++ [(cname, dvs, dv_ret)]);
                   eapply cfg_call_steps_to_ret_bind;
                   [unfold denote_exp', withCall;
                    eapply CCSR_GlobalRead;
                    [rewrite observe_translate; cbn [denote_exp lookup_id];
                     unfold gread, ITree.trigger, subevent; cbn [observe _observe translateF]; reflexivity
                    | apply CCSR_Ret; rewrite observe_translate; reflexivity]
                   | unfold call, ITree.trigger, subevent;
                     eapply CCSR_Call; [reflexivity | reflexivity | apply CCSR_Ret; reflexivity]]
                  | change [] with ([] ++ @nil (@mc_call_event Pa));
                    eapply cfg_call_steps_to_ret_bind;
                    [rewrite Hmr_none; exact (check_call_return_int_step genv sigma env (ann_fun_attributes anns)
                                                 (ann_ret_attributes anns) _ dvs rw v_ret Hfa Hra)
                    | change [] with ([] ++ @nil (@mc_call_event Pa));
                      eapply cfg_call_steps_to_ret_bind; [apply CCSR_Ret; reflexivity |];
                      apply cfg_steps_to_call_ret, cfg_steps_lwrite]]);
               repeat split; [| | exact IH];
               [intros sigma tr_r s' env' r Hs; unfold denote_code; cbn [loop_monad];
                change ((cname, dvs, dv_ret) :: tr_r) with ([(cname, dvs, dv_ret)] ++ tr_r);
                eapply cfg_call_steps_to_ret_ctxt_bind; [exact (Hcall_step sigma) | exact Hs]
               | intros sigma tr_r Hs; unfold denote_code; cbn [loop_monad];
                change ((cname, dvs, dv_ret) :: tr_r) with ([(cname, dvs, dv_ret)] ++ tr_r);
                eapply cfg_call_steps_to_ub_ctxt_bind_r; [exact (Hcall_step sigma) | exact Hs]]].
    + destruct ins; try discriminate Hrc; specialize (IH cid allowed lmap env ret_w k_end t ctx Hlmap Hpenv Henv Hk Hrc).
      eapply ir_tree_denotes_prepend_tau_pure with (env1 := env)
        (t1 := apply_cfg_ctxt ctx (denote_code rest None)); [| | exact IH].
      * intros sigma tr s' env' r Hs; eapply cfg_call_steps_to_ret_obs; [| exact Hs].
        apply apply_cfg_ctxt_obs; unfold denote_code;
          cbn [loop_monad denote_instr ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          rewrite observe_bind; cbn [observe _observe]; reflexivity.
      * intros sigma tr Hs; eapply cfg_call_steps_to_ub_obs; [| exact Hs].
        apply apply_cfg_ctxt_obs; unfold denote_code;
          cbn [loop_monad denote_instr ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          rewrite observe_bind; cbn [observe _observe]; reflexivity.
Qed.

Lemma cfg_call_steps_to_ret_bind_obs {Pa : Params} {R S : Type} (genv : raw_id -> @dvalue Pa) :
  forall s0 env0 (t1 t2 : @CFGtop Pa R) (k : R -> @CFGtop Pa S) tr s1 env1 y,
    observe t1 = observe t2 ->
    cfg_call_steps_to_ret genv s0 env0 (ITree.bind t1 k) tr s1 env1 y ->
    cfg_call_steps_to_ret genv s0 env0 (ITree.bind t2 k) tr s1 env1 y.
Proof.
  intros s0 env0 t1 t2 k tr s1 env1 y Ho H.
  eapply cfg_call_steps_to_ret_obs; [| exact H].
  rewrite !observe_bind, Ho; reflexivity.
Qed.

Lemma cfg_call_steps_to_ub_bind_obs {Pa : Params} {R S : Type} (genv : raw_id -> @dvalue Pa) :
  forall s0 env0 (t1 t2 : @CFGtop Pa R) (k : R -> @CFGtop Pa S) tr,
    observe t1 = observe t2 ->
    cfg_call_steps_to_ub genv s0 env0 (ITree.bind t1 k) tr ->
    cfg_call_steps_to_ub genv s0 env0 (ITree.bind t2 k) tr.
Proof.
  intros s0 env0 t1 t2 k tr Ho H.
  eapply cfg_call_steps_to_ub_obs; [| exact H].
  rewrite !observe_bind, Ho; reflexivity.
Qed.

Lemma reify_ir_call_at_exec {Pa : Params} :
  forall fuel (genv : raw_id -> @dvalue Pa) (penv : param_env Pa)
         callees bmap ret_w visited is_entry bid_from cur_bid cid allowed lmap env t,
    is_supported_bit_width ret_w = true ->
    wf_pure_lmap allowed lmap ->
    wf_param_env_for allowed penv ->
    lmap_matches_env penv lmap env ->
    reify_ir_call_at fuel callees bmap ret_w visited is_entry bid_from cur_bid cid lmap = inr t ->
    ir_tree_denotes genv penv ret_w env (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) t.
Proof.
  intro fuel; induction fuel as [| fuel' IH];
    intros genv penv callees bmap ret_w visited is_entry bid_from cur_bid cid allowed lmap env t
           Hrw Hlmap Hpenv Henv Hrec;
    cbn [reify_ir_call_at] in Hrec;
    destruct (raw_id_in_list cur_bid visited); try discriminate Hrec.
  destruct (RM.find cur_bid bmap) as [b |] eqn:Efind; [| discriminate Hrec].
  match type of Hrec with
  | match ?x with inl _ => _ | inr _ => _ end = _ => destruct x as [| lmap1] eqn:El1
  end; [discriminate Hrec |].
  assert (Hphis :
    wf_pure_lmap allowed lmap1 /\
    exists env1,
      lmap_matches_env penv lmap1 env1 /\
      pure_cfg_steps env (denote_phis bid_from (blk_phis b)) env1 tt).
  { destruct is_entry.
    - destruct (blk_phis b) eqn:Ebp; inversion El1; subst; split; [exact Hlmap |].
      exists env; split; [exact Henv | unfold denote_phis; cbn [map_monad];
        eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | apply PCS_Ret; reflexivity]]].
    - destruct (reify_pure_phis bid_from lmap (blk_phis b)) as [pevals |] eqn:Erp; [| discriminate El1].
      destruct (pevals_ub_free pevals) eqn:Eub; cbn [negb] in El1; [| discriminate El1].
      destruct (forallb (fun '(_, _, ce) => negb (expr_has_freeze ce)) pevals) eqn:Efr; cbn [negb] in El1;
        inversion El1; subst.
      pose proof (reify_pure_phis_typing (blk_phis b) allowed bid_from lmap pevals Hlmap Erp) as Htp_p.
      split; [exact (apply_reified_phis_wf _ _ _ Hlmap Htp_p) |].
      destruct (pure_phis_denote_step (blk_phis b) penv bid_from lmap env pevals Henv Erp)
        as [[_ (ce & msg & Hin_c & Hev_ub)] | [dvs [Hpm Hst_p]]].
      + unfold pevals_ub_free in Eub; rewrite forallb_forall in Eub.
        unfold peval_exprs in Hin_c; apply in_map_iff in Hin_c as [[[id_p w_p] ce_p] [<- Hin_p]].
        pose proof (Eub _ Hin_p) as Hce_ub.
        rewrite Forall_forall in Htp_p; destruct (Htp_p _ Hin_p) as (_ & _ & (Hwt_p & Hlf_p & Hfv_p)).
        destruct (ub_free_expr_eval_ret ce_p [] penv [] dummy_freeze_oracle Hce_ub Hwt_p wf_let_val_env_nil
                    (fun nm w0 Hin0 => Hpenv nm w0 (Hfv_p _ Hin0))) as [dv0 [Hev0 _]].
        unfold eval_closed_cert_expr in *; congruence.
      + exists (apply_phi_env env dvs); split;
          [exact (apply_reified_phis_matches _ _ _ _ _ Henv Hpm) | exact Hst_p]. }
  destruct Hphis as (Hlmap1 & env1 & Henv1 & Hst_phis).
  destruct (blk_term b) as [[tid term] tmd] eqn:Etb.
  set (k_bd := (fun bd : block_id + @dvalue Pa =>
    match bd with
    | inr dv => Ret (inr (inr dv))
    | inl bid_target => Ret (inl (cur_bid, bid_target))
    end) : (block_id + @dvalue Pa) -> @CFGtop Pa ((block_id * block_id) + ((block_id * block_id) + @dvalue Pa))).
  set (k_lr := (fun lr : (block_id * block_id) + ((block_id * block_id) + @dvalue Pa) =>
    match lr with
    | inl j => Tau (@denote_ocfg_map Pa bmap None j)
    | inr r => Ret r
    end) : ((block_id * block_id) + ((block_id * block_id) + @dvalue Pa)) -> @CFGtop Pa ((block_id * block_id) + @dvalue Pa)).
  set (k_outer := (fun r : (block_id * block_id) + @dvalue Pa =>
    match r with
    | inl bid => raise ("Can't find block in denote_cfg " ++ show (snd bid))%string
    | inr uv => ret uv
    end) : ((block_id * block_id) + @dvalue Pa) -> @CFGtop Pa (@dvalue Pa)).
  set (ctx_term := CBC_Bind k_bd (CBC_Bind k_lr (CBC_Bind k_outer CBC_Id))).
  set (ctx_code := CBC_Bind (fun _ : unit => denote_terminator (blk_term b)) ctx_term).
  assert (Hk : forall cid' allowed' lmap' env' t',
    incl allowed allowed' ->
    wf_pure_lmap allowed' lmap' ->
    wf_param_env_for allowed' penv ->
    lmap_matches_env penv lmap' env' ->
    (let '(_, t_k) := fst (blk_term b) in
     match t_k with
     | TERM_Ret (DTYPE_Base (DTYPE_I rw), op) =>
         if Pos.eqb rw ret_w then
           match reify_pure_exp lmap' (Some (DTYPE_Base (DTYPE_I rw))) op with
           | Some (_, ret_e) =>
               if negb (ub_free_expr ret_e) then inl (diag "mc-call-ir" ("non-UB-free return expression in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
               else if expr_has_freeze ret_e then inl (diag "mc-call-ir" ("freeze expression not allowed in return of block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
               else inr (ICT_Ret rw ret_e)
           | None => inl (diag "mc-call-ir" ("unsupported return operand in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
           end
         else inl (diag "mc-call-ir" ("return width i" ++ diag_pos_dec rw ++ " mismatches expected i" ++ diag_pos_dec ret_w ++ " in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
     | TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2 =>
         match reify_pure_exp lmap' (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
         | Some (_, cond_e) =>
             if negb (ub_free_expr cond_e) then inl (diag "mc-call-ir" ("non-UB-free branch condition in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
             else if expr_has_freeze cond_e then inl (diag "mc-call-ir" ("freeze expression not allowed in branch condition of block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
             else
               match reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' lmap' with
               | inl err => inl err
               | inr dt =>
                   match reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' lmap' with
                   | inl err => inl err
                   | inr df => inr (ICT_Branch cond_e dt df)
                   end
               end
         | None => inl (diag "mc-call-ir" ("unsupported branch condition in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
         end
     | TERM_Br_1 next_bid =>
         reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid next_bid cid' lmap'
     | TERM_Unreachable => inr ICT_UB
     | _ => inl (diag "mc-call-ir" ("unsupported terminator in block '" ++ cert_raw_id_bare cur_bid ++ "' (from '" ++ cert_raw_id_bare bid_from ++ "')"))
     end) = inr t' ->
    ir_tree_denotes genv penv ret_w env' (apply_cfg_ctxt ctx_code (Ret tt)) t').
  { intros cid' allowed' lmap' env' t' _ Hlmap' Hpenv' Henv' Ht'.
    assert (Hlift_t :
      ir_tree_denotes genv penv ret_w env' (apply_cfg_ctxt ctx_term (denote_terminator (blk_term b))) t' ->
      ir_tree_denotes genv penv ret_w env' (apply_cfg_ctxt ctx_code (Ret tt)) t').
    { apply ir_tree_denotes_prepend_tau_pure.
      - intros sigma tr s' env_f r Hs.
        eapply cfg_call_steps_to_ret_obs; [symmetry; apply apply_cfg_ctxt_obs with (ctx := ctx_term); rewrite observe_bind; reflexivity | exact Hs].
      - intros sigma tr Hs.
        eapply cfg_call_steps_to_ub_obs; [symmetry; apply apply_cfg_ctxt_obs with (ctx := ctx_term); rewrite observe_bind; reflexivity | exact Hs]. }
    apply Hlift_t; clear Hlift_t.
    rewrite Etb in Ht'; cbn [fst] in Ht'.
    destruct term; try discriminate Ht'.
    - (* TERM_Ret *)
      match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] op] end; try discriminate Ht'.
      destruct (Pos.eqb rw ret_w) eqn:Erw; [apply Pos.eqb_eq in Erw; subst rw | discriminate Ht'].
      destruct (reify_pure_exp lmap' (Some (DTYPE_Base (DTYPE_I ret_w))) op) as [[wa ret_e] |] eqn:Eop;
        [| discriminate Ht'].
      destruct (ub_free_expr ret_e) eqn:Hub_r; cbn [negb] in Ht'; [| discriminate Ht'].
      destruct (expr_has_freeze ret_e) eqn:Hnf_r; [discriminate Ht' |].
      inversion Ht'; subst t'; clear Ht'.
      destruct (eval_reified_pure_exp_no_ub allowed' penv lmap' env' op
                  (Some (DTYPE_Base (DTYPE_I ret_w))) wa ret_e Hlmap' Hpenv' Henv' Eop Hub_r Hnf_r)
        as (dv_ir & Hev & Hsc & Hst_op).
      pose proof (reify_pure_exp_top_width op lmap' (Some (DTYPE_Base (DTYPE_I ret_w))) wa ret_e Eop) as Htw.
      cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst wa.
      cbn [ir_tree_denotes]; split; [reflexivity |].
      exists env', dv_ir; repeat split; try assumption.
      intro sigma; apply pure_cfg_steps_to_call_ret.
      unfold ctx_term, apply_cfg_ctxt, k_bd, k_lr, k_outer; rewrite Etb; cbn [denote_terminator].
      eapply pure_cfg_steps_bind.
      + eapply pure_cfg_steps_bind.
        -- eapply pure_cfg_steps_bind.
           ++ eapply pure_cfg_steps_bind;
                [unfold denote_exp'; exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_op)
                | apply PCS_Ret; reflexivity].
           ++ apply PCS_Ret; reflexivity.
        -- apply PCS_Ret; reflexivity.
      + apply PCS_Ret; reflexivity.
    - (* TERM_Br *)
      match goal with x : texp dtyp |- _ => destruct x as [[[w | | | | | | | | | |] | |] op] end; try discriminate Ht'.
      destruct w; try discriminate Ht'.
      destruct (reify_pure_exp lmap' (Some (DTYPE_Base (DTYPE_I 1%positive))) op) as [[wc cond_e] |] eqn:Eop;
        [| discriminate Ht'].
      destruct (ub_free_expr cond_e) eqn:Hub_c; cbn [negb] in Ht'; [| discriminate Ht'].
      destruct (expr_has_freeze cond_e) eqn:Hnf_c; [discriminate Ht' |].
      destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' lmap')
        as [| dt1] eqn:Edt; [discriminate Ht' |].
      destruct (reify_ir_call_at fuel' callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' lmap')
        as [| df1] eqn:Edf; [discriminate Ht' |].
      inversion Ht'; subst t'; clear Ht'.
      destruct (eval_reified_pure_exp_no_ub allowed' penv lmap' env' op
                  (Some (DTYPE_Base (DTYPE_I 1%positive))) wc cond_e Hlmap' Hpenv' Henv' Eop Hub_c Hnf_c)
        as (dv_c & Hev & Hsc & Hst_op).
      pose proof (reify_pure_exp_top_width op lmap' (Some (DTYPE_Base (DTYPE_I 1%positive))) wc cond_e Eop) as Htw.
      cbn [check_opt_int_width] in Htw; apply Pos.eqb_eq in Htw; subst wc.
      cbn [wf_scalar_dvalue] in Hsc; destruct Hsc as [Hpois | [v1 ->]].
      + subst dv_c; cbn [ir_tree_denotes]; left; split; [exact Hev |].
        intro sigma; unfold ctx_term, apply_cfg_ctxt; rewrite Etb; cbn [denote_terminator].
        apply cfg_call_steps_to_ub_ctxt with (ctx := CBC_Bind k_bd (CBC_Bind k_lr (CBC_Bind k_outer CBC_Id))).
        change [] with ([] ++ @nil (@mc_call_event Pa)); eapply cfg_call_steps_to_ub_bind_r;
          [apply pure_cfg_steps_to_call_ret, pure_mcfg_to_pure_cfg; exact Hst_op |].
        eapply CCSU_UB; unfold raiseUB, trigger_cast', ITree.trigger; rewrite observe_bind; reflexivity.
      + set (bflag := ((@Integers.unsigned 1%positive v1 =? 1)%Z)).
        assert (Hv1_eq : v1 = if bflag then @Integers.one 1%positive else @Integers.zero 1%positive).
        { unfold bflag; pose proof (@Integers.unsigned_range 1%positive v1) as Hrng.
          change (@Integers.modulus 1%positive) with 2%Z in Hrng.
          destruct ((@Integers.unsigned 1%positive v1 =? 1)%Z) eqn:Eu.
          - apply Z.eqb_eq in Eu.
            rewrite <- (@Integers.repr_unsigned 1%positive v1), Eu.
            unfold Integers.one; reflexivity.
          - apply Z.eqb_neq in Eu.
            assert (Hu0 : @Integers.unsigned 1%positive v1 = 0%Z) by lia.
            rewrite <- (@Integers.repr_unsigned 1%positive v1), Hu0.
            unfold Integers.zero; reflexivity. }
        cbn [ir_tree_denotes]; right; exists bflag; split.
        * rewrite Hev, <- Hv1_eq; reflexivity.
        * set (br := if bflag then br1 else br2).
          assert (Hden_br : ir_tree_denotes genv penv ret_w env' (@denote_cfg_from Pa bmap None (cur_bid, br)) (if bflag then dt1 else df1)).
          { unfold br; destruct bflag.
            - exact (IH genv penv callees bmap ret_w (cur_bid :: visited) false cur_bid br1 cid' allowed' lmap' env' dt1 Hrw Hlmap' Hpenv' Henv' Edt).
            - exact (IH genv penv callees bmap ret_w (cur_bid :: visited) false cur_bid br2 cid' allowed' lmap' env' df1 Hrw Hlmap' Hpenv' Henv' Edf). }
          assert (Hjump_step : pure_cfg_steps env' (denote_terminator (blk_term b)) env' (inl br)).
          { rewrite Etb; cbn [denote_terminator].
            eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_op) |].
            cbn iota beta; rewrite bit_int_1_equ_one_eq_unsigned; unfold br; fold bflag; destruct bflag; apply PCS_Ret; reflexivity. }
          eapply ir_tree_denotes_prepend_tau_pure with (env1 := env') (t1 := @denote_cfg_from Pa bmap None (cur_bid, br));
            [| | exact Hden_br].
          -- intros sigma tr s' env_f r Hs.
             unfold ctx_term, apply_cfg_ctxt; change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind with (ctx := CBC_Bind k_lr (CBC_Bind k_outer CBC_Id)); [apply pure_cfg_steps_to_call_ret; exact Hjump_step |].
             unfold apply_cfg_ctxt, k_bd, k_lr, k_outer.
             eapply CCSR_Tau; [rewrite !observe_bind; reflexivity | exact Hs].
          -- intros sigma tr Hs.
             unfold ctx_term, apply_cfg_ctxt; change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r with (ctx := CBC_Bind k_lr (CBC_Bind k_outer CBC_Id)); [apply pure_cfg_steps_to_call_ret; exact Hjump_step |].
             unfold apply_cfg_ctxt, k_bd, k_lr, k_outer.
             eapply CCSU_Tau; [rewrite !observe_bind; reflexivity | exact Hs].
    - (* TERM_Br_1 *)
      match type of Ht' with
      | reify_ir_call_at _ _ _ _ _ _ _ ?nxt _ _ = _ => set (b_nxt := nxt) in *
      end.
      assert (Hden_br : ir_tree_denotes genv penv ret_w env' (@denote_cfg_from Pa bmap None (cur_bid, b_nxt)) t')
        by exact (IH genv penv callees bmap ret_w (cur_bid :: visited) false cur_bid b_nxt cid' allowed' lmap' env' t' Hrw Hlmap' Hpenv' Henv' Ht').
      assert (Hjump_step : pure_cfg_steps env' (denote_terminator (blk_term b)) env' (inl b_nxt))
        by (rewrite Etb; cbn [denote_terminator]; apply PCS_Ret; reflexivity).
      eapply ir_tree_denotes_prepend_tau_pure with (env1 := env') (t1 := @denote_cfg_from Pa bmap None (cur_bid, b_nxt));
        [| | exact Hden_br].
      + intros sigma tr s' env_f r Hs.
        unfold ctx_term, apply_cfg_ctxt; change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind with (ctx := CBC_Bind k_lr (CBC_Bind k_outer CBC_Id)); [apply pure_cfg_steps_to_call_ret; exact Hjump_step |].
        unfold apply_cfg_ctxt, k_bd, k_lr, k_outer.
        eapply CCSR_Tau; [rewrite !observe_bind; reflexivity | exact Hs].
      + intros sigma tr Hs.
        unfold ctx_term, apply_cfg_ctxt; change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r with (ctx := CBC_Bind k_lr (CBC_Bind k_outer CBC_Id)); [apply pure_cfg_steps_to_call_ret; exact Hjump_step |].
        unfold apply_cfg_ctxt, k_bd, k_lr, k_outer.
        eapply CCSU_Tau; [rewrite !observe_bind; reflexivity | exact Hs].
    - (* TERM_Unreachable *)
      inversion Ht'; subst t'; clear Ht'; cbn [ir_tree_denotes].
      intro sigma; unfold ctx_term; rewrite Etb; cbn [denote_terminator].
      apply cfg_call_steps_to_ub_ctxt; eapply CCSU_UB; unfold raiseUB, trigger_cast', ITree.trigger; rewrite observe_bind; reflexivity. }
  rewrite <- Etb in Hrec.
  pose proof (@reify_ir_code_calls_exec Pa cur_bid genv penv callees (blk_code b) cid allowed lmap1 env1 ret_w
                _ t ctx_code Hlmap1 Hpenv Henv1 Hk Hrec) as Hcode.
  eapply ir_tree_denotes_prepend_tau_pure with (env1 := env1) (t1 := apply_cfg_ctxt ctx_code (denote_code (blk_code b) None));
    [| | exact Hcode].
  - intros sigma tr s' env' r Hs.
    unfold ctx_code in Hs.
    change (apply_cfg_ctxt (CBC_Bind (fun _ : unit => denote_terminator (blk_term b)) ctx_term) (denote_code (blk_code b) None))
      with (apply_cfg_ctxt ctx_term (ITree.bind (denote_code (blk_code b) None) (fun _ : unit => denote_terminator (blk_term b)))) in Hs.
    assert (Hblk : cfg_call_steps_to_ret genv sigma env (apply_cfg_ctxt ctx_term (denote_block b bid_from None)) tr s' env' r).
    { unfold denote_block; change tr with ([] ++ tr); eapply cfg_call_steps_to_ret_ctxt_bind;
        [apply pure_cfg_steps_to_call_ret; exact Hst_phis | exact Hs]. }
    unfold denote_cfg_from, ctx_term, apply_cfg_ctxt in Hblk |- *.
    eapply cfg_call_steps_to_ret_bind_obs;
      [symmetry; exact (denote_ocfg_map_step_varargs_obs bmap None bid_from cur_bid b Efind) | exact Hblk].
  - intros sigma tr Hs.
    unfold ctx_code in Hs.
    change (apply_cfg_ctxt (CBC_Bind (fun _ : unit => denote_terminator (blk_term b)) ctx_term) (denote_code (blk_code b) None))
      with (apply_cfg_ctxt ctx_term (ITree.bind (denote_code (blk_code b) None) (fun _ : unit => denote_terminator (blk_term b)))) in Hs.
    assert (Hblk : cfg_call_steps_to_ub genv sigma env (apply_cfg_ctxt ctx_term (denote_block b bid_from None)) tr).
    { unfold denote_block; change tr with ([] ++ tr); eapply cfg_call_steps_to_ub_ctxt_bind_r;
        [apply pure_cfg_steps_to_call_ret; exact Hst_phis | exact Hs]. }
    unfold denote_cfg_from, ctx_term, apply_cfg_ctxt in Hblk |- *.
    eapply cfg_call_steps_to_ub_bind_obs;
      [symmetry; exact (denote_ocfg_map_step_varargs_obs bmap None bid_from cur_bid b Efind) | exact Hblk].
Qed.

Lemma reify_ir_call_tree_exec {Pa : Params} :
  forall (genv : raw_id -> @dvalue Pa) (penv : param_env Pa)
         ir_cfg arg_specs callees ret_w allowed arg_dtys vs t_ir,
    is_supported_bit_width ret_w = true ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    (forall idx dt, In (idx, dt) (arg_specs_uses_from 0%nat arg_specs) -> nth_error arg_dtys idx = Some dt) ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (arg_specs_uses_from 0%nat arg_specs) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    wf_param_env_for allowed penv ->
    reify_ir_call_tree ir_cfg arg_specs callees ret_w = inr t_ir ->
    ir_tree_denotes genv penv ret_w (init_cfg_locals (args ir_cfg) vs) (@denote_cfg Pa ir_cfg None) t_ir.
Proof.
  intros genv penv ir_cfg arg_specs callees ret_w allowed arg_dtys vs t_ir
         Hrw Hnda Hnds Hlens Hlenad Hcomp_n Hty Hpu Hpeq Hpenv Hrc.
  assert (Hlen_vs : List.length (args ir_cfg) = List.length vs)
    by (pose proof (Forall2_length Hty); lia).
  set (ir_pnames := List.map cert_reg_name (args ir_cfg)) in *.
  set (lmap_init := init_param_lmap (args ir_cfg) ir_pnames (arg_specs_uses_from 0%nat arg_specs)) in *.
  assert (Hwf_li : wf_pure_lmap allowed lmap_init)
    by exact (init_param_lmap_typing (arg_specs_uses_from 0%nat arg_specs) (args ir_cfg) ir_pnames allowed Hpu).
  assert (Henv_i : lmap_matches_env penv lmap_init (init_cfg_locals (args ir_cfg) vs)).
  { pose proof (init_param_lmap_matches (arg_specs_uses_from 0%nat arg_specs) (args ir_cfg) ir_pnames arg_dtys vs
                  Hnda Hnds Hlen_vs (eq_trans Hlens Hlen_vs) Hty Hcomp_n) as Hbase.
    intros r w ce Hf; destruct (Hbase r w ce Hf) as (dv & Hev & Hsc & Hrm).
    destruct (init_param_lmap_dom (args ir_cfg) ir_pnames (arg_specs_uses_from 0%nat arg_specs) r w ce Hf)
      as [pnm [-> Hinp]].
    exists dv; repeat split; try assumption.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr lookup_let_val] in *; rewrite (Hpeq pnm Hinp); exact Hsc. }
  exact (reify_ir_call_at_exec (S (List.length (blks ir_cfg) + 1)) genv penv callees
           (ocfg_map (blks ir_cfg)) ret_w [] true (init ir_cfg) (init ir_cfg) 0%nat allowed
           lmap_init (init_cfg_locals (args ir_cfg) vs) t_ir Hrw Hwf_li Hpenv Henv_i Hrc).
Qed.

Lemma summarize_rv64_call_tree_wfsym :
  forall insts callees arg_specs ret_w allowed t_mc,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true) ->
    forallb rv_call_inst_no_word_mulh insts = true ->
    forallb rv_valid_arg_spec arg_specs = true ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed) ->
    summarize_rv64_call_tree insts callees arg_specs ret_w = inr t_mc ->
    mc_call_tree_wf allowed ret_w t_mc.
Proof.
  intros insts callees arg_specs ret_w allowed t_mc Hrw Hcws Hmul Hws Hargs_al Hsum.
  unfold summarize_rv64_call_tree in Hsum.
  eapply summarize_rv64_call_at_wfsym;
    [exact (pt_of_list_first_lookup_rv_call insts)
    | exact Hrw | exact Hcws | exact Hmul | | | exact (rv_init_val_regs_wf allowed arg_specs Hargs_al Hws) | | exact Hsum].
  - unfold mc_frame_cap; lia.
  - unfold rv_val_read; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity.
  - constructor.
Qed.

Lemma a64_hi_vars_in_specs :
  forall (specs : list rv_arg_spec) sp,
    In sp specs ->
    ras_width sp <> 64%positive ->
    In (a64_hi_var_name (ras_name sp), 64%positive) (a64_hi_vars specs).
Proof.
  induction specs as [| s rest IH]; intros sp Hin Hw; cbn [In] in Hin;
    unfold a64_hi_vars in *; cbn [flat_map] in *; [contradiction |].
  destruct (Pos.eqb (ras_width s) 64%positive) eqn:E64.
  - destruct Hin as [<- | Hr]; [apply Pos.eqb_eq in E64; contradiction | exact (IH sp Hr Hw)].
  - destruct Hin as [<- | Hr]; [left; reflexivity | right; exact (IH sp Hr Hw)].
Qed.

Lemma summarize_a64_call_tree_wfsym :
  forall insts callees arg_specs ret_w allowed t_mc,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true) ->
    forallb a64_call_inst_valid insts = true ->
    forallb a64_valid_arg_spec arg_specs = true ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed) ->
    (forall nv, In nv (a64_hi_vars arg_specs) -> In nv allowed) ->
    summarize_a64_call_tree insts callees arg_specs ret_w = inr t_mc ->
    mc_call_tree_wf allowed ret_w t_mc.
Proof.
  intros insts callees arg_specs ret_w allowed t_mc Hrw Hcws Hval Hws Hargs_al Hhi_al Hsum.
  unfold summarize_a64_call_tree in Hsum.
  assert (Hall_a64 : forall sp, In sp arg_specs ->
    In (ras_name sp, ras_width sp) allowed /\
    (ras_width sp <> 64%positive -> In (a64_hi_var_name (ras_name sp), 64%positive) allowed)).
  { intros sp Hsp; split; [exact (Hargs_al sp Hsp) | intro Hne; exact (Hhi_al _ (a64_hi_vars_in_specs _ _ Hsp Hne))]. }
  eapply summarize_a64_call_at_wfsym;
    [exact (pt_of_list_first_lookup_a64_call insts)
    | exact Hrw | exact Hcws | exact Hval | | exact (a64_init_val_regs_wf allowed arg_specs Hall_a64 Hws) | | | exact Hsum].
  - unfold mc_frame_cap; lia.
  - constructor.
  - intro C; discriminate C.
Qed.

Lemma mc_tree_path_ok_repath {Pa : Params} (penv : param_env Pa) (ret_w : positive) :
  forall p1 p2 t_mc evs_mc v_mc_ret,
    mc_tree_path_ok penv ret_w p1 t_mc evs_mc v_mc_ret ->
    mc_tree_path_ok penv ret_w p2 t_mc evs_mc v_mc_ret.
Proof.
  intros p1 p2 t_mc evs_mc v_mc_ret H; revert p2;
    induction H; intros p2;
    [eapply MTPO_Ret; eassumption
    | eapply MTPO_Branch; [eassumption | exact (IHmc_tree_path_ok _)]
    | eapply MTPO_Call; [eassumption | eassumption | eassumption | exact (IHmc_tree_path_ok _)]].
Qed.

Lemma build_call_arg_obls_list_matches {Pa : Params} :
  forall cname arch (penv : param_env Pa) (path : list (bool * cert_expr)) specs ir_args mc_args64 obls arg_vals vs_ir,
    (forall (b : bool) c, In (b, c) path ->
       eval_closed_cert_expr penv dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv dummy_freeze_oracle None false) obls ->
    build_call_arg_obls cname arch path specs ir_args mc_args64 = inr obls ->
    Forall rv_valid_arg_spec specs ->
    NoDup (List.map ras_name specs) ->
    Forall2 (fun '(need_def, w, ce) dv =>
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv /\
      (need_def = false -> dvalue_well_defined dv = true)) ir_args vs_ir ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv dummy_freeze_oracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))) mc_args64 arg_vals ->
    List.length vs_ir = List.length specs /\
    List.length arg_vals = List.length specs /\
    (forall k sp v_mc,
       nth_error specs k = Some sp ->
       nth_error arg_vals k = Some v_mc ->
       exists v : @Integers.bit_int (ras_width sp),
         build_param_env (List.map ras_name specs) vs_ir (ras_name sp) =
           Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
         match arch with
         | EA_Riscv64 =>
             v_mc =
               (if Pos.eqb (ras_width sp) 64%positive then
                  @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                else
                  match ras_ext sp with
                  | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                  | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
                  end)
         | EA_AArch64 =>
             match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
             | true, RAE_None =>
                 v_mc = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
             | false, RAE_None =>
                 @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive v_mc) = v
             | false, RAE_SignExt =>
                 @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
                 @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
             | false, RAE_ZeroExt =>
                 @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
                 @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
             | _, _ => False
             end
         end).
Proof.
  intros cname arch penv path specs ir_args mc_args64 obls arg_vals vs_ir
         Hpath Hobls Hbao Hvs Hnd Hfir Hfmc.
  assert (Hlen_av : List.length arg_vals = List.length specs)
    by (destruct (build_call_arg_obls_length _ _ _ _ _ _ _ Hbao) as [_ Hl2];
        pose proof (Forall2_length Hfmc); congruence).
  assert (Hlen_vs : List.length vs_ir = List.length specs)
    by (destruct (build_call_arg_obls_length _ _ _ _ _ _ _ Hbao) as [Hl1 _];
        pose proof (Forall2_length Hfir); congruence).
  repeat split; [exact Hlen_vs | exact Hlen_av |].
  assert (Hitem : forall k sp v_mc,
    nth_error specs k = Some sp ->
    nth_error arg_vals k = Some v_mc ->
    exists v : @Integers.bit_int (ras_width sp),
      nth_error vs_ir k = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      match arch with
      | EA_Riscv64 =>
          v_mc =
            (if Pos.eqb (ras_width sp) 64%positive then
               @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
             else
               match ras_ext sp with
               | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
               | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
               end)
      | EA_AArch64 =>
          match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
          | true, RAE_None =>
              v_mc = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
          | false, RAE_None =>
              @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive v_mc) = v
          | false, RAE_SignExt =>
              @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
              @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
          | false, RAE_ZeroExt =>
              @Integers.repr 32%positive (@Integers.unsigned 64%positive v_mc) =
              @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
          | _, _ => False
          end
      end).
  { clear Hnd Hlen_av Hlen_vs.
    unfold build_call_arg_obls in Hbao; revert Hbao; generalize 0%nat as arg_idx.
    revert ir_args mc_args64 obls arg_vals vs_ir Hobls Hvs Hfir Hfmc.
    induction specs as [| sp0 srest IH];
      intros ir_args mc_args64 ob0 avs vs0 Hob0 Hvs0 Hfi0 Hfm0 arg_idx Hb0 k sp v_mc Hsp0_n Hav_n;
      try (destruct k; discriminate Hsp0_n);
      destruct ir_args as [| [[nd0 w0] e0] irest]; destruct mc_args64 as [| m0 mrest];
      try (cbn [build_call_arg_obls_from build_call_arg_obls_acc] in Hb0; discriminate Hb0).
    rewrite build_call_arg_obls_from_cons in Hb0.
    destruct (Pos.eqb w0 (ras_width sp0)) eqn:Epw; [apply Pos.eqb_eq in Epw; subst w0 | discriminate Hb0].
    match type of Hb0 with
    | context [match ?x with inl _ => _ | inr _ => _ end] => destruct x as [| cmp0] eqn:Ecmp0; [discriminate Hb0 |]
    end.
    destruct (build_call_arg_obls_from cname (S arg_idx) arch path srest irest mrest) as [| rest_o] eqn:Erest;
      cbn [mcc_sum_map] in Hb0; [discriminate Hb0 |].
    inversion Hb0; subst ob0; clear Hb0.
    destruct avs as [| vm0 av_r]; [inversion Hfm0 |].
    destruct vs0 as [| dv0 vs_r]; [inversion Hfi0 |].
    inversion Hvs0 as [| ? ? Hsp0_v Hvs_r]; subst.
    inversion Hfi0 as [| ? ? ? ? Hp0 Hfi_r]; subst; destruct Hp0 as [Hev0 [Hsc0 Hnd0]].
    inversion Hfm0 as [| ? ? ? ? Hm0 Hfm_r]; subst.
    rewrite Forall_app in Hob0; destruct Hob0 as [Hrest_o Hhead_o].
    assert (Hdef0 : Forall (mc_obl_holds penv dummy_freeze_oracle None false) (if nd0 then [MLO_Defined false path (ras_width sp0) e0] else [])).
    { destruct nd0; [inversion Hhead_o as [| ? ? Hd _]; constructor; [exact Hd | constructor] | constructor]. }
    assert (Hcmp0 : Forall (mc_obl_holds penv dummy_freeze_oracle None false) [cmp0]).
    { destruct nd0; [inversion Hhead_o as [| ? ? _ Hc]; exact Hc | exact Hhead_o]. }
    destruct k as [| k']; cbn in Hsp0_n, Hav_n.
    - inversion Hsp0_n; subst sp0; inversion Hav_n; subst vm0; clear Hsp0_n Hav_n.
      assert (Hwd0 : dvalue_well_defined dv0 = true).
      { destruct nd0; [| exact (Hnd0 eq_refl)].
        inversion Hdef0 as [| ? ? Hd _]; subst.
        pose proof (Hd eq_refl ltac:(discriminate) Hpath) as [v Hv1].
        unfold eval_closed_cert_expr in *; rewrite Hev0 in Hv1; inversion Hv1; reflexivity. }
      destruct Hsc0 as [Hbad | [iv ->]]; [rewrite Hbad in Hwd0; discriminate Hwd0 |].
      exists iv; split; [reflexivity |].
      destruct arch;
        [inversion Ecmp0; subst cmp0; clear Ecmp0;
         inversion Hcmp0 as [| ? ? Hc0 _]; subst;
         pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href;
         unfold refine_eou_dvalue, dvalue_refines, build_rv_call_arg_expr in Href |].
      + destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; generalize iv Hev0 Href; rewrite Ew64; intros iv64 Hev64 Href64; rewrite Hev64, Hm0 in Href64; cbn in Href64.
          destruct Href64 as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; symmetry in Heq; subst; rewrite (@Integers.repr_unsigned 64%positive); reflexivity].
        * assert (Hltb : (ras_width sp <? 64)%positive = true).
          { apply Pos.ltb_lt; unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _].
            apply rv_supported_arg_width_lt64 in Ew64; [apply Pos.ltb_lt; exact Ew64 | exact Hsup]. }
          destruct (ras_ext sp);
            erewrite ?eval_ce_sext, ?eval_ce_zext in Href by (first [exact Hltb | exact Hev0]);
            rewrite Hm0 in Href; cbn in Href; destruct Href as [Hbad | Heq];
            [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq | discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq | discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
      + unfold build_call_arg_cmp in Ecmp0; destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * destruct (ras_ext sp); inversion Ecmp0; subst cmp0; clear Ecmp0.
          inversion Hcmp0 as [| ? ? Hc0 _]; subst; pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href.
          unfold refine_eou_dvalue, dvalue_refines in Href.
          apply Pos.eqb_eq in Ew64; generalize iv Hev0 Href; rewrite Ew64; intros iv64 Hev64 Href64; rewrite Hev64, Hm0 in Href64.
          cbn in Href64; destruct Href64 as [Hbad | Heq];
            [discriminate Hbad | apply dvalue_i_inj in Heq; symmetry in Heq; subst; rewrite (@Integers.repr_unsigned 64%positive); reflexivity].
        * assert (Hltb : (ras_width sp <? 64)%positive = true).
          { apply Pos.ltb_lt; unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _].
            apply rv_supported_arg_width_lt64 in Ew64; [apply Pos.ltb_lt; exact Ew64 | exact Hsup]. }
          destruct (ras_ext sp); inversion Ecmp0; subst cmp0; clear Ecmp0;
            inversion Hcmp0 as [| ? ? Hc0 _]; subst;
            pose proof (Hc0 eq_refl ltac:(discriminate) Hpath) as Href;
            unfold refine_eou_dvalue, dvalue_refines in Href.
          -- erewrite eval_ce_trunc in Href by (first [exact Hltb | exact Hm0]).
             rewrite Hev0 in Href; cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
          -- erewrite eval_ce_trunc in Href by (first [reflexivity | exact Hm0]).
             destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
             ++ apply Pos.eqb_eq in Ew32; generalize iv Href Hev0; rewrite Ew32; intros iv' Href' Hev0'.
                rewrite Hev0' in Href'; cbn in Href'; destruct Href' as [Hbad | Heq];
                  [discriminate Hbad | apply dvalue_i_inj in Heq; subst iv'; rewrite (@Integers.repr_signed 32%positive); reflexivity].
             ++ assert (Hlt32 : (ras_width sp <? 32)%positive = true)
                  by (unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _];
                      exact (rv_supported_arg_width_lt32 _ Hsup Ew64 Ew32)).
                erewrite eval_ce_sext in Href by (first [exact Hlt32 | exact Hev0]).
                cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
          -- erewrite eval_ce_trunc in Href by (first [reflexivity | exact Hm0]).
             destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
             ++ apply Pos.eqb_eq in Ew32; generalize iv Href Hev0; rewrite Ew32; intros iv' Href' Hev0'.
                rewrite Hev0' in Href'; cbn in Href'; destruct Href' as [Hbad | Heq];
                  [discriminate Hbad | apply dvalue_i_inj in Heq; subst iv'; rewrite (@Integers.repr_unsigned 32%positive); reflexivity].
             ++ assert (Hlt32 : (ras_width sp <? 32)%positive = true)
                  by (unfold rv_valid_arg_spec in Hsp0_v; apply andb_true_iff in Hsp0_v as [Hsup _];
                      exact (rv_supported_arg_width_lt32 _ Hsup Ew64 Ew32)).
                erewrite eval_ce_zext in Href by (first [exact Hlt32 | exact Hev0]).
                cbn in Href; destruct Href as [Hbad | Heq]; [discriminate Hbad | apply dvalue_i_inj in Heq; exact Heq].
    - exact (IH irest mrest rest_o av_r vs_r Hrest_o Hvs_r Hfi_r Hfm_r (S arg_idx) Erest k' sp v_mc Hsp0_n Hav_n). }
  intros k sp v_mc Hsp_n Hav_n.
  destruct (Hitem k sp v_mc Hsp_n Hav_n) as (v & Hvs_n & Hvmc).
  exists v; split; [| exact Hvmc].
  destruct (build_param_env_nth (List.map ras_name specs) vs_ir k (ras_name sp) Hnd) as [dv [Hdv Hbp]].
  - rewrite List.length_map; symmetry; exact Hlen_vs.
  - erewrite nth_error_map, Hsp_n; reflexivity.
  - rewrite Hvs_n in Hdv; inversion Hdv; subst dv; exact Hbp.
Qed.

Lemma collect_call_obls_mct_branch :
  forall arch callees ret_w p t_ir c mt mf,
    t_ir <> ICT_UB ->
    (forall cond dt df, t_ir <> ICT_Branch cond dt df) ->
    collect_call_obls arch callees ret_w p t_ir (MCT_Branch c mt mf) =
    match collect_call_obls arch callees ret_w ((true, c) :: p) t_ir mt,
          collect_call_obls arch callees ret_w ((false, c) :: p) t_ir mf with
    | inr o1, inr o2 => inr (o2 ++ o1)
    | inl err, _ => inl err
    | _, inl err => inl err
    end.
Proof.
  intros arch callees ret_w p t_ir c mt mf Hub Hbr; unfold collect_call_obls;
    destruct t_ir as [rw e_ir | | cond dt df | cn_ir args_ir rw_ir rv_ir c_ir].
  - cbn [collect_call_obls_acc collect_call_obls_ret_acc].
    destruct (collect_call_obls_ret_acc ret_w rw e_ir ((true, c) :: p) mt []) as [| o1]; [reflexivity |].
    rewrite collect_call_obls_ret_acc_shift.
    destruct (collect_call_obls_ret_acc ret_w rw e_ir ((false, c) :: p) mf []) as [| o2]; reflexivity.
  - exfalso; exact (Hub eq_refl).
  - exfalso; exact (Hbr _ _ _ eq_refl).
  - rewrite collect_call_obls_acc_ict_call_branch.
    destruct (collect_call_obls_acc arch callees ret_w ((true, c) :: p) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mt []) as [| o1];
      [reflexivity |].
    rewrite collect_call_obls_acc_shift; unfold collect_call_obls.
    destruct (collect_call_obls_acc arch callees ret_w ((false, c) :: p) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mf []) as [| o2];
      reflexivity.
Qed.

Lemma collect_call_obls_ict_branch :
  forall arch callees ret_w p cond dt df m,
    collect_call_obls arch callees ret_w p (ICT_Branch cond dt df) m =
    match collect_call_obls arch callees ret_w ((true, cond) :: p) dt m,
          collect_call_obls arch callees ret_w ((false, cond) :: p) df m with
    | inr o1, inr o2 => inr (o2 ++ o1)
    | inl err, _ => inl err
    | _, inl err => inl err
    end.
Proof.
  intros arch callees ret_w p cond dt df m; unfold collect_call_obls;
    cbn [collect_call_obls_acc];
    destruct (collect_call_obls_acc arch callees ret_w ((true, cond) :: p) dt m []) as [| o1];
    [reflexivity |];
    rewrite collect_call_obls_acc_shift; unfold collect_call_obls;
    destruct (collect_call_obls_acc arch callees ret_w ((false, cond) :: p) df m []) as [| o2];
    reflexivity.
Qed.

Lemma ir_mc_call_trees_sound {Pa : Params} :
  forall arch callees ret_w genv (penv : param_env Pa)
         t_ir t_mc (path : list (bool * cert_expr)) obls allowed_ir env_cur it_cur evs_mc (v_mc_ret : @Integers.bit_int ret_w),
    (forall c, In c callees ->
       forallb rv_valid_arg_spec (mcs_args c) = true /\
       NoDup (List.map ras_name (mcs_args c))) ->
    (forall (b : bool) c, In (b, c) path ->
       eval_closed_cert_expr penv dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv dummy_freeze_oracle None false) obls ->
    collect_call_obls arch callees ret_w path t_ir t_mc = inr obls ->
    ir_call_tree_wf allowed_ir ret_w t_ir ->
    ir_tree_denotes genv penv ret_w env_cur it_cur t_ir ->
    mc_tree_path_ok penv ret_w path t_mc evs_mc v_mc_ret ->
    let rel :=
      (fun (ev_m : string * list (@Integers.bit_int 64%positive) * @Integers.bit_int 64%positive)
           (ev_i : @mc_call_event Pa) =>
         let '(cn_m, args_m, ret_m) := ev_m in
         let '(cn_i, vs_i, dv_i) := ev_i in
         cn_i = cn_m /\
         exists c,
           find_callee_spec callees cn_m = Some c /\
           In c callees /\
           mc_strip_leading_at (mcs_name c) = cn_m /\
           List.length args_m = List.length (mcs_args c) /\
           List.length vs_i = List.length (mcs_args c) /\
           (forall k sp v_m,
              nth_error (mcs_args c) k = Some sp ->
              nth_error args_m k = Some v_m ->
              exists v : @Integers.bit_int (ras_width sp),
                build_param_env (List.map ras_name (mcs_args c)) vs_i (ras_name sp) =
                  Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
                match arch with
                | EA_Riscv64 =>
                    v_m =
                      (if Pos.eqb (ras_width sp) 64%positive then
                         @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                       else
                         match ras_ext sp with
                         | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                         | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
                         end)
                | EA_AArch64 =>
                    match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
                    | true, RAE_None =>
                        v_m = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
                    | false, RAE_None =>
                        @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive v_m) = v
                    | false, RAE_SignExt =>
                        @Integers.repr 32%positive (@Integers.unsigned 64%positive v_m) =
                        @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
                    | false, RAE_ZeroExt =>
                        @Integers.repr 32%positive (@Integers.unsigned 64%positive v_m) =
                        @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
                    | _, _ => False
                    end
                end) /\
           dv_i = DVALUE_Base (@DVALUE_I Pa (mcs_ret_width c) (rv_trunc_ret_val (mcs_ret_width c) ret_m))) in
    (exists tr_ir_pre,
       prefix_matches rel tr_ir_pre evs_mc /\
       cfg_call_steps_to_ub genv default_draw_strat env_cur it_cur tr_ir_pre) \/
    (exists tr_ir env_out dv_ir,
       Forall2 rel evs_mc tr_ir /\
       cfg_call_steps_to_ret genv default_draw_strat env_cur it_cur tr_ir default_draw_strat env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w v_mc_ret))).
Proof.
  intros arch callees ret_w genv penv t_ir;
    induction t_ir as [rw e_ir | | cond dt IHt df IHf | cn_ir args_ir rw_ir rv_ir c_ir IHc];
    intros t_mc path obls allowed_ir env_cur it_cur evs_mc v_mc_ret
           Hcs Hpath Hobls Hco Hwf_ir Hden Hmt rel.
  - (* ICT_Ret *)
    revert obls Hobls Hco.
    induction Hmt as [p0 ret_e v0 Hev_mc | p0 cond0 mt mf b tr_v v0 Hev_c Hmt_r IHm | p0 cn_m aes rw_m rext rv_m ohi cont avals a0r vc tr_v v0];
      intros obls Hobls Hco.
    + cbn [collect_call_obls collect_call_obls_acc collect_call_obls_ret_acc] in Hco.
      destruct (Pos.eqb rw ret_w) eqn:Erw; [| discriminate Hco].
      apply Pos.eqb_eq in Erw; subst rw.
      inversion Hco; subst obls; clear Hco.
      inversion Hobls as [| ? ? Ho _]; subst.
      destruct Hden as [_ (env_out & dv_ir & Hev_ir & _ & Hst)].
      pose proof (Ho eq_refl ltac:(discriminate) Hpath) as Href.
      cbn [refine_eou_dvalue] in Href; rewrite Hev_ir, Hev_mc in Href.
      right; exists [], env_out, dv_ir; repeat split; [constructor | exact (Hst default_draw_strat) | exact Href].
    + rewrite collect_call_obls_mct_branch in Hco by ltac:(discriminate).
      destruct (collect_call_obls arch callees ret_w ((true, cond0) :: p0) (ICT_Ret rw e_ir) mt) as [| o1] eqn:Eo1;
        [discriminate Hco |].
      destruct (collect_call_obls arch callees ret_w ((false, cond0) :: p0) (ICT_Ret rw e_ir) mf) as [| o2] eqn:Eo2;
        [discriminate Hco |].
      inversion Hco; subst obls; rewrite Forall_app in Hobls; destruct Hobls as [Ho2 Ho1].
      assert (Hpath' : forall b0 c0, In (b0, c0) ((b, cond0) :: p0) ->
        eval_closed_cert_expr penv dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Hev_c | exact (Hpath b0 c0 Hin)]. }
      destruct b; [exact (IHm Hpath' _ Ho1 Eo1) | exact (IHm Hpath' _ Ho2 Eo2)].
    + cbn [collect_call_obls collect_call_obls_acc collect_call_obls_ret_acc] in Hco;
        destruct p0; [discriminate Hco |].
      rewrite app_nil_r in Hco; inversion Hco; subst obls.
      exfalso; exact (imposs_obl_absurd penv dummy_freeze_oracle None false _ (fun C => ltac:(discriminate C)) Hpath Hobls).
  - (* ICT_UB *)
    cbn [ir_tree_denotes] in Hden.
    left; exists []; split; [constructor | exact (Hden default_draw_strat)].
  - (* ICT_Branch *)
    rewrite collect_call_obls_ict_branch in Hco.
    destruct (collect_call_obls arch callees ret_w ((true, cond) :: path) dt t_mc) as [| o1] eqn:Eo1;
      [discriminate Hco |].
    destruct (collect_call_obls arch callees ret_w ((false, cond) :: path) df t_mc) as [| o2] eqn:Eo2;
      [discriminate Hco |].
    inversion Hco; subst obls; rewrite Forall_app in Hobls; destruct Hobls as [Ho2 Ho1].
    cbn [ir_call_tree_wf] in Hwf_ir; destruct Hwf_ir as [_ [Hwf_t Hwf_f]].
    cbn [ir_tree_denotes] in Hden; destruct Hden as [[_ Hub] | [b [Hev Hb]]].
    + left; exists []; split; [constructor | exact (Hub default_draw_strat)].
    + assert (Hpath' : forall b0 c0, In (b0, c0) ((b, cond) :: path) ->
        eval_closed_cert_expr penv dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Hev | exact (Hpath b0 c0 Hin)]. }
      pose proof (mc_tree_path_ok_repath penv ret_w path ((b, cond) :: path) t_mc evs_mc v_mc_ret Hmt) as Hmt'.
      destruct b;
        [exact (IHt t_mc ((true, cond) :: path) o1 allowed_ir env_cur it_cur evs_mc v_mc_ret Hcs Hpath' Ho1 Eo1 Hwf_t Hb Hmt')
        | exact (IHf t_mc ((false, cond) :: path) o2 allowed_ir env_cur it_cur evs_mc v_mc_ret Hcs Hpath' Ho2 Eo2 Hwf_f Hb Hmt')].
  - (* ICT_Call *)
    cbn [ir_call_tree_wf] in Hwf_ir; destruct Hwf_ir as [_ [Hsup_c Hwf_c]].
    revert obls Hobls Hco.
    induction Hmt as [p0 ret_e v0 Hev_mc | p0 cond0 mt mf b tr_v v0 Hev_c Hmt_r IHm
                     | p0 cn_m aes rw_m rext rv_m ohi cont avals a0r vc tr_v v0 Hfa_mc Hrv_m Hvc_eq Hmt_cont _];
      intros obls Hobls Hco.
    + unfold collect_call_obls in Hco; rewrite collect_call_obls_acc_ict_call_ret in Hco;
        destruct p0; [discriminate Hco |].
      rewrite app_nil_r in Hco; inversion Hco; subst obls.
      exfalso; exact (imposs_obl_absurd penv dummy_freeze_oracle None false _ (fun C => ltac:(discriminate C)) Hpath Hobls).
    + rewrite collect_call_obls_mct_branch in Hco by ltac:(discriminate).
      destruct (collect_call_obls arch callees ret_w ((true, cond0) :: p0) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mt)
        as [| o1] eqn:Eo1; [discriminate Hco |].
      destruct (collect_call_obls arch callees ret_w ((false, cond0) :: p0) (ICT_Call cn_ir args_ir rw_ir rv_ir c_ir) mf)
        as [| o2] eqn:Eo2; [discriminate Hco |].
      inversion Hco; subst obls; rewrite Forall_app in Hobls; destruct Hobls as [Ho2 Ho1].
      assert (Hpath' : forall b0 c0, In (b0, c0) ((b, cond0) :: p0) ->
        eval_closed_cert_expr penv dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Hev_c | exact (Hpath b0 c0 Hin)]. }
      destruct b; [exact (IHm Hpath' _ Ho1 Eo1) | exact (IHm Hpath' _ Ho2 Eo2)].
    + unfold collect_call_obls in Hco; rewrite collect_call_obls_acc_ict_call_call in Hco.
      destruct (String.eqb cn_ir cn_m && Pos.eqb rw_ir rw_m && String.eqb rv_ir rv_m) eqn:Em.
      * rewrite !andb_true_iff in Em; destruct Em as [[Ecn Erw] Erv].
        apply String.eqb_eq in Ecn; apply Pos.eqb_eq in Erw; apply String.eqb_eq in Erv; subst cn_m rw_m rv_m.
        destruct (find_callee_spec callees cn_ir) as [sp |] eqn:Efc; [| discriminate Hco].
        destruct (Pos.eqb rw_ir (mcs_ret_width sp)) eqn:Ewrw; [apply Pos.eqb_eq in Ewrw | discriminate Hco].
        unfold build_call_arg_obls in *;
          destruct (build_call_arg_obls_acc cn_ir 0%nat arch p0 (mcs_args sp) args_ir aes []) as [| aobls] eqn:Ebao; [discriminate Hco |].
        rewrite collect_call_obls_acc_shift in Hco; unfold collect_call_obls in Hco.
        destruct (collect_call_obls_acc arch callees ret_w p0 c_ir cont []) as [| cobls] eqn:Eco;
          cbn [mcc_sum_map] in Hco; [discriminate Hco |].
        inversion Hco; subst obls; rewrite Forall_app in Hobls; destruct Hobls as [Hcobls Haobls].
        pose proof (find_callee_spec_in _ _ _ Efc) as [Hin_sp Hstrip].
        destruct (Hcs sp Hin_sp) as [Hvs_sp Hnd_sp].
        assert (Hvs_f : Forall rv_valid_arg_spec (mcs_args sp))
          by (apply Forall_forall; apply forallb_forall; exact Hvs_sp).
        cbn [ir_tree_denotes] in Hden; destruct Hden as [Hub | (dvs & Hfa_ir & Hk)].
        -- left; exists []; split; [constructor | exact (Hub default_draw_strat)].
        -- assert (Herv : penv rv_ir = Some (DVALUE_Base (@DVALUE_I Pa rw_ir vc))) by exact Hrv_m.
           destruct (Hk vc Herv) as (env1 & t1 & Hret1 & Hub1 & Hden1).
           destruct (@build_call_arg_obls_list_matches Pa cn_ir arch penv p0 (mcs_args sp) args_ir aes aobls avals dvs
                       Hpath Haobls Ebao Hvs_f Hnd_sp Hfa_ir Hfa_mc)
             as (Hlen_v & Hlen_a & Hitem).
           assert (Hrel_hd :
             rel (cn_ir, avals, a0r)
                 (cn_ir, dvs, DVALUE_Base (@DVALUE_I Pa rw_ir vc))).
           { unfold rel; split; [reflexivity |].
             exists sp; repeat split; try assumption.
             subst rw_ir vc; reflexivity. }
           destruct (IHc cont p0 cobls ((rv_ir, rw_ir) :: allowed_ir) env1 t1 tr_v v0
                       Hcs Hpath Hcobls Eco Hwf_c Hden1 Hmt_cont)
             as [[tr_pre [Hpm Hub_t]] | (tr_t & env_out & dv_ir & Hfa_t & Hret_t & Href_t)].
           ++ left; exists ((cn_ir, dvs, DVALUE_Base (@DVALUE_I Pa rw_ir vc)) :: tr_pre); split.
              ** constructor; [exact Hrel_hd | exact Hpm].
              ** exact (Hub1 default_draw_strat tr_pre Hub_t).
           ++ right; exists ((cn_ir, dvs, DVALUE_Base (@DVALUE_I Pa rw_ir vc)) :: tr_t), env_out, dv_ir;
                repeat split; [constructor; [exact Hrel_hd | exact Hfa_t] | exact (Hret1 default_draw_strat tr_t default_draw_strat env_out dv_ir Hret_t) | exact Href_t].
      * destruct p0; [discriminate Hco |].
        rewrite app_nil_r in Hco; inversion Hco; subst obls.
        exfalso; exact (imposs_obl_absurd penv dummy_freeze_oracle None false _ (fun C => ltac:(discriminate C)) Hpath Hobls).
Qed.

