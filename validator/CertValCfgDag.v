(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Bounded-DAG Control-Flow Reifier & Soundness ([CertValidator.CertValCfgDag])

    Purpose:
      Defines phi reification ([reify_phi_evals]), instruction and block-body
      reification ([reify_code_step], [reify_code]) covering pure intrinsics,
      [vec1] poison extraction, and return-only calls, with src/tgt soundness.

    Trust Contract & Fail-Closed Boundary:
      Fail-closed code-block reifier ([reify_code_typing],
      [eval_reified_code_src], [eval_reified_code_tgt]); unmodeled instructions,
      unsupported calls, or typing mismatches fail closed ([None]).

    Assumptions:
      Depends on Stdlib, [Paco], [ITree], [ExtLib], [Vellvm], [Diag], and
      [CertFormat]/[AigLrat]/[AlgRules]/[CfgDag]/[CertValOpenWorld]/[CertValExpReify].

    Section Outline:
      5.5 Bounded-DAG Control-Flow Reifier ([cfg_dag]) & Operational Soundness:
      phi reification, [vec1]/call helpers, [reify_code], and src/tgt soundness. *)

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
  AlgRules
  CfgDag
  CertValOpenWorld
  CertValExpReify.

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

(** *** 5.5 Bounded-DAG Control-Flow Reifier ([cfg_dag]) & Operational Soundness *)

Lemma NoDup_app_inv_l {A : Type} :
  forall (xs ys : list A), NoDup (xs ++ ys) -> NoDup xs.
Proof.
  induction xs as [| x rx IH]; intros ys Hnd; [constructor |].
  cbn in Hnd; inversion Hnd as [| ? ? Hni Hndr]; subst.
  constructor; [intros Hin; apply Hni, in_app_iff; left; exact Hin | exact (IH ys Hndr)].
Qed.

Lemma bit_int_1_equ_one_eq_unsigned :
  forall (cbit : @Integers.bit_int 1),
    equ cbit one = (@Integers.unsigned 1 cbit =? 1)%Z.
Proof.
  intros cbit; cbn [equ one VInt_Bounded]; unfold Integers.eq.
  rewrite (@Integers.unsigned_one 1).
  match goal with
  | |- (if ?c then _ else _) = _ => destruct c as [Heq | Hneq]
  end.
  - symmetry; apply Z.eqb_eq; exact Heq.
  - symmetry; apply Z.eqb_neq; exact Hneq.
Qed.

Lemma assoc_in_pargs :
  forall (bid : block_id) (pargs : list (block_id * exp dtyp)) (op : exp dtyp),
    assoc bid pargs = Some op -> In (bid, op) pargs.
Proof.
  intros bid pargs op; induction pargs as [| [b' e'] rest IH]; intros H.
  - inversion H.
  - destruct (RawIDOrd.eq_dec bid b') as [<- | Hneq].
    + rewrite (assoc_hd bid e' rest) in H; inversion H; subst; left; reflexivity.
    + rewrite (assoc_tl bid b' e' rest Hneq) in H; right; exact (IH H).
Qed.

Lemma wf_smap_entries_empty :
  forall allowed defs seen uf,
    wf_smap_entries allowed defs seen uf (RM.empty _).
Proof.
  intros allowed defs seen uf r w ce Hf.
  rewrite RMF.F.empty_o in Hf; discriminate Hf.
Qed.

Lemma wf_smap_entries_add :
  forall allowed defs seen uf smap id w ce,
    wf_smap_entries allowed defs seen uf smap ->
    In id defs ->
    wt_cert_expr [] ce = true ->
    cert_expr_bit_width ce = w ->
    is_let_free_expr ce = true ->
    incl (collect_free_vars [] ce) allowed ->
    (uf = true -> incl (collect_freeze_keys ce) seen) ->
    wf_smap_entries allowed defs seen uf (RM.add id (w, ce) smap).
Proof.
  intros allowed defs seen uf smap id w ce Hsmap Hid Hwt Hbw Hlf Hfv Hfk r wr cer Hf.
  destruct (RawIDOrd.eq_dec id r) as [Heq | Hneq].
  - rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst r wr cer.
    repeat split; assumption.
  - rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (Hsmap r wr cer Hf).
Qed.

Lemma env_matches_smap_empty {Pa : Params} :
  forall defs (penv : param_env Pa) foracle env,
    env_matches_smap defs penv foracle (RM.empty _) env.
Proof.
  intros defs penv foracle env r w ce Hf.
  rewrite RMF.F.empty_o in Hf; discriminate Hf.
Qed.

Lemma env_matches_smap_add {Pa : Params} :
  forall defs (penv : param_env Pa) foracle smap (env : rmap (@dvalue Pa)) id w ce dv,
    env_matches_smap defs penv foracle smap env ->
    In id defs ->
    eval_closed_cert_expr penv foracle ce = raise_ret dv ->
    wf_scalar_dvalue w dv ->
    env_matches_smap defs penv foracle (RM.add id (w, ce) smap) (RM.add id dv env).
Proof.
  intros defs penv foracle smap env id w ce dv Henv Hid Hev Hsc r wr cer Hf.
  destruct (RawIDOrd.eq_dec id r) as [Heq | Hneq].
  - rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst r wr cer.
    split; [exact Hid | exists dv; split; [apply RMF.F.add_eq_o; reflexivity | split; assumption]].
  - rewrite RMF.F.add_neq_o in Hf by exact Hneq.
    destruct (Henv r wr cer Hf) as [Hr [dv' [Hfe [Hev' Hsc']]]].
    split; [exact Hr | exists dv'; split; [rewrite RMF.F.add_neq_o by exact Hneq; exact Hfe | split; assumption]].
Qed.

Fixpoint wrap_evals (evals : list (positive * cert_expr)) (k : cfg_dag)
  {struct evals} : cfg_dag :=
  match evals with
  | [] => k
  | (w, ce) :: rest => CD_Eval w ce (wrap_evals rest k)
  end.

Fixpoint wrap_phi_evals
  (pevals : list (raw_id * positive * cert_expr)) (k : cfg_dag)
  {struct pevals} : cfg_dag :=
  match pevals with
  | [] => k
  | (_, w, ce) :: rest => CD_Eval w ce (wrap_phi_evals rest k)
  end.

Fixpoint apply_phi_smap
  (smap : rmap (positive * cert_expr))
  (pevals : list (raw_id * positive * cert_expr))
  {struct pevals} : rmap (positive * cert_expr) :=
  match pevals with
  | [] => smap
  | (id, w, ce) :: rest => apply_phi_smap (RM.add id (w, ce) smap) rest
  end.

Fixpoint apply_phi_env {Pa : Params}
  (env : rmap (@dvalue Pa)) (dvs : list (raw_id * @dvalue Pa))
  {struct dvs} : rmap (@dvalue Pa) :=
  match dvs with
  | [] => env
  | (id, dv) :: rest => apply_phi_env (RM.add id dv env) rest
  end.

Lemma cfg_steps_lwrite_list {Pa : Params} :
  forall (dvs : list (raw_id * @dvalue Pa))
         (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)),
    cfg_steps_to_ret sigma env
      (map_monad (m := CFGtop) (fun '(id, dv) => lwrite id dv) dvs)
      sigma (apply_phi_env env dvs) (List.map (fun _ => tt) dvs).
Proof.
  induction dvs as [| [id dv] rest IH]; intros sigma env; cbn [map_monad apply_phi_env List.map].
  - apply CSR_Ret; reflexivity.
  - eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite |].
    eapply cfg_steps_to_ret_bind; [apply IH | apply CSR_Ret; reflexivity].
Qed.

Definition phi_eval_wf_entry
  (allowed : list (string * positive))
  (defs : list raw_id)
  (seen : list freeze_key)
  (uf : bool)
  (p : raw_id * positive * cert_expr) : Prop :=
  let '(id, w, ce) := p in
  In id defs /\
  wt_cert_expr [] ce = true /\
  cert_expr_bit_width ce = w /\
  is_let_free_expr ce = true /\
  incl (collect_free_vars [] ce) allowed /\
  (uf = true -> incl (collect_freeze_keys ce) seen).

Lemma phi_eval_wf_entry_mono :
  forall allowed defs seen1 seen2 uf pevals,
    incl seen1 seen2 ->
    Forall (phi_eval_wf_entry allowed defs seen1 uf) pevals ->
    Forall (phi_eval_wf_entry allowed defs seen2 uf) pevals.
Proof.
  intros allowed defs seen1 seen2 uf pevals Hinc Hfa.
  induction Hfa as [| [[id w] ce] rest (Hid & Hwt & Hbw & Hlf & Hfv & Hfk) _ IH]; [constructor |].
  constructor; [| exact IH].
  repeat split; try assumption.
  intros Huf u Hu; exact (Hinc u (Hfk Huf u Hu)).
Qed.

Lemma apply_phi_smap_wf :
  forall allowed defs seen uf pevals smap,
    wf_smap_entries allowed defs seen uf smap ->
    Forall (phi_eval_wf_entry allowed defs seen uf) pevals ->
    wf_smap_entries allowed defs seen uf (apply_phi_smap smap pevals).
Proof.
  intros allowed defs seen uf pevals smap Hsmap Hfa; revert smap Hsmap.
  induction Hfa as [| [[id w] ce] rest (Hid & Hwt & Hbw & Hlf & Hfv & Hfk) _ IH];
    intros smap Hsmap; cbn [apply_phi_smap]; [exact Hsmap |].
  apply IH; exact (wf_smap_entries_add allowed defs seen uf smap id w ce Hsmap Hid Hwt Hbw Hlf Hfv Hfk).
Qed.

Lemma wrap_phi_evals_wf :
  forall allowed defs seen uf pevals k,
    Forall (phi_eval_wf_entry allowed defs seen uf) pevals ->
    wf_cfg_dag allowed k = true ->
    wf_cfg_dag allowed (wrap_phi_evals pevals k) = true.
Proof.
  intros allowed defs seen uf pevals k Hfa Hk.
  induction Hfa as [| [[id w] ce] rest (_ & Hwt & Hbw & Hlf & Hfv & _) _ IH];
    cbn [wrap_phi_evals wf_cfg_dag]; [exact Hk |].
  rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), IH; reflexivity.
Qed.

Definition phi_eval_pair_matches {Pa : Params}
  (penv : param_env Pa)
  (foracle : freeze_oracle)
  (p : raw_id * positive * cert_expr)
  (dv_p : raw_id * @dvalue Pa) : Prop :=
  let '(id, w, ce) := p in
  let '(id', dv) := dv_p in
  id' = id /\
  eval_closed_cert_expr penv foracle ce = raise_ret dv /\
  wf_scalar_dvalue w dv.

Lemma phi_eval_pair_matches_prepend {Pa : Params} :
  forall allowed defs seen added fmap (penv : param_env Pa) pevals dvs,
    Forall (phi_eval_wf_entry allowed defs seen true) pevals ->
    (forall k z, In (k, z) added -> ~ In k seen) ->
    Forall2 (phi_eval_pair_matches penv (oracle_of_fmap fmap)) pevals dvs ->
    Forall2 (phi_eval_pair_matches penv (oracle_of_fmap (added ++ fmap))) pevals dvs.
Proof.
  intros allowed defs seen added fmap penv pevals dvs Hwf Hdisj Hfa2.
  revert dvs Hfa2.
  induction Hwf as [| [[id w] ce] rest (_ & _ & _ & Hlf & _ & Hfk) _ IH];
    intros dvs Hfa2.
  - inversion Hfa2; subst; constructor.
  - inversion Hfa2 as [| ? [id' dv] ? dvs_r Hpair Hfa2_r]; subst.
    cbn [phi_eval_pair_matches] in Hpair; destruct Hpair as [Heq [Hev Hsc]].
    constructor; [| exact (IH dvs_r Hfa2_r)].
    cbn [phi_eval_pair_matches]; split; [exact Heq | split; [| exact Hsc]].
    exact (eq_trans (eval_let_free_prepend_fmap ce penv added fmap seen Hlf (Hfk eq_refl) Hdisj) Hev).
Qed.

Lemma apply_phi_env_matches {Pa : Params} :
  forall allowed defs seen uf (penv : param_env Pa) foracle smap env pevals dvs,
    env_matches_smap defs penv foracle smap env ->
    Forall (phi_eval_wf_entry allowed defs seen uf) pevals ->
    Forall2 (phi_eval_pair_matches penv foracle) pevals dvs ->
    env_matches_smap defs penv foracle (apply_phi_smap smap pevals) (apply_phi_env env dvs).
Proof.
  intros allowed defs seen uf penv foracle smap env pevals dvs Henv Hwf Hfa2.
  revert smap env Henv dvs Hfa2.
  induction Hwf as [| [[id w] ce] rest (Hid & _) _ IH];
    intros smap env Henv dvs Hfa2.
  - inversion Hfa2; subst; exact Henv.
  - inversion Hfa2 as [| ? [id' dv] ? dvs_r Hpair Hfa2_r]; subst.
    cbn [phi_eval_pair_matches] in Hpair; destruct Hpair as [-> [Hev Hsc]].
    cbn [apply_phi_smap apply_phi_env].
    apply IH; [exact (env_matches_smap_add defs penv foracle smap env id w ce dv Henv Hid Hev Hsc) | exact Hfa2_r].
Qed.

Lemma apply_phi_env_preserves_nondefs {Pa : Params} :
  forall allowed defs seen uf (penv : param_env Pa) foracle (env : rmap (@dvalue Pa)) pevals dvs r,
    Forall (phi_eval_wf_entry allowed defs seen uf) pevals ->
    Forall2 (phi_eval_pair_matches penv foracle) pevals dvs ->
    ~ In r defs ->
    RM.find r (apply_phi_env env dvs) = RM.find r env.
Proof.
  intros allowed defs seen uf penv foracle env pevals dvs r Hwf Hfa2 Hnin.
  revert env dvs Hfa2.
  induction Hwf as [| [[id w] ce] rest (Hid & _) _ IH];
    intros env dvs Hfa2.
  - inversion Hfa2; subst; reflexivity.
  - inversion Hfa2 as [| ? [id' dv] ? dvs_r Hpair Hfa2_r]; subst.
    cbn [phi_eval_pair_matches] in Hpair; destruct Hpair as [-> _].
    cbn [apply_phi_env].
    rewrite (IH (RM.add id dv env) dvs_r Hfa2_r).
    apply RMF.F.add_neq_o; intros ->; exact (Hnin Hid).
Qed.

Fixpoint reify_phi_evals
  (uf : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (smap0 : rmap (positive * cert_expr))
  (bid_from : block_id)
  (seen : list freeze_key)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  {struct phis} : option (list (raw_id * positive * cert_expr) * list freeze_key) :=
  match phis with
  | [] => Some ([], seen)
  | (id, Phi _ dt pargs, _) :: rest =>
      if raw_id_in_list id defs then
        match dt, assoc bid_from pargs with
        | DTYPE_Base (DTYPE_I w), Some op =>
            match reify_exp uf params src_pnames defs smap0 seen
                    (Some (DTYPE_Base (DTYPE_I w))) op with
            | Some (_, ce, seen1) =>
                match reify_phi_evals uf params src_pnames defs smap0 bid_from seen1 rest with
                | Some (pevals, seen2) => Some ((id, w, ce) :: pevals, seen2)
                | None => None
                end
            | None => None
            end
        | _, _ => None
        end
      else None
  end.

Lemma reify_phi_evals_typing :
  forall phis uf params src_pnames defs allowed smap0 bid_from seen0 pevals seen2,
    wf_smap_entries allowed defs seen0 uf smap0 ->
    (forall id fm dt pargs md op idx w0 pnm,
      In (id, Phi fm dt pargs, md) phis ->
      In (bid_from, op) pargs ->
      In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some dt) op) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    reify_phi_evals uf params src_pnames defs smap0 bid_from seen0 phis = Some (pevals, seen2) ->
    incl seen0 seen2 /\
    Forall (phi_eval_wf_entry allowed defs seen2 uf) pevals.
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros uf params src_pnames defs allowed smap0 bid_from seen0 pevals seen2 Hsmap0 Hpu Hr;
    cbn [reify_phi_evals] in Hr.
  - inversion Hr; subst; split; [intros x Hx; exact Hx | constructor].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    apply raw_id_in_list_spec in Hid.
    destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    pose proof (assoc_in_pargs bid_from pargs op Hassoc) as Hin_op.
    destruct (reify_exp uf params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce] seen1] |] eqn:Hre; [| discriminate].
    destruct (reify_phi_evals uf params src_pnames defs smap0 bid_from seen1 rest)
      as [[pevals_r seen2'] |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals seen2'; clear Hr.
    destruct (reify_exp_typing op uf params src_pnames defs allowed smap0 seen0
                (Some (DTYPE_Base (DTYPE_I w))) w1 ce seen1 Hsmap0
                (fun idx w0 pnm Hin => Hpu id fm (DTYPE_Base (DTYPE_I w)) pargs md op idx w0 pnm
                                         (or_introl eq_refl) Hin_op Hin) Hre)
      as (Hcw & Hwt & Hbw & Hlf & Hfv & Hinc01 & Hfk).
    apply check_opt_int_width_some_inv in Hcw; subst w1.
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap0 Hinc01 Hsmap0) as Hsmap1.
    destruct (IH uf params src_pnames defs allowed smap0 bid_from seen1 pevals_r seen2 Hsmap1
                (fun id' fm' dt' pargs' md' op' idx w0 pnm Hin_p =>
                   Hpu id' fm' dt' pargs' md' op' idx w0 pnm (or_intror Hin_p)) Hrr)
      as [Hinc12 Hfa_r].
    split; [intros x Hx; exact (Hinc12 x (Hinc01 x Hx)) |].
    constructor; [| exact Hfa_r].
    repeat split; try assumption.
    intros Huf u Hu; exact (Hinc12 u (Hfk Huf u Hu)).
Qed.

Lemma eval_reified_phi_map_src {Pa : Params} :
  forall phis params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) smap0 (env0 : rmap (@dvalue Pa))
         bid_from seen0 pevals seen2,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall id fm dt pargs md op idx dt_u,
      In (id, Phi fm dt pargs, md) phis ->
      In (bid_from, op) pargs ->
      In (idx, dt_u) (exp_param_uses params defs (Some dt) op) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_smap_entries allowed defs seen0 false smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) foracle smap0 env0 ->
    reify_phi_evals false params src_pnames defs smap0 bid_from seen0 phis = Some (pevals, seen2) ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s,
           cfg_steps_to_ub (chain_draws draws tail_s) env0
             (map_monad (m := CFGtop) (denote_phi bid_from) phis)) /\
        (forall k, eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_phi_evals pevals k) = DO_UB)) \/
       (exists dvs,
          Forall2 (phi_eval_pair_matches (build_param_env src_pnames vs) foracle) pevals dvs /\
          (forall k,
             eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_phi_evals pevals k) =
             eval_cfg_dag (build_param_env src_pnames vs) foracle k) /\
          (forall tail_s,
             cfg_steps_to_ret (chain_draws draws tail_s) env0
               (map_monad (m := CFGtop) (denote_phi bid_from) phis)
               tail_s env0 dvs))).
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros params src_pnames defs allowed arg_dtys vs foracle smap0 env0 bid_from seen0 pevals seen2
           Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr;
    cbn [reify_phi_evals] in Hr.
  - inversion Hr; subst pevals seen2.
    exists []; split; [constructor | right; exists []].
    split; [constructor | split; [intros k; reflexivity | intros tail_s; apply CSR_Ret; reflexivity]].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    pose proof (assoc_in_pargs bid_from pargs op Hassoc) as Hin_op.
    destruct (reify_exp false params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce] seen1] |] eqn:Hre; [| discriminate].
    destruct (reify_phi_evals false params src_pnames defs smap0 bid_from seen1 rest)
      as [[pevals_r seen2'] |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals seen2'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hre)) as ->.
    destruct (eval_reified_exp_src op params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu id fm (DTYPE_Base (DTYPE_I w)) pargs md op idx d
                                    (or_introl eq_refl) Hin_op Hin)
                Hpe Hwfs Henv Hre)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
        apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub1 tail_s).
      * intros k; cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
    + pose proof (wf_smap_entries_false_seen allowed defs seen0 seen1 smap0 Hwfs) as Hwfs1.
      destruct (IH params src_pnames defs allowed arg_dtys vs foracle smap0 env0 bid_from seen1 pevals_r seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun id' fm' dt' pargs' md' op' idx d Hin_p =>
                     Hpu id' fm' dt' pargs' md' op' idx d (or_intror Hin_p))
                  Hpe Hwfs1 Henv Hrr)
        as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | [dvs_r [Hfa2_m [Hev_k Hst2]]]]).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply cfg_steps_to_ub_bind_r.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst1 (chain_draws draws2 tail_s)))
                | apply CSR_Ret; reflexivity].
           ++ apply cfg_steps_to_ub_bind_l; exact (Hub2 tail_s).
        -- intros k; cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_ub2 k).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right].
        exists ((id, dv1) :: dvs_r); split; [| split].
        -- constructor; [split; [reflexivity | split; assumption] | exact Hfa2_m].
        -- intros k; cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_k k).
        -- intros tail_s; rewrite chain_draws_app; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst1 (chain_draws draws2 tail_s)))
                | apply CSR_Ret; reflexivity].
           ++ eapply cfg_steps_to_ret_bind; [exact (Hst2 tail_s) | apply CSR_Ret; reflexivity].
Qed.

Lemma eval_reified_phi_map_tgt {Pa : Params} :
  forall phis params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         smap0 (env0 : rmap (@dvalue Pa)) bid_from seen0 pevals seen2,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall id fm dt pargs md op idx dt_u,
      In (id, Phi fm dt pargs, md) phis ->
      In (bid_from, op) pargs ->
      In (idx, dt_u) (exp_param_uses params defs (Some dt) op) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed defs seen0 true smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap0 env0 ->
    reify_phi_evals true params src_pnames defs smap0 bid_from seen0 phis = Some (pevals, seen2) ->
    exists added : list (freeze_key * Z),
      (forall key z, In (key, z) added -> In key seen2 /\ ~ In key seen0) /\
      ((forall k,
          eval_cfg_dag (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) (wrap_phi_evals pevals k) = DO_UB) \/
       (exists sigma1 dvs,
          wf_draw_strat sigma1 /\
          Forall2 (phi_eval_pair_matches (build_param_env src_pnames vs)
                     (oracle_of_fmap (added ++ fmap0))) pevals dvs /\
          (forall fmap_later k,
             (forall key z, In (key, z) fmap_later -> ~ In key seen2) ->
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) (wrap_phi_evals pevals k) =
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) k) /\
          cfg_steps_to_ret sigma0 env0
            (map_monad (m := CFGtop) (denote_phi bid_from) phis)
            sigma1 env0 dvs)).
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 bid_from seen0 pevals seen2
           Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr;
    cbn [reify_phi_evals] in Hr.
  - inversion Hr; subst pevals seen2.
    exists []; split; [intros _ _ [] | right; exists sigma0, []].
    split; [exact Hwfd0 | split; [constructor | split; [intros fmap_later k _; reflexivity | apply CSR_Ret; reflexivity]]].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    pose proof (assoc_in_pargs bid_from pargs op Hassoc) as Hin_op.
    destruct (reify_exp true params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce] seen1] |] eqn:Hre; [| discriminate].
    destruct (reify_phi_evals true params src_pnames defs smap0 bid_from seen1 rest)
      as [[pevals_r seen2'] |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals seen2'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hre)) as ->.
    destruct (reify_exp_freeze_props op true params src_pnames defs allowed smap0 seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce seen1 Hwfs0 Hre)
      as (Hlf1 & Hinc01 & Hfk1).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 true smap0 Hinc01 Hwfs0) as Hwfs1.
    assert (Hinc12 : incl seen1 seen2).
    { set (ext_vars :=
        allowed ++
        List.flat_map (fun '(_, Phi _ dt_p pargs_p, _) =>
          List.flat_map (fun '(_, e_p) =>
            List.flat_map (fun '(idx, dt_u) =>
              match dt_u, nth_error src_pnames idx with
              | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
              | _, _ => []
              end) (exp_param_uses params defs (Some dt_p) e_p)) pargs_p) rest).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen1 true smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs1 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpu_ext : forall id' fm' dt' pargs' md' op' idx w0 pnm,
        In (id', Phi fm' dt' pargs', md') rest ->
        In (bid_from, op') pargs' ->
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some dt') op') ->
        nth_error src_pnames idx = Some pnm ->
        In (pnm, w0) ext_vars).
      { intros id' fm' dt' pargs' md' op' idx w0 pnm Hin1 Hin2 Hin3 Hpnm.
        apply in_app_iff; right; apply in_flat_map; exists (id', Phi fm' dt' pargs', md'); split; [exact Hin1 |].
        apply in_flat_map; exists (bid_from, op'); split; [exact Hin2 |].
        apply in_flat_map; exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin3 | rewrite Hpnm; left; reflexivity]. }
      exact (proj1 (reify_phi_evals_typing rest true params src_pnames defs ext_vars smap0 bid_from
                      seen1 pevals_r seen2 Hsmap_ext Hpu_ext Hrr)). }
    destruct (eval_reified_exp_tgt op params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu id fm (DTYPE_Base (DTYPE_I w)) pargs md op idx d
                                    (or_introl eq_refl) Hin_op Hin)
                Hpe Hwfd0 Hwfs0 Henv0 Hre)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma_m & dv1 & Hwfd_m & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0].
      * left; intros k; cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                    (build_param_env src_pnames vs) smap0 env0 Hwfs0
                    (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv1.
      destruct (IH params src_pnames defs allowed arg_dtys vs sigma_m (added1 ++ fmap0) smap0 env0 bid_from
                  seen1 pevals_r seen2 Hnd Hlp Hls Hla Hvs
                  (fun id' fm' dt' pargs' md' op' idx d Hin_p =>
                     Hpu id' fm' dt' pargs' md' op' idx d (or_intror Hin_p))
                  Hpe Hwfd_m Hwfs1 Henv1 Hrr)
        as (added2 & Had2 & [Hev_ub2 | (sigma2 & dvs_r & Hwfd2 & Hfa2_m & Hev_k & Hst2)]).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
        split; [exact Had12 | left; intros k].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun q z H => proj2 (Had2 q z H))) as Hev1'.
        cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1', Hev1; exact (Hev_ub2 k).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
        split; [exact Had12 | right; exists sigma2, ((id, dv1) :: dvs_r)].
        pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun q z H => proj2 (Had2 q z H))) as Hev1'.
        split; [exact Hwfd2 | split; [| split]].
        -- rewrite <- app_assoc; constructor;
             [split; [reflexivity | split; [rewrite Hev1'; exact Hev1 | exact Hsc1]] | exact Hfa2_m].
        -- intros fmap_later k Hdisj_lat.
           assert (Hdisj_lat1 : forall key z, In (key, z) (fmap_later ++ added2) -> ~ In key seen1).
           { intros key z Hkz; apply in_app_iff in Hkz as [Hl | Ha2].
             - intros Hs1; exact (Hdisj_lat key z Hl (Hinc12 key Hs1)).
             - exact (proj2 (Had2 key z Ha2)). }
           replace (fmap_later ++ (added2 ++ added1) ++ fmap0)
             with ((fmap_later ++ added2) ++ (added1 ++ fmap0))
             by (rewrite !app_assoc; reflexivity).
           pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                         (fmap_later ++ added2) (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl) Hdisj_lat1)
             as Hev_lat1.
           cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev_lat1, Hev1.
           replace ((fmap_later ++ added2) ++ added1 ++ fmap0)
             with (fmap_later ++ (added2 ++ (added1 ++ fmap0)))
             by (rewrite !app_assoc; reflexivity).
           exact (Hev_k fmap_later k Hdisj_lat).
        -- cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst1) | apply CSR_Ret; reflexivity].
           ++ eapply cfg_steps_to_ret_bind; [exact Hst2 | apply CSR_Ret; reflexivity].
Qed.

Lemma list_2step_ind {A : Type} (P : list A -> Prop) :
  P [] ->
  (forall x, P [x]) ->
  (forall x y rest, P (y :: rest) -> P rest -> P (x :: y :: rest)) ->
  forall xs, P xs.
Proof.
  intros Hnil Hone Htwo xs.
  cut (P xs /\ match xs with [] => True | _ :: tl => P tl end); [tauto |].
  induction xs as [| x rest [Hrest Htl]].
  - split; [exact Hnil | exact I].
  - destruct rest as [| y rest'].
    + split; [exact (Hone x) | exact Hnil].
    + split; [exact (Htwo x y rest' Hrest Htl) | exact Hrest].
Qed.

Inductive vec1_extract_kind : Set :=
| V1K_Extract
| V1K_Bitcast.

Definition match_vec1_id_pair {M : Type}
  (smap : rmap (positive * cert_expr)) (defs params : list raw_id)
  (i1 i2 : instr_id * instr dtyp * M)
  : option (raw_id * raw_id * positive * exp dtyp * vec1_extract_kind) :=
  match i1, i2 with
  | (IId tmp,
     INSTR_Op (OP_InsertElement
                 (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w1)), EXP_Poison)
                 (DTYPE_Base (DTYPE_I w2), val_exp)
                 (DTYPE_Base (DTYPE_I 1%positive), EXP_Bool false)),
     _),
    (IId dst,
     INSTR_Op (OP_ExtractElement
                 (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w3)), EXP_Ident (ID_Local r3))
                 (DTYPE_Base (DTYPE_I 1%positive), EXP_Bool false)),
     _) =>
      if Pos.eqb w1 w2 && Pos.eqb w2 w3 && raw_id_eqb r3 tmp &&
         negb (raw_id_eqb tmp dst) &&
         raw_id_in_list tmp defs && raw_id_in_list dst defs &&
         negb (raw_id_in_list tmp params) &&
         match RM.find tmp smap with None => true | Some _ => false end
      then Some (tmp, dst, w1, val_exp, V1K_Extract)
      else None
  | (IId tmp,
     INSTR_Op (OP_InsertElement
                 (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w1)), EXP_Poison)
                 (DTYPE_Base (DTYPE_I w2), val_exp)
                 (DTYPE_Base (DTYPE_I 1%positive), EXP_Bool false)),
     _),
    (IId dst,
     INSTR_Op (OP_Conversion CONV_Bitcast
                 (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w3)))
                 (EXP_Ident (ID_Local r3))
                 (DTYPE_Base (DTYPE_I w4))),
     _) =>
      if Pos.eqb w1 w2 && Pos.eqb w2 w3 && Pos.eqb w3 w4 && raw_id_eqb r3 tmp &&
         negb (raw_id_eqb tmp dst) &&
         raw_id_in_list tmp defs && raw_id_in_list dst defs &&
         negb (raw_id_in_list tmp params) &&
         match RM.find tmp smap with None => true | Some _ => false end
      then Some (tmp, dst, w1, val_exp, V1K_Bitcast)
      else None
  | _, _ => None
  end.

Lemma cert_dtyp_eqb_vec1_base : forall w,
  dtyp_eqb (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w))) (DTYPE_Base (DTYPE_I w)) = false.
Proof.
  intros w; reflexivity.
Qed.

Lemma cert_bit_sizeof_vec1_eq {Pa : Params} : forall w,
  bit_sizeof_dtyp (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w))) =
  bit_sizeof_dtyp (DTYPE_Base (DTYPE_I w)).
Proof.
  intros w; rewrite bit_sizeof_dtyp_vector; apply N.mul_1_l.
Qed.

Lemma cert_wf_scalar_dvalue_base {Pa : Params} :
  forall w (dv : @dvalue Pa),
    wf_scalar_dvalue w dv ->
    exists db : @dvalue_base Pa,
      dv = DVALUE_Base db /\ @dvalue_to_dvalue_base Pa dv = raise_ret db.
Proof.
  intros w dv [-> | [iv ->]]; eexists; split; reflexivity.
Qed.

Lemma cert_insert_vec1_poison_zero {Pa : Params} :
  forall w (db : @dvalue_base Pa),
    @insert_element Pa (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w)))
      (DVALUE_Base DVALUE_Poison) (DVALUE_Base db)
      (DVALUE_Base (@DVALUE_I Pa 1%positive (@VellvmIntegers.zero (@Integers.bit_int 1%positive) (VInt_Bounded 1%positive)))) =
    raise_ret (DVALUE_Array true [DVALUE_Base db]).
Proof.
  intros w db; unfold insert_element, dvalue_to_Z;
    cbn [VellvmIntegers.signed VellvmIntegers.zero VInt_Bounded];
    rewrite (@Integers.signed_zero 1%positive); reflexivity.
Qed.

Lemma cert_extract_vec1_zero {Pa : Params} :
  forall (dv : @dvalue Pa),
    @extract_element Pa (DVALUE_Array true [dv])
      (DVALUE_Base (@DVALUE_I Pa 1%positive (@VellvmIntegers.zero (@Integers.bit_int 1%positive) (VInt_Bounded 1%positive)))) =
    raise_ret dv.
Proof.
  intros dv; unfold extract_element, dvalue_to_Z;
    cbn [VellvmIntegers.signed VellvmIntegers.zero VInt_Bounded];
    rewrite (@Integers.signed_zero 1%positive); reflexivity.
Qed.

Lemma cert_dvalue_to_memory_bytes_vec1 {Pa : Params} :
  forall w (dv : @dvalue Pa),
    wf_scalar_dvalue w dv ->
    @dvalue_to_memory_bytes Pa (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w)))
      (DVALUE_Array true [dv]) None =
    @dvalue_to_memory_bytes Pa (DTYPE_Base (DTYPE_I w)) dv None.
Proof.
  intros w dv [-> | [iv ->]];
    unfold dvalue_to_memory_bytes; cbn [acc_dvalue_to_memory_bytes_h];
    [set (res := acc_memory_bytes_of_dvalue_base (DTYPE_I w) DVALUE_Poison 0%N [])
    | set (res := acc_memory_bytes_of_dvalue_base (DTYPE_I w) (@DVALUE_I Pa w iv) 0%N [])];
    destruct res as [off bs];
    cbn [bind ret EOU_monad accumulate_padding_bytes accumulate_poison_bytes accumulate_memory_bytes accumulate_padding];
    reflexivity.
Qed.

Lemma cert_bitcast_vec1_scalar {Pa : Params} :
  forall w (dv : @dvalue Pa),
    wf_scalar_dvalue w dv ->
    @convert Pa CONV_Bitcast (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w)))
      (DVALUE_Array true [dv]) (DTYPE_Base (DTYPE_I w)) = Ret dv.
Proof.
  intros w dv Hwf.
  unfold convert; rewrite cert_dtyp_eqb_vec1_base, (@cert_bit_sizeof_vec1_eq Pa w), N.eqb_refl.
  rewrite (cert_dvalue_to_memory_bytes_vec1 w dv Hwf).
  assert (Hdtyp : dvalue_has_dtyp dv (DTYPE_Base (DTYPE_I w)))
    by (apply dvalue_has_dtyp_i_iff_wf_scalar; exact Hwf).
  assert (Hser : serializable (DTYPE_Base (DTYPE_I w))) by exact I.
  assert (Hret : exists bs,
    @dvalue_to_memory_bytes Pa (DTYPE_Base (DTYPE_I w)) dv None = raise_ret bs).
  { destruct Hwf as [-> | [iv ->]];
      unfold dvalue_to_memory_bytes; cbn [acc_dvalue_to_memory_bytes_h];
      [set (res := acc_memory_bytes_of_dvalue_base (DTYPE_I w) DVALUE_Poison 0%N [])
      | set (res := acc_memory_bytes_of_dvalue_base (DTYPE_I w) (@DVALUE_I Pa w iv) 0%N [])];
      destruct res as [off bs]; eexists; reflexivity. }
  destruct Hret as [bs Ebs]; rewrite Ebs.
  cbn [bind EOU_monad EOU_to_itree ret].
  rewrite (@MemoryBytesFacts.memory_bytes_round_trip1 Pa (DTYPE_Base (DTYPE_I w)) dv None bs Hser Hdtyp Ebs).
  cbn [EOU_to_itree]; reflexivity.
Qed.

Lemma match_vec1_id_pair_inv {M : Type} :
  forall smap defs params i1 i2 tmp dst w1 val_exp kind,
    @match_vec1_id_pair M smap defs params i1 i2 = Some (tmp, dst, w1, val_exp, kind) ->
    exists md1 md2,
      i1 = (IId tmp,
            INSTR_Op (OP_InsertElement
                        (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w1)), EXP_Poison)
                        (DTYPE_Base (DTYPE_I w1), val_exp)
                        (DTYPE_Base (DTYPE_I 1%positive), EXP_Bool false)),
            md1) /\
      In tmp defs /\
      In dst defs /\
      tmp <> dst /\
      RM.find tmp smap = None /\
      match kind with
      | V1K_Extract =>
          i2 = (IId dst,
                INSTR_Op (OP_ExtractElement
                            (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w1)), EXP_Ident (ID_Local tmp))
                            (DTYPE_Base (DTYPE_I 1%positive), EXP_Bool false)),
                md2)
      | V1K_Bitcast =>
          i2 = (IId dst,
                INSTR_Op (OP_Conversion CONV_Bitcast
                            (DTYPE_Array true 1%N (DTYPE_Base (DTYPE_I w1)))
                            (EXP_Ident (ID_Local tmp))
                            (DTYPE_Base (DTYPE_I w1))),
                md2)
      end.
Proof.
  intros smap defs params [[iid1 ins1] md1] [[iid2 ins2] md2] tmp dst w1 val_exp kind H.
  cbn [match_vec1_id_pair] in H.
  destruct iid1 as [id1 |]; [| discriminate].
  destruct ins1; try discriminate.
  destruct op; try discriminate.
  destruct vec as [dtv1 ev1], elt as [dte1 ee1], idx as [dti1 ei1].
  destruct dtv1 as [| | bv1 n1 dtv_e]; try discriminate; destruct bv1; [| discriminate].
  destruct n1 as [| pv1]; try discriminate; destruct pv1; try discriminate.
  destruct dtv_e as [tbv1 | |]; try discriminate; destruct tbv1 as [wv1 | | | | | | | | | |]; try discriminate.
  destruct ev1; try discriminate.
  destruct dte1 as [tbe1 | |]; try discriminate; destruct tbe1 as [we1 | | | | | | | | | |]; try discriminate.
  destruct dti1 as [tbi1 | |]; try discriminate; destruct tbi1 as [wi1 | | | | | | | | | |]; try discriminate.
  destruct wi1; try discriminate.
  destruct ei1; try discriminate; destruct b; [discriminate |].
  destruct iid2 as [id2 |]; [| discriminate].
  destruct ins2; try discriminate.
  destruct op; try discriminate.
  - destruct conv; try discriminate.
    destruct t_from as [| | bv2 n2 dtv_e2]; try discriminate; destruct bv2; [| discriminate].
    destruct n2 as [| pv2]; try discriminate; destruct pv2; try discriminate.
    destruct dtv_e2 as [tbv2 | |]; try discriminate; destruct tbv2 as [wv2 | | | | | | | | | |]; try discriminate.
    match type of H with
    | (match ?ev with _ => _ end) = _ => destruct ev; try discriminate
    end.
    match type of H with
    | (match ?idv with _ => _ end) = _ => destruct idv as [| r3]; [discriminate |]
    end.
    match type of H with
    | (match ?tto with _ => _ end) = _ =>
        destruct tto as [tbt2 | |]; try discriminate;
        destruct tbt2 as [wt2 | | | | | | | | | |]; try discriminate
    end.
    match type of H with
    | (if ?c then _ else _) = _ => destruct c eqn:Hcond; [| discriminate]
    end.
    inversion H; subst id1 id2 wv1 ee1 kind; clear H.
    rewrite !andb_true_iff in Hcond.
    destruct Hcond as ((((((((Hw12 & Hw23) & Hw34) & Hr3) & Hneq) & Hdtmp) & Hddst) & _) & Hfind).
    apply Pos.eqb_eq in Hw12; apply Pos.eqb_eq in Hw23; apply Pos.eqb_eq in Hw34; subst we1 wv2 wt2.
    apply raw_id_eqb_eq in Hr3; subst r3.
    apply raw_id_in_list_spec in Hdtmp; apply raw_id_in_list_spec in Hddst.
    exists md1, md2; repeat split; try assumption.
    + intros ->; assert (Hrefl : raw_id_eqb dst dst = true) by (apply raw_id_eqb_eq; reflexivity).
      rewrite Hrefl in Hneq; discriminate Hneq.
    + destruct (RM.find tmp smap); [discriminate | reflexivity].
  - destruct vec as [dtv2 ev2], idx as [dti2 ei2].
    destruct dtv2 as [| | bv2 n2 dtv_e2]; try discriminate; destruct bv2; [| discriminate].
    destruct n2 as [| pv2]; try discriminate; destruct pv2; try discriminate.
    destruct dtv_e2 as [tbv2 | |]; try discriminate; destruct tbv2 as [wv2 | | | | | | | | | |]; try discriminate.
    destruct ev2; try discriminate; destruct id as [| r3]; [discriminate |].
    destruct dti2 as [tbi2 | |]; try discriminate; destruct tbi2 as [wi2 | | | | | | | | | |]; try discriminate.
    destruct wi2; try discriminate.
    destruct ei2; try discriminate; destruct b; [discriminate |].
    match type of H with
    | (if ?c then _ else _) = _ => destruct c eqn:Hcond; [| discriminate]
    end.
    inversion H; subst id1 id2 wv1 ee1 kind; clear H.
    rewrite !andb_true_iff in Hcond.
    destruct Hcond as (((((((Hw12 & Hw23) & Hr3) & Hneq) & Hdtmp) & Hddst) & _) & Hfind).
    apply Pos.eqb_eq in Hw12; apply Pos.eqb_eq in Hw23; subst we1 wv2.
    apply raw_id_eqb_eq in Hr3; subst r3.
    apply raw_id_in_list_spec in Hdtmp; apply raw_id_in_list_spec in Hddst.
    exists md1, md2; repeat split; try assumption.
    + intros ->; assert (Hrefl : raw_id_eqb dst dst = true) by (apply raw_id_eqb_eq; reflexivity).
      rewrite Hrefl in Hneq; discriminate Hneq.
    + destruct (RM.find tmp smap); [discriminate | reflexivity].
Qed.

Lemma env_matches_smap_add_absent {Pa : Params} :
  forall defs (penv : param_env Pa) foracle smap (env : rmap (@dvalue Pa)) tmp dv_tmp,
    RM.find tmp smap = None ->
    env_matches_smap defs penv foracle smap env ->
    env_matches_smap defs penv foracle smap (RM.add tmp dv_tmp env).
Proof.
  intros defs penv foracle smap env tmp dv_tmp Hnone Henv r w ce Hf.
  destruct (Henv r w ce Hf) as [Hr [dv [Hfe [Hev Hsc]]]].
  split; [exact Hr | exists dv; split; [| split; assumption]].
  rewrite RMF.F.add_neq_o; [exact Hfe |].
  intros Heq; subst r; congruence.
Qed.

Lemma cfg_steps_vec1_pair_ub_val {Pa : Params} :
  forall smap defs params i1 i2 tmp dst w1 val_exp kind
         sigma0 (env0 : rmap (@dvalue Pa)) rest,
    @match_vec1_id_pair (list (metadata dtyp)) smap defs params i1 i2 =
      Some (tmp, dst, w1, val_exp, kind) ->
    mcfg_steps_to_ub sigma0 env0 (denote_exp (Some (DTYPE_Base (DTYPE_I w1))) val_exp) ->
    cfg_steps_to_ub sigma0 env0 (denote_code (i1 :: i2 :: rest) None).
Proof.
  intros smap defs params i1 i2 tmp dst w1 val_exp kind sigma0 env0 rest Hmatch Hub.
  destruct (match_vec1_id_pair_inv smap defs params i1 i2 tmp dst w1 val_exp kind Hmatch)
    as (md1 & md2 & -> & _).
  unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
  apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub.
  cbn [denote_exp].
  eapply mcfg_steps_to_ub_bind_r; [apply MSR_Ret; reflexivity |].
  apply mcfg_steps_to_ub_bind_l, mcfg_steps_to_ub_bind_l; exact Hub.
Qed.

Lemma cfg_steps_vec1_pair_bind {Pa : Params} :
  forall smap defs params i1 i2 tmp dst w1 val_exp kind
         sigma0 sigma1 (env0 : rmap (@dvalue Pa)) dv1
         (k : unit -> CFGtop unit) sigma2 env2,
    @match_vec1_id_pair (list (metadata dtyp)) smap defs params i1 i2 =
      Some (tmp, dst, w1, val_exp, kind) ->
    wf_scalar_dvalue w1 dv1 ->
    mcfg_steps_to_ret sigma0 env0
      (denote_exp (Some (DTYPE_Base (DTYPE_I w1))) val_exp) sigma1 env0 dv1 ->
    cfg_steps_to_ret sigma1
      (RM.add dst dv1 (RM.add tmp (DVALUE_Array true [dv1]) env0))
      (k tt) sigma2 env2 tt ->
    cfg_steps_to_ret sigma0 env0
      (ITree.bind (denote_instr i1 None) (fun _ => ITree.bind (denote_instr i2 None) k))
      sigma2 env2 tt.
Proof.
  intros smap defs params i1 i2 tmp dst w1 val_exp kind sigma0 sigma1 env0 dv1 k sigma2 env2
    Hmatch Hwf Hval Hk.
  destruct (match_vec1_id_pair_inv smap defs params i1 i2 tmp dst w1 val_exp kind Hmatch)
    as (md1 & md2 & -> & _ & _ & _ & _ & Hi2).
  destruct (cert_wf_scalar_dvalue_base w1 dv1 Hwf) as [db1 [Hdv1 Hdb1]].
  eapply cfg_steps_to_ret_bind.
  - cbn [denote_instr]; unfold denote_exp'.
    eapply cfg_steps_to_ret_bind; [apply mcfg_to_cfg_steps_ret |].
    + cbn [denote_exp].
      eapply mcfg_steps_to_ret_bind; [apply MSR_Ret; reflexivity |].
      eapply mcfg_steps_to_ret_bind.
      * eapply mcfg_steps_to_ret_bind; [exact Hval | rewrite Hdb1; apply mcfg_steps_eou_ret].
      * eapply mcfg_steps_to_ret_bind; [apply MSR_Ret; reflexivity |].
        rewrite (cert_insert_vec1_poison_zero w1 db1); apply mcfg_steps_eou_ret.
    + eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
  - eapply cfg_steps_to_ret_bind.
    + destruct kind; subst i2; cbn [denote_instr]; unfold denote_exp'.
      * eapply cfg_steps_to_ret_bind; [apply mcfg_to_cfg_steps_ret |].
        -- cbn [denote_exp lookup_id].
           eapply mcfg_steps_to_ret_bind.
           ++ eapply MSR_LocalRead; [reflexivity | apply RMF.F.add_eq_o; reflexivity | apply MSR_Ret; reflexivity].
           ++ eapply mcfg_steps_to_ret_bind; [apply MSR_Ret; reflexivity |].
              rewrite (cert_extract_vec1_zero (DVALUE_Base db1)); apply mcfg_steps_eou_ret.
        -- rewrite <- Hdv1; eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
      * eapply cfg_steps_to_ret_bind; [apply mcfg_to_cfg_steps_ret |].
        -- cbn [denote_exp lookup_id].
           eapply mcfg_steps_to_ret_bind.
           ++ eapply MSR_LocalRead; [reflexivity | apply RMF.F.add_eq_o; reflexivity | apply MSR_Ret; reflexivity].
           ++ rewrite <- Hdv1, (cert_bitcast_vec1_scalar w1 dv1 Hwf); apply MSR_Ret; reflexivity.
        -- eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
    + exact Hk.
Qed.

Lemma cfg_steps_vec1_pair_ub_rest {Pa : Params} :
  forall smap defs params i1 i2 tmp dst w1 val_exp kind
         sigma0 sigma1 (env0 : rmap (@dvalue Pa)) dv1 rest,
    @match_vec1_id_pair (list (metadata dtyp)) smap defs params i1 i2 =
      Some (tmp, dst, w1, val_exp, kind) ->
    wf_scalar_dvalue w1 dv1 ->
    mcfg_steps_to_ret sigma0 env0
      (denote_exp (Some (DTYPE_Base (DTYPE_I w1))) val_exp) sigma1 env0 dv1 ->
    cfg_steps_to_ub sigma1
      (RM.add dst dv1 (RM.add tmp (DVALUE_Array true [dv1]) env0))
      (denote_code rest None) ->
    cfg_steps_to_ub sigma0 env0 (denote_code (i1 :: i2 :: rest) None).
Proof.
  intros smap defs params i1 i2 tmp dst w1 val_exp kind sigma0 sigma1 env0 dv1 rest
    Hmatch Hwf Hval Hub.
  destruct (match_vec1_id_pair_inv smap defs params i1 i2 tmp dst w1 val_exp kind Hmatch)
    as (md1 & md2 & -> & _ & _ & _ & _ & Hi2).
  destruct (cert_wf_scalar_dvalue_base w1 dv1 Hwf) as [db1 [Hdv1 Hdb1]].
  unfold denote_code; cbn [loop_monad].
  eapply cfg_steps_to_ub_bind_r.
  - cbn [denote_instr]; unfold denote_exp'.
    eapply cfg_steps_to_ret_bind; [apply mcfg_to_cfg_steps_ret |].
    + cbn [denote_exp].
      eapply mcfg_steps_to_ret_bind; [apply MSR_Ret; reflexivity |].
      eapply mcfg_steps_to_ret_bind.
      * eapply mcfg_steps_to_ret_bind; [exact Hval | rewrite Hdb1; apply mcfg_steps_eou_ret].
      * eapply mcfg_steps_to_ret_bind; [apply MSR_Ret; reflexivity |].
        rewrite (cert_insert_vec1_poison_zero w1 db1); apply mcfg_steps_eou_ret.
    + eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
  - eapply cfg_steps_to_ub_bind_r.
    + destruct kind; subst i2; cbn [denote_instr]; unfold denote_exp'.
      * eapply cfg_steps_to_ret_bind; [apply mcfg_to_cfg_steps_ret |].
        -- cbn [denote_exp lookup_id].
           eapply mcfg_steps_to_ret_bind.
           ++ eapply MSR_LocalRead; [reflexivity | apply RMF.F.add_eq_o; reflexivity | apply MSR_Ret; reflexivity].
           ++ eapply mcfg_steps_to_ret_bind; [apply MSR_Ret; reflexivity |].
              rewrite (cert_extract_vec1_zero (DVALUE_Base db1)); apply mcfg_steps_eou_ret.
        -- rewrite <- Hdv1; eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
      * eapply cfg_steps_to_ret_bind; [apply mcfg_to_cfg_steps_ret |].
        -- cbn [denote_exp lookup_id].
           eapply mcfg_steps_to_ret_bind.
           ++ eapply MSR_LocalRead; [reflexivity | apply RMF.F.add_eq_o; reflexivity | apply MSR_Ret; reflexivity].
           ++ rewrite <- Hdv1, (cert_bitcast_vec1_scalar w1 dv1 Hwf); apply MSR_Ret; reflexivity.
        -- eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
    + exact Hub.
Qed.

Lemma string_substring_full :
  forall s, String.substring 0 (String.length s) s = s.
Proof.
  induction s as [| c s' IH]; cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma string_prefix_substring_eq :
  forall pfx s,
    String.prefix pfx s = true ->
    s = String.append pfx (String.substring (String.length pfx) (String.length s - String.length pfx) s).
Proof.
  induction pfx as [| c pfx' IH]; intros [| c' s'] H; cbn in H; try discriminate.
  - cbn; reflexivity.
  - cbn [String.append]; change (String.length "") with 0%nat; rewrite Nat.sub_0_r, string_substring_full; reflexivity.
  - destruct (Ascii.ascii_dec c c'); [subst c' | discriminate H].
    cbn [String.substring Nat.sub String.length]; unfold String.append at 1; fold String.append;
    f_equal; exact (IH s' H).
Qed.

Lemma parse_pure_int_intrinsic_is_intrinsic_exp :
  forall fname op w,
    parse_pure_int_intrinsic fname = Some (op, w) ->
    intrinsic_exp (T := dtyp) (EXP_Ident (ID_Global (Name fname))) = Some fname.
Proof.
  intros fname op w Hp.
  unfold parse_pure_int_intrinsic in Hp.
  repeat match type of Hp with
  | (if String.prefix ?pfx fname then option_map _ (parse_pure_int_intrinsic_width ?suf) else _) = _ =>
      let Ep := fresh "Ep" in
      destruct (String.prefix pfx fname) eqn:Ep;
      [ cbn iota in Hp;
        pose proof (string_prefix_substring_eq pfx fname Ep) as Hcat;
        cbn [String.length] in Hcat;
        destruct (parse_pure_int_intrinsic_width suf) as [w' |] eqn:Ew;
        cbn [option_map] in Hp; [| discriminate Hp]
      | cbn iota in Hp ]
  end; try discriminate Hp.
  all: unfold parse_pure_int_intrinsic_width in Ew;
    repeat match type of Ew with
    | (if String.eqb _ ?k then _ else _) = _ =>
        let Ek := fresh "Ek" in
        destruct (String.eqb _ k) eqn:Ek;
        [ apply String.eqb_eq in Ek; rewrite Ek in Hcat; cbn [String.append] in Hcat;
          subst fname; vm_compute; reflexivity
        | cbn iota in Ew ]
    end; discriminate Ew.
Qed.

Lemma list_empty_b_spec :
  forall {A : Type} (xs : list A), list_empty_b xs = true -> xs = [].
Proof.
  intros A [| ? ?] H; [reflexivity | discriminate H].
Qed.

Local Ltac solve_piica_binop H pic w w' args :=
  cbv iota in H;
  destruct (Pos.eqb w w') eqn:Ew;
  [cbv iota in H; apply Pos.eqb_eq in Ew; subst w'
  | cbv iota in H; discriminate];
  destruct args as [| [[dt0 a0] pa0] [| [[dt1 a1] pa1] [| ? ?]]];
  cbv iota in H; try discriminate;
  destruct dt0 as [[w0 | | | | | | | | | |] | |];
  cbv iota in H; try discriminate;
  destruct pa0;
  cbv iota in H; try discriminate;
  destruct dt1 as [[w1 | | | | | | | | | |] | |];
  cbv iota in H; try discriminate;
  destruct pa1;
  cbv iota in H; try discriminate;
  destruct (Pos.eqb w0 w && Pos.eqb w1 w) eqn:Ew01;
  cbv iota in H; try discriminate;
  apply andb_true_iff in Ew01 as [Ew0 Ew1];
  apply Pos.eqb_eq in Ew0; apply Pos.eqb_eq in Ew1; subst w0 w1;
  inversion H; subst pic; repeat split; try assumption; try reflexivity; discriminate.

Lemma match_pure_int_intrinsic_call_inv :
  forall ins pic,
    match_pure_int_intrinsic_call ins = Some pic ->
    match ins, pic with
    | INSTR_Call (dt, EXP_Ident (ID_Global (Name fname))) args anns [],
      PIICA_Binop op w a0 a1 =>
        dt = DTYPE_Base (DTYPE_I w) /\
        parse_pure_int_intrinsic fname = Some (op, w) /\
        op <> PII_Abs /\
        args = [((DTYPE_Base (DTYPE_I w), a0), []); ((DTYPE_Base (DTYPE_I w), a1), [])] /\
        ann_fun_attributes anns = [] /\
        ann_ret_attributes anns = []
    | INSTR_Call (dt, EXP_Ident (ID_Global (Name fname))) args anns [],
      PIICA_Abs w a0 flag =>
        dt = DTYPE_Base (DTYPE_I w) /\
        parse_pure_int_intrinsic fname = Some (PII_Abs, w) /\
        exists a1,
          args = [((DTYPE_Base (DTYPE_I w), a0), []); ((DTYPE_Base (DTYPE_I 1%positive), a1), [])] /\
          parse_imm_bool_arg a1 = Some flag /\
          ann_fun_attributes anns = [] /\
          ann_ret_attributes anns = []
    | _, _ => False
    end.
Proof.
  intros ins pic H; destruct ins; cbn [match_pure_int_intrinsic_call] in H; try discriminate.
  destruct fn as [dt fn_e].
  destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
  destruct fn_e; cbn [match_pure_int_intrinsic_call] in H; try discriminate.
  match type of H with
  | context [EXP_Ident ?id0] => destruct id0 as [gid | lid]; [| cbn [match_pure_int_intrinsic_call] in H; discriminate]
  | _ => destruct id as [gid | lid]; [| cbn [match_pure_int_intrinsic_call] in H; discriminate]
  end; destruct gid as [fname | |]; cbn [match_pure_int_intrinsic_call] in H; try discriminate.
  destruct obs; [| cbn [match_pure_int_intrinsic_call] in H; discriminate].
  unfold match_pure_int_intrinsic_call in H; cbv iota in H; try discriminate.
  destruct (ann_fun_attributes anns) as [| ? ?] eqn:Hfa;
    [cbn [list_empty_b andb] in H; cbv iota in H
    | cbn [list_empty_b andb] in H; cbv iota in H; discriminate].
  destruct (ann_ret_attributes anns) as [| ? ?] eqn:Hra;
    [cbn [list_empty_b andb] in H; cbv iota in H
    | cbn [list_empty_b andb] in H; cbv iota in H; discriminate].
  destruct (parse_pure_int_intrinsic fname) as [[op w'] |] eqn:Hp;
    [cbv iota in H | cbv iota in H; discriminate].
  destruct op;
    [ solve_piica_binop H pic w w' args
    | solve_piica_binop H pic w w' args
    | solve_piica_binop H pic w w' args
    | solve_piica_binop H pic w w' args
    | solve_piica_binop H pic w w' args
    | solve_piica_binop H pic w w' args
    | ].
  - cbv iota in H;
    destruct (Pos.eqb w w') eqn:Ew;
    [cbv iota in H; apply Pos.eqb_eq in Ew; subst w'
    | cbv iota in H; discriminate];
    destruct args as [| [[dt0 a0] pa0] [| [[dt1 a1] pa1] [| ? ?]]];
    cbv iota in H; try discriminate;
    destruct dt0 as [[w0 | | | | | | | | | |] | |];
    cbv iota in H; try discriminate;
    destruct pa0; cbv iota in H; try discriminate;
    destruct dt1 as [[w1 | | | | | | | | | |] | |];
    cbv iota in H; try discriminate;
    destruct w1; cbv iota in H; try discriminate;
    destruct pa1; cbv iota in H; try discriminate;
    destruct (Pos.eqb w0 w) eqn:Ew0; cbv iota in H; try discriminate;
    apply Pos.eqb_eq in Ew0; subst w0;
    destruct (parse_imm_bool_arg a1) as [flag |] eqn:Hb;
    cbv iota in H; try discriminate;
    inversion H; subst pic; repeat split; try assumption; try reflexivity;
    eexists; repeat split; try assumption; try reflexivity; discriminate.
Qed.

Definition lower_pure_int_intrinsic_binop
  (op : pure_int_intrinsic_op) (w : positive) (ca cb : cert_expr) : cert_expr :=
  match op with
  | PII_SMin => CE_Select w (CE_ICmp CIP_Slt false w ca cb) ca cb
  | PII_SMax => CE_Select w (CE_ICmp CIP_Slt false w ca cb) cb ca
  | PII_UMin => CE_Select w (CE_ICmp CIP_Ult false w ca cb) ca cb
  | PII_UMax => CE_Select w (CE_ICmp CIP_Ult false w ca cb) cb ca
  | PII_UAddSat =>
      let sum := CE_BinOp CB_Add w no_binop_flags ca cb in
      CE_Select w (CE_ICmp CIP_Ult false w sum ca)
        (CE_BvConst w (Z.to_N (@Integers.max_unsigned w))) sum
  | PII_USubSat =>
      CE_Select w (CE_ICmp CIP_Ult false w ca cb)
        (CE_BvConst w 0%N) (CE_BinOp CB_Sub w no_binop_flags ca cb)
  | PII_Abs => ca
  end.

Definition lower_pure_int_intrinsic_abs
  (w : positive) (ca : cert_expr) (flag : bool) : cert_expr :=
  CE_Select w
    (CE_ICmp CIP_Slt false w ca (CE_BvConst w 0%N))
    (CE_BinOp CB_Sub w (mk_cert_binop_flags false flag false false) (CE_BvConst w 0%N) ca)
    ca.

Lemma lower_pure_int_intrinsic_binop_typing :
  forall op w ca cb,
    wt_cert_expr [] ca = true ->
    cert_expr_bit_width ca = w ->
    is_let_free_expr ca = true ->
    collect_freeze_keys ca = [] ->
    wt_cert_expr [] cb = true ->
    cert_expr_bit_width cb = w ->
    is_let_free_expr cb = true ->
    collect_freeze_keys cb = [] ->
    let ce := lower_pure_int_intrinsic_binop op w ca cb in
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    collect_freeze_keys ce = [] /\
    incl (collect_free_vars [] ce) (collect_free_vars [] ca ++ collect_free_vars [] cb).
Proof.
  intros op w ca cb Hwta Hbwa Hlfa Hfka Hwtb Hbwb Hlfb Hfkb.
  destruct op;
    cbn [lower_pure_int_intrinsic_binop wt_cert_expr cert_expr_bit_width
         is_let_free_expr collect_freeze_keys collect_free_vars wf_binop_flags_for];
    rewrite ?Hwta, ?Hwtb, ?Hbwa, ?Hbwb, ?Hlfa, ?Hlfb, ?Hfka, ?Hfkb, ?Pos.eqb_refl;
    cbn; repeat split; try reflexivity;
    intros x Hx; rewrite !in_app_iff in *; cbn [In] in *; intuition auto.
Qed.

Lemma lower_pure_int_intrinsic_abs_typing :
  forall w ca flag,
    wt_cert_expr [] ca = true ->
    cert_expr_bit_width ca = w ->
    is_let_free_expr ca = true ->
    collect_freeze_keys ca = [] ->
    let ce := lower_pure_int_intrinsic_abs w ca flag in
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    collect_freeze_keys ce = [] /\
    incl (collect_free_vars [] ce) (collect_free_vars [] ca).
Proof.
  intros w ca flag Hwta Hbwa Hlfa Hfka.
  cbn [lower_pure_int_intrinsic_abs wt_cert_expr cert_expr_bit_width
       is_let_free_expr collect_freeze_keys collect_free_vars wf_binop_flags_for].
  rewrite Hwta, Hbwa, Hlfa, Hfka, ?Pos.eqb_refl; destruct flag; cbn;
    repeat split; try reflexivity;
    intros x Hx; rewrite !in_app_iff in *; cbn [In] in *; intuition auto.
Qed.

Lemma lower_pure_int_intrinsic_binop_ub_l {Pa : Params} :
  forall op w ca cb (penv : param_env Pa) foracle msg,
    op <> PII_Abs ->
    eval_closed_cert_expr penv foracle ca = raise_ub msg ->
    exists msg',
      eval_closed_cert_expr penv foracle (lower_pure_int_intrinsic_binop op w ca cb) = raise_ub msg'.
Proof.
  intros op w ca cb penv foracle msg Hneq Ha.
  destruct op; try (exfalso; exact (Hneq eq_refl));
    unfold eval_closed_cert_expr in *;
    cbn [lower_pure_int_intrinsic_binop eval_cert_expr];
    rewrite Ha; cbn [eou_bind]; eexists; reflexivity.
Qed.

Lemma lower_pure_int_intrinsic_binop_ub_r {Pa : Params} :
  forall op w ca cb (penv : param_env Pa) foracle va msg,
    op <> PII_Abs ->
    eval_closed_cert_expr penv foracle ca = raise_ret va ->
    eval_closed_cert_expr penv foracle cb = raise_ub msg ->
    exists msg',
      eval_closed_cert_expr penv foracle (lower_pure_int_intrinsic_binop op w ca cb) = raise_ub msg'.
Proof.
  intros op w ca cb penv foracle va msg Hneq Ha Hb.
  destruct op; try (exfalso; exact (Hneq eq_refl));
    unfold eval_closed_cert_expr in *;
    cbn [lower_pure_int_intrinsic_binop eval_cert_expr];
    rewrite Ha, Hb; cbn [eou_bind]; eexists; reflexivity.
Qed.

Lemma lower_pure_int_intrinsic_abs_ub {Pa : Params} :
  forall w ca flag (penv : param_env Pa) foracle msg,
    eval_closed_cert_expr penv foracle ca = raise_ub msg ->
    exists msg',
      eval_closed_cert_expr penv foracle (lower_pure_int_intrinsic_abs w ca flag) = raise_ub msg'.
Proof.
  intros w ca flag penv foracle msg Ha.
  unfold eval_closed_cert_expr in *; cbn [lower_pure_int_intrinsic_abs eval_cert_expr];
    rewrite Ha; cbn [eou_bind]; eexists; reflexivity.
Qed.

Lemma pure_int_intrinsic_binop_eval_helpers {Pa : Params} :
  forall op w ca cb (penv : param_env Pa) foracle va vb,
    op <> PII_Abs ->
    wf_scalar_dvalue w va ->
    wf_scalar_dvalue w vb ->
    eval_closed_cert_expr penv foracle ca = raise_ret va ->
    eval_closed_cert_expr penv foracle cb = raise_ret vb ->
    exists dv,
      pure_int_intrinsic_fn op w [va; vb] = raise_ret (inr dv) /\
      eval_closed_cert_expr penv foracle (lower_pure_int_intrinsic_binop op w ca cb) = raise_ret dv /\
      wf_scalar_dvalue w dv.
Proof.
  intros op w ca cb penv foracle va vb Hneq Hva Hvb Ha Hb.
  destruct Hva as [-> | [a ->]]; destruct Hvb as [-> | [b ->]];
    try (
      destruct op; try (exfalso; exact (Hneq eq_refl));
      unfold eval_closed_cert_expr in *;
      cbn [lower_pure_int_intrinsic_binop eval_cert_expr];
      rewrite Ha, Hb;
      cbn;
      unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_binop;
      cbn;
      repeat match goal with
      | |- context [Pos.eq_dec ?sz ?sz] => rewrite (alg_pos_eq_dec_refl sz)
      | |- context [Pos.eqb ?sz ?sz] => rewrite (Pos.eqb_refl sz)
      end;
      cbn;
      exists (DVALUE_Base DVALUE_Poison); repeat split; try left; reflexivity).
  destruct op; [| | | | | | exfalso; exact (Hneq eq_refl)];
    unfold eval_closed_cert_expr in *;
    cbn [lower_pure_int_intrinsic_binop eval_cert_expr].
  - (* PII_SMin *)
    rewrite Ha, Hb; cbn [eou_bind].
    unfold eval_icmp; rewrite eval_icmp_base_same_width.
    unfold cert_to_icmp, eval_int_icmp, Integers.cmp, dvp, tdb; cbn - [Integers.lt].
    destruct (@Integers.lt w a b) eqn:Elt; cbn;
      rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive); cbn;
      unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_binop, int_smin;
      cbn; rewrite !alg_pos_eq_dec_refl;
      cbn; rewrite Elt;
      eexists; repeat split; try reflexivity; right; eexists; reflexivity.
  - (* PII_SMax *)
    rewrite Ha, Hb; cbn [eou_bind].
    unfold eval_icmp; rewrite eval_icmp_base_same_width.
    unfold cert_to_icmp, eval_int_icmp, Integers.cmp, dvp, tdb; cbn - [Integers.lt].
    destruct (@Integers.lt w a b) eqn:Elt; cbn;
      rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive); cbn;
      unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_binop, int_smax;
      cbn; rewrite !alg_pos_eq_dec_refl;
      cbn; rewrite Elt;
      eexists; repeat split; try reflexivity; right; eexists; reflexivity.
  - (* PII_UMin *)
    rewrite Ha, Hb; cbn [eou_bind].
    unfold eval_icmp; rewrite eval_icmp_base_same_width.
    unfold cert_to_icmp, eval_int_icmp, Integers.cmpu, dvp, tdb; cbn - [Integers.ltu].
    destruct (@Integers.ltu w a b) eqn:Elt; cbn;
      rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive); cbn;
      unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_binop, int_umin;
      cbn; rewrite !alg_pos_eq_dec_refl;
      cbn; rewrite Elt;
      eexists; repeat split; try reflexivity; right; eexists; reflexivity.
  - (* PII_UMax *)
    rewrite Ha, Hb; cbn [eou_bind].
    unfold eval_icmp; rewrite eval_icmp_base_same_width.
    unfold cert_to_icmp, eval_int_icmp, Integers.cmpu, dvp, tdb; cbn - [Integers.ltu].
    destruct (@Integers.ltu w a b) eqn:Elt; cbn;
      rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive); cbn;
      unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_binop, int_umax;
      cbn; rewrite !alg_pos_eq_dec_refl;
      cbn; rewrite Elt;
      eexists; repeat split; try reflexivity; right; eexists; reflexivity.
  - (* PII_UAddSat *)
    rewrite Ha, Hb; cbn [eou_bind].
    unfold eval_iop; rewrite !eval_iop_integer_base_same_width;
      cbn - [eval_icmp eval_icmp_base Integers.add Integers.sub Integers.lt Integers.ltu Integers.cmp Integers.cmpu Integers.signed Integers.unsigned].
    unfold eval_icmp; rewrite eval_icmp_base_same_width.
    unfold cert_to_icmp, eval_int_icmp, Integers.cmpu, dvp, tdb; cbn - [Integers.ltu Integers.add].
    unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_binop, int_uadd_sat;
      cbn - [Integers.ltu Integers.add]; rewrite !alg_pos_eq_dec_refl;
      cbn - [Integers.ltu Integers.add].
    pose proof (@Integers.unsigned_range w a) as Hua.
    pose proof (@Integers.unsigned_range w b) as Hub.
    assert (Hmod_ge2 : (2 <= @Integers.modulus w)%Z).
    { rewrite modulus_pow_sz; change 2%Z with (2 ^ 1)%Z; apply Z.pow_le_mono_r; lia. }
    assert (Hmaxu_eq : @Integers.max_unsigned w = (@Integers.modulus w - 1)%Z)
      by (unfold Integers.max_unsigned; lia).
    unfold Integers.ltu.
    assert (Hadd_u : @Integers.unsigned w (@Integers.add w a b) =
                     ((@Integers.unsigned w a + @Integers.unsigned w b) mod @Integers.modulus w)%Z).
    { unfold Integers.add; rewrite (@Integers.unsigned_repr_eq w); reflexivity. }
    destruct (Z_lt_le_dec (@Integers.unsigned w a + @Integers.unsigned w b) (@Integers.modulus w)) as [Hno | Hov].
    + rewrite Hadd_u; rewrite (Z.mod_small (@Integers.unsigned w a + @Integers.unsigned w b) (@Integers.modulus w)) by lia.
      destruct (Numeric.Rocqlib.zlt (@Integers.unsigned w a + @Integers.unsigned w b) (@Integers.unsigned w a)); [lia |].
      cbn; rewrite (@Integers.unsigned_zero 1%positive); cbn.
      rewrite Z.min_l by lia.
      unfold Integers.add; eexists; split; [reflexivity | split; [reflexivity | right; eexists; reflexivity]].
    + assert (Hmod_ov : ((@Integers.unsigned w a + @Integers.unsigned w b) mod @Integers.modulus w =
                         @Integers.unsigned w a + @Integers.unsigned w b - @Integers.modulus w)%Z).
      { symmetry; eapply Z.mod_unique_pos with (q := 1%Z); lia. }
      rewrite Hadd_u, Hmod_ov.
      destruct (Numeric.Rocqlib.zlt (@Integers.unsigned w a + @Integers.unsigned w b - @Integers.modulus w)
                  (@Integers.unsigned w a)); [| lia].
      cbn; rewrite (@Integers.unsigned_one 1%positive); cbn.
      rewrite Z.min_r by lia.
      rewrite Z2N.id by lia.
      eexists; split; [reflexivity | split; [reflexivity | right; eexists; reflexivity]].
  - (* PII_USubSat *)
    rewrite Ha, Hb; cbn [eou_bind].
    unfold eval_iop; rewrite !eval_iop_integer_base_same_width;
      cbn - [eval_icmp eval_icmp_base Integers.add Integers.sub Integers.lt Integers.ltu Integers.cmp Integers.cmpu Integers.signed Integers.unsigned].
    unfold eval_icmp; rewrite eval_icmp_base_same_width.
    unfold cert_to_icmp, eval_int_icmp, Integers.cmpu, dvp, tdb; cbn - [Integers.ltu Integers.sub].
    unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_binop, int_usub_sat;
      cbn - [Integers.ltu Integers.sub]; rewrite !alg_pos_eq_dec_refl;
      cbn - [Integers.ltu Integers.sub].
    unfold Integers.ltu; destruct (Numeric.Rocqlib.zlt (@Integers.unsigned w a) (@Integers.unsigned w b)).
    + cbn; rewrite (@Integers.unsigned_one 1%positive); cbn.
      rewrite (Z.max_r _ 0%Z) by lia; rewrite repr_zero_N.
      eexists; split; [reflexivity | split; [reflexivity | right; eexists; reflexivity]].
    + cbn; rewrite (@Integers.unsigned_zero 1%positive); cbn.
      rewrite (Z.max_l _ 0%Z) by lia; unfold Integers.sub.
      eexists; split; [reflexivity | split; [reflexivity | right; eexists; reflexivity]].
Qed.

Lemma pure_int_intrinsic_abs_eval_helper {Pa : Params} :
  forall w ca (flag : bool) (penv : param_env Pa) foracle va,
    wf_scalar_dvalue w va ->
    eval_closed_cert_expr penv foracle ca = raise_ret va ->
    let vb := DVALUE_Base (@DVALUE_I Pa 1%positive (if flag then @Integers.one 1%positive else @Integers.zero 1%positive)) in
    exists dv,
      pure_int_intrinsic_fn PII_Abs w [va; vb] = raise_ret (inr dv) /\
      eval_closed_cert_expr penv foracle (lower_pure_int_intrinsic_abs w ca flag) = raise_ret dv /\
      wf_scalar_dvalue w dv.
Proof.
  intros w ca flag penv foracle va [-> | [a ->]] Ha;
    unfold eval_closed_cert_expr in *;
    cbn [lower_pure_int_intrinsic_abs eval_cert_expr].
  - rewrite Ha; cbn [eou_bind].
    unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_unop_flag;
      cbn.
    exists (DVALUE_Base DVALUE_Poison); repeat split; try left; reflexivity.
  - rewrite Ha; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width;
      cbn - [eval_icmp eval_icmp_base Integers.add Integers.sub Integers.lt Integers.ltu Integers.cmp Integers.cmpu Integers.signed Integers.unsigned].
    unfold eval_icmp; rewrite eval_icmp_base_same_width.
    unfold cert_to_icmp, eval_int_icmp, Integers.cmp, dvp, tdb; cbn - [Integers.lt].
    rewrite repr_zero_N; rewrite ?(@Integers.signed_zero w).
    unfold pure_int_intrinsic_fn, pure_base_to_pure, llvm_int_unop_flag, int_abs;
      cbn; rewrite !Pos.eqb_refl; cbn.
    assert (Hb_flag :
      negb (@Integers.eq 1%positive
              (if flag then @Integers.one 1%positive else @Integers.zero 1%positive)
              (@Integers.zero 1%positive)) = flag).
    { destruct flag; vm_compute; reflexivity. }
    rewrite Hb_flag.
    pose proof (@Integers.signed_range w a) as Hsr.
    pose proof (@Integers.min_signed_neg w) as Hmn.
    assert (Hmms : (@Integers.max_signed w = - @Integers.min_signed w - 1)%Z).
    { unfold Integers.min_signed, Integers.max_signed; lia. }
    unfold Integers.lt; rewrite (@Integers.signed_zero w).
    unfold Integers.sub_overflow; rewrite (@Integers.signed_zero w), Z.sub_0_r.
    destruct (Z.eqb_spec (@Integers.signed w a) (@Integers.min_signed w)) as [Heq_min | Hneq_min].
    + destruct (Numeric.Rocqlib.zlt (@Integers.signed w a) 0%Z); [| lia].
      cbn; rewrite (@Integers.unsigned_one 1%positive); cbn.
      destruct flag; cbn.
      * rewrite Heq_min.
        destruct (Numeric.Rocqlib.zle (@Integers.min_signed w) (- @Integers.min_signed w)%Z);
          destruct (Numeric.Rocqlib.zle (- @Integers.min_signed w)%Z (@Integers.max_signed w));
          try lia; cbn;
          try rewrite (@Integers.eq_true w (@Integers.one w)); cbn;
          exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | split; [reflexivity | left; reflexivity]].
      * assert (Hsub_min : @Integers.sub w (@Integers.zero w) a = a).
        { rewrite (@Integers.sub_signed w), (@Integers.signed_zero w), Heq_min.
          rewrite <- (@Integers.repr_signed w a); rewrite Heq_min.
          apply @Integers.eqm_samerepr.
          unfold Integers.eqm, Integers.eqmod.
          pose proof (@Integers.half_modulus_modulus w) as Hhm.
          unfold Integers.min_signed in *.
          first [exists 1%Z; lia | exists (-1)%Z; lia]. }
        exists (DVALUE_Base (@DVALUE_I Pa w a)); split;
          [reflexivity
          | split; [cbn; rewrite Hsub_min; reflexivity | right; eexists; reflexivity]].
    + destruct (Numeric.Rocqlib.zlt (@Integers.signed w a) 0%Z) as [Hneg | Hnonneg].
      * cbn; rewrite (@Integers.unsigned_one 1%positive); cbn; rewrite ?Z.sub_0_l.
        destruct (Numeric.Rocqlib.zle (@Integers.min_signed w) (- @Integers.signed w a)%Z); [| lia].
        destruct (Numeric.Rocqlib.zle (- @Integers.signed w a)%Z (@Integers.max_signed w)); [| lia].
        cbn [proj_sumbool andb].
        rewrite (@Integers.eq_false w (@Integers.zero w) (@Integers.one w)
                   (fun H => @Integers.one_not_zero w (eq_sym H))).
        destruct flag; cbn;
          rewrite ?(@Integers.sub_signed w), ?(@Integers.signed_zero w), ?Z.sub_0_l, (Z.abs_neq (@Integers.signed w a)) by lia;
          (eexists; split; [reflexivity | split; [reflexivity | right; eexists; reflexivity]]).
      * cbn; rewrite (@Integers.unsigned_zero 1%positive); cbn; rewrite ?Z.sub_0_l.
        destruct (Numeric.Rocqlib.zle (@Integers.min_signed w) (- @Integers.signed w a)%Z); [| lia].
        destruct (Numeric.Rocqlib.zle (- @Integers.signed w a)%Z (@Integers.max_signed w)); [| lia].
        cbn [proj_sumbool andb].
        rewrite (@Integers.eq_false w (@Integers.zero w) (@Integers.one w)
                   (fun H => @Integers.one_not_zero w (eq_sym H))).
        destruct flag; cbn;
          (rewrite (Z.abs_eq (@Integers.signed w a)) by lia;
           rewrite (@Integers.repr_signed w a);
           exists (DVALUE_Base (@DVALUE_I Pa w a));
           split; [reflexivity | split; [reflexivity | right; eexists; reflexivity]]).
Qed.

Lemma apply_attrs_nil_cfg_steps {Pa : Params} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (msg : string) (v : @dvalue Pa),
    cfg_steps_to_ret sigma env (apply_attrs (E := @CFGEtop Pa) [] msg v) sigma env v.
Proof.
  intros sigma env msg v; unfold apply_attrs, assert_attrs_dereferenceable.
  eapply cfg_steps_to_ret_bind; [cbn [apply_value_attrs EOU_to_itree]; apply CSR_Ret; reflexivity |].
  cbn [find_option]; destruct v as [[| | | | | | |] | |];
    eapply cfg_steps_to_ret_bind; apply CSR_Ret; reflexivity.
Qed.

Lemma denote_operand_bundles_nil_cfg_steps {Pa : Params} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (loc : string) (f : exp dtyp),
    cfg_steps_to_ret sigma env (@denote_operand_bundles Pa loc f []) sigma env tt.
Proof.
  intros sigma env loc f; unfold denote_operand_bundles;
    cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
  eapply cfg_steps_to_ret_bind; apply CSR_Ret; reflexivity.
Qed.

Lemma check_call_return_nil_inr_cfg_steps {Pa : Params} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (loc : string)
         (args : list (@dvalue Pa)) (v : @dvalue Pa),
    cfg_steps_to_ret sigma env
      (check_call_return (E := @CFGEtop Pa) [] [] None loc args (inr v)) sigma env (inr v).
Proof.
  intros sigma env loc args v; unfold check_call_return;
    cbn [check_call_result existsb value_metadata_range EOU_to_itree].
  eapply cfg_steps_to_ret_bind; [apply CSR_Ret; reflexivity |].
  eapply cfg_steps_to_ret_bind; [apply apply_attrs_nil_cfg_steps | apply CSR_Ret; reflexivity].
Qed.

Lemma denote_imm_bool_arg_steps {Pa : Params} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) a1 flag,
    parse_imm_bool_arg a1 = Some flag ->
    cfg_steps_to_ret sigma env
      (denote_exp' (Some (DTYPE_Base (DTYPE_I 1%positive))) a1) sigma env
      (DVALUE_Base (@DVALUE_I Pa 1%positive (if flag then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros sigma env a1 flag H; destruct a1; cbn [parse_imm_bool_arg] in H; try discriminate.
  - destruct (Z.eqb (denote_int_syntax x) 0%Z) eqn:Ez0.
    + apply Z.eqb_eq in Ez0; inversion H; subst flag.
      apply mcfg_to_cfg_steps_ret; unfold denote_exp; cbn; rewrite Ez0; apply MSR_Ret; reflexivity.
    + destruct (Z.eqb (denote_int_syntax x) 1%Z) eqn:Ez1; [| discriminate].
      apply Z.eqb_eq in Ez1; inversion H; subst flag.
      apply mcfg_to_cfg_steps_ret; unfold denote_exp; cbn; rewrite Ez1; apply MSR_Ret; reflexivity.
  - inversion H; subst flag; apply mcfg_to_cfg_steps_ret; unfold denote_exp;
      destruct b; cbn; apply MSR_Ret; reflexivity.
Qed.

Lemma denote_call_args_pair_steps {Pa : Params} :
  forall sigma0 sigma1 sigma2 (env0 : rmap (@dvalue Pa)) dt0 a0 dt1 a1 dv0 dv1 msg,
    cfg_steps_to_ret sigma0 env0 (denote_exp' (Some dt0) a0) sigma1 env0 dv0 ->
    cfg_steps_to_ret sigma1 env0 (denote_exp' (Some dt1) a1) sigma2 env0 dv1 ->
    cfg_steps_to_ret sigma0 env0
      (denote_call_args [((dt0, a0), []); ((dt1, a1), [])] msg) sigma2 env0 [dv0; dv1].
Proof.
  intros sigma0 sigma1 sigma2 env0 dt0 a0 dt1 a1 dv0 dv1 msg Ha0 Ha1.
  cbn [denote_call_args map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
  eapply cfg_steps_to_ret_bind.
  - eapply cfg_steps_to_ret_bind; [exact Ha0 | apply apply_attrs_nil_cfg_steps].
  - eapply cfg_steps_to_ret_bind.
    + eapply cfg_steps_to_ret_bind.
      * eapply cfg_steps_to_ret_bind; [exact Ha1 | apply apply_attrs_nil_cfg_steps].
      * eapply cfg_steps_to_ret_bind; apply CSR_Ret; reflexivity.
    + apply CSR_Ret; reflexivity.
Qed.

Lemma cfg_steps_pure_int_intrinsic_binop_ret {Pa : Params} :
  forall sigma0 sigma1 sigma2 (env0 : rmap (@dvalue Pa)) id dt fn_e args anns md
         fname op w a0 a1 dv0 dv1 dv_out varargs,
    fn_e = EXP_Ident (ID_Global (Name fname)) ->
    parse_pure_int_intrinsic fname = Some (op, w) ->
    args = [((DTYPE_Base (DTYPE_I w), a0), []); ((DTYPE_Base (DTYPE_I w), a1), [])] ->
    ann_fun_attributes anns = [] ->
    ann_ret_attributes anns = [] ->
    metadata_range md = None ->
    mcfg_steps_to_ret sigma0 env0 (denote_exp (Some (DTYPE_Base (DTYPE_I w))) a0) sigma1 env0 dv0 ->
    mcfg_steps_to_ret sigma1 env0 (denote_exp (Some (DTYPE_Base (DTYPE_I w))) a1) sigma2 env0 dv1 ->
    pure_int_intrinsic_fn op w [dv0; dv1] = raise_ret (inr dv_out) ->
    cfg_steps_to_ret sigma0 env0
      (denote_instr (IId id, INSTR_Call (dt, fn_e) args anns [], md) varargs)
      sigma2 (RM.add id dv_out env0) tt.
Proof.
  intros sigma0 sigma1 sigma2 env0 id dt fn_e args anns md fname op w a0 a1 dv0 dv1 dv_out varargs
    Hfn Hp Hargs Hfa Hra Hmr Ha0 Ha1 Hpi.
  subst fn_e args.
  cbn [denote_instr].
  eapply cfg_steps_to_ret_bind.
  - eapply denote_call_args_pair_steps;
      unfold denote_exp'; [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Ha0) | exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Ha1)].
  - eapply cfg_steps_to_ret_bind; [apply denote_operand_bundles_nil_cfg_steps |].
    eapply cfg_steps_to_ret_bind.
    + rewrite (parse_pure_int_intrinsic_is_intrinsic_exp fname op w Hp).
      eapply CSR_PureIntrinsic; [unfold intrinsic, ITree.trigger, subevent; reflexivity | exact Hp | exact Hpi |].
      apply CSR_Ret; reflexivity.
    + eapply cfg_steps_to_ret_bind;
        [rewrite Hfa, Hra, Hmr; apply check_call_return_nil_inr_cfg_steps |].
      eapply cfg_steps_to_ret_bind; [apply CSR_Ret; reflexivity | apply cfg_steps_lwrite].
Qed.

Lemma cfg_steps_pure_int_intrinsic_binop_ub0 {Pa : Params} :
  forall sigma0 (env0 : rmap (@dvalue Pa)) id dt fn_e args anns md
         w a0 a1 varargs rest,
    args = [((DTYPE_Base (DTYPE_I w), a0), []); ((DTYPE_Base (DTYPE_I w), a1), [])] ->
    mcfg_steps_to_ub sigma0 env0 (denote_exp (Some (DTYPE_Base (DTYPE_I w))) a0) ->
    cfg_steps_to_ub sigma0 env0
      (ITree.bind (denote_instr (IId id, INSTR_Call (dt, fn_e) args anns [], md) varargs)
         (fun _ => denote_code rest varargs)).
Proof.
  intros sigma0 env0 id dt fn_e args anns md w a0 a1 varargs rest -> Ha0.
  apply cfg_steps_to_ub_bind_l.
  cbn [denote_instr denote_call_args map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
  apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l; unfold denote_exp'.
  exact (mcfg_to_cfg_steps_ub _ _ _ Ha0).
Qed.

Lemma cfg_steps_pure_int_intrinsic_binop_ub1 {Pa : Params} :
  forall sigma0 sigma1 (env0 : rmap (@dvalue Pa)) id dt fn_e args anns md
         w a0 a1 dv0 varargs rest,
    args = [((DTYPE_Base (DTYPE_I w), a0), []); ((DTYPE_Base (DTYPE_I w), a1), [])] ->
    mcfg_steps_to_ret sigma0 env0 (denote_exp (Some (DTYPE_Base (DTYPE_I w))) a0) sigma1 env0 dv0 ->
    mcfg_steps_to_ub sigma1 env0 (denote_exp (Some (DTYPE_Base (DTYPE_I w))) a1) ->
    cfg_steps_to_ub sigma0 env0
      (ITree.bind (denote_instr (IId id, INSTR_Call (dt, fn_e) args anns [], md) varargs)
         (fun _ => denote_code rest varargs)).
Proof.
  intros sigma0 sigma1 env0 id dt fn_e args anns md w a0 a1 dv0 varargs rest -> Ha0 Ha1.
  apply cfg_steps_to_ub_bind_l.
  cbn [denote_instr denote_call_args map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
  apply cfg_steps_to_ub_bind_l.
  eapply cfg_steps_to_ub_bind_r;
    [eapply cfg_steps_to_ret_bind; [unfold denote_exp'; exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Ha0) | apply apply_attrs_nil_cfg_steps] |].
  apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l; unfold denote_exp'.
  exact (mcfg_to_cfg_steps_ub _ _ _ Ha1).
Qed.

Lemma cfg_steps_pure_int_intrinsic_abs_ret {Pa : Params} :
  forall sigma0 sigma1 (env0 : rmap (@dvalue Pa)) id dt fn_e args anns md
         fname w a0 a1 flag dv0 dv_out varargs,
    fn_e = EXP_Ident (ID_Global (Name fname)) ->
    parse_pure_int_intrinsic fname = Some (PII_Abs, w) ->
    args = [((DTYPE_Base (DTYPE_I w), a0), []); ((DTYPE_Base (DTYPE_I 1%positive), a1), [])] ->
    parse_imm_bool_arg a1 = Some flag ->
    ann_fun_attributes anns = [] ->
    ann_ret_attributes anns = [] ->
    metadata_range md = None ->
    mcfg_steps_to_ret sigma0 env0 (denote_exp (Some (DTYPE_Base (DTYPE_I w))) a0) sigma1 env0 dv0 ->
    pure_int_intrinsic_fn PII_Abs w
      [dv0; DVALUE_Base (@DVALUE_I Pa 1%positive (if flag then @Integers.one 1%positive else @Integers.zero 1%positive))] =
      raise_ret (inr dv_out) ->
    cfg_steps_to_ret sigma0 env0
      (denote_instr (IId id, INSTR_Call (dt, fn_e) args anns [], md) varargs)
      sigma1 (RM.add id dv_out env0) tt.
Proof.
  intros sigma0 sigma1 env0 id dt fn_e args anns md fname w a0 a1 flag dv0 dv_out varargs
    Hfn Hp Hargs Hflag Hfa Hra Hmr Ha0 Hpi.
  subst fn_e args.
  cbn [denote_instr].
  eapply cfg_steps_to_ret_bind.
  - eapply denote_call_args_pair_steps;
      [unfold denote_exp'; exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Ha0)
      | exact (denote_imm_bool_arg_steps sigma1 env0 a1 flag Hflag)].
  - eapply cfg_steps_to_ret_bind; [apply denote_operand_bundles_nil_cfg_steps |].
    eapply cfg_steps_to_ret_bind.
    + rewrite (parse_pure_int_intrinsic_is_intrinsic_exp fname PII_Abs w Hp).
      eapply CSR_PureIntrinsic; [unfold intrinsic, ITree.trigger, subevent; reflexivity | exact Hp | exact Hpi |].
      apply CSR_Ret; reflexivity.
    + eapply cfg_steps_to_ret_bind;
        [rewrite Hfa, Hra, Hmr; apply check_call_return_nil_inr_cfg_steps |].
      eapply cfg_steps_to_ret_bind; [apply CSR_Ret; reflexivity | apply cfg_steps_lwrite].
Qed.

Lemma cfg_steps_pure_int_intrinsic_abs_ub0 {Pa : Params} :
  forall sigma0 (env0 : rmap (@dvalue Pa)) id dt fn_e args anns md
         w a0 a1 varargs rest,
    args = [((DTYPE_Base (DTYPE_I w), a0), []); ((DTYPE_Base (DTYPE_I 1%positive), a1), [])] ->
    mcfg_steps_to_ub sigma0 env0 (denote_exp (Some (DTYPE_Base (DTYPE_I w))) a0) ->
    cfg_steps_to_ub sigma0 env0
      (ITree.bind (denote_instr (IId id, INSTR_Call (dt, fn_e) args anns [], md) varargs)
         (fun _ => denote_code rest varargs)).
Proof.
  intros sigma0 env0 id dt fn_e args anns md w a0 a1 varargs rest -> Ha0.
  apply cfg_steps_to_ub_bind_l.
  cbn [denote_instr denote_call_args map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
  apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l; unfold denote_exp'.
  exact (mcfg_to_cfg_steps_ub _ _ _ Ha0).
Qed.

Definition reify_code_step
  (uf : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (smap : rmap (positive * cert_expr))
  (seen : list freeze_key)
  (i : instr_id * instr dtyp * list (metadata dtyp))
  : option (option (positive * cert_expr) * rmap (positive * cert_expr) * list freeze_key) :=
  match i with
  | (IId id, INSTR_Op op, _) =>
      if raw_id_in_list id defs then
        match reify_exp uf params src_pnames defs smap seen None op with
        | Some (w, ce, seen1) => Some (Some (w, ce), RM.add id (w, ce) smap, seen1)
        | None => None
        end
      else None
  | (IId id, (INSTR_Call _ _ _ _ as ins), md) =>
      if raw_id_in_list id defs &&
         match metadata_range md with None => true | Some _ => false end then
        match match_pure_int_intrinsic_call ins with
        | Some (PIICA_Binop op w a0 a1) =>
            match reify_exp uf params src_pnames defs smap seen (Some (DTYPE_Base (DTYPE_I w))) a0 with
            | Some (_, ca, seen1) =>
                match reify_exp uf params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I w))) a1 with
                | Some (_, cb, seen2) =>
                    if list_empty_b (collect_freeze_keys ca) &&
                       list_empty_b (collect_freeze_keys cb) then
                      let ce := lower_pure_int_intrinsic_binop op w ca cb in
                      Some (Some (w, ce), RM.add id (w, ce) smap, seen2)
                    else None
                | None => None
                end
            | None => None
            end
        | Some (PIICA_Abs w a0 flag) =>
            match reify_exp uf params src_pnames defs smap seen (Some (DTYPE_Base (DTYPE_I w))) a0 with
            | Some (_, ca, seen1) =>
                if list_empty_b (collect_freeze_keys ca) then
                  let ce := lower_pure_int_intrinsic_abs w ca flag in
                  Some (Some (w, ce), RM.add id (w, ce) smap, seen1)
                else None
            | None => None
            end
        | None => None
        end
      else None
  | (IVoid _, INSTR_Comment _, _) => Some (None, smap, seen)
  | _ => None
  end.

Fixpoint reify_code
  (uf : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (smap : rmap (positive * cert_expr))
  (seen : list freeze_key)
  (c : code dtyp)
  {struct c} : option (list (positive * cert_expr) * rmap (positive * cert_expr) * list freeze_key) :=
  match c with
  | [] => Some ([], smap, seen)
  | i1 :: rest1 =>
      let do_single := fun (_ : unit) =>
        match reify_code_step uf params src_pnames defs smap seen i1 with
        | Some (opt_ev, smap1, seen1) =>
            match reify_code uf params src_pnames defs smap1 seen1 rest1 with
            | Some (cevals, smap2, seen2) =>
                let cevals' :=
                  match opt_ev with
                  | Some ev => ev :: cevals
                  | None => cevals
                  end in
                Some (cevals', smap2, seen2)
            | None => None
            end
        | None => None
        end in
      match rest1 with
      | i2 :: rest2 =>
          match match_vec1_id_pair smap defs params i1 i2 with
          | Some (_, dst, w1, val_exp, _) =>
              match reify_exp uf params src_pnames defs smap seen (Some (DTYPE_Base (DTYPE_I w1))) val_exp with
              | Some (w, ce, seen1) =>
                  let smap1 := RM.add dst (w, ce) smap in
                  match reify_code uf params src_pnames defs smap1 seen1 rest2 with
                  | Some (cevals, smap2, seen2) =>
                      Some ((w, ce) :: cevals, smap2, seen2)
                  | None => None
                  end
              | None => None
              end
          | None => do_single tt
          end
      | [] => do_single tt
      end
  end.

Lemma reify_code_unfold_pair :
  forall uf params src_pnames defs smap seen i1 i2 rest2,
    reify_code uf params src_pnames defs smap seen (i1 :: i2 :: rest2) =
    match match_vec1_id_pair smap defs params i1 i2 with
    | Some (_, dst, w1, val_exp, _) =>
        match reify_exp uf params src_pnames defs smap seen (Some (DTYPE_Base (DTYPE_I w1))) val_exp with
        | Some (w, ce, seen1) =>
            let smap1 := RM.add dst (w, ce) smap in
            match reify_code uf params src_pnames defs smap1 seen1 rest2 with
            | Some (cevals, smap2, seen2) => Some ((w, ce) :: cevals, smap2, seen2)
            | None => None
            end
        | None => None
        end
    | None =>
        match reify_code_step uf params src_pnames defs smap seen i1 with
        | Some (opt_ev, smap1, seen1) =>
            match reify_code uf params src_pnames defs smap1 seen1 (i2 :: rest2) with
            | Some (cevals, smap2, seen2) =>
                let cevals' :=
                  match opt_ev with
                  | Some ev => ev :: cevals
                  | None => cevals
                  end in
                Some (cevals', smap2, seen2)
            | None => None
            end
        | None => None
        end
    end.
Proof.
  reflexivity.
Qed.

Lemma reify_code_single_typing :
  forall i1 rest1 uf params src_pnames defs allowed smap0 seen0 opt_ev smap1 seen1 cevals_r cevals smap2 seen2,
    (forall smap1' seen1' cevals_r' smap2' seen2',
      wf_smap_entries allowed defs seen1' uf smap1' ->
      (forall iid ins md idx w0 pnm,
        In (iid, ins, md) rest1 ->
        In (idx, DTYPE_Base (DTYPE_I w0)) (instr_param_uses params defs ins) ->
        nth_error src_pnames idx = Some pnm ->
        In (pnm, w0) allowed) ->
      reify_code uf params src_pnames defs smap1' seen1' rest1 = Some (cevals_r', smap2', seen2') ->
      incl seen1' seen2' /\
      wf_smap_entries allowed defs seen2' uf smap2' /\
      (forall k, wf_cfg_dag allowed k = true -> wf_cfg_dag allowed (wrap_evals cevals_r' k) = true)) ->
    wf_smap_entries allowed defs seen0 uf smap0 ->
    (forall iid ins md idx w0 pnm,
      In (iid, ins, md) (i1 :: rest1) ->
      In (idx, DTYPE_Base (DTYPE_I w0)) (instr_param_uses params defs ins) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    reify_code_step uf params src_pnames defs smap0 seen0 i1 = Some (opt_ev, smap1, seen1) ->
    reify_code uf params src_pnames defs smap1 seen1 rest1 = Some (cevals_r, smap2, seen2) ->
    cevals = (match opt_ev with Some ev => ev :: cevals_r | None => cevals_r end) ->
    incl seen0 seen2 /\
    wf_smap_entries allowed defs seen2 uf smap2 /\
    (forall k, wf_cfg_dag allowed k = true -> wf_cfg_dag allowed (wrap_evals cevals k) = true).
Proof.
  intros [[iid ins] md] rest1 uf params src_pnames defs allowed smap0 seen0 opt_ev smap1 seen1 cevals_r cevals smap2 seen2
    IH_r Hsmap0 Hpu Hstep Hrr ->.
  cbn [reify_code_step] in Hstep.
  destruct iid as [id | vid]; [destruct ins; try discriminate | destruct ins; try discriminate].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    apply raw_id_in_list_spec in Hid.
    destruct (reify_exp uf params src_pnames defs smap0 seen0 None op)
      as [[[w ce] seen1'] |] eqn:Hre; [| discriminate].
    inversion Hstep; subst opt_ev smap1 seen1'; clear Hstep.
    destruct (reify_exp_typing op uf params src_pnames defs allowed smap0 seen0 None w ce seen1
                Hsmap0
                (fun idx w0 pnm Hin => Hpu (IId id) (INSTR_Op op) md idx w0 pnm (or_introl eq_refl) Hin)
                Hre)
      as (_ & Hwt & Hbw & Hlf & Hfv & Hinc01 & Hfk).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap0 Hinc01 Hsmap0) as Hsmap0'.
    pose proof (wf_smap_entries_add allowed defs seen1 uf smap0 id w ce Hsmap0'
                  Hid Hwt Hbw Hlf Hfv Hfk) as Hsmap1.
    destruct (IH_r (RM.add id (w, ce) smap0) seen1 cevals_r smap2 seen2 Hsmap1
                (fun iid' ins' md' idx w0 pnm Hin_i => Hpu iid' ins' md' idx w0 pnm (or_intror Hin_i))
                Hrr)
      as (Hinc12 & Hsmap2 & Hwk).
    split; [intros x Hx; exact (Hinc12 x (Hinc01 x Hx)) | split; [exact Hsmap2 |]].
    intros k Hk; cbn [wrap_evals wf_cfg_dag].
    rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), (Hwk k Hk); reflexivity.
  - set (ins := INSTR_Call fn args anns obs) in Hpu, Hstep |- *.
    destruct (raw_id_in_list id defs &&
              match metadata_range md with None => true | Some _ => false end) eqn:Hhdr;
      [| discriminate].
    apply andb_true_iff in Hhdr as [Hid _]; apply raw_id_in_list_spec in Hid.
    destruct (match_pure_int_intrinsic_call ins) as [pic |] eqn:Hpic; [| discriminate].
    pose proof (match_pure_int_intrinsic_call_inv ins pic Hpic) as Hpic_inv.
    destruct pic as [op w a0 a1 | w a0 flag].
    + destruct (reify_exp uf params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) a0)
        as [[[wa0 ca] seen_a] |] eqn:Hra0; [| discriminate].
      destruct (reify_exp uf params src_pnames defs smap0 seen_a (Some (DTYPE_Base (DTYPE_I w))) a1)
        as [[[wa1 cb] seen_b] |] eqn:Hra1; [| discriminate].
      destruct (list_empty_b (collect_freeze_keys ca) && list_empty_b (collect_freeze_keys cb)) eqn:Hfk01;
        [| discriminate].
      apply andb_true_iff in Hfk01 as [Hfka_b Hfkb_b].
      apply list_empty_b_spec in Hfka_b; apply list_empty_b_spec in Hfkb_b.
      inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
      assert (Hpua0 : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) allowed).
      { intros idx w0 pnm Hin Hpnm.
        eapply Hpu; [left; reflexivity | | exact Hpnm].
        unfold instr_param_uses; rewrite Hpic; apply in_app_iff; left; exact Hin. }
      assert (Hpua1 : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a1) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) allowed).
      { intros idx w0 pnm Hin Hpnm.
        eapply Hpu; [left; reflexivity | | exact Hpnm].
        unfold instr_param_uses; rewrite Hpic; apply in_app_iff; right; exact Hin. }
      destruct (reify_exp_typing a0 uf params src_pnames defs allowed smap0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) wa0 ca seen_a Hsmap0 Hpua0 Hra0)
        as (Htopa & Hwta & Hbwa & Hlfa & Hfva & Hinca & _).
      apply check_opt_int_width_some_inv in Htopa; subst wa0.
      pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen_a uf smap0 Hinca Hsmap0) as Hsmap_a.
      destruct (reify_exp_typing a1 uf params src_pnames defs allowed smap0 seen_a
                  (Some (DTYPE_Base (DTYPE_I w))) wa1 cb seen_b Hsmap_a Hpua1 Hra1)
        as (Htopb & Hwtb & Hbwb & Hlfb & Hfvb & Hincb & _).
      apply check_opt_int_width_some_inv in Htopb; subst wa1.
      destruct (lower_pure_int_intrinsic_binop_typing op w ca cb
                  Hwta Hbwa Hlfa Hfka_b Hwtb Hbwb Hlfb Hfkb_b)
        as (Hwt & Hbw & Hlf & Hfk_nil & Hfv_sub).
      assert (Hfv : incl (collect_free_vars [] (lower_pure_int_intrinsic_binop op w ca cb)) allowed).
      { intros x Hx; apply Hfv_sub, in_app_iff in Hx as [Hx | Hx]; [exact (Hfva x Hx) | exact (Hfvb x Hx)]. }
      assert (Hfk : uf = true -> incl (collect_freeze_keys (lower_pure_int_intrinsic_binop op w ca cb)) seen_b)
        by (intros _; rewrite Hfk_nil; intros ? []).
      assert (Hinc0b : incl seen0 seen_b) by (intros x Hx; exact (Hincb x (Hinca x Hx))).
      pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen_b uf smap0 Hinc0b Hsmap0) as Hsmap_b.
      pose proof (wf_smap_entries_add allowed defs seen_b uf smap0 id w
                    (lower_pure_int_intrinsic_binop op w ca cb) Hsmap_b Hid Hwt Hbw Hlf Hfv Hfk) as Hsmap1.
      destruct (IH_r (RM.add id (w, lower_pure_int_intrinsic_binop op w ca cb) smap0) seen_b
                  cevals_r smap2 seen2 Hsmap1
                  (fun iid' ins' md' idx w0 pnm Hin_i => Hpu iid' ins' md' idx w0 pnm (or_intror Hin_i))
                  Hrr)
        as (Hinc12 & Hsmap2 & Hwk).
      split; [intros x Hx; exact (Hinc12 x (Hinc0b x Hx)) | split; [exact Hsmap2 |]].
      intros k Hk; cbn [wrap_evals wf_cfg_dag].
      rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), (Hwk k Hk); reflexivity.
    + destruct (reify_exp uf params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) a0)
        as [[[wa0 ca] seen_a] |] eqn:Hra0; [| discriminate].
      destruct (list_empty_b (collect_freeze_keys ca)) eqn:Hfka_b; [| discriminate].
      apply list_empty_b_spec in Hfka_b.
      inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
      assert (Hpua0 : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) allowed).
      { intros idx w0 pnm Hin Hpnm.
        eapply Hpu; [left; reflexivity | | exact Hpnm].
        unfold instr_param_uses; rewrite Hpic; exact Hin. }
      destruct (reify_exp_typing a0 uf params src_pnames defs allowed smap0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) wa0 ca seen_a Hsmap0 Hpua0 Hra0)
        as (Htopa & Hwta & Hbwa & Hlfa & Hfva & Hinca & _).
      apply check_opt_int_width_some_inv in Htopa; subst wa0.
      destruct (lower_pure_int_intrinsic_abs_typing w ca flag Hwta Hbwa Hlfa Hfka_b)
        as (Hwt & Hbw & Hlf & Hfk_nil & Hfv_sub).
      assert (Hfv : incl (collect_free_vars [] (lower_pure_int_intrinsic_abs w ca flag)) allowed)
        by (intros x Hx; exact (Hfva x (Hfv_sub x Hx))).
      assert (Hfk : uf = true -> incl (collect_freeze_keys (lower_pure_int_intrinsic_abs w ca flag)) seen_a)
        by (intros _; rewrite Hfk_nil; intros ? []).
      pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen_a uf smap0 Hinca Hsmap0) as Hsmap_a.
      pose proof (wf_smap_entries_add allowed defs seen_a uf smap0 id w
                    (lower_pure_int_intrinsic_abs w ca flag) Hsmap_a Hid Hwt Hbw Hlf Hfv Hfk) as Hsmap1.
      destruct (IH_r (RM.add id (w, lower_pure_int_intrinsic_abs w ca flag) smap0) seen_a
                  cevals_r smap2 seen2 Hsmap1
                  (fun iid' ins' md' idx w0 pnm Hin_i => Hpu iid' ins' md' idx w0 pnm (or_intror Hin_i))
                  Hrr)
        as (Hinc12 & Hsmap2 & Hwk).
      split; [intros x Hx; exact (Hinc12 x (Hinca x Hx)) | split; [exact Hsmap2 |]].
      intros k Hk; cbn [wrap_evals wf_cfg_dag].
      rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), (Hwk k Hk); reflexivity.
  - inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
    exact (IH_r smap0 seen0 cevals_r smap2 seen2 Hsmap0
             (fun iid' ins' md' idx w0 pnm Hin_i => Hpu iid' ins' md' idx w0 pnm (or_intror Hin_i)) Hrr).
Qed.

Lemma reify_code_typing :
  forall c uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2,
    wf_smap_entries allowed defs seen0 uf smap0 ->
    (forall iid ins md idx w0 pnm,
      In (iid, ins, md) c ->
      In (idx, DTYPE_Base (DTYPE_I w0)) (instr_param_uses params defs ins) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    reify_code uf params src_pnames defs smap0 seen0 c = Some (cevals, smap2, seen2) ->
    incl seen0 seen2 /\
    wf_smap_entries allowed defs seen2 uf smap2 /\
    (forall k, wf_cfg_dag allowed k = true -> wf_cfg_dag allowed (wrap_evals cevals k) = true).
Proof.
  induction c as [| i1 | i1 i2 rest2 IH_tail IH_rest2] using list_2step_ind;
    intros uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2 Hsmap0 Hpu Hr.
  - cbn [reify_code] in Hr; inversion Hr; subst; split; [intros x Hx; exact Hx | split; [exact Hsmap0 | intros k Hk; exact Hk]].
  - cbn [reify_code] in Hr; destruct (reify_code_step uf params src_pnames defs smap0 seen0 i1)
      as [[[opt_ev smap1] seen1] |] eqn:Hstep; [| discriminate].
    assert (Hrr : reify_code uf params src_pnames defs smap1 seen1 [] = Some ([], smap1, seen1))
      by reflexivity.
    inversion Hr; subst cevals smap2 seen2; clear Hr.
    eapply reify_code_single_typing; [| exact Hsmap0 | exact Hpu | exact Hstep | exact Hrr | destruct opt_ev; reflexivity].
    intros smap1' seen1' cevals_r' smap2' seen2' Hs1' _ Hr'.
    cbn [reify_code] in Hr'; inversion Hr'; subst.
    split; [intros x Hx; exact Hx | split; [exact Hs1' | intros k Hk; exact Hk]].
  - rewrite reify_code_unfold_pair in Hr.
    destruct (match_vec1_id_pair smap0 defs params i1 i2)
      as [[[[[tmp dst] w1] val_exp] kind] |] eqn:Hvec; cbv iota beta zeta in Hr.
    + destruct (reify_exp uf params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w1))) val_exp)
        as [[[w ce] seen1] |] eqn:Hre; cbv iota beta zeta in Hr; [| discriminate].
      destruct (reify_code uf params src_pnames defs (RM.add dst (w, ce) smap0) seen1 rest2)
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; cbv iota beta zeta in Hr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      destruct (match_vec1_id_pair_inv smap0 defs params i1 i2 tmp dst w1 val_exp kind Hvec)
        as (md1 & md2 & Hi1 & _ & Hdst_def & _).
      assert (Hpu_val : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w1))) val_exp) ->
        nth_error src_pnames idx = Some pnm ->
        In (pnm, w0) allowed).
      { intros idx w0 pnm Hin Hpnm.
        eapply Hpu; [left; rewrite Hi1; reflexivity | | exact Hpnm].
        cbn [instr_param_uses exp_param_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hin. }
      destruct (reify_exp_typing val_exp uf params src_pnames defs allowed smap0 seen0
                  (Some (DTYPE_Base (DTYPE_I w1))) w ce seen1 Hsmap0 Hpu_val Hre)
        as (_ & Hwt & Hbw & Hlf & Hfv & Hinc01 & Hfk).
      pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap0 Hinc01 Hsmap0) as Hsmap0'.
      pose proof (wf_smap_entries_add allowed defs seen1 uf smap0 dst w ce Hsmap0'
                    Hdst_def Hwt Hbw Hlf Hfv Hfk) as Hsmap1.
      destruct (IH_rest2 uf params src_pnames defs allowed (RM.add dst (w, ce) smap0) seen1
                  cevals_r smap2 seen2 Hsmap1
                  (fun iid' ins' md' idx w0 pnm Hin_i => Hpu iid' ins' md' idx w0 pnm (or_intror (or_intror Hin_i)))
                  Hrr)
        as (Hinc12 & Hsmap2 & Hwk).
      split; [intros x Hx; exact (Hinc12 x (Hinc01 x Hx)) | split; [exact Hsmap2 |]].
      intros k Hk; cbn [wrap_evals wf_cfg_dag].
      rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), (Hwk k Hk); reflexivity.
    + destruct (reify_code_step uf params src_pnames defs smap0 seen0 i1)
        as [[[opt_ev smap1] seen1] |] eqn:Hstep; cbv iota beta zeta in Hr; [| discriminate].
      destruct (reify_code uf params src_pnames defs smap1 seen1 (i2 :: rest2))
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; cbv iota beta zeta in Hr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      eapply reify_code_single_typing; [| exact Hsmap0 | exact Hpu | exact Hstep | exact Hrr | reflexivity].
      intros smap1' seen1' cevals_r' smap2' seen2' Hs1' Hpu' Hr'.
      exact (IH_tail uf params src_pnames defs allowed smap1' seen1' cevals_r' smap2' seen2' Hs1' Hpu' Hr').
Qed.

Lemma eval_reified_code_single_src {Pa : Params} :
  forall i1 rest1 params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) smap0 (env0 : rmap (@dvalue Pa))
         seen0 opt_ev smap1 seen1 cevals_r cevals smap2 seen2,
    (forall allowed' smap0' env0' seen0' cevals' smap2' seen2',
      (forall iid ins md idx dt_u,
        In (iid, ins, md) rest1 ->
        In (idx, dt_u) (instr_param_uses params defs ins) ->
        nth_error arg_dtys idx = Some dt_u) ->
      (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
        exists dv, nth_error vs idx = Some dv /\ RM.find r env0' = Some dv) ->
      wf_smap_entries allowed' defs seen0' false smap0' ->
      env_matches_smap defs (build_param_env src_pnames vs) foracle smap0' env0' ->
      reify_code false params src_pnames defs smap0' seen0' rest1 = Some (cevals', smap2', seen2') ->
      exists draws : list (dtyp * @dvalue Pa),
        Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
        (((forall tail_s,
             cfg_steps_to_ub (chain_draws draws tail_s) env0' (denote_code rest1 None)) /\
          (forall k, eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_evals cevals' k) = DO_UB)) \/
         (exists env2,
            (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
               exists dv, nth_error vs idx = Some dv /\ RM.find r env2 = Some dv) /\
            env_matches_smap defs (build_param_env src_pnames vs) foracle smap2' env2 /\
            (forall k,
               eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_evals cevals' k) =
               eval_cfg_dag (build_param_env src_pnames vs) foracle k) /\
            (forall tail_s,
               cfg_steps_to_ret (chain_draws draws tail_s) env0' (denote_code rest1 None) tail_s env2 tt)))) ->
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall iid ins md idx dt_u,
      In (iid, ins, md) (i1 :: rest1) ->
      In (idx, dt_u) (instr_param_uses params defs ins) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_smap_entries allowed defs seen0 false smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) foracle smap0 env0 ->
    reify_code_step false params src_pnames defs smap0 seen0 i1 = Some (opt_ev, smap1, seen1) ->
    reify_code false params src_pnames defs smap1 seen1 rest1 = Some (cevals_r, smap2, seen2) ->
    cevals = (match opt_ev with Some ev => ev :: cevals_r | None => cevals_r end) ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s,
           cfg_steps_to_ub (chain_draws draws tail_s) env0 (denote_code (i1 :: rest1) None)) /\
        (forall k, eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_evals cevals k) = DO_UB)) \/
       (exists env2,
          (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
             exists dv, nth_error vs idx = Some dv /\ RM.find r env2 = Some dv) /\
          env_matches_smap defs (build_param_env src_pnames vs) foracle smap2 env2 /\
          (forall k,
             eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_evals cevals k) =
             eval_cfg_dag (build_param_env src_pnames vs) foracle k) /\
          (forall tail_s,
             cfg_steps_to_ret (chain_draws draws tail_s) env0 (denote_code (i1 :: rest1) None) tail_s env2 tt))).
Proof.
  intros [[iid ins] md] rest1 params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0
    opt_ev smap1 seen1 cevals_r cevals smap2 seen2
    IH Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hstep Hrr ->.
  cbn [reify_code_step] in Hstep.
  destruct iid as [id | vid]; [destruct ins; try discriminate | destruct ins; try discriminate].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    apply raw_id_in_list_spec in Hid.
    destruct (reify_exp false params src_pnames defs smap0 seen0 None op)
      as [[[w ce] seen1'] |] eqn:Hre; [| discriminate].
    inversion Hstep; subst opt_ev smap1 seen1'; clear Hstep.
    destruct (eval_reified_exp_src op params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0
                None w ce seen1 Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu (IId id) (INSTR_Op op) md idx d (or_introl eq_refl) Hin)
                Hpe Hwfs Henv Hre)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
        apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub1 tail_s).
      * intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
    + set (ext_vars :=
        allowed ++
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (exp_param_uses params defs None op)).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 false smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpu_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs None op) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | rewrite Hpnm; left; reflexivity]. }
      destruct (reify_exp_typing op false params src_pnames defs ext_vars smap0 seen0 None w ce seen1
                  Hsmap_ext Hpu_ext Hre)
        as (_ & Hwt_ce & Hbw_ce & Hlf_ce & Hfv_ce & Hinc01 & Hfk_ce).
      pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen1 false smap0 Hinc01 Hsmap_ext) as Hsmap_ext1.
      pose proof (wf_smap_entries_add ext_vars defs seen1 false smap0 id w ce Hsmap_ext1
                    Hid Hwt_ce Hbw_ce Hlf_ce Hfv_ce Hfk_ce) as Hwfs1.
      assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
        exists dv, nth_error vs idx = Some dv /\ RM.find r (RM.add id dv1 env0) = Some dv).
      { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
        exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o; [exact Hfe | intros ->; exact (Hnin Hid)]]. }
      pose proof (env_matches_smap_add defs (build_param_env src_pnames vs) foracle smap0 env0
                    id w ce dv1 Henv Hid Hev1 Hsc1) as Henv1.
      destruct (IH ext_vars (RM.add id (w, ce) smap0) (RM.add id dv1 env0) seen1 cevals_r smap2 seen2
                  (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror Hin_i))
                  Hpe1 Hwfs1 Henv1 Hrr)
        as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | (env2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
           eapply cfg_steps_to_ub_bind_r.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst1 (chain_draws draws2 tail_s))) |].
              eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
           ++ exact (Hub2 tail_s).
        -- intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_ub2 k).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right; exists env2].
        split; [exact Hpe2 | split; [exact Henv2 | split]].
        -- intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_k k).
        -- intros tail_s; rewrite chain_draws_app; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst1 (chain_draws draws2 tail_s))) |].
              eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
           ++ exact (Hst2 tail_s).
  - set (ins := INSTR_Call fn args anns obs) in Hstep |- *.
    destruct (raw_id_in_list id defs &&
              match metadata_range md with None => true | Some _ => false end) eqn:Hhdr;
      [| discriminate].
    apply andb_true_iff in Hhdr as [Hid Hmr_b]; apply raw_id_in_list_spec in Hid.
    assert (Hmr : metadata_range md = None) by (destruct (metadata_range md); [discriminate | reflexivity]).
    destruct (match_pure_int_intrinsic_call ins) as [pic |] eqn:Hpic; [| discriminate].
    pose proof (match_pure_int_intrinsic_call_inv ins pic Hpic) as Hpic_inv.
    unfold ins in Hpic, Hpic_inv;
    destruct pic as [op w a0 a1 | w a0 flag];
      destruct fn as [dt_fn fn_e]; destruct fn_e; cbn in Hpic_inv; try contradiction Hpic_inv;
      match type of Hpic_inv with
      | context [EXP_Ident ?id0] => destruct id0 as [gid_g | ?]; [| contradiction Hpic_inv]
      | _ =>
          match type of Hpic_inv with
          | context [match ?id0 with ID_Global _ => _ | ID_Local _ => _ end] =>
              destruct id0 as [gid_g | ?]; [| cbn in Hpic_inv; contradiction Hpic_inv]
          end
      end; destruct gid_g as [fname | |]; cbn in Hpic_inv; try contradiction Hpic_inv;
      destruct obs; cbn in Hpic_inv; try contradiction Hpic_inv;
      destruct Hpic_inv as (Hdt_fn & Hp_intr & Hpic_rest); subst dt_fn.
    + destruct Hpic_rest as (Hop_neq & Hargs & Hfa & Hra).
      destruct (reify_exp false params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) a0)
        as [[[wa0 ca] seen_a] |] eqn:Hra0; [| discriminate].
      destruct (reify_exp false params src_pnames defs smap0 seen_a (Some (DTYPE_Base (DTYPE_I w))) a1)
        as [[[wa1 cb] seen_b] |] eqn:Hra1; [| discriminate].
      destruct (list_empty_b (collect_freeze_keys ca) && list_empty_b (collect_freeze_keys cb)) eqn:Hfk01;
        [| discriminate].
      apply andb_true_iff in Hfk01 as [Hfka_b Hfkb_b].
      apply list_empty_b_spec in Hfka_b; apply list_empty_b_spec in Hfkb_b.
      inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
      assert (Hpua0 : forall idx dt_u,
        In (idx, dt_u) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error arg_dtys idx = Some dt_u).
      { intros idx dt_u Hin; eapply Hpu; [left; reflexivity |].
        unfold instr_param_uses; rewrite Hpic; apply in_app_iff; left; exact Hin. }
      assert (Hpua1 : forall idx dt_u,
        In (idx, dt_u) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a1) ->
        nth_error arg_dtys idx = Some dt_u).
      { intros idx dt_u Hin; eapply Hpu; [left; reflexivity |].
        unfold instr_param_uses; rewrite Hpic; apply in_app_iff; right; exact Hin. }
      set (ext_vars :=
        allowed ++
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (instr_param_uses params defs (INSTR_Call (DTYPE_Base (DTYPE_I w), EXP_Ident (ID_Global (Name fname))) args anns []))).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 false smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpua0_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split;
          [unfold instr_param_uses; rewrite Hpic; apply in_app_iff; left; exact Hin | rewrite Hpnm; left; reflexivity]. }
      assert (Hpua1_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a1) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split;
          [unfold instr_param_uses; rewrite Hpic; apply in_app_iff; right; exact Hin | rewrite Hpnm; left; reflexivity]. }
      destruct (reify_exp_typing a0 false params src_pnames defs ext_vars smap0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) wa0 ca seen_a Hsmap_ext Hpua0_ext Hra0)
        as (Htopa & Hwta & Hbwa & Hlfa & _ & Hinca & _).
      apply check_opt_int_width_some_inv in Htopa; subst wa0.
      pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen_a false smap0 Hinca Hsmap_ext) as Hsmap_ext_a.
      destruct (reify_exp_typing a1 false params src_pnames defs ext_vars smap0 seen_a
                  (Some (DTYPE_Base (DTYPE_I w))) wa1 cb seen_b Hsmap_ext_a Hpua1_ext Hra1)
        as (Htopb & Hwtb & Hbwb & Hlfb & _ & Hincb & _).
      apply check_opt_int_width_some_inv in Htopb; subst wa1.
      pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen_a false smap0 Hinca Hwfs) as Hwfs_a.
      destruct (eval_reified_exp_src a0 params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) w ca seen_a Hnd Hlp Hls Hla Hvs Hpua0 Hpe Hwfs Henv Hra0)
        as (draws0 & Hfa0 & [[Hub0 [msg0 Hev0]] | [dv0 [Hev0 [Hsc0 Hst0]]]]).
      * exists draws0; split; [exact Hfa0 | left; split].
        -- intros tail_s; unfold denote_code; cbn [loop_monad].
           exact (cfg_steps_pure_int_intrinsic_binop_ub0 (chain_draws draws0 tail_s) env0 id (DTYPE_Base (DTYPE_I w))
                    (EXP_Ident (ID_Global (Name fname))) args anns md w a0 a1 None rest1 Hargs (Hub0 tail_s)).
        -- intros k; cbn [wrap_evals eval_cfg_dag].
           destruct (lower_pure_int_intrinsic_binop_ub_l op w ca cb
                       (build_param_env src_pnames vs) foracle msg0 Hop_neq Hev0) as [msg' Hev'].
           rewrite Hev'; reflexivity.
      * destruct (eval_reified_exp_src a1 params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen_a
                    (Some (DTYPE_Base (DTYPE_I w))) w cb seen_b Hnd Hlp Hls Hla Hvs Hpua1 Hpe Hwfs_a Henv Hra1)
          as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
        -- exists (draws0 ++ draws1); split; [apply Forall_app; split; assumption | left; split].
           ++ intros tail_s; rewrite chain_draws_app; unfold denote_code; cbn [loop_monad].
              exact (cfg_steps_pure_int_intrinsic_binop_ub1
                       (chain_draws draws0 (chain_draws draws1 tail_s))
                       (chain_draws draws1 tail_s) env0 id (DTYPE_Base (DTYPE_I w))
                       (EXP_Ident (ID_Global (Name fname))) args anns md w a0 a1 dv0 None rest1
                       Hargs (Hst0 (chain_draws draws1 tail_s)) (Hub1 tail_s)).
           ++ intros k; cbn [wrap_evals eval_cfg_dag].
              destruct (lower_pure_int_intrinsic_binop_ub_r op w ca cb
                          (build_param_env src_pnames vs) foracle dv0 msg1 Hop_neq Hev0 Hev1) as [msg' Hev'].
              rewrite Hev'; reflexivity.
        -- destruct (pure_int_intrinsic_binop_eval_helpers op w ca cb
                       (build_param_env src_pnames vs) foracle dv0 dv1 Hop_neq Hsc0 Hsc1 Hev0 Hev1)
             as (dv_out & Hpi & Hev_ce & Hsc_out).
           pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen_b false smap0
                         (fun x Hx => Hincb x (Hinca x Hx)) Hsmap_ext) as Hsmap_ext_b.
           set (ce := lower_pure_int_intrinsic_binop op w ca cb).
           fold ce in Hev_ce.
           assert (Hext_ce : incl (collect_free_vars [] ce) ext_vars).
           { pose proof (reify_exp_typing a0 false params src_pnames defs ext_vars smap0 seen0
                           (Some (DTYPE_Base (DTYPE_I w))) w ca seen_a Hsmap_ext Hpua0_ext Hra0)
               as (_ & _ & _ & _ & Hfva_e & _).
             pose proof (reify_exp_typing a1 false params src_pnames defs ext_vars smap0 seen_a
                           (Some (DTYPE_Base (DTYPE_I w))) w cb seen_b Hsmap_ext_a Hpua1_ext Hra1)
               as (_ & _ & _ & _ & Hfvb_e & _).
             destruct (lower_pure_int_intrinsic_binop_typing op w ca cb
                         Hwta Hbwa Hlfa Hfka_b Hwtb Hbwb Hlfb Hfkb_b) as (_ & _ & _ & _ & Hsub).
             intros x Hx; apply Hsub, in_app_iff in Hx as [Hx | Hx];
               [exact (Hfva_e x Hx) | exact (Hfvb_e x Hx)]. }
           destruct (lower_pure_int_intrinsic_binop_typing op w ca cb
                       Hwta Hbwa Hlfa Hfka_b Hwtb Hbwb Hlfb Hfkb_b)
             as (Hwt_ce & Hbw_ce & Hlf_ce & Hfk_nil & _).
           pose proof (wf_smap_entries_add ext_vars defs seen_b false smap0 id w ce Hsmap_ext_b
                         Hid Hwt_ce Hbw_ce Hlf_ce Hext_ce (fun H => match H with end)) as Hwfs1.
           assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
             exists dv, nth_error vs idx = Some dv /\ RM.find r (RM.add id dv_out env0) = Some dv).
           { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
             exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o; [exact Hfe | intros ->; exact (Hnin Hid)]]. }
           pose proof (env_matches_smap_add defs (build_param_env src_pnames vs) foracle smap0 env0
                         id w ce dv_out Henv Hid Hev_ce Hsc_out) as Henv1.
           destruct (IH ext_vars (RM.add id (w, ce) smap0) (RM.add id dv_out env0) seen_b
                       cevals_r smap2 seen2
                       (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror Hin_i))
                       Hpe1 Hwfs1 Henv1 Hrr)
             as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | (env2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
           ++ exists (draws0 ++ draws1 ++ draws2); split;
                [apply Forall_app; split; [exact Hfa0 | apply Forall_app; split; assumption] | left; split].
              ** intros tail_s; rewrite !chain_draws_app; unfold denote_code; cbn [loop_monad].
                 eapply cfg_steps_to_ub_bind_r.
                 --- unfold ins; eapply cfg_steps_pure_int_intrinsic_binop_ret;
                       [reflexivity | exact Hp_intr | exact Hargs | exact Hfa | exact Hra | exact Hmr
                       | exact (Hst0 (chain_draws draws1 (chain_draws draws2 tail_s)))
                       | exact (Hst1 (chain_draws draws2 tail_s))
                       | exact Hpi].
                 --- exact (Hub2 tail_s).
              ** intros k; cbn [wrap_evals eval_cfg_dag]; fold ce; rewrite Hev_ce; exact (Hev_ub2 k).
           ++ exists (draws0 ++ draws1 ++ draws2); split;
                [apply Forall_app; split; [exact Hfa0 | apply Forall_app; split; assumption] | right; exists env2].
              split; [exact Hpe2 | split; [exact Henv2 | split]].
              ** intros k; cbn [wrap_evals eval_cfg_dag]; fold ce; rewrite Hev_ce; exact (Hev_k k).
              ** intros tail_s; rewrite !chain_draws_app; unfold denote_code; cbn [loop_monad].
                 eapply cfg_steps_to_ret_bind.
                 --- unfold ins; eapply cfg_steps_pure_int_intrinsic_binop_ret;
                       [reflexivity | exact Hp_intr | exact Hargs | exact Hfa | exact Hra | exact Hmr
                       | exact (Hst0 (chain_draws draws1 (chain_draws draws2 tail_s)))
                       | exact (Hst1 (chain_draws draws2 tail_s))
                       | exact Hpi].
                 --- exact (Hst2 tail_s).
    + destruct Hpic_rest as (a1 & Hargs & Hflag & Hfa & Hra).
      destruct (reify_exp false params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) a0)
        as [[[wa0 ca] seen_a] |] eqn:Hra0; [| discriminate].
      destruct (list_empty_b (collect_freeze_keys ca)) eqn:Hfka_b; [| discriminate].
      apply list_empty_b_spec in Hfka_b.
      inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
      assert (Hpua0 : forall idx dt_u,
        In (idx, dt_u) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error arg_dtys idx = Some dt_u).
      { intros idx dt_u Hin; eapply Hpu; [left; reflexivity |].
        unfold instr_param_uses; rewrite Hpic; exact Hin. }
      set (ext_vars :=
        allowed ++
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (instr_param_uses params defs (INSTR_Call (DTYPE_Base (DTYPE_I w), EXP_Ident (ID_Global (Name fname))) args anns []))).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 false smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpua0_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split;
          [unfold instr_param_uses; rewrite Hpic; exact Hin | rewrite Hpnm; left; reflexivity]. }
      destruct (reify_exp_typing a0 false params src_pnames defs ext_vars smap0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) wa0 ca seen_a Hsmap_ext Hpua0_ext Hra0)
        as (Htopa & Hwta & Hbwa & Hlfa & Hfva_e & Hinca & _).
      apply check_opt_int_width_some_inv in Htopa; subst wa0.
      destruct (eval_reified_exp_src a0 params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) w ca seen_a Hnd Hlp Hls Hla Hvs Hpua0 Hpe Hwfs Henv Hra0)
        as (draws0 & Hfa0 & [[Hub0 [msg0 Hev0]] | [dv0 [Hev0 [Hsc0 Hst0]]]]).
      * exists draws0; split; [exact Hfa0 | left; split].
        -- intros tail_s; unfold denote_code; cbn [loop_monad].
           exact (cfg_steps_pure_int_intrinsic_abs_ub0 (chain_draws draws0 tail_s) env0 id (DTYPE_Base (DTYPE_I w))
                    (EXP_Ident (ID_Global (Name fname))) args anns md w a0 a1 None rest1 Hargs (Hub0 tail_s)).
        -- intros k; cbn [wrap_evals eval_cfg_dag].
           destruct (lower_pure_int_intrinsic_abs_ub w ca flag
                       (build_param_env src_pnames vs) foracle msg0 Hev0) as [msg' Hev'].
           rewrite Hev'; reflexivity.
      * destruct (pure_int_intrinsic_abs_eval_helper w ca flag
                    (build_param_env src_pnames vs) foracle dv0 Hsc0 Hev0)
          as (dv_out & Hpi & Hev_ce & Hsc_out).
        pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen_a false smap0 Hinca Hsmap_ext) as Hsmap_ext_a.
        set (ce := lower_pure_int_intrinsic_abs w ca flag).
        fold ce in Hev_ce.
        destruct (lower_pure_int_intrinsic_abs_typing w ca flag Hwta Hbwa Hlfa Hfka_b)
          as (Hwt_ce & Hbw_ce & Hlf_ce & Hfk_nil & Hsub).
        assert (Hext_ce : incl (collect_free_vars [] ce) ext_vars)
          by (intros x Hx; exact (Hfva_e x (Hsub x Hx))).
        pose proof (wf_smap_entries_add ext_vars defs seen_a false smap0 id w ce Hsmap_ext_a
                      Hid Hwt_ce Hbw_ce Hlf_ce Hext_ce (fun H => match H with end)) as Hwfs1.
        assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
          exists dv, nth_error vs idx = Some dv /\ RM.find r (RM.add id dv_out env0) = Some dv).
        { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
          exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o; [exact Hfe | intros ->; exact (Hnin Hid)]]. }
        pose proof (env_matches_smap_add defs (build_param_env src_pnames vs) foracle smap0 env0
                      id w ce dv_out Henv Hid Hev_ce Hsc_out) as Henv1.
        destruct (IH ext_vars (RM.add id (w, ce) smap0) (RM.add id dv_out env0) seen_a
                    cevals_r smap2 seen2
                    (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror Hin_i))
                    Hpe1 Hwfs1 Henv1 Hrr)
          as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | (env2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
        -- exists (draws0 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
           ++ intros tail_s; rewrite chain_draws_app; unfold denote_code; cbn [loop_monad].
              eapply cfg_steps_to_ub_bind_r.
              ** unfold ins; eapply cfg_steps_pure_int_intrinsic_abs_ret;
                   [reflexivity | exact Hp_intr | exact Hargs | exact Hflag | exact Hfa | exact Hra | exact Hmr
                   | exact (Hst0 (chain_draws draws2 tail_s)) | exact Hpi].
              ** exact (Hub2 tail_s).
           ++ intros k; cbn [wrap_evals eval_cfg_dag]; fold ce; rewrite Hev_ce; exact (Hev_ub2 k).
        -- exists (draws0 ++ draws2); split; [apply Forall_app; split; assumption | right; exists env2].
           split; [exact Hpe2 | split; [exact Henv2 | split]].
           ++ intros k; cbn [wrap_evals eval_cfg_dag]; fold ce; rewrite Hev_ce; exact (Hev_k k).
           ++ intros tail_s; rewrite chain_draws_app; unfold denote_code; cbn [loop_monad].
              eapply cfg_steps_to_ret_bind.
              ** unfold ins; eapply cfg_steps_pure_int_intrinsic_abs_ret;
                   [reflexivity | exact Hp_intr | exact Hargs | exact Hflag | exact Hfa | exact Hra | exact Hmr
                   | exact (Hst0 (chain_draws draws2 tail_s)) | exact Hpi].
              ** exact (Hst2 tail_s).
  - inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
    destruct (IH allowed smap0 env0 seen0 cevals_r smap2 seen2
                (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror Hin_i))
                Hpe Hwfs Henv Hrr)
      as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | (env2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
    + exists draws2; split; [exact Hfa2 | left; split].
      * intros tail_s; unfold denote_code; cbn [loop_monad denote_instr].
        eapply cfg_steps_to_ub_bind_r; [apply CSR_Ret; reflexivity | exact (Hub2 tail_s)].
      * exact Hev_ub2.
    + exists draws2; split; [exact Hfa2 | right; exists env2].
      split; [exact Hpe2 | split; [exact Henv2 | split; [exact Hev_k |]]].
      intros tail_s; unfold denote_code; cbn [loop_monad denote_instr].
      eapply cfg_steps_to_ret_bind; [apply CSR_Ret; reflexivity | exact (Hst2 tail_s)].
Qed.

Lemma eval_reified_code_src {Pa : Params} :
  forall c params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) smap0 (env0 : rmap (@dvalue Pa))
         seen0 cevals smap2 seen2,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall iid ins md idx dt_u,
      In (iid, ins, md) c ->
      In (idx, dt_u) (instr_param_uses params defs ins) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_smap_entries allowed defs seen0 false smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) foracle smap0 env0 ->
    reify_code false params src_pnames defs smap0 seen0 c = Some (cevals, smap2, seen2) ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s,
           cfg_steps_to_ub (chain_draws draws tail_s) env0 (denote_code c None)) /\
        (forall k, eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_evals cevals k) = DO_UB)) \/
       (exists env2,
          (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
             exists dv, nth_error vs idx = Some dv /\ RM.find r env2 = Some dv) /\
          env_matches_smap defs (build_param_env src_pnames vs) foracle smap2 env2 /\
          (forall k,
             eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_evals cevals k) =
             eval_cfg_dag (build_param_env src_pnames vs) foracle k) /\
          (forall tail_s,
             cfg_steps_to_ret (chain_draws draws tail_s) env0 (denote_code c None) tail_s env2 tt))).
Proof.
  induction c as [| i1 | i1 i2 rest2 IH_tail IH_rest2] using list_2step_ind;
    intros params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0 cevals smap2 seen2
           Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
  - cbn [reify_code] in Hr; inversion Hr; subst cevals smap2 seen2.
    exists []; split; [constructor | right; exists env0].
    split; [exact Hpe | split; [exact Henv | split; [intros k; reflexivity | intros tail_s; apply CSR_Ret; reflexivity]]].
  - cbn [reify_code] in Hr; destruct (reify_code_step false params src_pnames defs smap0 seen0 i1)
      as [[[opt_ev smap1] seen1] |] eqn:Hstep; [| discriminate].
    assert (Hrr : reify_code false params src_pnames defs smap1 seen1 [] = Some ([], smap1, seen1))
      by reflexivity.
    inversion Hr; subst cevals smap2 seen2; clear Hr.
    eapply eval_reified_code_single_src;
      [| exact Hnd | exact Hlp | exact Hls | exact Hla | exact Hvs | exact Hpu
       | exact Hpe | exact Hwfs | exact Henv | exact Hstep | exact Hrr | destruct opt_ev; reflexivity].
    intros allowed' smap0' env0' seen0' cevals' smap2' seen2' _ Hpe' _ Henv' Hr'.
    cbn [reify_code] in Hr'; inversion Hr'; subst.
    exists []; split; [constructor | right; exists env0'].
    split; [exact Hpe' | split; [exact Henv' | split; [intros k; reflexivity | intros tail_s; apply CSR_Ret; reflexivity]]].
  - rewrite reify_code_unfold_pair in Hr.
    destruct (match_vec1_id_pair smap0 defs params i1 i2)
      as [[[[[tmp dst] w1] val_exp] kind] |] eqn:Hvec; cbv iota beta zeta in Hr.
    + destruct (reify_exp false params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w1))) val_exp)
        as [[[w ce] seen1] |] eqn:Hre; cbv iota beta zeta in Hr; [| discriminate].
      destruct (reify_code false params src_pnames defs (RM.add dst (w, ce) smap0) seen1 rest2)
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; cbv iota beta zeta in Hr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      destruct (match_vec1_id_pair_inv smap0 defs params i1 i2 tmp dst w1 val_exp kind Hvec)
        as (md1 & md2 & Hi1 & Htmp_def & Hdst_def & _ & Htmp_none & _).
      pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hre)) as Hww1.
      subst w1.
      assert (Hpu_val : forall idx dt_u,
        In (idx, dt_u) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) val_exp) ->
        nth_error arg_dtys idx = Some dt_u).
      { intros idx dt_u Hin.
        eapply Hpu; [left; rewrite Hi1; reflexivity |].
        cbn [instr_param_uses exp_param_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hin. }
      destruct (eval_reified_exp_src val_exp params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) w ce seen1 Hnd Hlp Hls Hla Hvs Hpu_val Hpe Hwfs Henv Hre)
        as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
      * exists draws1; split; [exact Hfa1 | left; split].
        -- intros tail_s; eapply cfg_steps_vec1_pair_ub_val; [exact Hvec | exact (Hub1 tail_s)].
        -- intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
      * set (ext_vars :=
          allowed ++
          List.flat_map (fun '(idx, dt_u) =>
            match dt_u, nth_error src_pnames idx with
            | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
            | _, _ => []
            end) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) val_exp)).
        assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 false smap0).
        { intros r0 wr0 cer0 Hf0; destruct (Hwfs r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
          repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
        assert (Hpu_ext : forall idx w0 pnm,
          In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) val_exp) ->
          nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
        { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
          exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | rewrite Hpnm; left; reflexivity]. }
        destruct (reify_exp_typing val_exp false params src_pnames defs ext_vars smap0 seen0
                    (Some (DTYPE_Base (DTYPE_I w))) w ce seen1 Hsmap_ext Hpu_ext Hre)
          as (_ & Hwt_ce & Hbw_ce & Hlf_ce & Hfv_ce & Hinc01 & Hfk_ce).
        pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen1 false smap0 Hinc01 Hsmap_ext) as Hsmap_ext1.
        pose proof (wf_smap_entries_add ext_vars defs seen1 false smap0 dst w ce Hsmap_ext1
                      Hdst_def Hwt_ce Hbw_ce Hlf_ce Hfv_ce Hfk_ce) as Hwfs1.
        set (env1 := RM.add dst dv1 (RM.add tmp (DVALUE_Array true [dv1]) env0)).
        assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
          exists dv, nth_error vs idx = Some dv /\ RM.find r env1 = Some dv).
        { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
          exists dv; split; [exact Hv |].
          unfold env1; rewrite !RMF.F.add_neq_o;
            [exact Hfe | intros ->; exact (Hnin Htmp_def) | intros ->; exact (Hnin Hdst_def)]. }
        pose proof (env_matches_smap_add_absent defs (build_param_env src_pnames vs) foracle smap0 env0
                      tmp (DVALUE_Array true [dv1]) Htmp_none Henv) as Henv_tmp.
        pose proof (env_matches_smap_add defs (build_param_env src_pnames vs) foracle smap0
                      (RM.add tmp (DVALUE_Array true [dv1]) env0)
                      dst w ce dv1 Henv_tmp Hdst_def Hev1 Hsc1) as Henv1.
        destruct (IH_rest2 params src_pnames defs ext_vars arg_dtys vs foracle
                    (RM.add dst (w, ce) smap0) env1 seen1 cevals_r smap2 seen2
                    Hnd Hlp Hls Hla Hvs
                    (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror (or_intror Hin_i)))
                    Hpe1 Hwfs1 Henv1 Hrr)
          as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | (env2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
        -- exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
           ++ intros tail_s; rewrite chain_draws_app.
              eapply cfg_steps_vec1_pair_ub_rest;
                [exact Hvec | exact Hsc1 | exact (Hst1 (chain_draws draws2 tail_s)) | exact (Hub2 tail_s)].
           ++ intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_ub2 k).
        -- exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right; exists env2].
           split; [exact Hpe2 | split; [exact Henv2 | split]].
           ++ intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_k k).
           ++ intros tail_s; rewrite chain_draws_app; unfold denote_code; cbn [loop_monad].
              eapply cfg_steps_vec1_pair_bind;
                [exact Hvec | exact Hsc1 | exact (Hst1 (chain_draws draws2 tail_s)) | exact (Hst2 tail_s)].
    + destruct (reify_code_step false params src_pnames defs smap0 seen0 i1)
        as [[[opt_ev smap1] seen1] |] eqn:Hstep; cbv iota beta zeta in Hr; [| discriminate].
      destruct (reify_code false params src_pnames defs smap1 seen1 (i2 :: rest2))
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; cbv iota beta zeta in Hr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      eapply eval_reified_code_single_src;
        [| exact Hnd | exact Hlp | exact Hls | exact Hla | exact Hvs | exact Hpu
         | exact Hpe | exact Hwfs | exact Henv | exact Hstep | exact Hrr | reflexivity].
      intros allowed' smap0' env0' seen0' cevals' smap2' seen2' Hpu' Hpe' Hwfs' Henv' Hr'.
      exact (IH_tail params src_pnames defs allowed' arg_dtys vs foracle smap0' env0' seen0'
               cevals' smap2' seen2' Hnd Hlp Hls Hla Hvs Hpu' Hpe' Hwfs' Henv' Hr').
Qed.

Lemma reify_code_wf_smap :
  forall c uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2,
    wf_smap_entries allowed defs seen0 uf smap0 ->
    reify_code uf params src_pnames defs smap0 seen0 c = Some (cevals, smap2, seen2) ->
    exists ext_vars,
      incl seen0 seen2 /\
      wf_smap_entries ext_vars defs seen2 uf smap2.
Proof.
  intros c uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2 Hsmap0 Hr.
  set (ext_vars :=
    allowed ++
    List.flat_map (fun '(_, ins, _) =>
      List.flat_map (fun '(idx, dt_u) =>
        match dt_u, nth_error src_pnames idx with
        | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
        | _, _ => []
        end) (instr_param_uses params defs ins)) c).
  assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 uf smap0).
  { intros r0 wr0 cer0 Hf0; destruct (Hsmap0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
    repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
  assert (Hpu_ext : forall iid ins md idx w0 pnm,
    In (iid, ins, md) c ->
    In (idx, DTYPE_Base (DTYPE_I w0)) (instr_param_uses params defs ins) ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) ext_vars).
  { intros iid ins md idx w0 pnm Hin1 Hin2 Hpnm.
    apply in_app_iff; right; apply in_flat_map; exists (iid, ins, md); split; [exact Hin1 |].
    apply in_flat_map; exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin2 | rewrite Hpnm; left; reflexivity]. }
  destruct (reify_code_typing c uf params src_pnames defs ext_vars smap0 seen0 cevals smap2 seen2
              Hsmap_ext Hpu_ext Hr)
    as (Hinc & Hsmap2 & _).
  exists ext_vars; split; assumption.
Qed.

Lemma reify_phi_evals_wf_smap :
  forall phis uf params src_pnames defs allowed smap0 bid_from seen0 pevals seen2,
    wf_smap_entries allowed defs seen0 uf smap0 ->
    reify_phi_evals uf params src_pnames defs smap0 bid_from seen0 phis = Some (pevals, seen2) ->
    exists ext_vars,
      incl seen0 seen2 /\
      Forall (phi_eval_wf_entry ext_vars defs seen2 uf) pevals /\
      wf_smap_entries ext_vars defs seen2 uf (apply_phi_smap smap0 pevals).
Proof.
  intros phis uf params src_pnames defs allowed smap0 bid_from seen0 pevals seen2 Hsmap0 Hr.
  set (ext_vars :=
    allowed ++
    List.flat_map (fun '(_, Phi _ dt_p pargs_p, _) =>
      List.flat_map (fun '(_, e_p) =>
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (exp_param_uses params defs (Some dt_p) e_p)) pargs_p) phis).
  assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 uf smap0).
  { intros r0 wr0 cer0 Hf0; destruct (Hsmap0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
    repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
  assert (Hpu_ext : forall id' fm' dt' pargs' md' op' idx w0 pnm,
    In (id', Phi fm' dt' pargs', md') phis ->
    In (bid_from, op') pargs' ->
    In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some dt') op') ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) ext_vars).
  { intros id' fm' dt' pargs' md' op' idx w0 pnm Hin1 Hin2 Hin3 Hpnm.
    apply in_app_iff; right; apply in_flat_map; exists (id', Phi fm' dt' pargs', md'); split; [exact Hin1 |].
    apply in_flat_map; exists (bid_from, op'); split; [exact Hin2 |].
    apply in_flat_map; exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin3 | rewrite Hpnm; left; reflexivity]. }
  destruct (reify_phi_evals_typing phis uf params src_pnames defs ext_vars smap0 bid_from
              seen0 pevals seen2 Hsmap_ext Hpu_ext Hr)
    as [Hinc Hfa].
  pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen2 uf smap0 Hinc Hsmap_ext) as Hsmap2.
  exists ext_vars; split; [exact Hinc | split; [exact Hfa | exact (apply_phi_smap_wf _ _ _ _ _ _ Hsmap2 Hfa)]].
Qed.

Lemma eval_reified_code_single_tgt {Pa : Params} :
  forall i1 rest1 params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         smap0 (env0 : rmap (@dvalue Pa)) seen0 opt_ev smap1 seen1 cevals_r cevals smap2 seen2,
    (forall allowed' sigma' fmap' smap' env' seen' cevals' smap2' seen2',
      (forall iid ins md idx dt_u,
        In (iid, ins, md) rest1 ->
        In (idx, dt_u) (instr_param_uses params defs ins) ->
        nth_error arg_dtys idx = Some dt_u) ->
      (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
        exists dv, nth_error vs idx = Some dv /\ RM.find r env' = Some dv) ->
      wf_draw_strat sigma' ->
      wf_smap_entries allowed' defs seen' true smap' ->
      env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap') smap' env' ->
      reify_code true params src_pnames defs smap' seen' rest1 = Some (cevals', smap2', seen2') ->
      exists added : list (freeze_key * Z),
        (forall key z, In (key, z) added -> In key seen2' /\ ~ In key seen') /\
        ((forall k,
            eval_cfg_dag (build_param_env src_pnames vs)
              (oracle_of_fmap (added ++ fmap')) (wrap_evals cevals' k) = DO_UB) \/
         (exists sigma2 env2,
            wf_draw_strat sigma2 /\
            (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
               exists dv, nth_error vs idx = Some dv /\ RM.find r env2 = Some dv) /\
            env_matches_smap defs (build_param_env src_pnames vs)
              (oracle_of_fmap (added ++ fmap')) smap2' env2 /\
            (forall fmap_later k,
               (forall key z, In (key, z) fmap_later -> ~ In key seen2') ->
               eval_cfg_dag (build_param_env src_pnames vs)
                 (oracle_of_fmap (fmap_later ++ added ++ fmap')) (wrap_evals cevals' k) =
               eval_cfg_dag (build_param_env src_pnames vs)
                 (oracle_of_fmap (fmap_later ++ added ++ fmap')) k) /\
            cfg_steps_to_ret sigma' env' (denote_code rest1 None) sigma2 env2 tt))) ->
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall iid ins md idx dt_u,
      In (iid, ins, md) (i1 :: rest1) ->
      In (idx, dt_u) (instr_param_uses params defs ins) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed defs seen0 true smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap0 env0 ->
    reify_code_step true params src_pnames defs smap0 seen0 i1 = Some (opt_ev, smap1, seen1) ->
    reify_code true params src_pnames defs smap1 seen1 rest1 = Some (cevals_r, smap2, seen2) ->
    cevals = (match opt_ev with Some ev => ev :: cevals_r | None => cevals_r end) ->
    exists added : list (freeze_key * Z),
      (forall key z, In (key, z) added -> In key seen2 /\ ~ In key seen0) /\
      ((forall k,
          eval_cfg_dag (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) (wrap_evals cevals k) = DO_UB) \/
       (exists sigma2 env2,
          wf_draw_strat sigma2 /\
          (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
             exists dv, nth_error vs idx = Some dv /\ RM.find r env2 = Some dv) /\
          env_matches_smap defs (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) smap2 env2 /\
          (forall fmap_later k,
             (forall key z, In (key, z) fmap_later -> ~ In key seen2) ->
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) (wrap_evals cevals k) =
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) k) /\
          cfg_steps_to_ret sigma0 env0 (denote_code (i1 :: rest1) None) sigma2 env2 tt)).
Proof.
  intros [[iid ins] md] rest1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0
    opt_ev smap1 seen1 cevals_r cevals smap2 seen2
    IH Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hstep Hrr ->.
  cbn [reify_code_step] in Hstep.
  destruct iid as [id | vid]; [destruct ins; try discriminate | destruct ins; try discriminate].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    apply raw_id_in_list_spec in Hid.
    destruct (reify_exp true params src_pnames defs smap0 seen0 None op)
      as [[[w ce] seen1'] |] eqn:Hre; [| discriminate].
    inversion Hstep; subst opt_ev smap1 seen1'; clear Hstep.
    set (ext_vars :=
      allowed ++
      List.flat_map (fun '(idx, dt_u) =>
        match dt_u, nth_error src_pnames idx with
        | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
        | _, _ => []
        end) (exp_param_uses params defs None op)).
    assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 true smap0).
    { intros r0 wr0 cer0 Hf0; destruct (Hwfs0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
      repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
    assert (Hpu_ext : forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs None op) ->
      nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
    { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
      exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | rewrite Hpnm; left; reflexivity]. }
    destruct (reify_exp_typing op true params src_pnames defs ext_vars smap0 seen0 None w ce seen1
                Hsmap_ext Hpu_ext Hre)
      as (_ & Hwt_ce & Hbw_ce & Hlf_ce & Hfv_ce & Hinc01 & Hfk_ce).
    pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen1 true smap0 Hinc01 Hsmap_ext) as Hsmap_ext1.
    pose proof (wf_smap_entries_add ext_vars defs seen1 true smap0 id w ce Hsmap_ext1
                  Hid Hwt_ce Hbw_ce Hlf_ce Hfv_ce Hfk_ce) as Hwfs1.
    destruct (reify_code_wf_smap rest1 true params src_pnames defs ext_vars
                (RM.add id (w, ce) smap0) seen1 cevals_r smap2 seen2 Hwfs1 Hrr)
      as (_ & Hinc12 & _).
    destruct (eval_reified_exp_tgt op params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0
                None w ce seen1 Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu (IId id) (INSTR_Op op) md idx d (or_introl eq_refl) Hin)
                Hpe Hwfd0 Hwfs0 Henv0 Hre)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0].
      * left; intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                    (build_param_env src_pnames vs) smap0 env0 Hwfs0
                    (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv0'.
      pose proof (env_matches_smap_add defs (build_param_env src_pnames vs) (oracle_of_fmap (added1 ++ fmap0))
                    smap0 env0 id w ce dv1 Henv0' Hid Hev1 Hsc1) as Henv1.
      assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
        exists dv, nth_error vs idx = Some dv /\ RM.find r (RM.add id dv1 env0) = Some dv).
      { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
        exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o; [exact Hfe | intros ->; exact (Hnin Hid)]]. }
      destruct (IH ext_vars sigma1 (added1 ++ fmap0)
                  (RM.add id (w, ce) smap0) (RM.add id dv1 env0) seen1 cevals_r smap2 seen2
                  (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror Hin_i))
                  Hpe1 Hwfd1 Hwfs1 Henv1 Hrr)
        as (added2 & Had2 & [Hev_ub2 | (sigma2 & env2 & Hwfd2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
        split; [exact Had12 | left; intros k].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf_ce (Hfk_ce eq_refl)
                      (fun q z H => proj2 (Had2 q z H))) as Hev1'.
        cbn [wrap_evals eval_cfg_dag]; rewrite Hev1', Hev1; exact (Hev_ub2 k).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
        split; [exact Had12 | right; exists sigma2, env2].
        split; [exact Hwfd2 | split; [exact Hpe2 | split; [rewrite <- app_assoc; exact Henv2 | split]]].
        -- intros fmap_later k Hdisj_lat.
           assert (Hdisj_lat1 : forall key z, In (key, z) (fmap_later ++ added2) -> ~ In key seen1).
           { intros key z Hkz; apply in_app_iff in Hkz as [Hl | Ha2].
             - intros Hs1; exact (Hdisj_lat key z Hl (Hinc12 key Hs1)).
             - exact (proj2 (Had2 key z Ha2)). }
           replace (fmap_later ++ (added2 ++ added1) ++ fmap0)
             with ((fmap_later ++ added2) ++ (added1 ++ fmap0))
             by (rewrite !app_assoc; reflexivity).
           pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                         (fmap_later ++ added2) (added1 ++ fmap0) seen1 Hlf_ce (Hfk_ce eq_refl) Hdisj_lat1)
             as Hev_lat1.
           cbn [wrap_evals eval_cfg_dag]; rewrite Hev_lat1, Hev1.
           replace ((fmap_later ++ added2) ++ added1 ++ fmap0)
             with (fmap_later ++ (added2 ++ (added1 ++ fmap0)))
             by (rewrite !app_assoc; reflexivity).
           exact (Hev_k fmap_later k Hdisj_lat).
        -- unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst1) |].
              eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
           ++ exact Hst2.
  - set (ins := INSTR_Call fn args anns obs) in Hstep |- *.
    destruct (raw_id_in_list id defs &&
              match metadata_range md with None => true | Some _ => false end) eqn:Hhdr;
      [| discriminate].
    apply andb_true_iff in Hhdr as [Hid Hmr_b]; apply raw_id_in_list_spec in Hid.
    assert (Hmr : metadata_range md = None) by (destruct (metadata_range md); [discriminate Hmr_b | reflexivity]).
    destruct (match_pure_int_intrinsic_call ins) as [pic |] eqn:Hpic; [| discriminate].
    pose proof (match_pure_int_intrinsic_call_inv ins pic Hpic) as Hpic_inv.
    unfold ins in Hpic, Hpic_inv;
    destruct pic as [op w a0 a1 | w a0 flag];
      destruct fn as [dt_fn fn_e]; destruct fn_e; cbn in Hpic_inv; try contradiction Hpic_inv;
      match type of Hpic_inv with
      | context [EXP_Ident ?id0] => destruct id0 as [gid_g | ?]; [| contradiction Hpic_inv]
      | _ =>
          match type of Hpic_inv with
          | context [match ?id0 with ID_Global _ => _ | ID_Local _ => _ end] =>
              destruct id0 as [gid_g | ?]; [| cbn in Hpic_inv; contradiction Hpic_inv]
          end
      end; destruct gid_g as [fname | |]; cbn in Hpic_inv; try contradiction Hpic_inv;
      destruct obs; cbn in Hpic_inv; try contradiction Hpic_inv;
      destruct Hpic_inv as (Hdt_fn & Hp_intr & Hpic_rest); subst dt_fn.
    + destruct Hpic_rest as (Hop_neq & Hargs & Hfa & Hra).
      destruct (reify_exp true params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) a0)
        as [[[wa0 ca] seen_a] |] eqn:Hra0; [| discriminate].
      destruct (reify_exp true params src_pnames defs smap0 seen_a (Some (DTYPE_Base (DTYPE_I w))) a1)
        as [[[wa1 cb] seen_b] |] eqn:Hra1; [| discriminate].
      destruct (list_empty_b (collect_freeze_keys ca) && list_empty_b (collect_freeze_keys cb)) eqn:Hfk01;
        [| discriminate].
      apply andb_true_iff in Hfk01 as [Hfka_b Hfkb_b].
      apply list_empty_b_spec in Hfka_b; apply list_empty_b_spec in Hfkb_b.
      inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
      assert (Hpua0 : forall idx dt_u,
        In (idx, dt_u) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error arg_dtys idx = Some dt_u).
      { intros idx dt_u Hin; eapply Hpu; [left; reflexivity |].
        unfold instr_param_uses; rewrite Hpic; apply in_app_iff; left; exact Hin. }
      assert (Hpua1 : forall idx dt_u,
        In (idx, dt_u) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a1) ->
        nth_error arg_dtys idx = Some dt_u).
      { intros idx dt_u Hin; eapply Hpu; [left; reflexivity |].
        unfold instr_param_uses; rewrite Hpic; apply in_app_iff; right; exact Hin. }
      set (ext_vars :=
        allowed ++
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (instr_param_uses params defs (INSTR_Call (DTYPE_Base (DTYPE_I w), EXP_Ident (ID_Global (Name fname))) args anns []))).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 true smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpua0_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split;
          [unfold instr_param_uses; rewrite Hpic; apply in_app_iff; left; exact Hin | rewrite Hpnm; left; reflexivity]. }
      assert (Hpua1_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a1) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split;
          [unfold instr_param_uses; rewrite Hpic; apply in_app_iff; right; exact Hin | rewrite Hpnm; left; reflexivity]. }
      destruct (reify_exp_typing a0 true params src_pnames defs ext_vars smap0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) wa0 ca seen_a Hsmap_ext Hpua0_ext Hra0)
        as (Htopa & Hwta & Hbwa & Hlfa & Hfva_e & Hinca & _).
      apply check_opt_int_width_some_inv in Htopa; subst wa0.
      pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen_a true smap0 Hinca Hsmap_ext) as Hsmap_ext_a.
      destruct (reify_exp_typing a1 true params src_pnames defs ext_vars smap0 seen_a
                  (Some (DTYPE_Base (DTYPE_I w))) wa1 cb seen_b Hsmap_ext_a Hpua1_ext Hra1)
        as (Htopb & Hwtb & Hbwb & Hlfb & Hfvb_e & Hincb & _).
      apply check_opt_int_width_some_inv in Htopb; subst wa1.
      assert (Hinc0b : incl seen0 seen_b) by (intros x Hx; exact (Hincb x (Hinca x Hx))).
      pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen_b true smap0 Hinc0b Hsmap_ext) as Hsmap_ext_b.
      set (ce := lower_pure_int_intrinsic_binop op w ca cb).
      destruct (lower_pure_int_intrinsic_binop_typing op w ca cb
                  Hwta Hbwa Hlfa Hfka_b Hwtb Hbwb Hlfb Hfkb_b)
        as (Hwt_ce & Hbw_ce & Hlf_ce & Hfk_nil & Hsub).
      assert (Hext_ce : incl (collect_free_vars [] ce) ext_vars).
      { intros x Hx; apply Hsub, in_app_iff in Hx as [Hx | Hx]; [exact (Hfva_e x Hx) | exact (Hfvb_e x Hx)]. }
      pose proof (wf_smap_entries_add ext_vars defs seen_b true smap0 id w ce Hsmap_ext_b
                    Hid Hwt_ce Hbw_ce Hlf_ce Hext_ce (fun _ x Hx => ltac:(unfold ce in Hx; rewrite Hfk_nil in Hx; destruct Hx))) as Hwfs1.
      destruct (reify_code_wf_smap rest1 true params src_pnames defs ext_vars
                  (RM.add id (w, ce) smap0) seen_b cevals_r smap2 seen2 Hwfs1 Hrr)
        as (_ & Hincb2 & _).
      pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen_a true smap0 Hinca Hwfs0) as Hwfs0_a.
      destruct (eval_reified_exp_tgt a0 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) w ca seen_a Hnd Hlp Hls Hla Hvs Hpua0
                  Hpe Hwfd0 Hwfs0 Henv0 Hra0)
        as (added0 & Had0 & [[msg0 Hev0] | (sigma1 & dv0 & Hwfd1 & Hev0 & Hsc0 & Hst0)]).
      * exists added0; split.
        -- intros k z Hkz; destruct (Had0 k z Hkz) as [Hsa Hn0];
             split; [exact (Hincb2 k (Hincb k Hsa)) | exact Hn0].
        -- left; intros k; cbn [wrap_evals eval_cfg_dag]; fold ce.
           destruct (lower_pure_int_intrinsic_binop_ub_l op w ca cb
                       (build_param_env src_pnames vs) (oracle_of_fmap (added0 ++ fmap0)) msg0 Hop_neq Hev0)
             as [msg' Hev'].
           unfold ce; rewrite Hev'; reflexivity.
      * pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added0 fmap0
                      (build_param_env src_pnames vs) smap0 env0 Hwfs0
                      (fun k z H => proj2 (Had0 k z H)) Henv0) as Henv0'.
        destruct (eval_reified_exp_tgt a1 params src_pnames defs allowed arg_dtys vs sigma1 (added0 ++ fmap0)
                    smap0 env0 seen_a (Some (DTYPE_Base (DTYPE_I w))) w cb seen_b
                    Hnd Hlp Hls Hla Hvs Hpua1 Hpe Hwfd1 Hwfs0_a Henv0' Hra1)
          as (added1 & Had1 & [[msg1 Hev1] | (sigma1b & dv1 & Hwfd1b & Hev1 & Hsc1 & Hst1)]).
        -- exists (added1 ++ added0); split.
           ++ intros k z Hkz; apply in_app_iff in Hkz as [Hk1 | Hk0].
              ** destruct (Had1 k z Hk1) as [Hsb Hn_a]; split; [exact (Hincb2 k Hsb) | intros Hs0; exact (Hn_a (Hinca k Hs0))].
              ** destruct (Had0 k z Hk0) as [Hsa Hn0]; split; [exact (Hincb2 k (Hincb k Hsa)) | exact Hn0].
           ++ left; intros k; rewrite <- app_assoc.
              pose proof (eval_let_free_prepend_fmap ca (build_param_env src_pnames vs)
                            added1 (added0 ++ fmap0) seen_a Hlfa
                            (fun q Hq => ltac:(rewrite Hfka_b in Hq; destruct Hq))
                            (fun q z H => proj2 (Had1 q z H))) as Hev0'.
              rewrite Hev0 in Hev0'.
              destruct (lower_pure_int_intrinsic_binop_ub_r op w ca cb
                          (build_param_env src_pnames vs) (oracle_of_fmap (added1 ++ added0 ++ fmap0))
                          dv0 msg1 Hop_neq Hev0' Hev1) as [msg' Hev'].
              cbn [wrap_evals eval_cfg_dag]; fold ce; unfold ce; rewrite Hev'; reflexivity.
        -- pose proof (eval_let_free_prepend_fmap ca (build_param_env src_pnames vs)
                         added1 (added0 ++ fmap0) seen_a Hlfa
                         (fun q Hq => ltac:(rewrite Hfka_b in Hq; destruct Hq))
                         (fun q z H => proj2 (Had1 q z H))) as Hev0'.
           rewrite Hev0 in Hev0'.
           destruct (pure_int_intrinsic_binop_eval_helpers op w ca cb
                       (build_param_env src_pnames vs) (oracle_of_fmap (added1 ++ added0 ++ fmap0))
                       dv0 dv1 Hop_neq Hsc0 Hsc1 Hev0' Hev1)
             as (dv_out & Hpi & Hev_ce & Hsc_out).
           fold ce in Hev_ce.
           pose proof (env_matches_smap_oracle_prepend allowed defs seen_a added1 (added0 ++ fmap0)
                         (build_param_env src_pnames vs) smap0 env0 Hwfs0_a
                         (fun k z H => proj2 (Had1 k z H)) Henv0') as Henv0''.
           pose proof (env_matches_smap_add defs (build_param_env src_pnames vs)
                         (oracle_of_fmap (added1 ++ added0 ++ fmap0)) smap0 env0
                         id w ce dv_out Henv0'' Hid Hev_ce Hsc_out) as Henv1.
           assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
             exists dv, nth_error vs idx = Some dv /\ RM.find r (RM.add id dv_out env0) = Some dv).
           { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
             exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o; [exact Hfe | intros ->; exact (Hnin Hid)]]. }
           destruct (IH ext_vars sigma1b (added1 ++ added0 ++ fmap0)
                       (RM.add id (w, ce) smap0) (RM.add id dv_out env0) seen_b cevals_r smap2 seen2
                       (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror Hin_i))
                       Hpe1 Hwfd1b Hwfs1 Henv1 Hrr)
             as (added2 & Had2 & [Hev_ub2 | (sigma2 & env2 & Hwfd2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
           ++ exists (added2 ++ added1 ++ added0); split.
              ** intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk10].
                 --- destruct (Had2 k z Hk2) as [Hs2 Hn_b]; split; [exact Hs2 | intros Hs0; exact (Hn_b (Hinc0b k Hs0))].
                 --- apply in_app_iff in Hk10 as [Hk1 | Hk0].
                     +++ destruct (Had1 k z Hk1) as [Hsb Hn_a]; split; [exact (Hincb2 k Hsb) | intros Hs0; exact (Hn_a (Hinca k Hs0))].
                     +++ destruct (Had0 k z Hk0) as [Hsa Hn0]; split; [exact (Hincb2 k (Hincb k Hsa)) | exact Hn0].
              ** left; intros k; rewrite <- !app_assoc.
                 pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                               added2 (added1 ++ added0 ++ fmap0) seen_b Hlf_ce
                               (fun q Hq => ltac:(unfold ce in Hq; rewrite Hfk_nil in Hq; destruct Hq))
                               (fun q z H => proj2 (Had2 q z H))) as Hev_ce'.
                 cbn [wrap_evals eval_cfg_dag]; fold ce; rewrite Hev_ce', Hev_ce; exact (Hev_ub2 k).
           ++ exists (added2 ++ added1 ++ added0); split.
              ** intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk10].
                 --- destruct (Had2 k z Hk2) as [Hs2 Hn_b]; split; [exact Hs2 | intros Hs0; exact (Hn_b (Hinc0b k Hs0))].
                 --- apply in_app_iff in Hk10 as [Hk1 | Hk0].
                     +++ destruct (Had1 k z Hk1) as [Hsb Hn_a]; split; [exact (Hincb2 k Hsb) | intros Hs0; exact (Hn_a (Hinca k Hs0))].
                     +++ destruct (Had0 k z Hk0) as [Hsa Hn0]; split; [exact (Hincb2 k (Hincb k Hsa)) | exact Hn0].
              ** right; exists sigma2, env2.
                 split; [exact Hwfd2 | split; [exact Hpe2 | split; [rewrite <- !app_assoc; exact Henv2 | split]]].
                 --- intros fmap_later k Hdisj_lat.
                     assert (Hdisj_latb : forall key z, In (key, z) (fmap_later ++ added2) -> ~ In key seen_b).
                     { intros key z Hkz; apply in_app_iff in Hkz as [Hl | Ha2].
                       - intros Hsb; exact (Hdisj_lat key z Hl (Hincb2 key Hsb)).
                       - exact (proj2 (Had2 key z Ha2)). }
                     replace (fmap_later ++ (added2 ++ added1 ++ added0) ++ fmap0)
                       with ((fmap_later ++ added2) ++ (added1 ++ added0 ++ fmap0))
                       by (rewrite !app_assoc; reflexivity).
                     pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                                   (fmap_later ++ added2) (added1 ++ added0 ++ fmap0) seen_b
                                   Hlf_ce (fun q Hq => ltac:(unfold ce in Hq; rewrite Hfk_nil in Hq; destruct Hq))
                                   Hdisj_latb) as Hev_lat.
                     cbn [wrap_evals eval_cfg_dag]; fold ce; rewrite Hev_lat, Hev_ce.
                     replace ((fmap_later ++ added2) ++ added1 ++ added0 ++ fmap0)
                       with (fmap_later ++ (added2 ++ (added1 ++ added0 ++ fmap0)))
                       by (rewrite !app_assoc; reflexivity).
                     exact (Hev_k fmap_later k Hdisj_lat).
                 --- unfold denote_code; cbn [loop_monad].
                     eapply cfg_steps_to_ret_bind.
                     +++ unfold ins; eapply cfg_steps_pure_int_intrinsic_binop_ret;
                           [reflexivity | exact Hp_intr | exact Hargs | exact Hfa | exact Hra | exact Hmr
                           | exact Hst0 | exact Hst1 | exact Hpi].
                     +++ exact Hst2.
    + destruct Hpic_rest as (a1 & Hargs & Hflag & Hfa & Hra).
      destruct (reify_exp true params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) a0)
        as [[[wa0 ca] seen_a] |] eqn:Hra0; [| discriminate].
      destruct (list_empty_b (collect_freeze_keys ca)) eqn:Hfka_b; [| discriminate].
      apply list_empty_b_spec in Hfka_b.
      inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
      assert (Hpua0 : forall idx dt_u,
        In (idx, dt_u) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error arg_dtys idx = Some dt_u).
      { intros idx dt_u Hin; eapply Hpu; [left; reflexivity |].
        unfold instr_param_uses; rewrite Hpic; exact Hin. }
      set (ext_vars :=
        allowed ++
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (instr_param_uses params defs (INSTR_Call (DTYPE_Base (DTYPE_I w), EXP_Ident (ID_Global (Name fname))) args anns []))).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 true smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpua0_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split;
          [unfold instr_param_uses; rewrite Hpic; exact Hin | rewrite Hpnm; left; reflexivity]. }
      destruct (reify_exp_typing a0 true params src_pnames defs ext_vars smap0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) wa0 ca seen_a Hsmap_ext Hpua0_ext Hra0)
        as (Htopa & Hwta & Hbwa & Hlfa & Hfva_e & Hinca & _).
      apply check_opt_int_width_some_inv in Htopa; subst wa0.
      pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen_a true smap0 Hinca Hsmap_ext) as Hsmap_ext_a.
      set (ce := lower_pure_int_intrinsic_abs w ca flag).
      destruct (lower_pure_int_intrinsic_abs_typing w ca flag Hwta Hbwa Hlfa Hfka_b)
        as (Hwt_ce & Hbw_ce & Hlf_ce & Hfk_nil & Hsub).
      assert (Hext_ce : incl (collect_free_vars [] ce) ext_vars)
        by (intros x Hx; exact (Hfva_e x (Hsub x Hx))).
      pose proof (wf_smap_entries_add ext_vars defs seen_a true smap0 id w ce Hsmap_ext_a
                    Hid Hwt_ce Hbw_ce Hlf_ce Hext_ce (fun _ x Hx => ltac:(unfold ce in Hx; rewrite Hfk_nil in Hx; destruct Hx))) as Hwfs1.
      destruct (reify_code_wf_smap rest1 true params src_pnames defs ext_vars
                  (RM.add id (w, ce) smap0) seen_a cevals_r smap2 seen2 Hwfs1 Hrr)
        as (_ & Hinca2 & _).
      destruct (eval_reified_exp_tgt a0 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) w ca seen_a Hnd Hlp Hls Hla Hvs Hpua0
                  Hpe Hwfd0 Hwfs0 Henv0 Hra0)
        as (added0 & Had0 & [[msg0 Hev0] | (sigma1 & dv0 & Hwfd1 & Hev0 & Hsc0 & Hst0)]).
      * exists added0; split.
        -- intros k z Hkz; destruct (Had0 k z Hkz) as [Hsa Hn0]; split; [exact (Hinca2 k Hsa) | exact Hn0].
        -- left; intros k; cbn [wrap_evals eval_cfg_dag]; fold ce.
           destruct (lower_pure_int_intrinsic_abs_ub w ca flag
                       (build_param_env src_pnames vs) (oracle_of_fmap (added0 ++ fmap0)) msg0 Hev0)
             as [msg' Hev'].
           unfold ce; rewrite Hev'; reflexivity.
      * destruct (pure_int_intrinsic_abs_eval_helper w ca flag
                    (build_param_env src_pnames vs) (oracle_of_fmap (added0 ++ fmap0)) dv0 Hsc0 Hev0)
          as (dv_out & Hpi & Hev_ce & Hsc_out).
        fold ce in Hev_ce.
        pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added0 fmap0
                      (build_param_env src_pnames vs) smap0 env0 Hwfs0
                      (fun k z H => proj2 (Had0 k z H)) Henv0) as Henv0'.
        pose proof (env_matches_smap_add defs (build_param_env src_pnames vs)
                      (oracle_of_fmap (added0 ++ fmap0)) smap0 env0
                      id w ce dv_out Henv0' Hid Hev_ce Hsc_out) as Henv1.
        assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
          exists dv, nth_error vs idx = Some dv /\ RM.find r (RM.add id dv_out env0) = Some dv).
        { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
          exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o; [exact Hfe | intros ->; exact (Hnin Hid)]]. }
        destruct (IH ext_vars sigma1 (added0 ++ fmap0)
                    (RM.add id (w, ce) smap0) (RM.add id dv_out env0) seen_a cevals_r smap2 seen2
                    (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror Hin_i))
                    Hpe1 Hwfd1 Hwfs1 Henv1 Hrr)
          as (added2 & Had2 & [Hev_ub2 | (sigma2 & env2 & Hwfd2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
        -- exists (added2 ++ added0); split.
           ++ intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk0].
              ** destruct (Had2 k z Hk2) as [Hs2 Hn_a]; split; [exact Hs2 | intros Hs0; exact (Hn_a (Hinca k Hs0))].
              ** destruct (Had0 k z Hk0) as [Hsa Hn0]; split; [exact (Hinca2 k Hsa) | exact Hn0].
           ++ left; intros k; rewrite <- app_assoc.
              pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                            added2 (added0 ++ fmap0) seen_a Hlf_ce
                            (fun q Hq => ltac:(unfold ce in Hq; rewrite Hfk_nil in Hq; destruct Hq))
                            (fun q z H => proj2 (Had2 q z H))) as Hev_ce'.
              cbn [wrap_evals eval_cfg_dag]; fold ce; rewrite Hev_ce', Hev_ce; exact (Hev_ub2 k).
        -- exists (added2 ++ added0); split.
           ++ intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk0].
              ** destruct (Had2 k z Hk2) as [Hs2 Hn_a]; split; [exact Hs2 | intros Hs0; exact (Hn_a (Hinca k Hs0))].
              ** destruct (Had0 k z Hk0) as [Hsa Hn0]; split; [exact (Hinca2 k Hsa) | exact Hn0].
           ++ right; exists sigma2, env2.
              split; [exact Hwfd2 | split; [exact Hpe2 | split; [rewrite <- app_assoc; exact Henv2 | split]]].
              ** intros fmap_later k Hdisj_lat.
                 assert (Hdisj_lata : forall key z, In (key, z) (fmap_later ++ added2) -> ~ In key seen_a).
                 { intros key z Hkz; apply in_app_iff in Hkz as [Hl | Ha2].
                   - intros Hsa; exact (Hdisj_lat key z Hl (Hinca2 key Hsa)).
                   - exact (proj2 (Had2 key z Ha2)). }
                 replace (fmap_later ++ (added2 ++ added0) ++ fmap0)
                   with ((fmap_later ++ added2) ++ (added0 ++ fmap0))
                   by (rewrite !app_assoc; reflexivity).
                 pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                               (fmap_later ++ added2) (added0 ++ fmap0) seen_a
                               Hlf_ce (fun q Hq => ltac:(unfold ce in Hq; rewrite Hfk_nil in Hq; destruct Hq))
                               Hdisj_lata) as Hev_lat.
                 cbn [wrap_evals eval_cfg_dag]; fold ce; rewrite Hev_lat, Hev_ce.
                 replace ((fmap_later ++ added2) ++ added0 ++ fmap0)
                   with (fmap_later ++ (added2 ++ (added0 ++ fmap0)))
                   by (rewrite !app_assoc; reflexivity).
                 exact (Hev_k fmap_later k Hdisj_lat).
              ** unfold denote_code; cbn [loop_monad].
                 eapply cfg_steps_to_ret_bind.
                 --- unfold ins; eapply cfg_steps_pure_int_intrinsic_abs_ret;
                       [reflexivity | exact Hp_intr | exact Hargs | exact Hflag | exact Hfa | exact Hra | exact Hmr
                       | exact Hst0 | exact Hpi].
                 --- exact Hst2.
  - inversion Hstep; subst opt_ev smap1 seen1; clear Hstep.
    destruct (IH allowed sigma0 fmap0 smap0 env0 seen0 cevals_r smap2 seen2
                (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror Hin_i))
                Hpe Hwfd0 Hwfs0 Henv0 Hrr)
      as (added2 & Had2 & [Hev_ub2 | (sigma2 & env2 & Hwfd2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
    + exists added2; split; [exact Had2 | left; exact Hev_ub2].
    + exists added2; split; [exact Had2 | right; exists sigma2, env2].
      split; [exact Hwfd2 | split; [exact Hpe2 | split; [exact Henv2 | split; [exact Hev_k |]]]].
      unfold denote_code; cbn [loop_monad denote_instr].
      eapply cfg_steps_to_ret_bind; [apply CSR_Ret; reflexivity | exact Hst2].
Qed.

Lemma eval_reified_code_tgt {Pa : Params} :
  forall c params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         smap0 (env0 : rmap (@dvalue Pa)) seen0 cevals smap2 seen2,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall iid ins md idx dt_u,
      In (iid, ins, md) c ->
      In (idx, dt_u) (instr_param_uses params defs ins) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed defs seen0 true smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap0 env0 ->
    reify_code true params src_pnames defs smap0 seen0 c = Some (cevals, smap2, seen2) ->
    exists added : list (freeze_key * Z),
      (forall key z, In (key, z) added -> In key seen2 /\ ~ In key seen0) /\
      ((forall k,
          eval_cfg_dag (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) (wrap_evals cevals k) = DO_UB) \/
       (exists sigma2 env2,
          wf_draw_strat sigma2 /\
          (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
             exists dv, nth_error vs idx = Some dv /\ RM.find r env2 = Some dv) /\
          env_matches_smap defs (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) smap2 env2 /\
          (forall fmap_later k,
             (forall key z, In (key, z) fmap_later -> ~ In key seen2) ->
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) (wrap_evals cevals k) =
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) k) /\
          cfg_steps_to_ret sigma0 env0 (denote_code c None) sigma2 env2 tt)).
Proof.
  induction c as [| i1 | i1 i2 rest2 IH_tail IH_rest2] using list_2step_ind;
    intros params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0 cevals smap2 seen2
           Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
  - cbn [reify_code] in Hr; inversion Hr; subst cevals smap2 seen2.
    exists []; split; [intros _ _ [] | right; exists sigma0, env0].
    split; [exact Hwfd0 | split; [exact Hpe | split; [exact Henv0 |
      split; [intros fmap_later k _; reflexivity | apply CSR_Ret; reflexivity]]]].
  - cbn [reify_code] in Hr; destruct (reify_code_step true params src_pnames defs smap0 seen0 i1)
      as [[[opt_ev smap1] seen1] |] eqn:Hstep; [| discriminate].
    assert (Hrr : reify_code true params src_pnames defs smap1 seen1 [] = Some ([], smap1, seen1))
      by reflexivity.
    inversion Hr; subst cevals smap2 seen2; clear Hr.
    eapply eval_reified_code_single_tgt;
      [| exact Hnd | exact Hlp | exact Hls | exact Hla | exact Hvs | exact Hpu
       | exact Hpe | exact Hwfd0 | exact Hwfs0 | exact Henv0 | exact Hstep | exact Hrr | destruct opt_ev; reflexivity].
    intros allowed' sigma' fmap' smap' env' seen' cevals' smap2' seen2' _ Hpe' Hwfd' _ Henv' Hr'.
    cbn [reify_code] in Hr'; inversion Hr'; subst.
    exists []; split; [intros _ _ [] | right; exists sigma', env'].
    split; [exact Hwfd' | split; [exact Hpe' | split; [exact Henv' |
      split; [intros fmap_later k _; reflexivity | apply CSR_Ret; reflexivity]]]].
  - rewrite reify_code_unfold_pair in Hr.
    destruct (match_vec1_id_pair smap0 defs params i1 i2)
      as [[[[[tmp dst] w1] val_exp] kind] |] eqn:Hvec; cbv iota beta zeta in Hr.
    + destruct (reify_exp true params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w1))) val_exp)
        as [[[w ce] seen1] |] eqn:Hre; cbv iota beta zeta in Hr; [| discriminate].
      destruct (reify_code true params src_pnames defs (RM.add dst (w, ce) smap0) seen1 rest2)
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; cbv iota beta zeta in Hr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      destruct (match_vec1_id_pair_inv smap0 defs params i1 i2 tmp dst w1 val_exp kind Hvec)
        as (md1 & md2 & Hi1 & Htmp_def & Hdst_def & _ & Htmp_none & _).
      pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hre)) as Hww1.
      subst w1.
      assert (Hpu_val : forall idx dt_u,
        In (idx, dt_u) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) val_exp) ->
        nth_error arg_dtys idx = Some dt_u).
      { intros idx dt_u Hin.
        eapply Hpu; [left; rewrite Hi1; reflexivity |].
        cbn [instr_param_uses exp_param_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hin. }
      set (ext_vars :=
        allowed ++
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) val_exp)).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 true smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpu_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) val_exp) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | rewrite Hpnm; left; reflexivity]. }
      destruct (reify_exp_typing val_exp true params src_pnames defs ext_vars smap0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) w ce seen1 Hsmap_ext Hpu_ext Hre)
        as (_ & Hwt_ce & Hbw_ce & Hlf_ce & Hfv_ce & Hinc01 & Hfk_ce).
      pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen1 true smap0 Hinc01 Hsmap_ext) as Hsmap_ext1.
      pose proof (wf_smap_entries_add ext_vars defs seen1 true smap0 dst w ce Hsmap_ext1
                    Hdst_def Hwt_ce Hbw_ce Hlf_ce Hfv_ce Hfk_ce) as Hwfs1.
      destruct (reify_code_wf_smap rest2 true params src_pnames defs ext_vars
                  (RM.add dst (w, ce) smap0) seen1 cevals_r smap2 seen2 Hwfs1 Hrr)
        as (_ & Hinc12 & _).
      destruct (eval_reified_exp_tgt val_exp params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0
                  (Some (DTYPE_Base (DTYPE_I w))) w ce seen1 Hnd Hlp Hls Hla Hvs Hpu_val
                  Hpe Hwfd0 Hwfs0 Henv0 Hre)
        as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
      * exists added1; split.
        -- intros k z Hkz; destruct (Had1 k z Hkz) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0].
        -- left; intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
      * pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                      (build_param_env src_pnames vs) smap0 env0 Hwfs0
                      (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv0'.
        pose proof (env_matches_smap_add_absent defs (build_param_env src_pnames vs)
                      (oracle_of_fmap (added1 ++ fmap0)) smap0 env0
                      tmp (DVALUE_Array true [dv1]) Htmp_none Henv0') as Henv_tmp.
        set (env1 := RM.add dst dv1 (RM.add tmp (DVALUE_Array true [dv1]) env0)).
        pose proof (env_matches_smap_add defs (build_param_env src_pnames vs)
                      (oracle_of_fmap (added1 ++ fmap0)) smap0
                      (RM.add tmp (DVALUE_Array true [dv1]) env0)
                      dst w ce dv1 Henv_tmp Hdst_def Hev1 Hsc1) as Henv1.
        assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
          exists dv, nth_error vs idx = Some dv /\ RM.find r env1 = Some dv).
        { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
          exists dv; split; [exact Hv |].
          unfold env1; rewrite !RMF.F.add_neq_o;
            [exact Hfe | intros ->; exact (Hnin Htmp_def) | intros ->; exact (Hnin Hdst_def)]. }
        destruct (IH_rest2 params src_pnames defs ext_vars arg_dtys vs sigma1 (added1 ++ fmap0)
                    (RM.add dst (w, ce) smap0) env1 seen1 cevals_r smap2 seen2
                    Hnd Hlp Hls Hla Hvs
                    (fun iid' ins' md' idx d Hin_i => Hpu iid' ins' md' idx d (or_intror (or_intror Hin_i)))
                    Hpe1 Hwfd1 Hwfs1 Henv1 Hrr)
          as (added2 & Had2 & [Hev_ub2 | (sigma2 & env2 & Hwfd2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
        -- exists (added2 ++ added1).
           assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
           { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
             - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
             - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
           split; [exact Had12 | left; intros k].
           rewrite <- app_assoc.
           pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                         added2 (added1 ++ fmap0) seen1 Hlf_ce (Hfk_ce eq_refl)
                         (fun q z H => proj2 (Had2 q z H))) as Hev1'.
           cbn [wrap_evals eval_cfg_dag]; rewrite Hev1', Hev1; exact (Hev_ub2 k).
        -- exists (added2 ++ added1).
           assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
           { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
             - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
             - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
           split; [exact Had12 | right; exists sigma2, env2].
           split; [exact Hwfd2 | split; [exact Hpe2 | split; [rewrite <- app_assoc; exact Henv2 | split]]].
           ++ intros fmap_later k Hdisj_lat.
              assert (Hdisj_lat1 : forall key z, In (key, z) (fmap_later ++ added2) -> ~ In key seen1).
              { intros key z Hkz; apply in_app_iff in Hkz as [Hl | Ha2].
                - intros Hs1; exact (Hdisj_lat key z Hl (Hinc12 key Hs1)).
                - exact (proj2 (Had2 key z Ha2)). }
              replace (fmap_later ++ (added2 ++ added1) ++ fmap0)
                with ((fmap_later ++ added2) ++ (added1 ++ fmap0))
                by (rewrite !app_assoc; reflexivity).
              pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                            (fmap_later ++ added2) (added1 ++ fmap0) seen1 Hlf_ce (Hfk_ce eq_refl) Hdisj_lat1)
                as Hev_lat1.
              cbn [wrap_evals eval_cfg_dag]; rewrite Hev_lat1, Hev1.
              replace ((fmap_later ++ added2) ++ added1 ++ fmap0)
                with (fmap_later ++ (added2 ++ (added1 ++ fmap0)))
                by (rewrite !app_assoc; reflexivity).
              exact (Hev_k fmap_later k Hdisj_lat).
           ++ unfold denote_code; cbn [loop_monad].
              eapply cfg_steps_vec1_pair_bind;
                [exact Hvec | exact Hsc1 | exact Hst1 | exact Hst2].
    + destruct (reify_code_step true params src_pnames defs smap0 seen0 i1)
        as [[[opt_ev smap1] seen1] |] eqn:Hstep; cbv iota beta zeta in Hr; [| discriminate].
      destruct (reify_code true params src_pnames defs smap1 seen1 (i2 :: rest2))
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; cbv iota beta zeta in Hr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      eapply eval_reified_code_single_tgt;
        [| exact Hnd | exact Hlp | exact Hls | exact Hla | exact Hvs | exact Hpu
         | exact Hpe | exact Hwfd0 | exact Hwfs0 | exact Henv0 | exact Hstep | exact Hrr | reflexivity].
      intros allowed' sigma' fmap' smap' env' seen' cevals' smap2' seen2' Hpu' Hpe' Hwfd' Hwfs' Henv' Hr'.
      exact (IH_tail params src_pnames defs allowed' arg_dtys vs sigma' fmap' smap' env' seen'
               cevals' smap2' seen2' Hnd Hlp Hls Hla Hvs Hpu' Hpe' Hwfd' Hwfs' Henv' Hr').
Qed.

Lemma reify_exp_wt_lf :
  forall (o : exp dtyp) uf params src_pnames defs allowed smap seen0 top w ce seen1,
    wf_smap_entries allowed defs seen0 uf smap ->
    reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    wt_cert_expr [] ce = true /\ is_let_free_expr ce = true.
Proof.
  intros o uf params src_pnames defs allowed smap seen0 top w ce seen1 Hsmap Hr.
  set (ext_vars :=
    allowed ++
    List.flat_map (fun '(idx, dt) =>
      match dt, nth_error src_pnames idx with
      | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
      | _, _ => []
      end) (exp_param_uses params defs top o)).
  assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 uf smap).
  { intros r wr cer Hf.
    destruct (Hsmap r wr cer Hf) as (Hr_in & Hwt & Hbw & Hlf & Hfv & Hfk).
    repeat split; try assumption.
    intros u Hu; apply in_app_iff; left; exact (Hfv u Hu). }
  assert (Hpu_ext : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs top o) ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) ext_vars).
  { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
    exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | rewrite Hpnm; left; reflexivity]. }
  destruct (reify_exp_typing o uf params src_pnames defs ext_vars smap seen0 top w ce seen1
              Hsmap_ext Hpu_ext Hr)
    as (_ & Hwt & _ & Hlf & _).
  exact (conj Hwt Hlf).
Qed.

Lemma eval_closed_lf_ret_wf_param_env {Pa : Params} :
  forall (e : cert_expr) (penv : param_env Pa) (foracle : freeze_oracle) (dv : @dvalue Pa),
    is_let_free_expr e = true ->
    eval_closed_cert_expr penv foracle e = raise_ret dv ->
    wf_param_env_for (collect_free_vars [] e) penv.
Proof.
  unfold eval_closed_cert_expr.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv foracle dv Hlf Hev x wx Hx;
    cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in Hlf, Hev, Hx;
    try contradiction Hx; try discriminate Hlf.
  - destruct Hx as [Heq | []]; inversion Heq; subst x wx.
    destruct (penv nm) as [v |] eqn:Ep; [| discriminate Hev].
    exists v; split; [reflexivity |].
    destruct v as [db | |]; try discriminate Hev.
    destruct db as [| sz iv | | | | | |]; try discriminate Hev.
    + cbn [check_scalar_width] in Hev.
      destruct (Pos.eqb sz w) eqn:Esz; [| discriminate Hev].
      apply Pos.eqb_eq in Esz; subst sz; right; exists iv; reflexivity.
    + left; reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; try discriminate Hev.
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; try discriminate Hev.
    apply in_app_iff in Hx as [Hxl | Hxr];
      [exact (IHl penv foracle vl Hlfl El x wx Hxl)
      | exact (IHr penv foracle vr Hlfr Er x wx Hxr)].
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; try discriminate Hev.
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; try discriminate Hev.
    apply in_app_iff in Hx as [Hxl | Hxr];
      [exact (IHl penv foracle vl Hlfl El x wx Hxl)
      | exact (IHr penv foracle vr Hlfr Er x wx Hxr)].
  - destruct (eval_cert_expr penv [] foracle o) as [| | | vo] eqn:Eo; try discriminate Hev.
    exact (IHo penv foracle vo Hlf Eo x wx Hx).
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hlfc Hlft] & Hlff).
    destruct (eval_cert_expr penv [] foracle c) as [| | | vc] eqn:Ec; try discriminate Hev.
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv [] foracle t) as [| | | vt] eqn:Et; try discriminate Hev.
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv [] foracle f) as [| | | vf] eqn:Ef; try discriminate Hev.
    apply in_app_iff in Hx as [Hxc | Hxtf];
      [exact (IHc penv foracle vc Hlfc Ec x wx Hxc) |].
    apply in_app_iff in Hxtf as [Hxt | Hxf];
      [exact (IHt penv foracle vt Hlft Et x wx Hxt)
      | exact (IHf penv foracle vf Hlff Ef x wx Hxf)].
  - destruct (eval_cert_expr penv [] foracle o) as [| | | vo] eqn:Eo; try discriminate Hev.
    exact (IHo penv foracle vo Hlf Eo x wx Hx).
Qed.

