(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Freeze-Key Tracking, Parameter Envs & Exp Reification ([CertValidator.CertValExpReify])

    Purpose:
      Defines canonical register naming, freeze-key tracking and oracle
      agreement ([collect_freeze_keys], [oracle_of_fmap]), parameter environments
      ([build_param_env]), and bounded-DAG expression reification ([reify_exp]).

    Trust Contract & Fail-Closed Boundary:
      Fail-closed SSA expression reifier ([reify_exp_typing],
      [eval_reified_exp_src], [eval_reified_exp_tgt]); unsupported types, ops,
      or exhausted fuel return [None] and preserve exact [freeze]-key tracking.

    Assumptions:
      Depends on Stdlib, [Paco], [ITree], [ExtLib], [Vellvm], [Diag], and
      [CertFormatAst]/[CertFormatGates]/[AlgRulesEval]/[CfgDag]/[CertValOpenWorld].

    Section Outline:
      5. Bounded-DAG SSA Reification: 5.1 Naming & [ocfg_map]; 5.2 Freeze Keys;
      5.3 Parameter Environments & Frame Locals; 5.4 [reify_exp] & Soundness. *)

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
  CertFormatAst
  CertFormatGates
  AlgRulesEval
  CfgDag
  CertValOpenWorld.

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

(** ** 5. Bounded-DAG SSA Reification, [cert-v1] Checker & Soundness ([0 Admitted]) *)

(** *** 5.1 Canonical Register Naming, Distinctness & [ocfg_map] Membership *)

Definition show_Z_dec (z : Z) : string :=
  NilEmpty.string_of_int (Z.to_int z).

Definition cert_raw_id_bare (id : raw_id) : string :=
  match id with
  | Name s => s
  | Anon z => show_Z_dec z
  | Raw z => ("_RAW_" ++ show_Z_dec z)%string
  end.

Definition cert_reg_name (id : raw_id) : string :=
  ("%" ++ cert_raw_id_bare id)%string.

Lemma cert_reg_name_not_dollar : forall id,
  starts_with_dollar (cert_reg_name id) = false.
Proof.
  intros id; reflexivity.
Qed.

Fixpoint no_dup_strings (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: rx => negb (string_in_list x rx) && no_dup_strings rx
  end.

Lemma no_dup_strings_spec : forall xs,
  no_dup_strings xs = true <-> NoDup xs.
Proof.
  induction xs as [| x rx IH]; cbn.
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH.
    split.
    + intros [Hni Hnd]; constructor; [| exact Hnd].
      intros Hin; apply string_in_list_spec in Hin; congruence.
    + intros Hnd; inversion Hnd as [| ? ? Hni Hndr]; subst; split; [| exact Hndr].
      destruct (string_in_list x rx) eqn:E; [| reflexivity].
      apply string_in_list_spec in E; contradiction.
Qed.

Fixpoint no_dup_raw_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: rx => negb (raw_id_in_list x rx) && no_dup_raw_ids rx
  end.

Lemma no_dup_raw_ids_spec : forall xs,
  no_dup_raw_ids xs = true <-> NoDup xs.
Proof.
  induction xs as [| x rx IH]; cbn.
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH.
    split.
    + intros [Hni Hnd]; constructor; [| exact Hnd].
      intros Hin; apply raw_id_in_list_spec in Hin; congruence.
    + intros Hnd; inversion Hnd as [| ? ? Hni Hndr]; subst; split; [| exact Hndr].
      destruct (raw_id_in_list x rx) eqn:E; [| reflexivity].
      apply raw_id_in_list_spec in E; contradiction.
Qed.

Lemma ocfg_map_in {T : Set} :
  forall (bs : list (block T)) bid b,
    RM.find bid (ocfg_map bs) = Some b ->
    In b bs.
Proof.
  induction bs as [| b0 rest IH]; intros bid b H; cbn [ocfg_map fold_right] in H.
  - rewrite RMF.F.empty_o in H; discriminate.
  - destruct (RawIDOrd.eq_dec (blk_id b0) bid) as [Heq | Hneq].
    + rewrite RMF.F.add_eq_o in H by exact Heq; injection H as ->; left; reflexivity.
    + rewrite RMF.F.add_neq_o in H by exact Hneq; right; exact (IH bid b H).
Qed.

Fixpoint chain_draws {Pa : Params} (draws : list (dtyp * @dvalue Pa))
  (tail_s : @draw_strat Pa) {struct draws} : @draw_strat Pa :=
  match draws with
  | [] => tail_s
  | (dt0, v0) :: rest => prepend_draws [(dt0, v0)] (chain_draws rest tail_s)
  end.

Lemma chain_draws_app {Pa : Params} :
  forall (d1 d2 : list (dtyp * @dvalue Pa)) (tail_s : @draw_strat Pa),
    chain_draws (d1 ++ d2) tail_s = chain_draws d1 (chain_draws d2 tail_s).
Proof.
  induction d1 as [| [dt0 v0] rest IH]; intros d2 tail_s; cbn; [reflexivity |].
  rewrite IH; reflexivity.
Qed.

Lemma chain_draws_wf {Pa : Params} :
  forall (draws : list (dtyp * @dvalue Pa)) (tail_s : @draw_strat Pa),
    Forall (fun '(dt, v) => valid_draw_value dt v) draws ->
    wf_draw_strat tail_s ->
    wf_draw_strat (chain_draws draws tail_s).
Proof.
  intros draws tail_s Hfa Htail.
  induction Hfa as [| [dt0 v0] rest Hv0 _ IH]; cbn [chain_draws]; [exact Htail |].
  apply prepend_draws_wf; [constructor; [exact Hv0 | constructor] | exact IH].
Qed.


(** *** 5.2 Freeze-Key Tracking & Oracle Agreement on Let-Free Expressions *)

Definition freeze_key : Set := (positive * cert_expr)%type.

Definition freeze_key_eqb (k1 k2 : freeze_key) : bool :=
  Pos.eqb (fst k1) (fst k2) && cert_expr_eqb (snd k1) (snd k2).

Lemma freeze_key_eqb_refl : forall k, freeze_key_eqb k k = true.
Proof.
  intros [w e]; unfold freeze_key_eqb; cbn.
  rewrite Pos.eqb_refl, cert_expr_eqb_refl; reflexivity.
Qed.

Lemma freeze_key_eqb_eq : forall k1 k2,
  freeze_key_eqb k1 k2 = true <-> k1 = k2.
Proof.
  intros [w1 e1] [w2 e2]; unfold freeze_key_eqb; cbn.
  rewrite andb_true_iff, Pos.eqb_eq, cert_expr_eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Fixpoint freeze_key_in (k : freeze_key) (ks : list freeze_key) {struct ks} : bool :=
  match ks with
  | [] => false
  | x :: rx => freeze_key_eqb k x || freeze_key_in k rx
  end.

Lemma freeze_key_in_spec : forall k ks,
  freeze_key_in k ks = true <-> In k ks.
Proof.
  intros k ks; induction ks as [| x rx IH]; cbn; [split; [discriminate | contradiction] |].
  destruct (freeze_key_eqb k x) eqn:E.
  - apply freeze_key_eqb_eq in E; subst; split; [intros _; left; reflexivity | intros _; reflexivity].
  - rewrite IH; split; [intros H; right; exact H | intros [-> | H];
      [rewrite freeze_key_eqb_refl in E; discriminate | exact H]].
Qed.

Fixpoint collect_freeze_keys (e : cert_expr) : list freeze_key :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => []
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      collect_freeze_keys l ++ collect_freeze_keys r
  | CE_Cast _ _ _ _ o => collect_freeze_keys o
  | CE_Select _ c t f =>
      collect_freeze_keys c ++ collect_freeze_keys t ++ collect_freeze_keys f
  | CE_Freeze w o => (w, o) :: collect_freeze_keys o
  end.

Fixpoint oracle_of_fmap (fmap : list (freeze_key * Z)) : freeze_oracle :=
  fun w e =>
    match fmap with
    | [] => 0%Z
    | (k, z) :: rest =>
        if freeze_key_eqb (w, e) k then z else oracle_of_fmap rest w e
    end.

Lemma oracle_of_fmap_prepend_agree :
  forall added fmap seen,
    (forall k z, In (k, z) added -> ~ In k seen) ->
    forall w e,
      In (w, e) seen ->
      oracle_of_fmap (added ++ fmap) w e = oracle_of_fmap fmap w e.
Proof.
  induction added as [| [k0 z0] rest IH]; intros fmap seen Hdisj w e Hin; cbn; [reflexivity |].
  destruct (freeze_key_eqb (w, e) k0) eqn:Eqk.
  - apply freeze_key_eqb_eq in Eqk; subst k0.
    exfalso; exact (Hdisj (w, e) z0 (or_introl eq_refl) Hin).
  - apply (IH fmap seen); [intros k z H; exact (Hdisj k z (or_intror H)) | exact Hin].
Qed.

Lemma expand_lets_let_free : forall e,
  is_let_free_expr e = true ->
  expand_lets_with [] e = e.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf; cbn in Hlf |- *; try reflexivity; try discriminate.
  - apply andb_true_iff in Hlf as [Hl Hr]; rewrite (IHl Hl), (IHr Hr); reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr]; rewrite (IHl Hl), (IHr Hr); reflexivity.
  - rewrite (IHo Hlf); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hc Ht] & Hf).
    rewrite (IHc Hc), (IHt Ht), (IHf Hf); reflexivity.
  - rewrite (IHo Hlf); reflexivity.
Qed.

Lemma eval_let_free_oracle_agree {Pa : Params} :
  forall (e : cert_expr) (penv : param_env Pa) (fo1 fo2 : freeze_oracle),
    is_let_free_expr e = true ->
    (forall w o, In (w, o) (collect_freeze_keys e) -> fo1 w o = fo2 w o) ->
    eval_cert_expr penv [] fo1 e = eval_cert_expr penv [] fo2 e.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv fo1 fo2 Hlf Hag; cbn in Hlf |- *; try reflexivity; try discriminate.
  - apply andb_true_iff in Hlf as [Hl Hr].
    rewrite (IHl penv fo1 fo2 Hl (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr penv fo1 fo2 Hr (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr].
    rewrite (IHl penv fo1 fo2 Hl (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr penv fo1 fo2 Hr (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - rewrite (IHo penv fo1 fo2 Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hc Ht] & Hf).
    rewrite (IHc penv fo1 fo2 Hc (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHt penv fo1 fo2 Ht (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl H)))))).
    rewrite (IHf penv fo1 fo2 Hf (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror H)))))).
    reflexivity.
  - rewrite (IHo penv fo1 fo2 Hlf (fun kw ko H => Hag kw ko (or_intror H))).
    cbn [let_val_exprs List.map]; rewrite (expand_lets_let_free o Hlf).
    rewrite (Hag w o (or_introl eq_refl)); reflexivity.
Qed.

(** *** 5.3 Parameter Environments & Initial Frame Locals *)

Fixpoint build_param_env {Pa : Params}
  (pnames : list string) (vs : list (@dvalue Pa)) {struct pnames} : param_env Pa :=
  fun nm =>
    match pnames, vs with
    | p :: pr, v :: vr =>
        if String.eqb p nm then Some v else build_param_env pr vr nm
    | _, _ => None
    end.

Lemma build_param_env_nth {Pa : Params} :
  forall (pnames : list string) (vs : list (@dvalue Pa)) (idx : nat) (nm : string),
    NoDup pnames ->
    List.length pnames = List.length vs ->
    nth_error pnames idx = Some nm ->
    exists dv,
      nth_error vs idx = Some dv /\
      build_param_env pnames vs nm = Some dv.
Proof.
  induction pnames as [| p pr IH]; intros [| v vr] idx nm Hnd Hlen Hnth;
    try discriminate Hlen; [destruct idx; discriminate Hnth |].
  inversion Hnd as [| ? ? Hni Hndr]; subst.
  destruct idx as [| idx']; cbn in Hnth |- *.
  - inversion Hnth; subst p; rewrite String.eqb_refl; exists v; auto.
  - injection Hlen as Hlen'.
    destruct (IH vr idx' nm Hndr Hlen' Hnth) as [dv [Hv Hb]].
    destruct (String.eqb p nm) eqn:Ep.
    + apply String.eqb_eq in Ep; subst p.
      exfalso; apply Hni; eapply nth_error_In; exact Hnth.
    + exists dv; split; [exact Hv | exact Hb].
Qed.

Lemma init_cfg_locals_nth {Pa : Params} :
  forall (params : list raw_id) (vs : list (@dvalue Pa)) (idx : nat) (r : raw_id),
    NoDup params ->
    List.length params = List.length vs ->
    nth_error params idx = Some r ->
    exists dv,
      nth_error vs idx = Some dv /\
      RM.find r (init_cfg_locals params vs) = Some dv.
Proof.
  induction params as [| p pr IH]; intros [| v vr] idx r Hnd Hlen Hnth;
    try discriminate Hlen; [destruct idx; discriminate Hnth |].
  inversion Hnd as [| ? ? Hni Hndr]; subst.
  destruct idx as [| idx']; cbn [nth_error init_cfg_locals] in Hnth |- *.
  - inversion Hnth; subst p.
    exists v; split; [reflexivity | apply RMF.F.add_eq_o; reflexivity].
  - injection Hlen as Hlen'.
    destruct (IH vr idx' r Hndr Hlen' Hnth) as [dv [Hv Hf]].
    assert (Hneq : p <> r)
      by (intros ->; apply Hni; eapply nth_error_In; exact Hnth).
    exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o by exact Hneq; exact Hf].
Qed.

Lemma Forall2_nth_error_l {A B : Type} (R : A -> B -> Prop) :
  forall (xs : list A) (ys : list B),
    Forall2 R xs ys ->
    forall idx x y,
      nth_error xs idx = Some x ->
      nth_error ys idx = Some y ->
      R x y.
Proof.
  intros xs ys Hfa; induction Hfa as [| x0 y0 rx ry Hr _ IH];
    intros [| idx'] x y Hx Hy; cbn in Hx, Hy; try discriminate.
  - inversion Hx; inversion Hy; subst; exact Hr.
  - exact (IH idx' x y Hx Hy).
Qed.

Lemma vars_subset_b_wf_param {Pa : Params} :
  forall vs allowed (penv : param_env Pa),
    vars_subset_b vs allowed = true ->
    wf_param_env_for allowed penv ->
    wf_param_env_for vs penv.
Proof.
  intros vs allowed penv Hsub Hwf nm w Hin.
  unfold vars_subset_b in Hsub; rewrite forallb_forall in Hsub.
  pose proof (Hsub (nm, w) Hin) as Hin'.
  apply var_pair_in_spec in Hin'; exact (Hwf nm w Hin').
Qed.

Definition used_src_param_vars (src_cfg : CFG.cfg dtyp) : list (string * positive) :=
  let pnames := List.map cert_reg_name (args src_cfg) in
  List.flat_map (fun '(idx, dt) =>
    match dt, nth_error pnames idx with
    | DTYPE_Base (DTYPE_I w), Some nm => [(nm, w)]
    | _, _ => []
    end) (param_idx_uses_cfg src_cfg).

Lemma used_src_param_vars_wf {Pa : Params} :
  forall (src_cfg : CFG.cfg dtyp) (arg_dtys : list dtyp) (vs : list (@dvalue Pa)),
    NoDup (List.map cert_reg_name (args src_cfg)) ->
    List.length arg_dtys = List.length (args src_cfg) ->
    cfg_param_dtyp_compatible src_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    wf_param_env_for (used_src_param_vars src_cfg)
      (build_param_env (List.map cert_reg_name (args src_cfg)) vs).
Proof.
  intros src_cfg arg_dtys vs Hnd Hlen_dt Hcomp Hvs nm w Hin.
  unfold used_src_param_vars in Hin.
  apply in_flat_map in Hin as [[idx dt] [Hin_use Hin_here]].
  destruct dt as [tb | |]; try contradiction.
  destruct tb as [w' | | | | | | | | | | ]; try contradiction.
  destruct (nth_error (List.map cert_reg_name (args src_cfg)) idx) as [nm' |] eqn:Hnth_nm;
    [| contradiction].
  destruct Hin_here as [Heq | []]; inversion Heq; subst w' nm'.
  unfold cfg_param_dtyp_compatible in Hcomp; rewrite forallb_forall in Hcomp.
  pose proof (Hcomp (idx, DTYPE_Base (DTYPE_I w)) Hin_use) as Hdt_idx.
  cbn zeta iota in Hdt_idx.
  destruct (nth_error arg_dtys idx) as [dt_arg |] eqn:Hnth_dt; [| discriminate Hdt_idx].
  apply dtyp_eqb_dec_eq in Hdt_idx; subst dt_arg.
  assert (Hlen_vs : List.length vs = List.length arg_dtys) by (exact (Forall2_length Hvs)).
  assert (Hlen_pn : List.length (List.map cert_reg_name (args src_cfg)) = List.length vs)
    by (rewrite List.length_map; lia).
  destruct (build_param_env_nth (List.map cert_reg_name (args src_cfg)) vs idx nm Hnd Hlen_pn Hnth_nm)
    as [dv [Hnth_v Hpenv]].
  pose proof (Forall2_nth_error_l dvalue_has_dtyp vs arg_dtys Hvs idx dv (DTYPE_Base (DTYPE_I w)) Hnth_v Hnth_dt)
    as Hty.
  apply dvalue_has_dtyp_i_iff_wf_scalar in Hty.
  exists dv; split; [exact Hpenv | exact Hty].
Qed.

(** *** 5.4 Bounded-DAG SSA Expression Reifier & Operational Soundness *)

Lemma scalar_exp_ind (P : exp dtyp -> Prop)
  (HBin : forall iop dt e1 e2, P e1 -> P e2 -> P (OP_IBinop iop dt e1 e2))
  (HCmp : forall ss cmp dt e1 e2, P e1 -> P e2 -> P (OP_ICmp ss cmp dt e1 e2))
  (HConv : forall ct dtf e1 dtt, P e1 -> P (OP_Conversion ct dtf e1 dtt))
  (HSel : forall fm dtc ec dt1 e1 dt2 e2,
            P ec -> P e1 -> P e2 -> P (OP_Select fm (dtc, ec) (dt1, e1) (dt2, e2)))
  (HFrz : forall dt e1, P e1 -> P (OP_Freeze (dt, e1)))
  (HOther : forall o,
    match o with
    | OP_IBinop _ _ _ _ | OP_ICmp _ _ _ _ _ | OP_Conversion _ _ _ _
    | OP_Select _ _ _ _ | OP_Freeze _ => True
    | _ => P o
    end) :
  forall o : exp dtyp, P o.
Proof.
  fix IH 1; intros o; pose proof (HOther o) as Ho.
  destruct o; try exact Ho.
  - apply HBin; apply IH.
  - apply HCmp; apply IH.
  - apply HConv; apply IH.
  - match goal with |- P (OP_Select _ ?c ?x ?y) => destruct c, x, y end;
      apply HSel; apply IH.
  - match goal with |- P (OP_Freeze ?x) => destruct x end;
      apply HFrz; apply IH.
Qed.

Definition reify_int_const (w : positive) (z : Z) : N :=
  Z.to_N (Z.land z (Z.ones (Z.pos w))).

Lemma repr_reify_int_const : forall (w : positive) (z : Z),
  @Integers.repr w (Z.of_N (reify_int_const w z)) = @Integers.repr w z.
Proof.
  intros w z; unfold reify_int_const.
  assert (Hones : (0 <= Z.ones (Z.pos w))%Z).
  { rewrite Z.ones_equiv;
      assert (Hp : (0 < 2 ^ Z.pos w)%Z) by (apply Z.pow_pos_nonneg; lia); lia. }
  assert (Hnn : (0 <= Z.land z (Z.ones (Z.pos w)))%Z)
    by (apply Z.land_nonneg; right; exact Hones).
  rewrite (Z2N.id _ Hnn).
  apply @Integers.same_bits_eq; intros i Hi.
  rewrite !@Integers.testbit_repr by exact Hi.
  unfold Integers.zwordsize in Hi.
  rewrite Z.land_spec, (Z.ones_spec_low (Z.pos w) i Hi), Bool.andb_true_r.
  reflexivity.
Qed.

Definition check_opt_int_width (top : option dtyp) (w : positive) : bool :=
  match top with
  | None => true
  | Some (DTYPE_Base (DTYPE_I w')) => Pos.eqb w w'
  | Some _ => false
  end.

Lemma check_opt_int_width_some_inv : forall w' w,
  check_opt_int_width (Some (DTYPE_Base (DTYPE_I w'))) w = true -> w = w'.
Proof.
  intros w' w H; cbn in H; apply Pos.eqb_eq in H; exact H.
Qed.

Fixpoint reify_exp
  (unique_freezes : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (smap : rmap (positive * cert_expr))
  (seen : list freeze_key)
  (top : option dtyp)
  (o : exp dtyp)
  {struct o} : option (positive * cert_expr * list freeze_key) :=
  match o with
  | EXP_Ident (ID_Local r) =>
      match RM.find r smap with
      | Some (w, ce) =>
          if check_opt_int_width top w then Some (w, ce, seen) else None
      | None =>
          if raw_id_in_list r defs then None
          else
            match top, find_raw_id_index r params with
            | Some (DTYPE_Base (DTYPE_I w)), Some idx =>
                match nth_error src_pnames idx with
                | Some pnm =>
                    if starts_with_dollar pnm then None
                    else Some (w, CE_Var pnm w, seen)
                | None => None
                end
            | _, _ => None
            end
      end
  | EXP_Integer x =>
      match top with
      | Some (DTYPE_Base (DTYPE_I w)) =>
          Some (w, CE_BvConst w (reify_int_const w (denote_int_syntax x)), seen)
      | _ => None
      end
  | EXP_Bool b =>
      if check_opt_int_width top 1%positive
      then Some (1%positive, CE_BvConst 1%positive (if b then 1%N else 0%N), seen)
      else None
  | EXP_Undef | EXP_Poison =>
      match top with
      | Some (DTYPE_Base (DTYPE_I w)) => Some (w, CE_Poison w, seen)
      | _ => None
      end
  | OP_IBinop iop (DTYPE_Base (DTYPE_I w)) e1 e2 =>
      if check_opt_int_width top w then
        match reify_exp unique_freezes params src_pnames defs smap seen
                (Some (DTYPE_Base (DTYPE_I w))) e1 with
        | Some (_, ce1, seen1) =>
            match reify_exp unique_freezes params src_pnames defs smap seen1
                    (Some (DTYPE_Base (DTYPE_I w))) e2 with
            | Some (_, ce2, seen2) =>
                let '(cop, cfl) := ibinop_to_cert iop in
                Some (w, CE_BinOp cop w cfl ce1 ce2, seen2)
            | None => None
            end
        | None => None
        end
      else None
  | OP_ICmp ss cmp (DTYPE_Base (DTYPE_I w)) e1 e2 =>
      if check_opt_int_width top 1%positive then
        match reify_exp unique_freezes params src_pnames defs smap seen
                (Some (DTYPE_Base (DTYPE_I w))) e1 with
        | Some (_, ce1, seen1) =>
            match reify_exp unique_freezes params src_pnames defs smap seen1
                    (Some (DTYPE_Base (DTYPE_I w))) e2 with
            | Some (_, ce2, seen2) =>
                Some (1%positive, CE_ICmp (icmp_to_cert cmp) ss w ce1 ce2, seen2)
            | None => None
            end
        | None => None
        end
      else None
  | OP_Conversion (CONV_Pure pc) (DTYPE_Base (DTYPE_I fw)) e1 (DTYPE_Base (DTYPE_I tw)) =>
      if check_opt_int_width top tw then
        match pure_conv_to_cert pc with
        | Some (ck, cfl) =>
            let w_ok :=
              match ck with
              | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
              | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
              | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
              end in
            if w_ok then
              match reify_exp unique_freezes params src_pnames defs smap seen
                      (Some (DTYPE_Base (DTYPE_I fw))) e1 with
              | Some (_, ce1, seen1) =>
                  Some (tw, CE_Cast ck fw tw cfl ce1, seen1)
              | None => None
              end
            else None
        | None => None
        end
      else None
  | OP_Select _ (DTYPE_Base (DTYPE_I 1%positive), ec)
                (DTYPE_Base (DTYPE_I w1), e1)
                (DTYPE_Base (DTYPE_I w2), e2) =>
      if Pos.eqb w1 w2 && check_opt_int_width top w1 then
        match reify_exp unique_freezes params src_pnames defs smap seen
                (Some (DTYPE_Base (DTYPE_I 1%positive))) ec with
        | Some (_, cec, seen1) =>
            match reify_exp unique_freezes params src_pnames defs smap seen1
                    (Some (DTYPE_Base (DTYPE_I w1))) e1 with
            | Some (_, ce1, seen2) =>
                match reify_exp unique_freezes params src_pnames defs smap seen2
                        (Some (DTYPE_Base (DTYPE_I w1))) e2 with
                | Some (_, ce2, seen3) =>
                    Some (w1, CE_Select w1 cec ce1 ce2, seen3)
                | None => None
                end
            | None => None
            end
        | None => None
        end
      else None
  | OP_Freeze (DTYPE_Base (DTYPE_I w), e1) =>
      if check_opt_int_width top w then
        match reify_exp unique_freezes params src_pnames defs smap seen
                (Some (DTYPE_Base (DTYPE_I w))) e1 with
        | Some (_, ce1, seen1) =>
            if unique_freezes then
              if freeze_key_in (w, ce1) seen1 then None
              else Some (w, CE_Freeze w ce1, (w, ce1) :: seen1)
            else Some (w, CE_Freeze w ce1, seen1)
        | None => None
        end
      else None
  | _ => None
  end.

Definition wf_smap_entries
  (allowed_vars : list (string * positive))
  (defs : list raw_id)
  (seen : list freeze_key)
  (unique_freezes : bool)
  (smap : rmap (positive * cert_expr)) : Prop :=
  forall r w ce,
    RM.find r smap = Some (w, ce) ->
    In r defs /\
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    incl (collect_free_vars [] ce) allowed_vars /\
    (unique_freezes = true -> incl (collect_freeze_keys ce) seen).

Lemma wf_smap_entries_seen_mono :
  forall allowed defs seen1 seen2 uf smap,
    incl seen1 seen2 ->
    wf_smap_entries allowed defs seen1 uf smap ->
    wf_smap_entries allowed defs seen2 uf smap.
Proof.
  intros allowed defs seen1 seen2 uf smap Hinc Hsmap r w ce Hf.
  destruct (Hsmap r w ce Hf) as (Hr & Hwt & Hbw & Hlf & Hfv & Hfk).
  repeat split; try assumption.
  intros Huf x Hx; exact (Hinc x (Hfk Huf x Hx)).
Qed.

Lemma reify_exp_typing :
  forall (o : exp dtyp) uf params src_pnames defs allowed smap seen0 top w ce seen1,
    wf_smap_entries allowed defs seen0 uf smap ->
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs top o) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    check_opt_int_width top w = true /\
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    incl (collect_free_vars [] ce) allowed /\
    incl seen0 seen1 /\
    (uf = true -> incl (collect_freeze_keys ce) seen1).
Proof.
  apply (scalar_exp_ind (fun o =>
    forall uf params src_pnames defs allowed smap seen0 top w ce seen1,
      wf_smap_entries allowed defs seen0 uf smap ->
      (forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs top o) ->
        nth_error src_pnames idx = Some pnm ->
        In (pnm, w0) allowed) ->
      reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
      check_opt_int_width top w = true /\
      wt_cert_expr [] ce = true /\
      cert_expr_bit_width ce = w /\
      is_let_free_expr ce = true /\
      incl (collect_free_vars [] ce) allowed /\
      incl seen0 seen1 /\
      (uf = true -> incl (collect_freeze_keys ce) seen1))).
  - (* OP_IBinop *)
    intros iop dt e1 e2 IH1 IH2 uf params src_pnames defs allowed smap seen0 top w ce seen2 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce seen2'; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [_ Hfl].
    destruct (IH1 uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I w))) w1 ce1 seen1
                Hsmap
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hr1)
      as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc01 & Hfk1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap Hinc01 Hsmap) as Hsmap1.
    destruct (IH2 uf params src_pnames defs allowed smap seen1 (Some (DTYPE_Base (DTYPE_I w))) w2 ce2 seen2
                Hsmap1
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                Hr2)
      as (Hcw2 & Hwt2 & Hbw2 & Hlf2 & Hfv2 & Hinc12 & Hfk2).
    apply check_opt_int_width_some_inv in Hcw2; subst w2.
    repeat split; try assumption.
    + cbn; rewrite Hfl, Hwt1, Hwt2, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; assumption.
    + intros x Hx; exact (Hinc12 x (Hinc01 x Hx)).
    + intros Huf; cbn; apply incl_app;
        [intros x Hx; exact (Hinc12 x (Hfk1 Huf x Hx)) | exact (Hfk2 Huf)].
  - (* OP_ICmp *)
    intros ss cmp dt e1 e2 IH1 IH2 uf params src_pnames defs allowed smap seen0 top w ce seen2 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce seen2'; clear Hr.
    destruct (IH1 uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) w1 ce1 seen1
                Hsmap
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hr1)
      as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc01 & Hfk1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap Hinc01 Hsmap) as Hsmap1.
    destruct (IH2 uf params src_pnames defs allowed smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) w2 ce2 seen2
                Hsmap1
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                Hr2)
      as (Hcw2 & Hwt2 & Hbw2 & Hlf2 & Hfv2 & Hinc12 & Hfk2).
    apply check_opt_int_width_some_inv in Hcw2; subst w2.
    repeat split; try assumption.
    + cbn; rewrite Hwt1, Hwt2, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; assumption.
    + intros x Hx; exact (Hinc12 x (Hinc01 x Hx)).
    + intros Huf; cbn; apply incl_app;
        [intros x Hx; exact (Hinc12 x (Hfk1 Huf x Hx)) | exact (Hfk2 Huf)].
  - (* OP_Conversion *)
    intros ct dtf e1 dtt IH1 uf params src_pnames defs allowed smap seen0 top w ce seen1 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct ct as [| pc | ic]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |] eqn:Hpc; [| discriminate].
    set (w_ok :=
      match ck with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
      end) in *.
    destruct w_ok eqn:Hwok; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) e1)
      as [[[w1 ce1] seen1'] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce seen1'; clear Hr.
    destruct (IH1 uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) w1 ce1 seen1
                Hsmap Hpu Hr1)
      as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc01 & Hfk1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    repeat split; try assumption.
    + cbn; unfold w_ok in Hwok; rewrite Hwok, Hwt1, Hbw1, Pos.eqb_refl; reflexivity.
  - (* OP_Select *)
    intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 uf params src_pnames defs allowed smap seen0 top w ce seen3 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[[wc' cec] seen1] |] eqn:Hrc; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I w1))) e1)
      as [[[wa ce1] seen2] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen2 (Some (DTYPE_Base (DTYPE_I w1))) e2)
      as [[[wb ce2] seen3'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce seen3'; clear Hr.
    destruct (IHc uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) wc' cec seen1
                Hsmap
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hrc)
      as (Hcwc & Hwtc & Hbwc & Hlfc & Hfvc & Hinc01 & Hfkc).
    apply check_opt_int_width_some_inv in Hcwc; subst wc'.
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap Hinc01 Hsmap) as Hsmap1.
    destruct (IH1 uf params src_pnames defs allowed smap seen1 (Some (DTYPE_Base (DTYPE_I w))) wa ce1 seen2
                Hsmap1
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hin)))))
                Hr1)
      as (Hcwa & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc12 & Hfk1).
    apply check_opt_int_width_some_inv in Hcwa; subst wa.
    pose proof (wf_smap_entries_seen_mono allowed defs seen1 seen2 uf smap Hinc12 Hsmap1) as Hsmap2.
    destruct (IH2 uf params src_pnames defs allowed smap seen2 (Some (DTYPE_Base (DTYPE_I w))) wb ce2 seen3
                Hsmap2
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror Hin)))))
                Hr2)
      as (Hcwb & Hwt2 & Hbw2 & Hlf2 & Hfv2 & Hinc23 & Hfk2).
    apply check_opt_int_width_some_inv in Hcwb; subst wb.
    repeat split; try assumption.
    + cbn; rewrite Hwtc, Hwt1, Hwt2, Hbwc, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlfc, Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; [exact Hfvc | apply incl_app; assumption].
    + intros x Hx; exact (Hinc23 x (Hinc12 x (Hinc01 x Hx))).
    + intros Huf; cbn; apply incl_app; [| apply incl_app].
      * intros x Hx; exact (Hinc23 x (Hinc12 x (Hfkc Huf x Hx))).
      * intros x Hx; exact (Hinc23 x (Hfk1 Huf x Hx)).
      * exact (Hfk2 Huf).
  - (* OP_Freeze *)
    intros dt e1 IH1 uf params src_pnames defs allowed smap seen0 top w ce seen1 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; try discriminate; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen_mid] |] eqn:Hr1; [| discriminate].
    destruct (IH1 uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) w1 ce1 seen_mid
                Hsmap Hpu Hr1)
      as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc0m & Hfk1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    destruct uf.
    + destruct (freeze_key_in (wb, ce1) seen_mid); [discriminate |].
      inversion Hr; subst w ce seen1; clear Hr.
      repeat split; try assumption.
      * cbn; rewrite Hwt1, Hbw1, Pos.eqb_refl; reflexivity.
      * intros x Hx; right; exact (Hinc0m x Hx).
      * intros _; cbn; intros x [<- | Hx];
          [left; reflexivity | right; exact (Hfk1 eq_refl x Hx)].
    + inversion Hr; subst w ce seen1; clear Hr.
      repeat split; try assumption.
      * cbn; rewrite Hwt1, Hbw1, Pos.eqb_refl; reflexivity.
      * intros Huf; discriminate Huf.
  - (* Non-recursive base cases *)
    intros o; destruct o; try exact I;
      intros uf params src_pnames defs allowed smap seen0 top w ce seen1 Hsmap Hpu Hr;
      cbn [reify_exp] in Hr; try discriminate.
    + (* EXP_Ident *)
      destruct id as [| r]; [discriminate |].
      destruct (RM.find r smap) as [[wr cer] |] eqn:Hfind.
      * destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
        inversion Hr; subst wr ce seen1; clear Hr.
        destruct (Hsmap r w cer Hfind) as (_ & Hwt & Hbw & Hlf & Hfv & Hfk).
        repeat split; try assumption; intros x Hx; exact Hx.
      * destruct (raw_id_in_list r defs) eqn:Hrd; [discriminate |].
        destruct top as [dt |]; [| discriminate].
        destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
        destruct (find_raw_id_index r params) as [idx |] eqn:Hidx; [| discriminate].
        destruct (nth_error src_pnames idx) as [pnm |] eqn:Hpnm; [| discriminate].
        destruct (starts_with_dollar pnm) eqn:Hdl; [discriminate |].
        inversion Hr; subst wt ce seen1; clear Hr.
        repeat split; try reflexivity.
        -- cbn; apply Pos.eqb_refl.
        -- cbn; rewrite Hdl; reflexivity.
        -- cbn; intros u [<- | []].
           apply (Hpu idx w pnm); [| exact Hpnm].
           cbn [exp_param_uses]; rewrite Hrd, Hidx; left; reflexivity.
        -- intros x Hx; exact Hx.
        -- intros _ x [].
    + (* EXP_Integer *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      repeat split; try reflexivity.
      * cbn; apply Pos.eqb_refl.
      * intros u [].
      * intros u Hu; exact Hu.
      * intros _ u [].
    + (* EXP_Bool *)
      destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce seen1; clear Hr.
      repeat split; try assumption; try reflexivity;
        [intros u [] | intros u Hu; exact Hu | intros _ u []].
    + (* EXP_Undef *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      repeat split; try reflexivity;
        [cbn; apply Pos.eqb_refl | intros u [] | intros u Hu; exact Hu | intros _ u []].
    + (* EXP_Poison *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      repeat split; try reflexivity;
        [cbn; apply Pos.eqb_refl | intros u [] | intros u Hu; exact Hu | intros _ u []].
Qed.

Lemma wf_smap_entries_false_seen :
  forall allowed defs seen0 seen1 smap,
    wf_smap_entries allowed defs seen0 false smap ->
    wf_smap_entries allowed defs seen1 false smap.
Proof.
  intros allowed defs seen0 seen1 smap Hsmap r w ce Hf.
  destruct (Hsmap r w ce Hf) as (Hr & Hwt & Hbw & Hlf & Hfv & _).
  repeat split; try assumption; intros Huf; discriminate Huf.
Qed.

Lemma reify_exp_top_width :
  forall uf params src_pnames defs smap seen0 top o w ce seen1,
    reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    check_opt_int_width top w = true.
Proof.
  intros uf params src_pnames defs smap seen0 top o w ce seen1 Hr.
  destruct o; cbn [reify_exp] in Hr; try discriminate.
  - destruct id as [| r]; [discriminate |].
    destruct (RM.find r smap) as [[wr cer] |].
    + destruct (check_opt_int_width top wr) eqn:E; [inversion Hr; subst; exact E | discriminate].
    + destruct (raw_id_in_list r defs); [discriminate |].
      destruct top as [[tb | |] |]; try discriminate; destruct tb; try discriminate.
      destruct (find_raw_id_index r params); [| discriminate].
      destruct (nth_error src_pnames n); [| discriminate].
      destruct (starts_with_dollar s); [discriminate |].
      inversion Hr; subst; cbn; apply Pos.eqb_refl.
  - destruct top as [[tb | |] |]; try discriminate; destruct tb; try discriminate.
    inversion Hr; subst; cbn; apply Pos.eqb_refl.
  - destruct (check_opt_int_width top 1%positive) eqn:E; [inversion Hr; subst; exact E | discriminate].
  - destruct top as [[tb | |] |]; try discriminate; destruct tb; try discriminate.
    inversion Hr; subst; cbn; apply Pos.eqb_refl.
  - destruct top as [[tb | |] |]; try discriminate; destruct tb; try discriminate.
    inversion Hr; subst; cbn; apply Pos.eqb_refl.
  - destruct t as [[wb | | | | | | | | | |] | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:E; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) o1)
      as [[[w1 ce1] sn1] |]; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap sn1 (Some (DTYPE_Base (DTYPE_I wb))) o2)
      as [[[w2 ce2] sn2] |]; [| discriminate].
    destruct (ibinop_to_cert iop); inversion Hr; subst; exact E.
  - destruct t as [[wb | | | | | | | | | |] | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:E; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) o1)
      as [[[w1 ce1] sn1] |]; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap sn1 (Some (DTYPE_Base (DTYPE_I wb))) o2)
      as [[[w2 ce2] sn2] |]; [| discriminate].
    inversion Hr; subst; exact E.
  - destruct conv as [| pc | ic]; try discriminate.
    destruct t_from as [[fw | | | | | | | | | |] | |]; try discriminate.
    destruct t_to as [[tw | | | | | | | | | |] | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:E; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |]; [| discriminate].
    destruct (match ck with CCK_ZExt => _ | CCK_SExt => _ | CCK_Trunc => _ end); [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) o)
      as [[[w1 ce1] sn1] |]; [| discriminate].
    inversion Hr; subst; exact E.
  - destruct cnd as [dtc ec], v1 as [dt1 e1], v2 as [dt2 e2].
    destruct dtc as [[[| | ] | | | | | | | | | |] | |]; try discriminate.
    destruct dt1 as [[w1 | | | | | | | | | |] | |]; try discriminate.
    destruct dt2 as [[w2 | | | | | | | | | |] | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:E; [| discriminate].
    apply andb_true_iff in E as [_ E].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[[wc cec] sn1] |]; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap sn1 (Some (DTYPE_Base (DTYPE_I w1))) e1)
      as [[[wa ce1] sn2] |]; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap sn2 (Some (DTYPE_Base (DTYPE_I w1))) e2)
      as [[[wb ce2] sn3] |]; [| discriminate].
    inversion Hr; subst; exact E.
  - destruct v as [dt e1].
    destruct dt as [[wb | | | | | | | | | |] | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:E; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen_m] |]; [| discriminate].
    destruct uf;
      [destruct (freeze_key_in (wb, ce1) seen_m); [discriminate | inversion Hr; subst; exact E]
      | inversion Hr; subst; exact E].
Qed.

Lemma reify_exp_freeze_props :
  forall (o : exp dtyp) uf params src_pnames defs allowed smap seen0 top w ce seen1,
    wf_smap_entries allowed defs seen0 uf smap ->
    reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    is_let_free_expr ce = true /\
    incl seen0 seen1 /\
    (uf = true -> incl (collect_freeze_keys ce) seen1).
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
    as (_ & _ & _ & Hlf & _ & Hinc & Hfk).
  exact (conj Hlf (conj Hinc Hfk)).
Qed.

Lemma eval_let_free_prepend_fmap {Pa : Params} :
  forall (ce : cert_expr) (penv : param_env Pa) added fmap seen,
    is_let_free_expr ce = true ->
    incl (collect_freeze_keys ce) seen ->
    (forall k z, In (k, z) added -> ~ In k seen) ->
    eval_closed_cert_expr penv (oracle_of_fmap (added ++ fmap)) ce =
    eval_closed_cert_expr penv (oracle_of_fmap fmap) ce.
Proof.
  intros ce penv added fmap seen Hlf Hfk Hdisj.
  unfold eval_closed_cert_expr.
  apply eval_let_free_oracle_agree; [exact Hlf |].
  intros kw ko Hin.
  exact (oracle_of_fmap_prepend_agree added fmap seen Hdisj kw ko (Hfk (kw, ko) Hin)).
Qed.

Definition env_matches_smap {Pa : Params}
  (defs : list raw_id)
  (penv : param_env Pa)
  (foracle : freeze_oracle)
  (smap : rmap (positive * cert_expr))
  (env : rmap (@dvalue Pa)) : Prop :=
  forall r w ce,
    RM.find r smap = Some (w, ce) ->
    In r defs /\
    exists dv,
      RM.find r env = Some dv /\
      eval_closed_cert_expr penv foracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv.

Lemma env_matches_smap_oracle_prepend {Pa : Params} :
  forall allowed defs seen added fmap (penv : param_env Pa) smap env,
    wf_smap_entries allowed defs seen true smap ->
    (forall k z, In (k, z) added -> ~ In k seen) ->
    env_matches_smap defs penv (oracle_of_fmap fmap) smap env ->
    env_matches_smap defs penv (oracle_of_fmap (added ++ fmap)) smap env.
Proof.
  intros allowed defs seen added fmap penv smap env Hwfs Hdisj Henv r w ce Hf.
  destruct (Henv r w ce Hf) as [Hr [dv [Hfe [Hev Hsc]]]].
  destruct (Hwfs r w ce Hf) as (_ & _ & _ & Hlf & _ & Hfk).
  split; [exact Hr | exists dv; repeat split; try assumption].
  exact (eq_trans
           (eval_let_free_prepend_fmap ce penv added fmap seen Hlf (Hfk eq_refl) Hdisj)
           Hev).
Qed.

Lemma mcfg_steps_eou_ret {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (r : R),
    mcfg_steps_to_ret sigma env (EOU_to_itree (E := MCFGEtop) (raise_ret r)) sigma env r.
Proof.
  intros sigma env r; apply MSR_Ret; reflexivity.
Qed.

Lemma mcfg_steps_raiseUB {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (msg : string),
    mcfg_steps_to_ub sigma env (raiseUB (E := @MCFGEtop Pa) (X := R) msg).
Proof.
  intros sigma env msg; eapply MSU_UB;
    unfold raiseUB, trigger_cast', ITree.trigger; rewrite observe_bind; reflexivity.
Qed.

Lemma cfg_steps_raiseUB {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (msg : string),
    cfg_steps_to_ub sigma env (raiseUB (E := @CFGEtop Pa) (X := R) msg).
Proof.
  intros sigma env msg; eapply CSU_UB;
    unfold raiseUB, trigger_cast', ITree.trigger; rewrite observe_bind; reflexivity.
Qed.

Lemma mcfg_steps_eou_ub {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (msg : string),
    mcfg_steps_to_ub sigma env (EOU_to_itree (E := MCFGEtop) (@raise_ub R msg)).
Proof.
  intros sigma env msg; cbn [EOU_to_itree]; apply mcfg_steps_raiseUB.
Qed.

Lemma cfg_steps_lwrite {Pa : Params} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (id : raw_id) (dv : @dvalue Pa),
    cfg_steps_to_ret sigma env (lwrite (E := CFGEtop) id dv) sigma (RM.add id dv env) tt.
Proof.
  intros sigma env id dv; eapply CSR_LocalWrite; [reflexivity | apply CSR_Ret; reflexivity].
Qed.

Lemma eval_reified_exp_src {Pa : Params} :
  forall (o : exp dtyp) params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) smap (env : rmap (@dvalue Pa)) seen0 top w ce seen1,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx dt, In (idx, dt) (exp_param_uses params defs top o) -> nth_error arg_dtys idx = Some dt) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
    wf_smap_entries allowed defs seen0 false smap ->
    env_matches_smap defs (build_param_env src_pnames vs) foracle smap env ->
    reify_exp false params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s, mcfg_steps_to_ub (chain_draws draws tail_s) env (denote_exp top o)) /\
        (exists msg, eval_closed_cert_expr (build_param_env src_pnames vs) foracle ce = raise_ub msg)) \/
       (exists dv,
          eval_closed_cert_expr (build_param_env src_pnames vs) foracle ce = raise_ret dv /\
          wf_scalar_dvalue w dv /\
          (forall tail_s, mcfg_steps_to_ret (chain_draws draws tail_s) env (denote_exp top o) tail_s env dv))).
Proof.
  apply (scalar_exp_ind (fun o =>
    forall params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
           (foracle : freeze_oracle) smap (env : rmap (@dvalue Pa)) seen0 top w ce seen1,
      NoDup src_pnames ->
      List.length params = List.length vs ->
      List.length src_pnames = List.length vs ->
      List.length arg_dtys = List.length params ->
      Forall2 dvalue_has_dtyp vs arg_dtys ->
      (forall idx dt, In (idx, dt) (exp_param_uses params defs top o) -> nth_error arg_dtys idx = Some dt) ->
      (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
        exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
      wf_smap_entries allowed defs seen0 false smap ->
      env_matches_smap defs (build_param_env src_pnames vs) foracle smap env ->
      reify_exp false params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
      exists draws : list (dtyp * @dvalue Pa),
        Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
        (((forall tail_s, mcfg_steps_to_ub (chain_draws draws tail_s) env (denote_exp top o)) /\
          (exists msg, eval_closed_cert_expr (build_param_env src_pnames vs) foracle ce = raise_ub msg)) \/
         (exists dv,
            eval_closed_cert_expr (build_param_env src_pnames vs) foracle ce = raise_ret dv /\
            wf_scalar_dvalue w dv /\
            (forall tail_s, mcfg_steps_to_ret (chain_draws draws tail_s) env (denote_exp top o) tail_s env dv))))).
  - (* OP_IBinop *)
    intros iop dt e1 e2 IH1 IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen2
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce seen2'; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [Heq_iop _].
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfs Henv Hr1)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (wf_smap_entries_false_seen allowed defs seen0 seen1 smap Hwfs) as Hwfs1.
      destruct (IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen1
                  (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                  Hpe Hwfs1 Henv Hr2)
        as (draws2 & Hfa2 & [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]]).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
           eapply mcfg_steps_to_ub_bind_r;
             [exact (Hst1 (chain_draws draws2 tail_s))
             | apply mcfg_steps_to_ub_bind_l; exact (Hub2 tail_s)].
        -- exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1, Hev2; reflexivity.
      * destruct (eval_iop_wf_scalar cop cfl w dv1 dv2 Hsc1 Hsc2)
          as [[msg_op Hev_op] | [vout [Hev_op Hsc_out]]].
        -- exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
           ++ intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
              eapply mcfg_steps_to_ub_bind_r; [exact (Hst1 (chain_draws draws2 tail_s)) |].
              eapply mcfg_steps_to_ub_bind_r; [exact (Hst2 tail_s) |].
              rewrite <- Heq_iop, Hev_op; apply mcfg_steps_eou_ub.
           ++ exists msg_op; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
        -- exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right].
           exists vout; split; [| split; [exact Hsc_out |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
           ++ intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
              eapply mcfg_steps_to_ret_bind; [exact (Hst1 (chain_draws draws2 tail_s)) |].
              eapply mcfg_steps_to_ret_bind; [exact (Hst2 tail_s) |].
              rewrite <- Heq_iop, Hev_op; apply mcfg_steps_eou_ret.
  - (* OP_ICmp *)
    intros ss cmp dt e1 e2 IH1 IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen2
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce seen2'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I wb))) wb ce1 seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfs Henv Hr1)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (wf_smap_entries_false_seen allowed defs seen0 seen1 smap Hwfs) as Hwfs1.
      destruct (IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen1
                  (Some (DTYPE_Base (DTYPE_I wb))) wb ce2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                  Hpe Hwfs1 Henv Hr2)
        as (draws2 & Hfa2 & [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]]).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
           eapply mcfg_steps_to_ub_bind_r;
             [exact (Hst1 (chain_draws draws2 tail_s))
             | apply mcfg_steps_to_ub_bind_l; exact (Hub2 tail_s)].
        -- exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1, Hev2; reflexivity.
      * destruct (eval_icmp_wf_scalar ss (icmp_to_cert cmp) wb dv1 dv2 Hsc1 Hsc2)
          as [vout [Hev_cmp Hsc_out]].
        exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right].
        exists vout; split; [| split; [exact Hsc_out |]].
        -- unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_cmp.
        -- intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
           eapply mcfg_steps_to_ret_bind; [exact (Hst1 (chain_draws draws2 tail_s)) |].
           eapply mcfg_steps_to_ret_bind; [exact (Hst2 tail_s) |].
           rewrite <- (icmp_to_cert_roundtrip cmp), Hev_cmp; apply mcfg_steps_eou_ret.
  - (* OP_Conversion *)
    intros ct dtf e1 dtt IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen1
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct ct as [| pc | ic]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |] eqn:Hpc; [| discriminate].
    set (w_ok :=
      match ck with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
      end) in *.
    destruct w_ok eqn:Hwok; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) e1)
      as [[[w1 ce1] seen1'] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce seen1'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (pure_conv_to_cert_roundtrip pc ck cfl Hpc) as Heq_pc.
    destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I fw))) fw ce1 seen1
                Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr1)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + unfold w_ok in Hwok.
      destruct (eval_cast_wf_scalar ck fw tw cfl dv1 Hwok Hsc1) as [vout [Hev_cast Hsc_out]].
      exists draws1; split; [exact Hfa1 | right].
      exists vout; split; [| split; [exact Hsc_out |]].
      * unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; cbn [eou_bind]; exact Hev_cast.
      * intros tail_s; cbn [denote_exp convert].
        eapply mcfg_steps_to_ret_bind; [exact (Hst1 tail_s) |].
        rewrite <- Heq_pc, Hev_cast; apply mcfg_steps_eou_ret.
  - (* OP_Select *)
    intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen3
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[[wc' cec] seen1] |] eqn:Hrc; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I w1))) e1)
      as [[[wa ce1] seen2] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen2 (Some (DTYPE_Base (DTYPE_I w1))) e2)
      as [[[wb ce2] seen3'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce seen3'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hrc)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (IHc params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive cec seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfs Henv Hrc)
      as (drawsc & Hfac & [[Hubc [msgc Hevc]] | [dvc [Hevc [Hscc Hstc]]]]).
    + exists drawsc; split; [exact Hfac | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hubc tail_s).
      * exists msgc; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hevc; reflexivity.
    + pose proof (wf_smap_entries_false_seen allowed defs seen0 seen1 smap Hwfs) as Hwfs1.
      destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen1
                  (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hin)))))
                  Hpe Hwfs1 Henv Hr1)
        as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
      * exists (drawsc ++ draws1); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
           eapply mcfg_steps_to_ub_bind_r;
             [exact (Hstc (chain_draws draws1 tail_s))
             | apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s)].
        -- exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hevc, Hev1; reflexivity.
      * pose proof (wf_smap_entries_false_seen allowed defs seen0 seen2 smap Hwfs) as Hwfs2.
        destruct (IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen2
                    (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen3
                    Hnd Hlp Hls Hla Hvs
                    (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror Hin)))))
                    Hpe Hwfs2 Henv Hr2)
          as (draws2 & Hfa2 & [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]]).
        -- exists (drawsc ++ draws1 ++ draws2); split;
             [apply Forall_app; split; [exact Hfac | apply Forall_app; split; assumption] | left; split].
           ++ intros tail_s; rewrite !chain_draws_app; cbn [denote_exp].
              eapply mcfg_steps_to_ub_bind_r; [exact (Hstc (chain_draws draws1 (chain_draws draws2 tail_s))) |].
              eapply mcfg_steps_to_ub_bind_r; [exact (Hst1 (chain_draws draws2 tail_s)) |].
              apply mcfg_steps_to_ub_bind_l; exact (Hub2 tail_s).
           ++ exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hevc, Hev1, Hev2; reflexivity.
        -- destruct (eval_select_wf_scalar w dvc dv1 dv2 Hscc Hsc1 Hsc2)
             as [vout [Hev_sel Hsc_out]].
           exists (drawsc ++ draws1 ++ draws2); split;
             [apply Forall_app; split; [exact Hfac | apply Forall_app; split; assumption] | right].
           exists vout; split; [| split; [exact Hsc_out |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hevc, Hev1, Hev2; cbn [eou_bind]; exact Hev_sel.
           ++ intros tail_s; rewrite !chain_draws_app; cbn [denote_exp].
              eapply mcfg_steps_to_ret_bind; [exact (Hstc (chain_draws draws1 (chain_draws draws2 tail_s))) |].
              eapply mcfg_steps_to_ret_bind; [exact (Hst1 (chain_draws draws2 tail_s)) |].
              eapply mcfg_steps_to_ret_bind; [exact (Hst2 tail_s) |].
              rewrite Hev_sel; apply mcfg_steps_eou_ret.
  - (* OP_Freeze *)
    intros dt e1 IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen1
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; try discriminate; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen_mid] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst wb ce seen1; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    destruct (reify_exp_freeze_props e1 false params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen_mid Hwfs Hr1)
      as (Hlf1 & _ & _).
    destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen_mid
                Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr1)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + destruct Hsc1 as [-> | [iv ->]].
      * set (fv := DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (foracle w ce1)))).
        exists (draws1 ++ [(DTYPE_Base (DTYPE_I w), fv)]).
        split.
        -- apply Forall_app; split; [exact Hfa1 |].
           constructor; [apply valid_draw_i_iff; eexists; reflexivity | constructor].
        -- right; exists fv; split; [| split; [right; eexists; reflexivity |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr let_val_exprs List.map].
              rewrite Hev1, (expand_lets_let_free ce1 Hlf1); reflexivity.
           ++ intros tail_s; rewrite chain_draws_app; cbn [chain_draws denote_exp].
              eapply mcfg_steps_to_ret_bind;
                [exact (Hst1 (prepend_draws [(DTYPE_Base (DTYPE_I w), fv)] tail_s)) |].
              eapply MSR_Draw; [reflexivity | intros n d; reflexivity |].
              cbn [prepend_draws].
              destruct (dtyp_eq_dec (DTYPE_Base (DTYPE_I w)) (DTYPE_Base (DTYPE_I w))) as [_ | Hneq];
                [apply MSR_Ret; reflexivity | exfalso; exact (Hneq eq_refl)].
      * exists draws1; split; [exact Hfa1 | right].
        exists (DVALUE_Base (@DVALUE_I Pa w iv)).
        split; [| split; [right; exists iv; reflexivity |]].
        -- unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
        -- intros tail_s; cbn [denote_exp].
           eapply mcfg_steps_to_ret_bind; [exact (Hst1 tail_s) | apply MSR_Ret; reflexivity].
  - (* Non-recursive base cases *)
    intros o; destruct o; try exact I;
      intros params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen1
             Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr;
      cbn [reify_exp] in Hr; try discriminate.
    + (* EXP_Ident *)
      destruct id as [| r]; [discriminate |].
      destruct (RM.find r smap) as [[wr cer] |] eqn:Hfind.
      * destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
        inversion Hr; subst wr ce seen1; clear Hr.
        destruct (Henv r w cer Hfind) as [_ [dv [Hfe [Hev Hsc]]]].
        exists []; split; [constructor | right; exists dv; split; [exact Hev | split; [exact Hsc |]]].
        intros tail_s; cbn [chain_draws denote_exp lookup_id].
        eapply MSR_LocalRead; [reflexivity | exact Hfe | apply MSR_Ret; reflexivity].
      * destruct (raw_id_in_list r defs) eqn:Hrd; [discriminate |].
        destruct top as [dt |]; [| discriminate].
        destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
        destruct (find_raw_id_index r params) as [idx |] eqn:Hidx; [| discriminate].
        destruct (nth_error src_pnames idx) as [pnm |] eqn:Hpnm; [| discriminate].
        destruct (starts_with_dollar pnm) eqn:Hdl; [discriminate |].
        inversion Hr; subst wt ce seen1; clear Hr.
        assert (Hnin : ~ In r defs)
          by (intros Hin; apply raw_id_in_list_spec in Hin; congruence).
        pose proof (find_raw_id_index_nth_error params r idx Hidx) as Hnth_p.
        destruct (Hpe idx r Hnth_p Hnin) as [dv [Hnth_v Hfe]].
        assert (Hnth_dt : nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I w))).
        { apply Hpu; cbn [exp_param_uses]; rewrite Hrd, Hidx; left; reflexivity. }
        pose proof (Forall2_nth_error_l dvalue_has_dtyp vs arg_dtys Hvs idx dv
                      (DTYPE_Base (DTYPE_I w)) Hnth_v Hnth_dt) as Hsc.
        apply dvalue_has_dtyp_i_iff_wf_scalar in Hsc.
        destruct (build_param_env_nth src_pnames vs idx pnm Hnd Hls Hpnm) as [dv' [Hnth_v' Hbp]].
        assert (Heq_dv : dv' = dv) by congruence; subst dv'.
        exists []; split; [constructor | right; exists dv; split; [| split; [exact Hsc |]]].
        -- unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
           rewrite Hbp; exact (check_scalar_width_ok w dv Hsc).
        -- intros tail_s; cbn [chain_draws denote_exp lookup_id].
           eapply MSR_LocalRead; [reflexivity | exact Hfe | apply MSR_Ret; reflexivity].
    + (* EXP_Integer *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [constructor | right].
      exists (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (reify_int_const w (denote_int_syntax x)))))).
      split; [reflexivity | split; [right; eexists; reflexivity |]].
      intros tail_s; cbn [chain_draws denote_exp]; rewrite repr_reify_int_const.
      apply MSR_Ret; reflexivity.
    + (* EXP_Bool *)
      destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce seen1; clear Hr.
      exists []; split; [constructor | right].
      destruct b.
      * exists (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 1%N)))).
        split; [reflexivity | split; [right; eexists; reflexivity |]].
        intros tail_s; cbn [chain_draws denote_exp]; rewrite repr_one_N.
        apply MSR_Ret; reflexivity.
      * exists (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 0%N)))).
        split; [reflexivity | split; [right; eexists; reflexivity |]].
        intros tail_s; cbn [chain_draws denote_exp]; rewrite repr_zero_N.
        apply MSR_Ret; reflexivity.
    + (* EXP_Undef *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [constructor | right].
      exists (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [left; reflexivity | intros tail_s; apply MSR_Ret; reflexivity]].
    + (* EXP_Poison *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [constructor | right].
      exists (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [left; reflexivity | intros tail_s; apply MSR_Ret; reflexivity]].
Qed.

Lemma eval_reified_exp_tgt {Pa : Params} :
  forall (o : exp dtyp) params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         smap (env : rmap (@dvalue Pa)) seen0 top w ce seen1,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx dt, In (idx, dt) (exp_param_uses params defs top o) -> nth_error arg_dtys idx = Some dt) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed defs seen0 true smap ->
    env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap env ->
    reify_exp true params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    exists added : list (freeze_key * Z),
      (forall k z, In (k, z) added -> In k seen1 /\ ~ In k seen0) /\
      ((exists msg,
          eval_closed_cert_expr (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) ce = raise_ub msg) \/
       (exists sigma1 dv,
          wf_draw_strat sigma1 /\
          eval_closed_cert_expr (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) ce = raise_ret dv /\
          wf_scalar_dvalue w dv /\
          mcfg_steps_to_ret sigma0 env (denote_exp top o) sigma1 env dv)).
Proof.
  apply (scalar_exp_ind (fun o =>
    forall params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
           (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
           smap (env : rmap (@dvalue Pa)) seen0 top w ce seen1,
      NoDup src_pnames ->
      List.length params = List.length vs ->
      List.length src_pnames = List.length vs ->
      List.length arg_dtys = List.length params ->
      Forall2 dvalue_has_dtyp vs arg_dtys ->
      (forall idx dt, In (idx, dt) (exp_param_uses params defs top o) -> nth_error arg_dtys idx = Some dt) ->
      (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
        exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
      wf_draw_strat sigma0 ->
      wf_smap_entries allowed defs seen0 true smap ->
      env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap env ->
      reify_exp true params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
      exists added : list (freeze_key * Z),
        (forall k z, In (k, z) added -> In k seen1 /\ ~ In k seen0) /\
        ((exists msg,
            eval_closed_cert_expr (build_param_env src_pnames vs)
              (oracle_of_fmap (added ++ fmap0)) ce = raise_ub msg) \/
         (exists sigma1 dv,
            wf_draw_strat sigma1 /\
            eval_closed_cert_expr (build_param_env src_pnames vs)
              (oracle_of_fmap (added ++ fmap0)) ce = raise_ret dv /\
            wf_scalar_dvalue w dv /\
            mcfg_steps_to_ret sigma0 env (denote_exp top o) sigma1 env dv)))).
  - (* OP_IBinop *)
    intros iop dt e1 e2 IH1 IH2 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen2
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce seen2'; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [Heq_iop _].
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (reify_exp_freeze_props e1 true params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen1 Hwfs0 Hr1)
      as (Hlf1 & Hinc01 & Hfk1).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 true smap Hinc01 Hwfs0) as Hwfs1.
    destruct (reify_exp_freeze_props e2 true params src_pnames defs allowed smap seen1
                (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen2 Hwfs1 Hr2)
      as (_ & Hinc12 & _).
    destruct (IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfd0 Hwfs0 Henv0 Hr1)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hm Hn0]; split; [exact (Hinc12 k Hm) | exact Hn0].
      * left; exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                    (build_param_env src_pnames vs) smap env Hwfs0
                    (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv1.
      destruct (IH2 params src_pnames defs allowed arg_dtys vs sigma1 (added1 ++ fmap0) smap env seen1
                  (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                  Hpe Hwfd1 Hwfs1 Henv1 Hr2)
        as (added2 & Had2 & [[msg2 Hev2] | (sigma2 & dv2 & Hwfd2 & Hev2 & Hsc2 & Hst2)]).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hns1]; split; [exact Hs2 | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hns0]; split; [exact (Hinc12 k Hs1) | exact Hns0]. }
        split; [exact Had12 | left; exists msg2].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun k z H => proj2 (Had2 k z H))) as Hev1'.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1', Hev1, Hev2; reflexivity.
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hns1]; split; [exact Hs2 | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hns0]; split; [exact (Hinc12 k Hs1) | exact Hns0]. }
        split; [exact Had12 |].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun k z H => proj2 (Had2 k z H))) as Hev1'.
        destruct (eval_iop_wf_scalar cop cfl w dv1 dv2 Hsc1 Hsc2)
          as [[msg_op Hev_op] | [vout [Hev_op Hsc_out]]].
        -- left; exists msg_op; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1', Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
        -- right; exists sigma2, vout; split; [exact Hwfd2 | split; [| split; [exact Hsc_out |]]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1', Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
           ++ cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
              eapply mcfg_steps_to_ret_bind; [exact Hst2 |].
              rewrite <- Heq_iop, Hev_op; apply mcfg_steps_eou_ret.
  - (* OP_ICmp *)
    intros ss cmp dt e1 e2 IH1 IH2 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen2
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce seen2'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (reify_exp_freeze_props e1 true params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I wb))) wb ce1 seen1 Hwfs0 Hr1)
      as (Hlf1 & Hinc01 & Hfk1).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 true smap Hinc01 Hwfs0) as Hwfs1.
    destruct (reify_exp_freeze_props e2 true params src_pnames defs allowed smap seen1
                (Some (DTYPE_Base (DTYPE_I wb))) wb ce2 seen2 Hwfs1 Hr2)
      as (_ & Hinc12 & _).
    destruct (IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I wb))) wb ce1 seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfd0 Hwfs0 Henv0 Hr1)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hm Hn0]; split; [exact (Hinc12 k Hm) | exact Hn0].
      * left; exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                    (build_param_env src_pnames vs) smap env Hwfs0
                    (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv1.
      destruct (IH2 params src_pnames defs allowed arg_dtys vs sigma1 (added1 ++ fmap0) smap env seen1
                  (Some (DTYPE_Base (DTYPE_I wb))) wb ce2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                  Hpe Hwfd1 Hwfs1 Henv1 Hr2)
        as (added2 & Had2 & [[msg2 Hev2] | (sigma2 & dv2 & Hwfd2 & Hev2 & Hsc2 & Hst2)]).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hns1]; split; [exact Hs2 | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hns0]; split; [exact (Hinc12 k Hs1) | exact Hns0]. }
        split; [exact Had12 | left; exists msg2].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun k z H => proj2 (Had2 k z H))) as Hev1'.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1', Hev1, Hev2; reflexivity.
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hns1]; split; [exact Hs2 | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hns0]; split; [exact (Hinc12 k Hs1) | exact Hns0]. }
        split; [exact Had12 | right].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun k z H => proj2 (Had2 k z H))) as Hev1'.
        destruct (eval_icmp_wf_scalar ss (icmp_to_cert cmp) wb dv1 dv2 Hsc1 Hsc2)
          as [vout [Hev_cmp Hsc_out]].
        exists sigma2, vout; split; [exact Hwfd2 | split; [| split; [exact Hsc_out |]]].
        -- unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1', Hev1, Hev2; cbn [eou_bind]; exact Hev_cmp.
        -- cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
           eapply mcfg_steps_to_ret_bind; [exact Hst2 |].
           rewrite <- (icmp_to_cert_roundtrip cmp), Hev_cmp; apply mcfg_steps_eou_ret.
  - (* OP_Conversion *)
    intros ct dtf e1 dtt IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen1
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct ct as [| pc | ic]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |] eqn:Hpc; [| discriminate].
    set (w_ok :=
      match ck with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
      end) in *.
    destruct w_ok eqn:Hwok; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) e1)
      as [[[w1 ce1] seen1'] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce seen1'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (pure_conv_to_cert_roundtrip pc ck cfl Hpc) as Heq_pc.
    destruct (IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I fw))) fw ce1 seen1
                Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr1)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split; [exact Had1 | left; exists msg1].
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + unfold w_ok in Hwok.
      destruct (eval_cast_wf_scalar ck fw tw cfl dv1 Hwok Hsc1) as [vout [Hev_cast Hsc_out]].
      exists added1; split; [exact Had1 | right].
      exists sigma1, vout; split; [exact Hwfd1 | split; [| split; [exact Hsc_out |]]].
      * unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; cbn [eou_bind]; exact Hev_cast.
      * cbn [denote_exp convert]; eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
        rewrite <- Heq_pc, Hev_cast; apply mcfg_steps_eou_ret.
  - (* OP_Select *)
    intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen3
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[[wc' cec] seen1] |] eqn:Hrc; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I w1))) e1)
      as [[[wa ce1] seen2] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen2 (Some (DTYPE_Base (DTYPE_I w1))) e2)
      as [[[wb ce2] seen3'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce seen3'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hrc)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (reify_exp_freeze_props ec true params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive cec seen1 Hwfs0 Hrc)
      as (Hlfc & Hinc01 & Hfkc).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 true smap Hinc01 Hwfs0) as Hwfs1.
    destruct (reify_exp_freeze_props e1 true params src_pnames defs allowed smap seen1
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen2 Hwfs1 Hr1)
      as (Hlf1 & Hinc12 & Hfk1).
    pose proof (wf_smap_entries_seen_mono allowed defs seen1 seen2 true smap Hinc12 Hwfs1) as Hwfs2.
    destruct (reify_exp_freeze_props e2 true params src_pnames defs allowed smap seen2
                (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen3 Hwfs2 Hr2)
      as (_ & Hinc23 & _).
    destruct (IHc params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive cec seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfd0 Hwfs0 Henv0 Hrc)
      as (addedc & Hadc & [[msgc Hevc] | (sigmac & dvc & Hwfdc & Hevc & Hscc & Hstc)]).
    + exists addedc; split.
      * intros k z Hkz; destruct (Hadc k z Hkz) as [Hm Hn0]; split; [exact (Hinc23 k (Hinc12 k Hm)) | exact Hn0].
      * left; exists msgc; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hevc; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 addedc fmap0
                    (build_param_env src_pnames vs) smap env Hwfs0
                    (fun k z H => proj2 (Hadc k z H)) Henv0) as Henv1.
      destruct (IH1 params src_pnames defs allowed arg_dtys vs sigmac (addedc ++ fmap0) smap env seen1
                  (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hin)))))
                  Hpe Hwfdc Hwfs1 Henv1 Hr1)
        as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
      * exists (added1 ++ addedc).
        assert (Had_c1 : forall k z, In (k, z) (added1 ++ addedc) -> In k seen3 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk1 | Hkc].
          - destruct (Had1 k z Hk1) as [Hs2 Hns1]; split; [exact (Hinc23 k Hs2) | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Hadc k z Hkc) as [Hs1 Hns0]; split; [exact (Hinc23 k (Hinc12 k Hs1)) | exact Hns0]. }
        split; [exact Had_c1 | left; exists msg1].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                      added1 (addedc ++ fmap0) seen1 Hlfc (Hfkc eq_refl)
                      (fun k z H => proj2 (Had1 k z H))) as Hevc'.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hevc', Hevc, Hev1; reflexivity.
      * pose proof (env_matches_smap_oracle_prepend allowed defs seen1 added1 (addedc ++ fmap0)
                      (build_param_env src_pnames vs) smap env Hwfs1
                      (fun k z H => proj2 (Had1 k z H)) Henv1) as Henv2.
        destruct (IH2 params src_pnames defs allowed arg_dtys vs sigma1 (added1 ++ (addedc ++ fmap0)) smap env seen2
                    (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen3
                    Hnd Hlp Hls Hla Hvs
                    (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror Hin)))))
                    Hpe Hwfd1 Hwfs2 Henv2 Hr2)
          as (added2 & Had2 & [[msg2 Hev2] | (sigma2 & dv2 & Hwfd2 & Hev2 & Hsc2 & Hst2)]).
        -- exists (added2 ++ added1 ++ addedc).
           assert (Had_all : forall k z, In (k, z) (added2 ++ added1 ++ addedc) -> In k seen3 /\ ~ In k seen0).
           { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1c].
             - destruct (Had2 k z Hk2) as [Hs3 Hns2]; split; [exact Hs3 | intros Hs0; exact (Hns2 (Hinc12 k (Hinc01 k Hs0)))].
             - apply in_app_iff in Hk1c as [Hk1 | Hkc].
               + destruct (Had1 k z Hk1) as [Hs2 Hns1]; split; [exact (Hinc23 k Hs2) | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
               + destruct (Hadc k z Hkc) as [Hs1 Hns0]; split; [exact (Hinc23 k (Hinc12 k Hs1)) | exact Hns0]. }
           split; [exact Had_all | left; exists msg2].
           replace ((added2 ++ added1 ++ addedc) ++ fmap0) with (added2 ++ (added1 ++ (addedc ++ fmap0)))
             by (rewrite !app_assoc; reflexivity).
           pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                         added1 (addedc ++ fmap0) seen1 Hlfc (Hfkc eq_refl)
                         (fun k z H => proj2 (Had1 k z H))) as Hevc1.
           pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                         added2 (added1 ++ (addedc ++ fmap0)) seen2 Hlfc
                         (fun u Hu => Hinc12 u (Hfkc eq_refl u Hu))
                         (fun k z H => proj2 (Had2 k z H))) as Hevc2.
           pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                         added2 (added1 ++ (addedc ++ fmap0)) seen2 Hlf1 (Hfk1 eq_refl)
                         (fun k z H => proj2 (Had2 k z H))) as Hev12.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hevc2, Hevc1, Hevc, Hev12, Hev1, Hev2; reflexivity.
        -- exists (added2 ++ added1 ++ addedc).
           assert (Had_all : forall k z, In (k, z) (added2 ++ added1 ++ addedc) -> In k seen3 /\ ~ In k seen0).
           { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1c].
             - destruct (Had2 k z Hk2) as [Hs3 Hns2]; split; [exact Hs3 | intros Hs0; exact (Hns2 (Hinc12 k (Hinc01 k Hs0)))].
             - apply in_app_iff in Hk1c as [Hk1 | Hkc].
               + destruct (Had1 k z Hk1) as [Hs2 Hns1]; split; [exact (Hinc23 k Hs2) | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
               + destruct (Hadc k z Hkc) as [Hs1 Hns0]; split; [exact (Hinc23 k (Hinc12 k Hs1)) | exact Hns0]. }
           split; [exact Had_all | right].
           replace ((added2 ++ added1 ++ addedc) ++ fmap0) with (added2 ++ (added1 ++ (addedc ++ fmap0)))
             by (rewrite !app_assoc; reflexivity).
           pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                         added1 (addedc ++ fmap0) seen1 Hlfc (Hfkc eq_refl)
                         (fun k z H => proj2 (Had1 k z H))) as Hevc1.
           pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                         added2 (added1 ++ (addedc ++ fmap0)) seen2 Hlfc
                         (fun u Hu => Hinc12 u (Hfkc eq_refl u Hu))
                         (fun k z H => proj2 (Had2 k z H))) as Hevc2.
           pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                         added2 (added1 ++ (addedc ++ fmap0)) seen2 Hlf1 (Hfk1 eq_refl)
                         (fun k z H => proj2 (Had2 k z H))) as Hev12.
           destruct (eval_select_wf_scalar w dvc dv1 dv2 Hscc Hsc1 Hsc2)
             as [vout [Hev_sel Hsc_out]].
           exists sigma2, vout; split; [exact Hwfd2 | split; [| split; [exact Hsc_out |]]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hevc2, Hevc1, Hevc, Hev12, Hev1, Hev2; cbn [eou_bind]; exact Hev_sel.
           ++ cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hstc |].
              eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
              eapply mcfg_steps_to_ret_bind; [exact Hst2 |].
              rewrite Hev_sel; apply mcfg_steps_eou_ret.
  - (* OP_Freeze *)
    intros dt e1 IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen1
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; try discriminate; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen_mid] |] eqn:Hr1; [| discriminate].
    destruct (freeze_key_in (wb, ce1) seen_mid) eqn:Hfk_in; [discriminate |].
    inversion Hr; subst wb ce seen1; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    assert (Hfnin : ~ In (w, ce1) seen_mid)
      by (intros Hin; apply freeze_key_in_spec in Hin; congruence).
    destruct (reify_exp_freeze_props e1 true params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen_mid Hwfs0 Hr1)
      as (Hlf1 & Hinc0m & Hfk1).
    destruct (IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen_mid
                Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr1)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma_m & dv1 & Hwfd_m & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hm Hn0]; split; [right; exact Hm | exact Hn0].
      * left; exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + destruct Hsc1 as [-> | [iv ->]].
      * pose proof (Hwfd_m 0%nat (DTYPE_Base (DTYPE_I w)) (inhabited_draw_dtyp_i w)) as Hvd.
        apply valid_draw_i_iff in Hvd as [idraw Hidraw].
        set (z_draw := @Integers.unsigned w idraw).
        exists ([((w, ce1), z_draw)] ++ added1).
        split.
        -- intros k z [Heq | Hkz].
           ++ inversion Heq; subst k z; split;
                [left; reflexivity | intros Hs0; exact (Hfnin (Hinc0m _ Hs0))].
           ++ destruct (Had1 k z Hkz) as [Hm Hn0]; split; [right; exact Hm | exact Hn0].
        -- right; exists (shift_draw_strat sigma_m), (DVALUE_Base (@DVALUE_I Pa w idraw)).
           split; [exact (shift_draw_strat_wf sigma_m Hwfd_m) | split; [| split; [right; exists idraw; reflexivity |]]].
           ++ rewrite <- app_assoc.
              pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                            [((w, ce1), z_draw)] (added1 ++ fmap0) seen_mid Hlf1 (Hfk1 eq_refl)
                            (fun k z H => match H with
                                          | or_introl Heq => eq_ind_r (fun u => ~ In u seen_mid) Hfnin (eq_sym (f_equal fst Heq))
                                          | or_intror Hfalse => False_ind _ Hfalse
                                          end)) as Hev1'.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr let_val_exprs List.map].
              match goal with
              | |- eou_bind _ ?K = _ =>
                  transitivity (eou_bind (raise_ret (DVALUE_Base DVALUE_Poison)) K);
                  [f_equal; exact (eq_trans Hev1' Hev1) |]
              end.
              cbn [eou_bind]; rewrite (expand_lets_let_free ce1 Hlf1); cbn [app oracle_of_fmap].
              rewrite freeze_key_eqb_refl; unfold z_draw; rewrite (@Integers.repr_unsigned w idraw); reflexivity.
           ++ cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
              eapply MSR_Draw; [reflexivity | intros n d; reflexivity | rewrite Hidraw; apply MSR_Ret; reflexivity].
      * exists added1; split.
        -- intros k z Hkz; destruct (Had1 k z Hkz) as [Hm Hn0]; split; [right; exact Hm | exact Hn0].
        -- right; exists sigma_m, (DVALUE_Base (@DVALUE_I Pa w iv)).
           split; [exact Hwfd_m | split; [| split; [right; exists iv; reflexivity |]]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
           ++ cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hst1 | apply MSR_Ret; reflexivity].
  - (* Non-recursive base cases *)
    intros o; destruct o; try exact I;
      intros params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen1
             Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr;
      cbn [reify_exp] in Hr; try discriminate.
    + (* EXP_Ident *)
      destruct id as [| r]; [discriminate |].
      destruct (RM.find r smap) as [[wr cer] |] eqn:Hfind.
      * destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
        inversion Hr; subst wr ce seen1; clear Hr.
        destruct (Henv0 r w cer Hfind) as [_ [dv [Hfe [Hev Hsc]]]].
        exists []; split; [intros _ _ [] | right; exists sigma0, dv].
        split; [exact Hwfd0 | split; [exact Hev | split; [exact Hsc |]]].
        cbn [denote_exp lookup_id]; eapply MSR_LocalRead; [reflexivity | exact Hfe | apply MSR_Ret; reflexivity].
      * destruct (raw_id_in_list r defs) eqn:Hrd; [discriminate |].
        destruct top as [dt |]; [| discriminate].
        destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
        destruct (find_raw_id_index r params) as [idx |] eqn:Hidx; [| discriminate].
        destruct (nth_error src_pnames idx) as [pnm |] eqn:Hpnm; [| discriminate].
        destruct (starts_with_dollar pnm) eqn:Hdl; [discriminate |].
        inversion Hr; subst wt ce seen1; clear Hr.
        assert (Hnin : ~ In r defs)
          by (intros Hin; apply raw_id_in_list_spec in Hin; congruence).
        pose proof (find_raw_id_index_nth_error params r idx Hidx) as Hnth_p.
        destruct (Hpe idx r Hnth_p Hnin) as [dv [Hnth_v Hfe]].
        assert (Hnth_dt : nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I w))).
        { apply Hpu; cbn [exp_param_uses]; rewrite Hrd, Hidx; left; reflexivity. }
        pose proof (Forall2_nth_error_l dvalue_has_dtyp vs arg_dtys Hvs idx dv
                      (DTYPE_Base (DTYPE_I w)) Hnth_v Hnth_dt) as Hsc.
        apply dvalue_has_dtyp_i_iff_wf_scalar in Hsc.
        destruct (build_param_env_nth src_pnames vs idx pnm Hnd Hls Hpnm) as [dv' [Hnth_v' Hbp]].
        assert (Heq_dv : dv' = dv) by congruence; subst dv'.
        exists []; split; [intros _ _ [] | right; exists sigma0, dv].
        split; [exact Hwfd0 | split; [| split; [exact Hsc |]]].
        -- unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
           rewrite Hbp; exact (check_scalar_width_ok w dv Hsc).
        -- cbn [denote_exp lookup_id]; eapply MSR_LocalRead; [reflexivity | exact Hfe | apply MSR_Ret; reflexivity].
    + (* EXP_Integer *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [intros _ _ [] | right].
      exists sigma0,
        (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (reify_int_const w (denote_int_syntax x)))))).
      split; [exact Hwfd0 | split; [reflexivity | split; [right; eexists; reflexivity |]]].
      cbn [denote_exp]; rewrite repr_reify_int_const; apply MSR_Ret; reflexivity.
    + (* EXP_Bool *)
      destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce seen1; clear Hr.
      exists []; split; [intros _ _ [] | right].
      destruct b.
      * exists sigma0, (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 1%N)))).
        split; [exact Hwfd0 | split; [reflexivity | split; [right; eexists; reflexivity |]]].
        cbn [denote_exp]; rewrite repr_one_N; apply MSR_Ret; reflexivity.
      * exists sigma0, (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 0%N)))).
        split; [exact Hwfd0 | split; [reflexivity | split; [right; eexists; reflexivity |]]].
        cbn [denote_exp]; rewrite repr_zero_N; apply MSR_Ret; reflexivity.
    + (* EXP_Undef *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [intros _ _ [] | right].
      exists sigma0, (DVALUE_Base DVALUE_Poison).
      split; [exact Hwfd0 | split; [reflexivity | split; [left; reflexivity | apply MSR_Ret; reflexivity]]].
    + (* EXP_Poison *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [intros _ _ [] | right].
      exists sigma0, (DVALUE_Base DVALUE_Poison).
      split; [exact Hwfd0 | split; [reflexivity | split; [left; reflexivity | apply MSR_Ret; reflexivity]]].
Qed.


