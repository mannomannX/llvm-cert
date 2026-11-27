(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Multi-Obligation SAT/LRAT Discharger & Shared MC Helpers ([CertValidator.McOblDischarger])

    Provides the ISA-agnostic single-CNF multi-obligation SAT/LRAT discharger
    ([mc_loop_obl], [check_mc_loop_obls], [emit_mc_loop_cnf],
    [check_mc_loop_obls_sound]) plus shared proof helpers used by both
    [CertValidator.McLoop] and [CertValidator.McCall]. *)

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

From Vellvm Require Import
  Utils
  Utils.Assoc
  Utils.ListUtil
  Numeric.Zbits
  Numeric.Integers
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.DynamicTypes
  Syntax.RawIdMaps
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  CertValidator
  Elf64Spec
  McFrameMem.

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
#[local] Arguments Integers.mul : simpl never.
#[local] Arguments Integers.divs : simpl never.
#[local] Arguments Integers.shru : simpl never.
#[local] Arguments Integers.shr : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. Shared Naming, Phi-Map & Overlay Helpers *)

Definition mc_starts_with_bang (s : string) : bool :=
  match s with
  | String c _ => Ascii.eqb c "!"%char
  | EmptyString => false
  end.

Lemma show_Z_dec_pos_inj : forall n1 n2 : Z,
  (0 <= n1)%Z -> (0 <= n2)%Z ->
  show_Z_dec n1 = show_Z_dec n2 -> n1 = n2.
Proof.
  intros n1 n2 Hn1 Hn2 Heq.
  unfold show_Z_dec in Heq.
  pose proof (f_equal NilEmpty.int_of_string Heq) as Hinv.
  rewrite !NilEmpty.isi in Hinv.
  inversion Hinv as [Hi].
  pose proof (f_equal Z.of_int Hi) as Hz.
  rewrite !DecimalZ.of_to in Hz; exact Hz.
Qed.

Fixpoint apply_reified_phis
  (lmap : rmap (positive * cert_expr)) (pevals : list (raw_id * positive * cert_expr))
  {struct pevals} : rmap (positive * cert_expr) :=
  match pevals with
  | [] => lmap
  | (id, w, ce) :: rest => apply_reified_phis (RM.add id (w, ce) lmap) rest
  end.

Definition pevals_ub_free (pevals : list (raw_id * positive * cert_expr)) : bool :=
  forallb (fun '(_, _, ce) => ub_free_expr ce) pevals.

Lemma apply_reified_phis_wf : forall pevals allowed lmap,
  wf_pure_lmap allowed lmap ->
  Forall (fun '(_, w, ce) => is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals ->
  wf_pure_lmap allowed (apply_reified_phis lmap pevals).
Proof.
  intros pevals allowed lmap Hlmap Hfa; revert lmap Hlmap;
    induction Hfa as [| [[id w] ce] rest (_ & Hbw & (Hwt & Hlf & Hfv)) _ IH];
    intros lmap Hlmap; cbn [apply_reified_phis]; [exact Hlmap |].
  apply IH; exact (wf_pure_lmap_add allowed lmap id w ce Hlmap Hwt Hbw Hlf Hfv).
Qed.

Lemma apply_reified_phis_matches {Pa : Params} :
  forall pevals dvs (penv : param_env Pa) lmap env,
    lmap_matches_env penv lmap env ->
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs ->
    lmap_matches_env penv (apply_reified_phis lmap pevals) (apply_phi_env env dvs).
Proof.
  intros pevals dvs penv lmap env Henv Hfa2; revert lmap env Henv;
    induction Hfa2 as [| [[id w] ce] [id' dv] restp restdvs Hpair Hrest IH];
    intros lmap env Henv; cbn [apply_reified_phis apply_phi_env]; [exact Henv |].
  destruct Hpair as [Heq [Hev Hsc]]; subst id'.
  exact (IH _ _ (lmap_matches_env_add penv lmap env id w ce dv Henv Hev Hsc)).
Qed.

Lemma pevals_ub_free_split : forall pevals,
  pevals_ub_free pevals = true ->
  forall id w ce, In (id, w, ce) pevals -> ub_free_expr ce = true.
Proof.
  intros pevals H id w ce Hin; unfold pevals_ub_free in H; rewrite forallb_forall in H.
  exact (H (id, w, ce) Hin).
Qed.

Fixpoint overlay_penv {Pa : Params} (binds : list (string * @dvalue Pa)) (base : param_env Pa)
  : param_env Pa :=
  fun nm =>
    match binds with
    | [] => base nm
    | (x, dv) :: rest => if String.eqb nm x then Some dv else overlay_penv rest base nm
    end.

Lemma overlay_penv_lookup_in {Pa : Params} :
  forall (binds : list (string * @dvalue Pa)) (base : param_env Pa) x dv,
    NoDup (List.map fst binds) ->
    In (x, dv) binds ->
    overlay_penv binds base x = Some dv.
Proof.
  induction binds as [| [y v] rest IH]; intros base x dv Hnd Hin; [contradiction |].
  inversion Hnd as [| ? ? Hnin Hnd']; subst; cbn [overlay_penv List.map] in *.
  destruct Hin as [Heq | Hinr].
  - inversion Heq; subst; rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb x y) eqn:Exy; [| exact (IH base x dv Hnd' Hinr)].
    apply String.eqb_eq in Exy; subst y; exfalso; apply Hnin, in_map_iff; exists (x, dv); split; [reflexivity | exact Hinr].
Qed.

Lemma overlay_penv_not_in {Pa : Params} :
  forall (binds : list (string * @dvalue Pa)) (base : param_env Pa) nm,
    ~ In nm (List.map fst binds) ->
    overlay_penv binds base nm = base nm.
Proof.
  induction binds as [| [y v] rest IH]; intros base nm Hnin; cbn [overlay_penv List.map] in *; [reflexivity |].
  destruct (String.eqb nm y) eqn:Eny.
  - apply String.eqb_eq in Eny; subst y; exfalso; apply Hnin; left; reflexivity.
  - apply IH; intro H; apply Hnin; right; exact H.
Qed.

Lemma overlay_penv_non_bang {Pa : Params} :
  forall (binds : list (string * @dvalue Pa)) (base : param_env Pa) nm,
    (forall y, In y (List.map fst binds) -> mc_starts_with_bang y = true) ->
    mc_starts_with_bang nm = false ->
    overlay_penv binds base nm = base nm.
Proof.
  intros binds base nm Hbang Hnb; apply overlay_penv_not_in.
  intro Hin; rewrite (Hbang nm Hin) in Hnb; discriminate Hnb.
Qed.

Lemma mc_sp_aligned16_bounds : forall sp_off,
  mc_sp_aligned16 sp_off = true -> (- mc_frame_cap <= sp_off <= 0)%Z.
Proof.
  intros sp_off H; unfold mc_sp_aligned16 in H; rewrite !andb_true_iff in H; destruct H as [[Hlo Hhi] _].
  split; apply Z.leb_le; assumption.
Qed.

Lemma NoDup_app_intro : forall {A : Type} (xs ys : list A),
  NoDup xs -> NoDup ys -> (forall x, In x xs -> ~ In x ys) -> NoDup (xs ++ ys).
Proof.
  intros A xs; induction xs as [| x rx IH]; intros ys Hxs Hys Hdisj; cbn [app]; [exact Hys |].
  inversion Hxs as [| ? ? Hnin Hrx]; subst; constructor.
  - intro Hin; apply in_app_iff in Hin as [Hx | Hy]; [exact (Hnin Hx) | exact (Hdisj x (or_introl eq_refl) Hy)].
  - exact (IH ys Hrx Hys (fun y Hy => Hdisj y (or_intror Hy))).
Qed.

Lemma init_param_lmap_dom : forall params pnames uses r w ce,
  RM.find r (init_param_lmap params pnames uses) = Some (w, ce) ->
  exists pnm, ce = CE_Var pnm w /\ In pnm pnames.
Proof.
  intros params pnames uses; induction uses as [| [idx dt] rest IH]; intros r w ce Hf.
  - cbn [init_param_lmap] in Hf; rewrite RMF.F.empty_o in Hf; discriminate Hf.
  - destruct dt as [[w0 | | | | | | | | | |] | |]; cbn [init_param_lmap] in Hf;
      try exact (IH r w ce Hf).
    destruct (is_supported_bit_width w0); [| exact (IH r w ce Hf)].
    destruct (nth_error params idx) as [r0 |]; [| exact (IH r w ce Hf)].
    destruct (nth_error pnames idx) as [pnm |] eqn:Hpnm; [| exact (IH r w ce Hf)].
    destruct (starts_with_dollar pnm); [exact (IH r w ce Hf) |].
    destruct (RawIDOrd.eq_dec r0 r) as [<- | Hneq].
    + rewrite RMF.F.add_eq_o in Hf by reflexivity; inversion Hf; subst w0 ce.
      exists pnm; split; [reflexivity | exact (nth_error_In pnames idx Hpnm)].
    + rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (IH r w ce Hf).
Qed.

(** ** 2. Single-CNF Multi-Obligation SAT/LRAT Discharger *)

(** ** 3. Single-CNF Multi-Obligation SAT/LRAT Discharger ([check_mc_loop_obls]) *)

Inductive mc_loop_obl : Set :=
| MLO_Refine (is_body : bool) (path : list (bool * cert_expr)) (w : positive) (e_src e_tgt : cert_expr)
| MLO_Defined (is_body : bool) (path : list (bool * cert_expr)) (w : positive) (e : cert_expr).

Definition obl_is_body (o : mc_loop_obl) : bool :=
  match o with
  | MLO_Refine ib _ _ _ _ => ib
  | MLO_Defined ib _ _ _ => ib
  end.

Definition obl_path (o : mc_loop_obl) : list (bool * cert_expr) :=
  match o with
  | MLO_Refine _ p _ _ _ => p
  | MLO_Defined _ p _ _ => p
  end.

Definition obl_wf_exprs (allowed : list (string * positive)) (o : mc_loop_obl) : bool :=
  forallb (fun '(_, c) =>
    wt_cert_expr [] c && Pos.eqb (cert_expr_bit_width c) 1%positive &&
    is_let_free_expr c && ub_free_expr c &&
    vars_subset_b (collect_free_vars [] c) allowed) (obl_path o) &&
  match o with
  | MLO_Refine _ _ w s t =>
      wt_cert_expr [] s && wt_cert_expr [] t &&
      Pos.eqb (cert_expr_bit_width s) w && Pos.eqb (cert_expr_bit_width t) w &&
      is_let_free_expr s && is_let_free_expr t &&
      ub_free_expr s && ub_free_expr t &&
      vars_subset_b (collect_free_vars [] s) allowed &&
      vars_subset_b (collect_free_vars [] t) allowed
  | MLO_Defined _ _ w e =>
      wt_cert_expr [] e && Pos.eqb (cert_expr_bit_width e) w &&
      is_let_free_expr e && ub_free_expr e &&
      vars_subset_b (collect_free_vars [] e) allowed
  end.

Lemma blast_refinement_cex_opt_gates_step :
  forall (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv)
         (st : blast_state) (asg : positive -> bool) cex_lit st',
    sat_blast_st asg st ->
    wf_lit_bound (bs_next_var st) src_no_ub ->
    wf_rail_bound sz (bs_next_var st) src_r ->
    wf_rail_bound sz (bs_next_var st) tgt_r ->
    blast_refinement_cex_opt_gates sz src_no_ub src_r tgt_r st = (cex_lit, st') ->
    exists asg',
      step_spec st st' asg asg' /\
      wf_lit_bound (bs_next_var st') cex_lit /\
      (eval_lit asg' cex_lit = false ->
       eval_lit asg src_no_ub = true ->
       eval_rail_psn asg src_r = false ->
       eval_rail_psn asg tgt_r = false /\
       eval_rail_val sz asg tgt_r = eval_rail_val sz asg src_r).
Proof.
  intros sz src_no_ub src_r tgt_r st asg cex_lit st' Hsat Hnub Hbs Hbt Hgates.
  destruct Hbs as ((Hws & Hls) & Hbs0 & Hps).
  destruct Hbt as ((Hwt & Hlt) & Hbt0 & Hpt).
  unfold blast_refinement_cex_opt_gates in Hgates.
  destruct (map2_emit emit_xor2_opt (rbv_bits src_r) (rbv_bits tgt_r) st) as [xor_bits st1] eqn:Hm.
  destruct (emit_or_list_opt xor_bits st1) as [val_diff st2] eqn:Horl.
  destruct (emit_or2_opt (rbv_psn tgt_r) val_diff st2) as [bad_tgt st3] eqn:Hbad.
  destruct (emit_and2_opt (neg_lit (rbv_psn src_r)) bad_tgt st3) as [def_bad st4] eqn:Hdef.
  destruct (emit_and2_opt src_no_ub def_bad st4) as [cex_lit0 st5] eqn:Hcex.
  inversion Hgates; subst cex_lit0 st5; clear Hgates.
  assert (Hlen_st : List.length (rbv_bits src_r) = List.length (rbv_bits tgt_r)) by congruence.
  destruct (map2_emit_step emit_xor2_opt xorb emit_xor2_opt_step _ _ asg st xor_bits st1
              Hlen_st Hbs0 Hbt0 Hsat Hm)
    as (asg1 & Hs1 & Hxlen & Hxwf & Hxev).
  destruct (emit_or_list_opt_step xor_bits asg1 st1 val_diff st2 Hxwf (proj2 (proj2 Hs1)) Horl)
    as (asg2 & Hs2 & Hvd_wf & Hvd_ev).
  pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs12.
  destruct (emit_or2_opt_step asg2 (rbv_psn tgt_r) val_diff st2 bad_tgt st3 (proj2 (proj2 Hs2))
              (wf_lit_bound_mono _ _ _ (proj1 Hs12) Hpt) Hvd_wf Hbad)
    as (asg3 & Hs3 & Hbt_wf & Hbt_ev).
  pose proof (step_spec_trans st st2 st3 asg asg2 asg3 Hs12 Hs3) as Hs13.
  destruct (emit_and2_opt_step asg3 (neg_lit (rbv_psn src_r)) bad_tgt st3 def_bad st4
              (proj2 (proj2 Hs3))
              (wf_lit_bound_neg _ _ (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hps))
              Hbt_wf Hdef)
    as (asg4 & Hs4 & Hdb_wf & Hdb_ev).
  pose proof (step_spec_trans st st3 st4 asg asg3 asg4 Hs13 Hs4) as Hs14.
  destruct (emit_and2_opt_step asg4 src_no_ub def_bad st4 cex_lit st' (proj2 (proj2 Hs4))
              (wf_lit_bound_mono _ _ _ (proj1 Hs14) Hnub) Hdb_wf Hcex)
    as (asg5 & Hs5 & Hcx_wf & Hcx_ev).
  pose proof (step_spec_trans st st4 st' asg asg4 asg5 Hs14 Hs5) as Hs15.
  exists asg5; split; [exact Hs15 | split; [exact Hcx_wf |]].
  intros Hqf Hno_ub Hps_f.
  unfold eval_rail_psn in Hps_f.
  rewrite Hcx_ev,
          (step_spec_eval_lit st st4 asg asg4 src_no_ub Hs14 Hnub),
          Hno_ub, Hdb_ev,
          (eval_neg_lit_nonzero asg3 (rbv_psn src_r) (wf_lit_bound_nonzero _ _ (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hps))),
          (step_spec_eval_lit st st3 asg asg3 (rbv_psn src_r) Hs13 Hps),
          Hps_f, Hbt_ev,
          (step_spec_eval_lit st st2 asg asg2 (rbv_psn tgt_r) Hs12 Hpt),
          Hvd_ev in Hqf.
  cbn [andb] in Hqf; apply orb_false_iff in Hqf as [Htgt_def Hxor_false].
  split; [exact Htgt_def |].
  destruct (eval_rail_agree sz _ asg asg1 src_r (proj1 (proj2 Hs1)) (conj (conj Hws Hls) (conj Hbs0 Hps))) as [_ Hvs1].
  destruct (eval_rail_agree sz _ asg asg1 tgt_r (proj1 (proj2 Hs1)) (conj (conj Hwt Hlt) (conj Hbt0 Hpt))) as [_ Hvt1].
  rewrite Hvs1, Hvt1.
  apply (existsb_xor_bits_diff sz asg1 src_r tgt_r xor_bits (conj Hws Hls) (conj Hwt Hlt)); [congruence | |].
  - intros k Hk.
    unfold wf_lits_bound in Hbs0, Hbt0; rewrite Forall_forall in Hbs0, Hbt0.
    assert (Hs_eq : List.map (eval_lit asg1) (rbv_bits src_r) = List.map (eval_lit asg) (rbv_bits src_r))
      by (apply map_ext_in; intros l Hl; exact (step_spec_eval_lit _ _ _ _ _ Hs1 (Hbs0 l Hl))).
    assert (Ht_eq : List.map (eval_lit asg1) (rbv_bits tgt_r) = List.map (eval_lit asg) (rbv_bits tgt_r))
      by (apply map_ext_in; intros l Hl; exact (step_spec_eval_lit _ _ _ _ _ Hs1 (Hbt0 l Hl))).
    rewrite Hxev, Hs_eq, Ht_eq.
    clear -Hws Hls Hwt Hlt Hk.
    remember (List.map (eval_lit asg) (rbv_bits src_r)) as xs eqn:Exs.
    remember (List.map (eval_lit asg) (rbv_bits tgt_r)) as ys eqn:Eys.
    assert (Hlen_xs : (k < List.length xs)%nat) by (subst xs; rewrite length_map; congruence).
    assert (Hlen_eq : List.length xs = List.length ys) by (subst xs ys; rewrite !length_map; congruence).
    clear -Hlen_xs Hlen_eq; revert xs ys Hlen_xs Hlen_eq.
    induction k as [| k' IHk]; intros [| x rx] [| y ry] Hlt Hleq; cbn in *; try lia;
      [reflexivity | exact (IHk rx ry ltac:(lia) ltac:(lia))].
  - rewrite <- existsb_id_map_eval_lit; exact Hxor_false.
Qed.

Definition mc_ms_opt (e : cert_expr) : option (sized_let_map * nat) :=
  if expr_has_freeze e then Some ([], default_let_expand_budget) else None.

Fixpoint emit_path_lits
  (ctx : ub_ctx) (g_lit : lit) (path : list (bool * cert_expr)) (env : blast_env)
  {struct path} : option (lit * blast_env) :=
  match path with
  | [] => Some (g_lit, env)
  | (b, c) :: rest =>
      match blast_cert_expr ctx [] (mc_ms_opt c) c env with
      | None => None
      | Some (rc, env1) =>
          let b0 := match rbv_bits rc with x :: _ => if b then x else neg_lit x | [] => lit_false end in
          let '(cond_lit, st1) := emit_and2_opt (neg_lit (rbv_psn rc)) b0 (be_st env1) in
          let '(g', st2) := emit_and2_opt g_lit cond_lit st1 in
          emit_path_lits ctx g' rest (mk_blast_env st2 (be_vars env1) (be_freezes env1))
      end
  end.

Definition blast_mc_obl
  (ctx : ub_ctx) (body_hyp_lit : lit) (env : blast_env) (o : mc_loop_obl)
  : option (lit * blast_env) :=
  let g0 := if obl_is_body o then body_hyp_lit else lit_true in
  match emit_path_lits ctx g0 (obl_path o) env with
  | None => None
  | Some (g_lit, env1) =>
      match o with
      | MLO_Refine _ _ w e_src e_tgt =>
          match blast_cert_expr ctx [] (mc_ms_opt e_src) e_src env1 with
          | None => None
          | Some (rs, env2) =>
              match blast_cert_expr ctx [] (mc_ms_opt e_tgt) e_tgt env2 with
              | None => None
              | Some (rt, env3) =>
                  let '(cex, st4) := blast_refinement_cex_opt_gates w g_lit rs rt (be_st env3) in
                  Some (cex, mk_blast_env st4 (be_vars env3) (be_freezes env3))
              end
          end
      | MLO_Defined _ _ w e =>
          match blast_cert_expr ctx [] (mc_ms_opt e) e env1 with
          | None => None
          | Some (re, env2) =>
              let '(cex, st3) := emit_and2_opt g_lit (rbv_psn re) (be_st env2) in
              Some (cex, mk_blast_env st3 (be_vars env2) (be_freezes env2))
          end
      end
  end.

Fixpoint mc_filter_tr_acc {A : Type} (p : A -> bool) (acc xs : list A) {struct xs} : list A :=
  match xs with
  | [] => elf_rev_tr acc
  | x :: rest => mc_filter_tr_acc p (if p x then x :: acc else acc) rest
  end.

Definition mc_filter_tr {A : Type} (p : A -> bool) (xs : list A) : list A :=
  mc_filter_tr_acc p [] xs.

Lemma mc_filter_tr_acc_eq : forall {A : Type} (p : A -> bool) (acc xs : list A),
  mc_filter_tr_acc p acc xs = List.rev_append acc (List.filter p xs).
Proof.
  intros A p acc xs; revert acc; induction xs as [| x rest IH]; intro acc;
    cbn [mc_filter_tr_acc List.filter].
  - unfold elf_rev_tr; reflexivity.
  - destruct (p x); rewrite IH; reflexivity.
Qed.

Lemma mc_filter_tr_eq : forall {A : Type} (p : A -> bool) (xs : list A),
  mc_filter_tr p xs = List.filter p xs.
Proof.
  intros A p xs; unfold mc_filter_tr; exact (mc_filter_tr_acc_eq p [] xs).
Qed.

Fixpoint blast_mc_obls_list_acc
  (ctx : ub_ctx) (body_hyp_lit : lit) (obls : list mc_loop_obl)
  (env : blast_env) (acc : list lit)
  {struct obls} : option (list lit * blast_env) :=
  match obls with
  | [] => Some (elf_rev_tr acc, env)
  | o :: rest =>
      match blast_mc_obl ctx body_hyp_lit env o with
      | None => None
      | Some (cex, env1) =>
          blast_mc_obls_list_acc ctx body_hyp_lit rest env1 (cex :: acc)
      end
  end.

Definition blast_mc_obls_list
  (ctx : ub_ctx) (body_hyp_lit : lit) (obls : list mc_loop_obl) (env : blast_env)
  : option (list lit * blast_env) :=
  blast_mc_obls_list_acc ctx body_hyp_lit obls env [].

Definition obl_is_alg_ok (ctx : ub_ctx) (o : mc_loop_obl) : bool :=
  match o with
  | MLO_Refine false [] _ s t => check_expr_refines ctx s t
  | _ => false
  end.

Fixpoint check_obls_wf_diag_acc
  (tag : string) (known_vars : list (string * positive))
  (idx : nat) (obls : list mc_loop_obl) {struct obls} : string + unit :=
  match obls with
  | [] => inr tt
  | o :: rest =>
      if obl_wf_exprs known_vars o then
        check_obls_wf_diag_acc tag known_vars (S idx) rest
      else
        let phase := if obl_is_body o then "body" else "entry" in
        inl (diag (tag ++ "-obl")%string
          ("ill-typed or ill-scoped " ++ phase ++ " obligation #" ++ diag_nat_dec idx))
  end.

Lemma check_obls_wf_diag_acc_sound : forall tag known_vars idx obls,
  check_obls_wf_diag_acc tag known_vars idx obls = inr tt ->
  forallb (obl_wf_exprs known_vars) obls = true.
Proof.
  intros tag known_vars idx obls; revert idx;
    induction obls as [| o rest IH]; intros idx H; cbn in *; [reflexivity |].
  destruct (obl_wf_exprs known_vars o) eqn:Ho; [| discriminate H].
  cbn; exact (IH (S idx) H).
Qed.

Definition build_mc_loop_cnf
  (tag : string) (ctx : ub_ctx) (known_vars : list (string * positive))
  (opt_inv : option cert_expr) (obls : list mc_loop_obl)
  : string + (positive * cnf) :=
  match check_obls_wf_diag_acc tag known_vars 0%nat obls with
  | inl err => inl err
  | inr tt =>
      let init_env := mk_blast_env (init_blast_state 2%positive) [] [] in
      let env0 := blast_ub_ctx ctx known_vars ctx init_env in
      let hyp_res : string + (lit * blast_env) :=
        match opt_inv with
        | None => inr (lit_true, env0)
        | Some inv_e =>
            if wt_cert_expr [] inv_e && Pos.eqb (cert_expr_bit_width inv_e) 1%positive &&
               is_let_free_expr inv_e && ub_free_expr inv_e &&
               vars_subset_b (collect_free_vars [] inv_e) known_vars
            then
              match blast_cert_expr ctx [] (mc_ms_opt inv_e) inv_e env0 with
              | None =>
                  inl (diag (tag ++ "-blast")%string "failed to bit-blast loop invariant")
              | Some (ri, env_i) =>
                  let b0 := match rbv_bits ri with x :: _ => x | [] => lit_false end in
                  let '(hlit, st1) := emit_and2_opt (neg_lit (rbv_psn ri)) b0 (be_st env_i) in
                  inr (hlit, mk_blast_env st1 (be_vars env_i) (be_freezes env_i))
              end
            else inl (diag (tag ++ "-inv")%string "loop invariant expression failed typing or variable-scope check")
        end in
      match hyp_res with
      | inl err => inl err
      | inr (body_hyp_lit, env1) =>
          match blast_mc_obls_list ctx body_hyp_lit obls env1 with
          | None =>
              inl (diag (tag ++ "-blast")%string
                ("failed to bit-blast " ++ diag_nat_dec (List.length obls) ++ " obligation(s)"))
          | Some (cex_lits, env2) =>
              let '(any_cex, st_or) := emit_or_list_opt cex_lits (be_st env2) in
              let st_fin := add_clauses [[any_cex]] st_or in
              inr (Pos.pred (bs_next_var st_fin), bs_cnf st_fin)
          end
      end
  end.

Definition check_mc_loop_obls
  (tag : string) (ctx : ub_ctx) (known_vars : list (string * positive))
  (opt_inv : option cert_expr) (obls : list mc_loop_obl)
  (opt_pf : option (list lrat_step)) : string + unit :=
  match check_obls_wf_diag_acc tag known_vars 0%nat obls with
  | inl err => inl err
  | inr tt =>
      let rem := mc_filter_tr (fun o => negb (obl_is_alg_ok ctx o)) obls in
      match rem with
      | [] => inr tt
      | _ :: _ =>
          match build_mc_loop_cnf tag ctx known_vars opt_inv rem with
          | inl err => inl err
          | inr (nv, f) =>
              if check_cex_unsat f opt_pf then inr tt
              else
                match opt_pf with
                | None =>
                    inl (diag (tag ++ "-sat")%string
                      ("bounded SAT solver failed to discharge " ++
                       diag_nat_dec (List.length rem) ++ " obligation(s) (" ++
                       diag_pos_dec nv ++ " vars)"))
                | Some pf =>
                    inl (diag "lrat-check"
                      ("LRAT proof (" ++ diag_nat_dec (List.length pf) ++
                       " step(s)) failed to discharge " ++ diag_nat_dec (List.length rem) ++
                       " obligation(s) (" ++ diag_pos_dec nv ++ " vars)"))
                end
          end
      end
  end.

Definition emit_mc_loop_cnf
  (tag : string) (ctx : ub_ctx) (known_vars : list (string * positive))
  (opt_inv : option cert_expr) (obls : list mc_loop_obl)
  : string + option (positive * cnf) :=
  match check_obls_wf_diag_acc tag known_vars 0%nat obls with
  | inl err => inl err
  | inr tt =>
      let rem := mc_filter_tr (fun o => negb (obl_is_alg_ok ctx o)) obls in
      match rem with
      | [] => inr None
      | _ :: _ =>
          match build_mc_loop_cnf tag ctx known_vars opt_inv rem with
          | inl err => inl err
          | inr nf => inr (Some nf)
          end
      end
  end.

Definition mc_obl_holds {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (opt_inv : option cert_expr) (is_body_mode : bool) (o : mc_loop_obl) : Prop :=
  (obl_is_body o = is_body_mode) ->
  (is_body_mode = true ->
   match opt_inv with
   | None => True
   | Some inv_e =>
       eval_closed_cert_expr penv foracle inv_e =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
   end) ->
  (forall b c, In (b, c) (obl_path o) ->
     eval_closed_cert_expr penv foracle c =
     raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
       (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
  match o with
  | MLO_Refine _ _ _ e_src e_tgt =>
      refine_eou_dvalue (eval_closed_cert_expr penv foracle e_src)
                        (eval_closed_cert_expr penv foracle e_tgt)
  | MLO_Defined _ _ w e =>
      exists (v : @Integers.bit_int w),
        eval_closed_cert_expr penv foracle e =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w v))
  end.

Lemma mc_ms_opt_sync {Pa : Params} : forall e,
  wf_ms_sync (@nil (string * (@dvalue Pa * cert_expr))) (mc_ms_opt e).
Proof.
  intro e; unfold mc_ms_opt; destruct (expr_has_freeze e);
    cbn [wf_ms_sync strip_let_sizes let_val_exprs List.map]; trivial.
Qed.

Lemma emit_path_lits_sat {Pa : Params} :
  forall ctx (penv : param_env Pa) foracle known_vars g_lit path env out_lit env' asg,
    forallb (fun '(_, c) =>
      wt_cert_expr [] c && Pos.eqb (cert_expr_bit_width c) 1%positive &&
      is_let_free_expr c && ub_free_expr c &&
      vars_subset_b (collect_free_vars [] c) known_vars) path = true ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    wf_lit_bound (bs_next_var (be_st env)) g_lit ->
    emit_path_lits ctx g_lit path env = Some (out_lit, env') ->
    exists asg',
      step_spec (be_st env) (be_st env') asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_lit_bound (bs_next_var (be_st env')) out_lit /\
      (eval_lit asg g_lit = true ->
       (forall b c, In (b, c) path ->
          eval_closed_cert_expr penv foracle c =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
            (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
       eval_lit asg' out_lit = true).
Proof.
  intros ctx penv foracle known_vars g_lit path; revert g_lit.
  induction path as [| [b c] rest IH];
    intros g_lit env out_lit env' asg Hwf Hpenv Hctx Henv Hwg Hem;
    cbn [emit_path_lits] in Hem.
  - inversion Hem; subst out_lit env'; exists asg.
    split; [exact (step_spec_refl _ _ (proj1 Henv)) | split; [exact Henv | split; [exact Hwg | intros Hg _; exact Hg]]].
  - cbn [forallb] in Hwf; apply andb_true_iff in Hwf as [Hc Hrest].
    rewrite !andb_true_iff in Hc; destruct Hc as ((((Hwt & Hbw1) & Hlf) & _) & Hsub).
    apply Pos.eqb_eq in Hbw1.
    destruct (blast_cert_expr ctx [] (mc_ms_opt c) c env) as [[rc env1] |] eqn:Ebc; [| discriminate Hem].
    destruct (emit_and2_opt (neg_lit (rbv_psn rc))
                match rbv_bits rc with x :: _ => if b then x else neg_lit x | [] => lit_false end (be_st env1))
      as [cond_lit st1] eqn:Ea1.
    destruct (emit_and2_opt g_lit cond_lit st1) as [g' st2] eqn:Ea2.
    destruct (blast_cert_expr_sat c ctx [] [] (mc_ms_opt c) penv [] foracle asg env env1 rc
                Ebc Hwt (wf_let_rails_sync_nil asg _) (mc_ms_opt_sync c)
                (vars_subset_b_wf_param_env _ _ penv Hsub Hpenv) Hctx Henv)
      as (asg1 & vc & Evc & Hs1 & Henv1 & Hwfc & Hmrc).
    rewrite Hbw1 in Hwfc, Hmrc.
    destruct Hwfc as ((Hrwc & Hlen1) & Hlbs1 & Hps1).
    destruct (rbv_bits rc) as [| b0 rbits] eqn:Ebits; [cbn in Hlen1; discriminate Hlen1 |].
    assert (Hb0_wf : wf_lit_bound (bs_next_var (be_st env1)) (if b then b0 else neg_lit b0)).
    { inversion Hlbs1; destruct b; [exact H1 | apply wf_lit_bound_neg; exact H1]. }
    destruct (emit_and2_opt_step asg1 (neg_lit (rbv_psn rc)) (if b then b0 else neg_lit b0) (be_st env1) cond_lit st1
                (proj1 Henv1) (wf_lit_bound_neg _ _ Hps1) Hb0_wf Ea1)
      as (asg2 & Hs2 & Hwc_wf & Hwc_ev).
    pose proof (step_spec_trans (be_st env) (be_st env1) st1 asg asg1 asg2 Hs1 Hs2) as Hs12.
    destruct (emit_and2_opt_step asg2 g_lit cond_lit st1 g' st2 (proj2 (proj2 Hs2))
                (wf_lit_bound_mono _ _ _ (proj1 Hs12) Hwg) Hwc_wf Ea2)
      as (asg3 & Hs3 & Hwg'_wf & Hwg'_ev).
    pose proof (step_spec_trans (be_st env) st1 st2 asg asg2 asg3 Hs12 Hs3) as Hs13.
    pose proof (sat_blast_env_step penv foracle asg1 asg3 env1 st2 Henv1 (step_spec_trans _ _ _ _ _ _ Hs2 Hs3)) as Henv3.
    destruct (IH g' (mk_blast_env st2 (be_vars env1) (be_freezes env1)) out_lit env' asg3
                Hrest Hpenv Hctx Henv3 Hwg'_wf Hem)
      as (asg4 & Hs4 & Henv4 & Hwo_wf & Hwo_ev).
    exists asg4; split; [exact (step_spec_trans _ _ _ _ _ _ Hs13 Hs4) | split; [exact Henv4 | split; [exact Hwo_wf |]]].
    intros Hg Hpath; apply Hwo_ev; [| intros b1 c1 Hc1; apply Hpath; right; exact Hc1].
    rewrite Hwg'_ev, (step_spec_eval_lit _ _ _ _ _ Hs12 Hwg), Hg, Hwc_ev,
            (eval_neg_lit_nonzero asg1 (rbv_psn rc) (wf_lit_bound_nonzero _ _ Hps1)).
    pose proof (Hpath b c (or_introl eq_refl)) as Hpc.
    unfold eval_closed_cert_expr in Hpc; rewrite Evc in Hpc; inversion Hpc; subst vc; clear Hpc.
    unfold rail_matches_dvalue in Hmrc.
    destruct (eval_rail_psn asg1 rc) eqn:Eps; [discriminate Hmrc |].
    unfold eval_rail_val in Hmrc; rewrite Ebits in Hmrc.
    unfold eval_rail_psn in Eps; rewrite Eps; cbn [negb andb].
    pose proof (f_equal dvalue_int_unsigned Hmrc) as Hu; cbn in Hu.
    destruct rbits as [| ? ?]; [| cbn in Hlen1; discriminate Hlen1].
    assert (Hevb0 : eval_lit asg1 b0 = b).
    { destruct b;
        rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive) in Hu;
        destruct (eval_lit asg1 b0); try reflexivity;
        cbn [List.map bools_to_Z Zshiftin dvalue_int_unsigned] in Hu;
        rewrite Integers.unsigned_repr in Hu by (change (@Integers.max_unsigned 1%positive) with 1%Z; lia); lia. }
    destruct b; [exact Hevb0 |].
    rewrite (eval_neg_lit_nonzero asg1 b0 (wf_lit_bound_nonzero _ _ ltac:(inversion Hlbs1; exact H1))), Hevb0; reflexivity.
Qed.

Lemma blast_mc_obl_sat {Pa : Params} :
  forall ctx (penv : param_env Pa) foracle known_vars opt_inv is_body_mode body_hyp_lit env o cex env' asg,
    obl_wf_exprs known_vars o = true ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    wf_lit_bound (bs_next_var (be_st env)) body_hyp_lit ->
    (is_body_mode = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv foracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end ->
     eval_lit asg body_hyp_lit = true) ->
    blast_mc_obl ctx body_hyp_lit env o = Some (cex, env') ->
    exists asg',
      step_spec (be_st env) (be_st env') asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_lit_bound (bs_next_var (be_st env')) cex /\
      (eval_lit asg' cex = false -> mc_obl_holds penv foracle opt_inv is_body_mode o).
Proof.
  intros ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit env o cex env' asg
         Hwf Hpenv Hctx Henv Hwbh Hbh_true Hbl.
  unfold obl_wf_exprs in Hwf; apply andb_true_iff in Hwf as [Hwfp Hwfo].
  unfold blast_mc_obl in Hbl.
  set (g0 := if obl_is_body o then body_hyp_lit else lit_true) in *.
  assert (Hwg0 : wf_lit_bound (bs_next_var (be_st env)) g0).
  { unfold g0; destruct (obl_is_body o); [exact Hwbh | cbn; pose proof (proj1 (proj1 (proj1 Henv))); lia]. }
  destruct (emit_path_lits ctx g0 (obl_path o) env) as [[g_lit env1] |] eqn:Epl; [| discriminate Hbl].
  destruct (emit_path_lits_sat ctx penv foracle known_vars g0 (obl_path o) env g_lit env1 asg
              Hwfp Hpenv Hctx Henv Hwg0 Epl)
    as (asg1 & Hs1 & Henv1 & Hwg1 & Hg1_true).
  destruct o as [ib p w s t | ib p w e]; cbn [obl_is_body obl_path] in *.
  - rewrite !andb_true_iff in Hwfo; destruct Hwfo as (((((((((Hwts & Hwtt) & Hbws) & Hbwt) & Hlfs) & Hlft) & _) & _) & Hsubs) & Hsubt).
    apply Pos.eqb_eq in Hbws; apply Pos.eqb_eq in Hbwt.
    destruct (blast_cert_expr ctx [] (mc_ms_opt s) s env1) as [[rs env2] |] eqn:Ebs; [| discriminate Hbl].
    destruct (blast_cert_expr ctx [] (mc_ms_opt t) t env2) as [[rt env3] |] eqn:Ebt; [| discriminate Hbl].
    destruct (blast_refinement_cex_opt_gates w g_lit rs rt (be_st env3)) as [cex0 st4] eqn:Hgat.
    inversion Hbl; subst cex0 env'; clear Hbl.
    destruct (blast_cert_expr_sat s ctx [] [] (mc_ms_opt s) penv [] foracle asg1 env1 env2 rs
                Ebs Hwts (wf_let_rails_sync_nil asg1 _) (mc_ms_opt_sync s)
                (vars_subset_b_wf_param_env _ _ penv Hsubs Hpenv) Hctx Henv1)
      as (asg2 & vs & Evs & Hs2 & Henv2 & Hwfs & Hms).
    destruct (blast_cert_expr_sat t ctx [] [] (mc_ms_opt t) penv [] foracle asg2 env2 env3 rt
                Ebt Hwtt (wf_let_rails_sync_nil asg2 _) (mc_ms_opt_sync t)
                (vars_subset_b_wf_param_env _ _ penv Hsubt Hpenv) Hctx Henv2)
      as (asg3 & vt & Evt & Hs3 & Henv3 & Hwft & Hmt).
    pose proof (step_spec_trans _ _ _ _ _ _ Hs2 Hs3) as Hs23.
    rewrite Hbws in Hwfs, Hms; rewrite Hbwt in Hwft, Hmt.
    pose proof (wf_rail_bound_mono w _ _ rs (proj1 Hs3) Hwfs) as Hwfs3.
    pose proof (wf_lit_bound_mono _ _ g_lit (proj1 Hs23) Hwg1) as Hwg3.
    destruct (blast_refinement_cex_opt_gates_step w g_lit rs rt (be_st env3) asg3 cex st4
                (proj1 Henv3) Hwg3 Hwfs3 Hwft Hgat)
      as (asg4 & Hs4 & Hwcex & Hcex_sound).
    pose proof (sat_blast_env_step penv foracle asg3 asg4 env3 st4 Henv3 Hs4) as Henv4.
    exists asg4; split; [exact (step_spec_trans _ _ _ _ _ _ Hs1 (step_spec_trans _ _ _ _ _ _ Hs23 Hs4))
                       | split; [exact Henv4 | split; [exact Hwcex |]]].
    intros Hqf Hib Hinv Hpath; unfold eval_closed_cert_expr; rewrite Evs, Evt; cbn [refine_eou_dvalue].
    pose proof (rail_matches_dvalue_agree w _ asg2 asg3 rs vs (proj1 (proj2 Hs3)) Hwfs Hms) as Hms3.
    unfold rail_matches_dvalue in Hms3, Hmt.
    destruct (eval_rail_psn asg3 rs) eqn:Eps; [subst vs; apply dvalue_refines_poison_l |].
    assert (Hg3 : eval_lit asg3 g_lit = true).
    { rewrite (step_spec_eval_lit _ _ _ _ _ Hs23 Hwg1); apply Hg1_true; [| exact Hpath].
      cbn [obl_is_body] in Hib; subst ib; unfold g0; destruct is_body_mode.
      - exact (Hbh_true eq_refl (Hinv eq_refl)).
      - exact (proj1 (proj2 (proj1 Henv))). }
    destruct (Hcex_sound Hqf Hg3 eq_refl) as [Ept Heqv].
    rewrite Ept, Heqv in Hmt; subst vs vt; apply dvalue_refines_refl.
  - rewrite !andb_true_iff in Hwfo; destruct Hwfo as ((((Hwte & Hbwe) & Hlfe) & _) & Hsube).
    apply Pos.eqb_eq in Hbwe.
    destruct (blast_cert_expr ctx [] (mc_ms_opt e) e env1) as [[re env2] |] eqn:Ebe; [| discriminate Hbl].
    destruct (emit_and2_opt g_lit (rbv_psn re) (be_st env2)) as [cex0 st3] eqn:Ea2.
    inversion Hbl; subst cex0 env'; clear Hbl.
    destruct (blast_cert_expr_sat e ctx [] [] (mc_ms_opt e) penv [] foracle asg1 env1 env2 re
                Ebe Hwte (wf_let_rails_sync_nil asg1 _) (mc_ms_opt_sync e)
                (vars_subset_b_wf_param_env _ _ penv Hsube Hpenv) Hctx Henv1)
      as (asg2 & ve & Eve & Hs2 & Henv2 & Hwfe & Hme).
    rewrite Hbwe in Hwfe, Hme.
    destruct (emit_and2_opt_step asg2 g_lit (rbv_psn re) (be_st env2) cex st3 (proj1 Henv2)
                (wf_lit_bound_mono _ _ _ (proj1 Hs2) Hwg1) (proj2 (proj2 Hwfe)) Ea2)
      as (asg3 & Hs3 & Hwcex & Hevcex).
    pose proof (sat_blast_env_step penv foracle asg2 asg3 env2 st3 Henv2 Hs3) as Henv3.
    exists asg3; split; [exact (step_spec_trans _ _ _ _ _ _ Hs1 (step_spec_trans _ _ _ _ _ _ Hs2 Hs3))
                       | split; [exact Henv3 | split; [exact Hwcex |]]].
    intros Hqf Hib Hinv Hpath.
    assert (Hg2 : eval_lit asg2 g_lit = true).
    { rewrite (step_spec_eval_lit _ _ _ _ _ Hs2 Hwg1); apply Hg1_true; [| exact Hpath].
      cbn [obl_is_body] in Hib; subst ib; unfold g0; destruct is_body_mode.
      - exact (Hbh_true eq_refl (Hinv eq_refl)).
      - exact (proj1 (proj2 (proj1 Henv))). }
    rewrite Hevcex, Hg2 in Hqf; cbn [andb] in Hqf.
    unfold rail_matches_dvalue in Hme; unfold eval_rail_psn in Hme; rewrite Hqf in Hme.
    subst ve; exists (eval_rail_val w asg2 re); exact Eve.
Qed.

Lemma blast_mc_obls_list_acc_sat {Pa : Params} :
  forall ctx (penv : param_env Pa) foracle known_vars opt_inv is_body_mode body_hyp_lit obls env acc cexs env' asg,
    forallb (obl_wf_exprs known_vars) obls = true ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    wf_lit_bound (bs_next_var (be_st env)) body_hyp_lit ->
    wf_lits_bound (bs_next_var (be_st env)) acc ->
    (is_body_mode = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv foracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end ->
     eval_lit asg body_hyp_lit = true) ->
    blast_mc_obls_list_acc ctx body_hyp_lit obls env acc = Some (cexs, env') ->
    exists asg',
      step_spec (be_st env) (be_st env') asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_lits_bound (bs_next_var (be_st env')) cexs /\
      ((forall l, In l cexs -> eval_lit asg' l = false) ->
       Forall (mc_obl_holds penv foracle opt_inv is_body_mode) obls /\
       (forall l, In l acc -> eval_lit asg' l = false)).
Proof.
  intros ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit obls;
    induction obls as [| o rest IH];
    intros env acc cexs env' asg Hwf Hpenv Hctx Henv Hwbh Hwacc Hbh_true Hbl;
    cbn [blast_mc_obls_list_acc] in Hbl.
  - inversion Hbl; subst cexs env'; exists asg; split;
      [exact (step_spec_refl _ _ (proj1 Henv)) | split; [exact Henv | split]].
    + rewrite elf_rev_tr_eq; unfold wf_lits_bound in *; rewrite Forall_forall in Hwacc |- *.
      intros l Hl; rewrite <- in_rev in Hl; exact (Hwacc l Hl).
    + intros Hall; split; [constructor | intros l Hl; apply Hall; rewrite elf_rev_tr_eq, <- in_rev; exact Hl].
  - cbn [forallb] in Hwf; apply andb_true_iff in Hwf as [Ho Hrest].
    destruct (blast_mc_obl ctx body_hyp_lit env o) as [[cx env1] |] eqn:Ebo; [| discriminate Hbl].
    destruct (blast_mc_obl_sat ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit env o cx env1 asg
                Ho Hpenv Hctx Henv Hwbh Hbh_true Ebo)
      as (asg1 & Hs1 & Henv1 & Hwcx & Ho_sound).
    assert (Hbh1_wf : wf_lit_bound (bs_next_var (be_st env1)) body_hyp_lit)
      by exact (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hwbh).
    assert (Hwacc1 : wf_lits_bound (bs_next_var (be_st env1)) (cx :: acc))
      by (constructor; [exact Hwcx | exact (wf_lits_bound_mono _ _ _ (proj1 Hs1) Hwacc)]).
    assert (Hbh1_true : is_body_mode = true -> match opt_inv with None => True | Some inv_e => eval_closed_cert_expr penv foracle inv_e = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive))) end -> eval_lit asg1 body_hyp_lit = true).
    { intros Hbm Hinv; rewrite (step_spec_eval_lit _ _ _ _ _ Hs1 Hwbh); exact (Hbh_true Hbm Hinv). }
    destruct (IH env1 (cx :: acc) cexs env' asg1 Hrest Hpenv Hctx Henv1 Hbh1_wf Hwacc1 Hbh1_true Hbl)
      as (asg2 & Hs2 & Henv2 & Hwcxs & Hrest_sound).
    exists asg2; split; [exact (step_spec_trans _ _ _ _ _ _ Hs1 Hs2) | split; [exact Henv2 | split; [exact Hwcxs |]]].
    intros Hall; destruct (Hrest_sound Hall) as [Hfa2 Hacc2]; split.
    + constructor; [| exact Hfa2].
      apply Ho_sound; rewrite <- (step_spec_eval_lit _ _ _ _ _ Hs2 Hwcx); apply Hacc2; left; reflexivity.
    + intros l Hl; apply Hacc2; right; exact Hl.
Qed.

Lemma blast_mc_obls_list_sat {Pa : Params} :
  forall ctx (penv : param_env Pa) foracle known_vars opt_inv is_body_mode body_hyp_lit obls env cexs env' asg,
    forallb (obl_wf_exprs known_vars) obls = true ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    wf_lit_bound (bs_next_var (be_st env)) body_hyp_lit ->
    (is_body_mode = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv foracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end ->
     eval_lit asg body_hyp_lit = true) ->
    blast_mc_obls_list ctx body_hyp_lit obls env = Some (cexs, env') ->
    exists asg',
      step_spec (be_st env) (be_st env') asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_lits_bound (bs_next_var (be_st env')) cexs /\
      ((forall l, In l cexs -> eval_lit asg' l = false) ->
       Forall (mc_obl_holds penv foracle opt_inv is_body_mode) obls).
Proof.
  intros ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit obls env cexs env' asg
         Hwf Hpenv Hctx Henv Hwbh Hbh_true Hbl.
  destruct (blast_mc_obls_list_acc_sat ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit
              obls env [] cexs env' asg Hwf Hpenv Hctx Henv Hwbh (Forall_nil _) Hbh_true Hbl)
    as (asg' & Hs & Henv' & Hwc & Hfa).
  exists asg'; split; [exact Hs | split; [exact Henv' | split; [exact Hwc | intro Hall; exact (proj1 (Hfa Hall))]]].
Qed.

Theorem check_mc_loop_obls_sound {Pa : Params} :
  forall tag ctx known_vars opt_inv obls opt_pf (penv : param_env Pa) foracle is_body_mode,
    check_mc_loop_obls tag ctx known_vars opt_inv obls opt_pf = inr tt ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    Forall (mc_obl_holds penv foracle opt_inv is_body_mode) obls.
Proof.
  intros tag ctx known_vars opt_inv obls opt_pf penv foracle is_body_mode Hchk Hpenv Hctx.
  unfold check_mc_loop_obls in Hchk.
  destruct (check_obls_wf_diag_acc tag known_vars 0%nat obls) as [| []] eqn:Hwf_d; [discriminate Hchk |].
  pose proof (check_obls_wf_diag_acc_sound _ _ _ _ Hwf_d) as Hwf_all.
  rewrite mc_filter_tr_eq in Hchk.
  remember (List.filter (fun o => negb (obl_is_alg_ok ctx o)) obls) as rem eqn:Erem.
  assert (Halg : forall o, In o obls -> obl_is_alg_ok ctx o = true -> mc_obl_holds penv foracle opt_inv is_body_mode o).
  { intros o Ho Hal Hbm Hinv Hpath.
    rewrite forallb_forall in Hwf_all; pose proof (Hwf_all o Ho) as Hwfo.
    unfold obl_wf_exprs in Hwfo; apply andb_true_iff in Hwfo as [_ Hwfo].
    destruct o as [ib p w s t | ib p w e]; cbn in Hal; try discriminate Hal.
    destruct ib; [discriminate Hal |]; destruct p; [| discriminate Hal].
    rewrite !andb_true_iff in Hwfo; destruct Hwfo as (((((((((Hwts & Hwtt) & Hbws) & Hbwt) & Hlfs) & Hlft) & _) & _) & Hsubs) & Hsubt).
    exact (check_expr_refines_sound ctx s t penv foracle Hal
             (vars_subset_b_wf_param_env _ _ penv Hsubs Hpenv)
             (vars_subset_b_wf_param_env _ _ penv Hsubt Hpenv) Hctx). }
  assert (Hrem_wf : forallb (obl_wf_exprs known_vars) rem = true).
  { rewrite forallb_forall; intros o Ho; rewrite Erem in Ho; apply filter_In in Ho as [Ho _].
    rewrite forallb_forall in Hwf_all; exact (Hwf_all o Ho). }
  assert (Hfrom_rem : Forall (mc_obl_holds penv foracle opt_inv is_body_mode) rem ->
                      Forall (mc_obl_holds penv foracle opt_inv is_body_mode) obls).
  { intro Hfr; rewrite Forall_forall in Hfr |- *; intros o Ho.
    destruct (obl_is_alg_ok ctx o) eqn:Eal; [exact (Halg o Ho Eal) |].
    apply Hfr; rewrite Erem; apply filter_In; split; [exact Ho | rewrite Eal; reflexivity]. }
  apply Hfrom_rem.
  destruct rem as [| r0 rem']; [constructor |].
  destruct (build_mc_loop_cnf tag ctx known_vars opt_inv (r0 :: rem')) as [| [nv f]] eqn:Ebld; [discriminate Hchk |].
  destruct (check_cex_unsat f opt_pf) eqn:Hcun; [| destruct opt_pf; discriminate Hchk].
  clear Hchk.
  unfold build_mc_loop_cnf in Ebld.
  destruct (check_obls_wf_diag_acc tag known_vars 0%nat (r0 :: rem')) as [| []]; [discriminate Ebld |].
  set (init_env := mk_blast_env (init_blast_state 2%positive) [] []) in *.
  set (env0 := blast_ub_ctx ctx known_vars ctx init_env) in *.
  assert (Hinit_env : sat_blast_env penv foracle (fun _ => true) init_env)
    by (split; [exact init_blast_state_sat | split; intros; discriminate]).
  destruct (blast_ub_ctx_sat ctx known_vars ctx penv foracle (fun _ => true) init_env
              Hctx Hctx Hpenv Hinit_env) as [asg0 Henv0].
  set (hyp_res := match opt_inv with None => inr (lit_true, env0) | Some inv_e => if wt_cert_expr [] inv_e && Pos.eqb (cert_expr_bit_width inv_e) 1%positive && is_let_free_expr inv_e && ub_free_expr inv_e && vars_subset_b (collect_free_vars [] inv_e) known_vars then match blast_cert_expr ctx [] (mc_ms_opt inv_e) inv_e env0 with Some (ri, env_i) => let b0 := match rbv_bits ri with x :: _ => x | [] => lit_false end in let '(hlit, st1) := emit_and2_opt (neg_lit (rbv_psn ri)) b0 (be_st env_i) in inr (hlit, mk_blast_env st1 (be_vars env_i) (be_freezes env_i)) | None => inl (diag (tag ++ "-blast")%string "failed to bit-blast loop invariant") end else inl (diag (tag ++ "-inv")%string "loop invariant expression failed typing or variable-scope check") end) in *.
  destruct hyp_res as [| [body_hyp_lit env1]] eqn:Ehyp; [discriminate Ebld |].
  assert (Hhyp_sat : exists asg1,
    sat_blast_env penv foracle asg1 env1 /\
    wf_lit_bound (bs_next_var (be_st env1)) body_hyp_lit /\
    (is_body_mode = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv foracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end ->
     eval_lit asg1 body_hyp_lit = true)).
  { unfold hyp_res in Ehyp; destruct opt_inv as [inv_e |].
    - destruct (wt_cert_expr [] inv_e && Pos.eqb (cert_expr_bit_width inv_e) 1%positive && is_let_free_expr inv_e && ub_free_expr inv_e && vars_subset_b (collect_free_vars [] inv_e) known_vars) eqn:Ewi; [| discriminate Ehyp].
      rewrite !andb_true_iff in Ewi; destruct Ewi as ((((Hwti & Hbwi) & _) & _) & Hsubi); apply Pos.eqb_eq in Hbwi.
      destruct (blast_cert_expr ctx [] (mc_ms_opt inv_e) inv_e env0) as [[ri env_i] |] eqn:Ebi; [| discriminate Ehyp].
      destruct (blast_cert_expr_sat inv_e ctx [] [] (mc_ms_opt inv_e) penv [] foracle asg0 env0 env_i ri
                  Ebi Hwti (wf_let_rails_sync_nil asg0 _) (mc_ms_opt_sync inv_e)
                  (vars_subset_b_wf_param_env _ _ penv Hsubi Hpenv) Hctx Henv0)
        as (asg_i & vi & Evi & Hsi & Henv_i & Hwfi & Hmri).
      rewrite Hbwi in Hwfi, Hmri; destruct Hwfi as ((_ & Hleni) & Hlbsi & Hpsi).
      destruct (rbv_bits ri) as [| bi0 rbitsi] eqn:Ebitsi; [cbn in Hleni; discriminate Hleni |].
      destruct (emit_and2_opt (neg_lit (rbv_psn ri)) bi0 (be_st env_i)) as [hlit st1] eqn:Ea_h.
      inversion Ehyp; subst body_hyp_lit env1; clear Ehyp.
      destruct (emit_and2_opt_step asg_i (neg_lit (rbv_psn ri)) bi0 (be_st env_i) hlit st1
                  (proj1 Henv_i) (wf_lit_bound_neg _ _ Hpsi) ltac:(inversion Hlbsi; assumption) Ea_h)
        as (asg1 & Hs1 & Hwhl & Hevh).
      exists asg1; split; [exact (sat_blast_env_step penv foracle asg_i asg1 env_i st1 Henv_i Hs1) | split; [exact Hwhl |]].
      intros _ Hinv; unfold eval_closed_cert_expr in Hinv; rewrite Evi in Hinv; inversion Hinv; subst vi; clear Hinv.
      unfold rail_matches_dvalue in Hmri.
      destruct (eval_rail_psn asg_i ri) eqn:Epsi; [discriminate Hmri |].
      unfold eval_rail_val in Hmri; rewrite Ebitsi in Hmri.
      unfold eval_rail_psn in Epsi; rewrite Hevh, (eval_neg_lit_nonzero asg_i _ (wf_lit_bound_nonzero _ _ Hpsi)), Epsi; cbn [negb andb].
      destruct rbitsi as [| ? ?]; [| cbn in Hleni; discriminate Hleni].
      pose proof (f_equal dvalue_int_unsigned Hmri) as Hu; cbn [List.map bools_to_Z Zshiftin dvalue_int_unsigned] in Hu;
        rewrite (@Integers.unsigned_one 1%positive) in Hu.
      destruct (eval_lit asg_i bi0); [reflexivity |
        cbn [List.map bools_to_Z Zshiftin dvalue_int_unsigned] in Hu;
        rewrite Integers.unsigned_repr in Hu by (change (@Integers.max_unsigned 1%positive) with 1%Z; lia); lia].
    - inversion Ehyp; subst body_hyp_lit env1; exists asg0.
      pose proof Henv0 as [[Hwf0 [Ht _]] _]; destruct Hwf0 as [Hge0 _].
      split; [exact Henv0 | split; [unfold env0, wf_lit_bound, lit_true; lia | intros _ _; cbn [eval_lit]; exact Ht]]. }
  destruct Hhyp_sat as (asg1 & Henv1 & Hbh_wf & Hbh_true).
  destruct (blast_mc_obls_list ctx body_hyp_lit (r0 :: rem') env1) as [[cex_lits env2] |] eqn:Eobls; [| discriminate Ebld].
  destruct (emit_or_list_opt cex_lits (be_st env2)) as [any_cex st_or] eqn:Eor.
  inversion Ebld; subst f; clear Ebld.
  destruct (blast_mc_obls_list_sat ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit (r0 :: rem')
              env1 cex_lits env2 asg1 Hrem_wf Hpenv Hctx Henv1 Hbh_wf Hbh_true Eobls)
    as (asg2 & Hs2 & Henv2 & Hwcexs & Hsound).
  destruct (emit_or_list_opt_step cex_lits asg2 (be_st env2) any_cex st_or Hwcexs (proj1 Henv2) Eor)
    as (asg3 & Hs3 & Hwany & Hev_any).
  assert (Hany_false : eval_lit asg3 any_cex = false).
  { destruct (eval_lit asg3 any_cex) eqn:Etrue; [| reflexivity].
    destruct (proj2 (proj2 Hs3)) as ([Hge3 Hwf_st3] & Ha1_3 & Hev_st3).
    assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st_or)) [[any_cex]]) by (repeat constructor; exact Hwany).
    assert (Hcls_sat : forall cl, In cl [[any_cex]] -> eval_clause asg3 cl = true)
      by (intros cl [<- | []]; cbn; rewrite Etrue; reflexivity).
    pose proof (add_clauses_sat_intro asg3 st_or [[any_cex]] Hge3 Ha1_3 Hwf_st3 Hcls_wf Hev_st3 Hcls_sat) as Hsat_fin.
    pose proof (check_cex_unsat_sound _ opt_pf Hcun asg3) as Huns.
    destruct Hsat_fin as [_ [_ Hsat_cnf]]; unfold add_clauses, bs_cnf in Hsat_cnf, Huns; cbn [prepend_clauses_rev fst snd] in Hsat_cnf.
    rewrite Huns in Hsat_cnf; discriminate Hsat_cnf. }
  apply Hsound; intros l Hl.
  rewrite Hev_any, existsb_id_map_eval_lit in Hany_false.
  destruct (eval_lit asg2 l) eqn:Elt; [| reflexivity].
  exfalso; assert (Hex : existsb (eval_lit asg2) cex_lits = true)
    by (apply existsb_exists; exists l; split; [exact Hl | exact Elt]).
  congruence.
Qed.

Definition imposs_obl (is_body : bool) (path : list (bool * cert_expr)) : list mc_loop_obl :=
  [MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (CE_BvConst 1%positive 0%N)].

Definition imposs_obl_cons (is_body : bool) (path : list (bool * cert_expr)) (acc : list mc_loop_obl)
  : list mc_loop_obl :=
  MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (CE_BvConst 1%positive 0%N) :: acc.

Lemma imposs_obl_absurd {Pa : Params} :
  forall (penv : param_env Pa) foracle opt_inv (is_body : bool) (path : list (bool * cert_expr)),
    (is_body = true -> match opt_inv with None => True | Some inv_e => eval_closed_cert_expr penv foracle inv_e = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive))) end) ->
    (forall (b : bool) (c : cert_expr), In (b, c) path ->
       eval_closed_cert_expr penv foracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv foracle opt_inv is_body) (imposs_obl is_body path) ->
    False.
Proof.
  intros penv foracle opt_inv is_body path Hinv Hpath Hfa.
  inversion Hfa as [| ? ? H0 _]; subst.
  pose proof (H0 eq_refl Hinv Hpath) as Href.
  cbn [eval_closed_cert_expr eval_cert_expr refine_eou_dvalue] in Href.
  rewrite repr_one_N, repr_zero_N in Href.
  destruct Href as [Hbad | Hbad]; [inversion Hbad |].
  pose proof (f_equal dvalue_int_unsigned Hbad) as Hu.
  cbn in Hu; rewrite (@Integers.unsigned_one 1%positive), (@Integers.unsigned_zero 1%positive) in Hu; discriminate Hu.
Qed.
