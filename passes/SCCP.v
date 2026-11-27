(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Sparse Conditional Constant Propagation ([CertPasses.SCCP])

    Purpose:
      Re-exports [CertPasses.SCCPSpec], proves block-address preservation
      ([sccp_cfg_block_addresses]) and constant-evaluator soundness, builds
      local-environment simulation ([sccp_cfg_sim]) from [check_sccp_valid],
      and proves whole-program refinement ([sccp_mcfg_refines]).

    Trust Contract & Fail-Closed Boundary:
      Proof-only verification module over [CertPasses.SCCPSpec] (listed in
      [Extract.v] alongside [SCCPSpec]); runtime execution relies on
      [SCCPSpec.sccp_cfg]'s fail-closed fallback when [sccp_check_guards] or
      [check_sccp_valid] fails.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.PassCommon],
      and [CertPasses.SCCPSpec]; zero custom axioms (parameterized over
      [IP : IPtr] and [IPT : @IPtrTheory IP]).

    Section Outline:
      (4) Syntactic, lookup, block-address, & [ConstEvalSound];
      (5) [cfg_local_sim] primitives, [env_matches_cert], expression/instr/phi/
      terminator simulation; (6) [sccp_mcfg_refines]. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
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
  Eq.Eqit.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads
  Data.Monads.OptionMonad.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  ScopeTheory
  Theory.Equational
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Implementations.ParamsV
  Semantics.TopLevel.

From CertPasses Require Import PassCommon.
From CertPasses Require Export SCCPSpec.
Import Logic.

Set Default Goal Selector "!".
#[local] Unset Implicit Arguments.

(** * 4. Syntactic, Lookup, Block-Address, and Constant-Operation Lemmas *)

Lemma sccp_find_block_some_id {T : Set} (bks : ocfg T) (bid : block_id) (bk : block T) :
  find_block bks bid = Some bk ->
  blk_id bk = bid.
Proof.
  induction bks as [| x rest IH]; intros H; [discriminate H |].
  destruct (Eqv.eqv_dec_p (blk_id x) bid) as [Heq | Hneq].
  - rewrite find_block_eq in H by exact Heq.
    inversion H; subst; exact Heq.
  - rewrite find_block_ineq in H by exact Hneq.
    apply IH, H.
Qed.

Lemma sccp_find_block_map_preserve {T : Set} (g : block T -> block T)
  (Hg : forall bk, blk_id (g bk) = blk_id bk)
  (bks : ocfg T) (bid : block_id) :
  find_block (List.map g bks) bid = option_map g (find_block bks bid).
Proof.
  apply find_block_map; exact Hg.
Qed.

Lemma sccp_rewrite_block_id (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
  (b : block dtyp) :
  blk_id (sccp_rewrite_block fargs c exec_edges md_in cm b) = blk_id b.
Proof.
  unfold sccp_rewrite_block; cbn zeta.
  destruct (sccp_is_reachable_blk exec_edges (blk_id b)); [| reflexivity].
  destruct (blk_term b) as [[tiid tm] tmd]; reflexivity.
Qed.

Lemma sccp_is_reachable_from_edge (exec_edges : list cfg_edge)
  (bid_from bid_src : block_id) :
  sccp_in_edges (bid_from, bid_src) exec_edges = true ->
  sccp_is_reachable_blk exec_edges bid_src = true.
Proof.
  intros Hin; apply sccp_in_edges_spec in Hin.
  unfold sccp_is_reachable_blk; apply existsb_exists.
  exists (bid_from, bid_src); split; [exact Hin | apply raw_id_eqb_refl].
Qed.

Lemma sccp_assoc_map_dep {V1 V2 : Type}
  (g : block_id -> V1 -> V2) (k : block_id) (al : list (block_id * V1)) :
  assoc k (List.map (fun '(k', v) => (k', g k' v)) al) =
  option_map (g k) (assoc k al).
Proof.
  induction al as [| [k' v] rest IH]; [reflexivity |].
  cbn [List.map].
  destruct (RawIDOrd.eq_dec k k') as [<- | Hne].
  - rewrite !assoc_hd; reflexivity.
  - rewrite !assoc_tl by exact Hne; exact IH.
Qed.

Lemma eval_cert_exp_const_to_lit (cm : rmap const_val) (defs : list raw_id)
  (cv : const_val) (dt_cv : dtyp) (e_lit : exp dtyp) :
  const_to_lit_exp cv = Some (dt_cv, e_lit) ->
  eval_cert_exp cm defs (Some dt_cv) e_lit = Some cv.
Proof.
  destruct cv as [sz val]; cbn [const_to_lit_exp].
  destruct (Pos.eq_dec sz 1%positive) as [Heq | Hne].
  - rewrite <- (sccp_eq_sym_involutive Heq).
    revert val; generalize (Logic.eq_sym Heq); clear Heq; intros p; destruct p; intros val.
    cbn [eq_rect eq_sym]; intros H; inversion H; subst dt_cv e_lit; clear H.
    cbn [eval_cert_exp].
    pose proof (sccp_bit_int_1_cases val) as Hcases.
    destruct (@Integers.unsigned 1 val =? 1)%Z; subst val; reflexivity.
  - destruct (sccp_z_to_lit_checked (@Integers.unsigned sz val)) as [lit |] eqn:Elit;
      [| discriminate].
    intros H; inversion H; subst dt_cv e_lit; clear H.
    cbn [eval_cert_exp].
    rewrite (sccp_z_to_lit_checked_sound _ _ Elit), (@Integers.repr_unsigned sz val).
    reflexivity.
Qed.

Lemma eval_cert_exp_const_to_exp_at (cm : rmap const_val) (defs : list raw_id)
  (cv : const_val) (top : option dtyp) (ec : exp dtyp) :
  const_to_exp_at cv top = Some ec ->
  eval_cert_exp cm defs top ec = Some cv.
Proof.
  unfold const_to_exp_at.
  destruct (const_to_lit_exp cv) as [[dt_cv e_lit] |] eqn:Elit; [| discriminate].
  destruct top as [dt |].
  - destruct (dtyp_eqb dt dt_cv) eqn:Heqb; [| discriminate].
    intros H; inversion H; subst ec; clear H.
    apply dtyp_eqb_eq in Heqb; subst dt.
    eapply eval_cert_exp_const_to_lit, Elit.
  - intros H; inversion H; subst ec; clear H.
    cbn [mk_copy_exp eval_cert_exp sccp_safe_atom].
    rewrite sccp_pos_eq_dec_refl; cbn [eq_rect].
    rewrite (@Integers.unsigned_one 1), Z.eqb_refl.
    exact (eval_cert_exp_const_to_lit cm defs cv dt_cv e_lit Elit).
Qed.

Lemma sccp_safe_atom_subst (cm : rmap const_val) (defs : list raw_id)
  (dt : dtyp) (e : exp dtyp) :
  sccp_safe_atom defs dt e = true ->
  sccp_safe_atom defs dt (subst_exp_at cm defs (Some dt) e) = true.
Proof.
  destruct e; cbn [sccp_safe_atom subst_exp_at];
    try (intros H; first [exact H | discriminate H]).
  destruct id as [gid | y]; [discriminate |].
  intros Hin; rewrite Hin.
  destruct (RM.find y cm) as [cv |]; [| exact Hin].
  unfold const_to_exp_at.
  destruct (const_to_lit_exp cv) as [[dt_cv e_lit] |] eqn:Elit; [| exact Hin].
  destruct (dtyp_eqb dt dt_cv) eqn:Heqb; [| exact Hin].
  apply dtyp_eqb_eq in Heqb; subst dt.
  destruct cv as [sz val]; cbn [const_to_lit_exp] in Elit.
  destruct (Pos.eq_dec sz 1%positive) as [Heq | Hne].
  - revert Elit; rewrite <- (sccp_eq_sym_involutive Heq).
    revert val; generalize (Logic.eq_sym Heq); clear Heq; intros p; destruct p; intros val Elit.
    cbn [eq_rect eq_sym] in Elit; inversion Elit; subst; reflexivity.
  - destruct (sccp_z_to_lit_checked (@Integers.unsigned sz val)); [| discriminate].
    inversion Elit; subst; reflexivity.
Qed.

Lemma eval_cert_exp_subst (cm : rmap const_val) (defs : list raw_id) :
  forall (e : exp dtyp) (top : option dtyp) (cv : const_val),
    eval_cert_exp cm defs top e = Some cv ->
    eval_cert_exp cm defs top (subst_exp_at cm defs top e) = Some cv.
Proof.
  apply (@exp_ind_full dtyp
           (fun e => forall top cv,
              eval_cert_exp cm defs top e = Some cv ->
              eval_cert_exp cm defs top (subst_exp_at cm defs top e) = Some cv)
           (fun md =>
              match md with
              | METADATA_Const (dt, ex) =>
                  forall top cv,
                    eval_cert_exp cm defs top ex = Some cv ->
                    eval_cert_exp cm defs top (subst_exp_at cm defs top ex) = Some cv
              | _ => True
              end));
    try (intros; discriminate);
    try (intros; exact I).
  - (* EXP_Ident *)
    intros [gid | y] top cv H; [discriminate H |].
    cbn [eval_cert_exp] in H; cbn [subst_exp_at].
    destruct (in_raw_ids y defs) eqn:Hin; [| discriminate H].
    rewrite H.
    destruct (const_to_exp_at cv top) as [ec |] eqn:Eec.
    + eapply eval_cert_exp_const_to_exp_at, Eec.
    + cbn [eval_cert_exp]; rewrite Hin; exact H.
  - (* EXP_Integer *)
    intros x top cv H; exact H.
  - (* EXP_Bool *)
    intros b top cv H; exact H.
  - (* OP_IBinop *)
    intros iop dt e1 e2 IH1 IH2 top cv H.
    cbn [eval_cert_exp] in H; cbn [subst_exp_at eval_cert_exp].
    destruct (eval_cert_exp cm defs (Some dt) e1) as [c1 |] eqn:E1; [| discriminate H].
    destruct (eval_cert_exp cm defs (Some dt) e2) as [c2 |] eqn:E2; [| discriminate H].
    rewrite (IH1 (Some dt) c1 E1), (IH2 (Some dt) c2 E2); exact H.
  - (* OP_ICmp *)
    intros samesign_f cmp_op dt e1 e2 IH1 IH2 top cv H.
    cbn [eval_cert_exp] in H; cbn [subst_exp_at eval_cert_exp].
    destruct (eval_cert_exp cm defs (Some dt) e1) as [c1 |] eqn:E1; [| discriminate H].
    destruct (eval_cert_exp cm defs (Some dt) e2) as [c2 |] eqn:E2; [| discriminate H].
    rewrite (IH1 (Some dt) c1 E1), (IH2 (Some dt) c2 E2); exact H.
  - (* OP_Conversion *)
    intros conv dt_from e1 dt_to IH1 top cv H.
    cbn [eval_cert_exp] in H; cbn [subst_exp_at eval_cert_exp].
    destruct (eval_cert_exp cm defs (Some dt_from) e1) as [c1 |] eqn:E1; [| discriminate H].
    rewrite (IH1 (Some dt_from) c1 E1); exact H.
  - (* OP_Select *)
    intros fm [dt_c cnd] [dt1 op1] [dt2 op2] IHc IH1 IH2 top cv H.
    cbn [snd] in IHc, IH1, IH2.
    cbn [eval_cert_exp] in H; cbn [subst_exp_at eval_cert_exp].
    destruct (eval_cert_exp cm defs (Some dt_c) cnd) as [[sz_c vc] |] eqn:Ec; [| discriminate H].
    rewrite (IHc (Some dt_c) (CInt sz_c vc) Ec).
    destruct (Pos.eq_dec sz_c 1%positive) as [Heq | _]; [| discriminate H].
    destruct (@Integers.unsigned 1 (eq_rect sz_c (fun s => @bit_int s) vc 1%positive Heq) =? 1)%Z.
    + destruct (eval_cert_exp cm defs (Some dt2) op2) as [c2 |] eqn:E2.
      * rewrite (IH2 (Some dt2) c2 E2).
        destruct (eval_cert_exp cm defs (Some dt1) op1) as [c1 |] eqn:E1; [| discriminate H].
        inversion H; subst c1; apply IH1, E1.
      * destruct (sccp_safe_atom defs dt2 op2) eqn:Hsafe2; [| discriminate H].
        rewrite (sccp_safe_atom_subst cm defs dt2 op2 Hsafe2).
        destruct (eval_cert_exp cm defs (Some dt1) op1) as [c1 |] eqn:E1; [| discriminate H].
        inversion H; subst c1.
        rewrite (IH1 (Some dt1) cv E1).
        destruct (eval_cert_exp cm defs (Some dt2) (subst_exp_at cm defs (Some dt2) op2));
          reflexivity.
    + destruct (eval_cert_exp cm defs (Some dt1) op1) as [c1 |] eqn:E1.
      * rewrite (IH1 (Some dt1) c1 E1).
        destruct (eval_cert_exp cm defs (Some dt2) op2) as [c2 |] eqn:E2; [| discriminate H].
        inversion H; subst c2; apply IH2, E2.
      * destruct (sccp_safe_atom defs dt1 op1) eqn:Hsafe1; [| discriminate H].
        rewrite (sccp_safe_atom_subst cm defs dt1 op1 Hsafe1).
        destruct (eval_cert_exp cm defs (Some dt2) op2) as [c2 |] eqn:E2; [| discriminate H].
        inversion H; subst c2.
        rewrite (IH2 (Some dt2) cv E2).
        destruct (eval_cert_exp cm defs (Some dt1) (subst_exp_at cm defs (Some dt1) op1));
          reflexivity.
  - (* EXP_Metadata *)
    intros md IHmd top cv H.
    destruct md as [| | [dt ex] | | | |]; try discriminate H.
    cbn [eval_cert_exp] in H; cbn [subst_exp_at eval_cert_exp].
    apply IHmd, H.
  - (* IH_METADATA_Const *)
    intros [dt ex] Hex; exact Hex.
Qed.

Lemma sccp_map_texps_id (cm : rmap const_val) (defs : list raw_id)
  (es : list (dtyp * exp dtyp))
  (IH : forall p, In p es -> forall top, subst_exp_at cm defs top (snd p) = snd p) :
  (fix go (l : list (dtyp * exp dtyp)) : list (dtyp * exp dtyp) :=
     match l with
     | [] => []
     | (dt, ex) :: rest => (dt, subst_exp_at cm defs (Some dt) ex) :: go rest
     end) es = es.
Proof.
  induction es as [| [dt ex] rest IHr]; [reflexivity |].
  f_equal.
  - f_equal; apply (IH (dt, ex) (or_introl Logic.eq_refl) (Some dt)).
  - apply IHr; intros p Hp; apply (IH p (or_intror Hp)).
Qed.

Lemma subst_exp_at_empty :
  forall (e : exp dtyp) (top : option dtyp),
    subst_exp_at (RM.empty const_val) [] top e = e.
Proof.
  apply (@exp_ind_full dtyp
           (fun e => forall top, subst_exp_at (RM.empty const_val) [] top e = e)
           (fun md =>
              match md with
              | METADATA_Const (dt, ex) =>
                  forall top, subst_exp_at (RM.empty const_val) [] top ex = ex
              | _ => True
              end));
    try (intros; reflexivity);
    try exact I.
  - intros [gid | y] top; reflexivity.
  - intros es IH top; cbn [subst_exp_at]; f_equal; apply sccp_map_texps_id, IH.
  - intros es IH top; cbn [subst_exp_at]; f_equal; apply sccp_map_texps_id, IH.
  - intros es IH top; cbn [subst_exp_at]; f_equal; apply sccp_map_texps_id, IH.
  - intros es IH top; cbn [subst_exp_at]; f_equal; apply sccp_map_texps_id, IH.
  - intros es IH top; cbn [subst_exp_at]; f_equal; apply sccp_map_texps_id, IH.
  - intros iop dt e1 e2 IH1 IH2 top; cbn [subst_exp_at]; rewrite IH1, IH2; reflexivity.
  - intros fm [dt e1] IH1 top; cbn [snd] in IH1; cbn [subst_exp_at]; rewrite IH1; reflexivity.
  - intros ss cmp_op dt e1 e2 IH1 IH2 top; cbn [subst_exp_at]; rewrite IH1, IH2; reflexivity.
  - intros fop fm dt e1 e2 IH1 IH2 top; cbn [subst_exp_at]; rewrite IH1, IH2; reflexivity.
  - intros fcmp_op fm dt e1 e2 IH1 IH2 top; cbn [subst_exp_at]; rewrite IH1, IH2; reflexivity.
  - intros conv dt_f e1 dt_t IH1 top; cbn [subst_exp_at]; rewrite IH1; reflexivity.
  - intros flags dt1 [dt2 ep] idxs IHp IHi top; cbn [snd] in IHp; cbn [subst_exp_at].
    rewrite IHp, (sccp_map_texps_id _ _ idxs IHi); reflexivity.
  - intros [dt1 e1] [dt2 e2] IH1 IH2 top; cbn [snd] in *; cbn [subst_exp_at].
    rewrite IH1, IH2; reflexivity.
  - intros [dt1 e1] [dt2 e2] [dt3 e3] IH1 IH2 IH3 top; cbn [snd] in *; cbn [subst_exp_at].
    rewrite IH1, IH2, IH3; reflexivity.
  - intros [dt1 e1] [dt2 e2] [dt3 e3] IH1 IH2 IH3 top; cbn [snd] in *; cbn [subst_exp_at].
    rewrite IH1, IH2, IH3; reflexivity.
  - intros [dt1 e1] idxs IH1 top; cbn [snd] in IH1; cbn [subst_exp_at]; rewrite IH1; reflexivity.
  - intros [dt1 e1] [dt2 e2] idxs IH1 IH2 top; cbn [snd] in *; cbn [subst_exp_at].
    rewrite IH1, IH2; reflexivity.
  - intros fm [dtc ec] [dt1 e1] [dt2 e2] IHc IH1 IH2 top; cbn [snd] in *; cbn [subst_exp_at].
    rewrite IHc, IH1, IH2; reflexivity.
  - intros [dt e1] IH1 top; cbn [snd] in IH1; cbn [subst_exp_at]; rewrite IH1; reflexivity.
  - intros md IHmd top; destruct md as [| | [dt ex] | | | |]; try reflexivity.
    cbn [subst_exp_at]; rewrite IHmd; reflexivity.
  - intros [dt e1] IH1 top; cbn [snd] in IH1; cbn [subst_exp_at]; rewrite IH1; reflexivity.
  - intros [dt ex] Hex; exact Hex.
Qed.

Lemma sccp_rewrite_call_args_empty (args : list (texp dtyp * list param_attr)) :
  sccp_rewrite_call_args (RM.empty const_val) [] args = args.
Proof.
  induction args as [| [[t op] attrs] rest IH]; [reflexivity |].
  unfold sccp_rewrite_call_args in *; cbn [List.map].
  rewrite subst_exp_at_empty, IH; reflexivity.
Qed.

Lemma sccp_rewrite_obs_empty (obs : list (@operand_bundle dtyp)) :
  List.map (sccp_rewrite_ob (RM.empty const_val) []) obs = obs.
Proof.
  induction obs as [| [tag ops] rest IH]; [reflexivity |].
  cbn [List.map]; unfold sccp_rewrite_ob; cbn [ob_tag ob_ops].
  f_equal; [| exact IH].
  f_equal.
  induction ops as [| [[t ex] | md] r_ops IHo]; [reflexivity | |].
  - cbn [List.map]; rewrite subst_exp_at_empty, IHo; reflexivity.
  - cbn [List.map]; rewrite IHo; reflexivity.
Qed.

Lemma sccp_rewrite_instr_empty (ins : instr dtyp) :
  sccp_rewrite_instr (RM.empty const_val) [] ins = ins.
Proof.
  destruct ins as [msg | op | fn args anns obs | dt anns | dt [du ptr] anns
                   | [dt val] [du ptr] anns | sc ord | cpx | armw | [t ptr_exp] argty
                   | rty cl cs];
    cbn [sccp_rewrite_instr];
    try rewrite !subst_exp_at_empty;
    try rewrite sccp_rewrite_call_args_empty, sccp_rewrite_obs_empty;
    try reflexivity.
  - destruct cpx as [cw cv [pt pv] [ct cv_e] [nt nv] cs_o cso cfo cal]; cbn.
    rewrite !subst_exp_at_empty; reflexivity.
  - destruct armw as [av aop [pt pv] [at_t av_e] as_o aord aal]; cbn.
    rewrite !subst_exp_at_empty; reflexivity.
Qed.

Lemma sccp_rewrite_term_empty (tm : terminator dtyp) :
  sccp_rewrite_term false (RM.empty const_val) [] tm = tm.
Proof.
  destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt ex] def_br dests
                  | [dt ex] brs fn | [dt ex] | fn args to_lbl unwind_lbl anns obs |];
    cbn [sccp_rewrite_term];
    try rewrite !subst_exp_at_empty;
    try rewrite sccp_rewrite_call_args_empty, sccp_rewrite_obs_empty;
    reflexivity.
Qed.

Lemma sccp_rewrite_phis_empty (fargs : list local_id) (c : CFG.cfg dtyp)
  (md_in : rmap (list raw_id)) (bid_src : block_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp))) :
  sccp_rewrite_phis fargs c [] md_in (RM.empty const_val) bid_src phis = phis.
Proof.
  induction phis as [| [[x [fm dt args]] md] rest IH]; [reflexivity |].
  cbn [sccp_rewrite_phis List.map].
  f_equal; [| exact IH].
  do 3 f_equal.
  unfold sccp_rewrite_phi_args;
    induction args as [| [pred0 op0] r_args IHa]; [reflexivity |].
  cbn [List.map sccp_in_edges existsb]; f_equal; exact IHa.
Qed.

(** Block-address preservation ([Hba] obligation of [lift_cfg_with_args_local_pass]). *)
Lemma exp_block_addresses_const_to_lit (cv : const_val) (dt_cv : dtyp) (e_lit : exp dtyp) :
  const_to_lit_exp cv = Some (dt_cv, e_lit) ->
  exp_block_addresses e_lit = [].
Proof.
  destruct cv as [sz val]; cbn [const_to_lit_exp].
  destruct (Pos.eq_dec sz 1%positive) as [Heq | _].
  - intros H; inversion H; subst; reflexivity.
  - destruct (sccp_z_to_lit_checked (@Integers.unsigned sz val)); [| discriminate].
    intros H; inversion H; subst; reflexivity.
Qed.

Lemma exp_block_addresses_const_to_exp_at (cv : const_val) (top : option dtyp) (ec : exp dtyp) :
  const_to_exp_at cv top = Some ec ->
  exp_block_addresses ec = [].
Proof.
  unfold const_to_exp_at.
  destruct (const_to_lit_exp cv) as [[dt_cv e_lit] |] eqn:Elit; [| discriminate].
  destruct top as [dt |].
  - destruct (dtyp_eqb dt dt_cv); [| discriminate].
    intros H; inversion H; subst ec.
    eapply exp_block_addresses_const_to_lit, Elit.
  - intros H; inversion H; subst ec; cbn [mk_copy_exp exp_block_addresses app].
    rewrite (exp_block_addresses_const_to_lit cv dt_cv e_lit Elit); reflexivity.
Qed.

Lemma sccp_flat_map_ba_subst (cm : rmap const_val) (defs : list raw_id)
  (es : list (dtyp * exp dtyp))
  (IH : forall p, In p es ->
          forall top, exp_block_addresses (subst_exp_at cm defs top (snd p)) =
                      exp_block_addresses (snd p)) :
  flat_map (fun x => exp_block_addresses (snd x))
    ((fix go (l : list (dtyp * exp dtyp)) : list (dtyp * exp dtyp) :=
        match l with
        | [] => []
        | (dt, ex) :: rest => (dt, subst_exp_at cm defs (Some dt) ex) :: go rest
        end) es) =
  flat_map (fun x => exp_block_addresses (snd x)) es.
Proof.
  induction es as [| [dt ex] rest IHr]; [reflexivity |].
  cbn [flat_map snd].
  pose proof (IH (dt, ex) (or_introl Logic.eq_refl) (Some dt)) as Hhd;
    cbn [snd] in Hhd; rewrite Hhd.
  f_equal; apply IHr; intros p Hp; apply (IH p (or_intror Hp)).
Qed.

Lemma exp_block_addresses_subst (cm : rmap const_val) (defs : list raw_id) :
  forall (e : exp dtyp) (top : option dtyp),
    exp_block_addresses (subst_exp_at cm defs top e) = exp_block_addresses e.
Proof.
  apply (@exp_ind_full dtyp
           (fun e => forall top,
              exp_block_addresses (subst_exp_at cm defs top e) = exp_block_addresses e)
           (fun _ => True));
    try (intros; reflexivity);
    try exact I.
  - intros [gid | y] top; [reflexivity |].
    cbn [subst_exp_at].
    destruct (in_raw_ids y defs); [| reflexivity].
    destruct (RM.find y cm) as [cv |]; [| reflexivity].
    destruct (const_to_exp_at cv top) as [ec |] eqn:Eec; [| reflexivity].
    eapply exp_block_addresses_const_to_exp_at, Eec.
  - intros es IH top; cbn [subst_exp_at exp_block_addresses]; apply sccp_flat_map_ba_subst, IH.
  - intros es IH top; cbn [subst_exp_at exp_block_addresses]; apply sccp_flat_map_ba_subst, IH.
  - intros es IH top; cbn [subst_exp_at exp_block_addresses]; apply sccp_flat_map_ba_subst, IH.
  - intros es IH top; cbn [subst_exp_at exp_block_addresses]; apply sccp_flat_map_ba_subst, IH.
  - intros es IH top; cbn [subst_exp_at exp_block_addresses]; apply sccp_flat_map_ba_subst, IH.
  - intros iop dt e1 e2 IH1 IH2 top; cbn [subst_exp_at exp_block_addresses].
    rewrite IH1, IH2; reflexivity.
  - intros fm [dt e1] IH1 top; cbn [snd] in IH1; cbn [subst_exp_at exp_block_addresses].
    apply IH1.
  - intros ss cmp_op dt e1 e2 IH1 IH2 top; cbn [subst_exp_at exp_block_addresses].
    rewrite IH1, IH2; reflexivity.
  - intros fop fm dt e1 e2 IH1 IH2 top; cbn [subst_exp_at exp_block_addresses].
    rewrite IH1, IH2; reflexivity.
  - intros fcmp_op fm dt e1 e2 IH1 IH2 top; cbn [subst_exp_at exp_block_addresses].
    rewrite IH1, IH2; reflexivity.
  - intros conv dt_f e1 dt_t IH1 top; cbn [subst_exp_at exp_block_addresses]; apply IH1.
  - intros flags dt1 [dt2 ep] idxs IHp IHi top; cbn [snd] in IHp.
    cbn [subst_exp_at exp_block_addresses].
    rewrite IHp, (sccp_flat_map_ba_subst cm defs idxs IHi); reflexivity.
  - intros [dt1 e1] [dt2 e2] IH1 IH2 top; cbn [snd] in *; cbn [subst_exp_at exp_block_addresses].
    rewrite IH1, IH2; reflexivity.
  - intros [dt1 e1] [dt2 e2] [dt3 e3] IH1 IH2 IH3 top; cbn [snd] in *.
    cbn [subst_exp_at exp_block_addresses]; rewrite IH1, IH2, IH3; reflexivity.
  - intros [dt1 e1] [dt2 e2] [dt3 e3] IH1 IH2 IH3 top; cbn [snd] in *.
    cbn [subst_exp_at exp_block_addresses]; rewrite IH1, IH2, IH3; reflexivity.
  - intros [dt1 e1] idxs IH1 top; cbn [snd] in IH1; cbn [subst_exp_at exp_block_addresses].
    apply IH1.
  - intros [dt1 e1] [dt2 e2] idxs IH1 IH2 top; cbn [snd] in *.
    cbn [subst_exp_at exp_block_addresses]; rewrite IH1, IH2; reflexivity.
  - intros fm [dtc ec] [dt1 e1] [dt2 e2] IHc IH1 IH2 top; cbn [snd] in *.
    cbn [subst_exp_at exp_block_addresses]; rewrite IHc, IH1, IH2; reflexivity.
  - intros [dt e1] IH1 top; cbn [snd] in IH1; cbn [subst_exp_at exp_block_addresses]; apply IH1.
  - intros md _ top; destruct md as [| | [dt ex] | | | |]; reflexivity.
  - intros [dt e1] IH1 top; cbn [snd] in IH1; cbn [subst_exp_at exp_block_addresses]; apply IH1.
Qed.

Lemma sccp_call_args_ba (cm : rmap const_val) (defs : list raw_id)
  (args : list (texp dtyp * list param_attr)) :
  texps_block_addresses (List.map fst (sccp_rewrite_call_args cm defs args)) =
  texps_block_addresses (List.map fst args).
Proof.
  induction args as [| [[t op] attrs] rest IH]; [reflexivity |].
  unfold sccp_rewrite_call_args, texps_block_addresses in *;
    cbn [List.map fst flat_map snd] in *.
  rewrite exp_block_addresses_subst, IH; reflexivity.
Qed.

Lemma instr_block_addresses_rewrite (cm : rmap const_val) (defs : list raw_id)
  (ins : instr dtyp) :
  instr_block_addresses (sccp_rewrite_instr cm defs ins) = instr_block_addresses ins.
Proof.
  destruct ins as [msg | op | fn args anns obs | dt anns | dt [du ptr] anns
                   | [dt val] [du ptr] anns | sc ord | cpx | armw | [t ptr_exp] argty
                   | rty cl cs];
    cbn [sccp_rewrite_instr instr_block_addresses texps_block_addresses flat_map snd];
    try rewrite !exp_block_addresses_subst;
    try reflexivity.
  - f_equal; apply (sccp_call_args_ba cm defs args).
  - destruct cpx as [cw cv [pt pv] [ct cv_e] [nt nv] cs_o cso cfo cal]; cbn.
    rewrite !exp_block_addresses_subst; reflexivity.
  - destruct armw as [av aop [pt pv] [at_t av_e] as_o aord aal]; cbn.
    rewrite !exp_block_addresses_subst; reflexivity.
Qed.

Lemma code_block_addresses_rewrite (cm : rmap const_val) (cd : code dtyp) :
  forall cur_defs,
    flat_map (fun '(_, i, _) => instr_block_addresses i) (sccp_rewrite_code cm cur_defs cd) =
    flat_map (fun '(_, i, _) => instr_block_addresses i) cd.
Proof.
  induction cd as [| [[iid ins] md] rest IH]; intros cur_defs; [reflexivity |].
  cbn [sccp_rewrite_code flat_map].
  rewrite instr_block_addresses_rewrite, IH; reflexivity.
Qed.

Lemma term_block_addresses_rewrite_nil (allow_fold : bool) (cm : rmap const_val)
  (defs_end : list raw_id) (tm : terminator dtyp) :
  term_block_addresses tm = [] ->
  term_block_addresses (sccp_rewrite_term allow_fold cm defs_end tm) = [].
Proof.
  destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt ex] def_br dests
                  | [dt ex] brs fn | [dt ex] | fn args to_lbl unwind_lbl anns obs |];
    cbn [sccp_rewrite_term term_block_addresses texps_block_addresses flat_map snd];
    try (rewrite ?exp_block_addresses_subst; intros H; exact H).
  - destruct allow_fold.
    + destruct (sccp_branch_target cm defs_end dt op br1 br2).
      * intros _; reflexivity.
      * cbn [term_block_addresses texps_block_addresses flat_map snd].
        rewrite exp_block_addresses_subst; intros H; exact H.
    + cbn [term_block_addresses texps_block_addresses flat_map snd].
      rewrite exp_block_addresses_subst; intros H; exact H.
  - intros H; apply app_eq_nil in H as [Hfn Hargs].
    rewrite Hfn; cbn [app].
    pose proof (sccp_call_args_ba cm defs_end args) as Hba.
    unfold texps_block_addresses in Hba; rewrite Hba; exact Hargs.
Qed.

Lemma phis_block_addresses_rewrite (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
  (bid : block_id) (phis : list (local_id * phi dtyp * list (metadata dtyp))) :
  flat_map (fun '(_, Phi _ _ args, _) => flat_map (fun x => exp_block_addresses (snd x)) args)
    (sccp_rewrite_phis fargs c exec_edges md_in cm bid phis) =
  flat_map (fun '(_, Phi _ _ args, _) => flat_map (fun x => exp_block_addresses (snd x)) args)
    phis.
Proof.
  induction phis as [| [[x [fm dt args]] md] rest IH]; [reflexivity |].
  cbn [sccp_rewrite_phis List.map flat_map].
  f_equal; [| exact IH].
  induction args as [| [pred op] r_args IHa]; [reflexivity |].
  cbn [sccp_rewrite_phi_args List.map flat_map].
  fold (sccp_rewrite_phi_args fargs c exec_edges md_in cm bid dt r_args).
  destruct (sccp_in_edges (pred, bid) exec_edges); cbn [snd].
  - rewrite exp_block_addresses_subst, IHa; reflexivity.
  - rewrite IHa; reflexivity.
Qed.

Lemma block_block_addresses_rewrite_nil (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
  (b : block dtyp) :
  block_block_addresses b = [] ->
  block_block_addresses (sccp_rewrite_block fargs c exec_edges md_in cm b) = [].
Proof.
  unfold sccp_rewrite_block; cbn zeta.
  destruct (sccp_is_reachable_blk exec_edges (blk_id b)); [| intros H; exact H].
  unfold block_block_addresses; destruct (blk_term b) as [[tiid tm] tmd]; cbn [blk_phis blk_code blk_term].
  intros H.
  apply app_eq_nil in H as [Hp Hrest].
  apply app_eq_nil in Hrest as [Hc Ht].
  rewrite phis_block_addresses_rewrite, code_block_addresses_rewrite.
  rewrite Hp, Hc, (term_block_addresses_rewrite_nil _ _ _ tm Ht); reflexivity.
Qed.

Lemma sccp_cfg_block_addresses (fargs : list local_id) (c : CFG.cfg dtyp) :
  flat_map block_block_addresses (blks (sccp_cfg fargs c)) =
  flat_map block_block_addresses (blks c).
Proof.
  unfold sccp_cfg; cbn zeta.
  destruct (sccp_check_guards fargs c) eqn:Hg; [| reflexivity].
  destruct (sccp_solve fargs c) as [exec_edges lm].
  set (md_in := sccp_compute_must_def fargs c exec_edges).
  set (cm := sccp_build_cert fargs c exec_edges md_in lm).
  destruct (check_sccp_valid fargs c exec_edges md_in cm); [| reflexivity].
  cbn [blks].
  unfold sccp_check_guards in Hg.
  apply Bool.andb_true_iff in Hg as [Hg1 _].
  apply Bool.andb_true_iff in Hg1 as [Hba _].
  apply cfg_no_block_addresses_nil in Hba.
  rewrite Hba.
  induction (blks c) as [| b rest IH]; [reflexivity |].
  cbn [flat_map] in Hba; apply app_eq_nil in Hba as [Hb Hrest].
  cbn [List.map flat_map].
  rewrite (block_block_addresses_rewrite_nil fargs c exec_edges md_in cm b Hb).
  apply (IH Hrest).
Qed.

(** Constant-operation soundness under arbitrary [Params]. *)
Section ConstEvalSound.
  Context {Pa : Params}.

  Lemma const_to_lit_exp_sound (cv : const_val) (dt_cv : dtyp) (e_lit : exp dtyp) :
    const_to_lit_exp cv = Some (dt_cv, e_lit) ->
    @denote_exp Pa (Some dt_cv) e_lit ≅ Ret (@const_to_dvalue Pa cv).
  Proof using.
    destruct cv as [sz val]; cbn [const_to_lit_exp].
    destruct (Pos.eq_dec sz 1%positive) as [Heq | Hne].
    - rewrite <- (sccp_eq_sym_involutive Heq).
      revert val; generalize (Logic.eq_sym Heq); clear Heq; intros p; destruct p; intros val.
      cbn [eq_rect eq_sym]; intros H; inversion H; subst dt_cv e_lit; clear H.
      pose proof (sccp_bit_int_1_cases val) as Hcases.
      destruct (@Integers.unsigned 1 val =? 1)%Z; subst val; reflexivity.
    - destruct (sccp_z_to_lit_checked (@Integers.unsigned sz val)) as [lit |] eqn:Elit;
        [| discriminate].
      intros H; inversion H; subst dt_cv e_lit; clear H.
      cbn [denote_exp denote_int_syntax_as_int coerce_integer_to_int
           VellvmIntegers.repr VellvmIntegers.VInt_Bounded
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_itree
           EOU_to_itree const_to_dvalue].
      rewrite (sccp_z_to_lit_checked_sound _ _ Elit), (@Integers.repr_unsigned sz val).
      reflexivity.
  Qed.

  Lemma const_to_exp_at_sound (cv : const_val) (top : option dtyp) (ec : exp dtyp) :
    const_to_exp_at cv top = Some ec ->
    @denote_exp Pa top ec ≅ Ret (@const_to_dvalue Pa cv).
  Proof using.
    unfold const_to_exp_at.
    destruct (const_to_lit_exp cv) as [[dt_cv e_lit] |] eqn:Elit; [| discriminate].
    destruct top as [dt |].
    - destruct (dtyp_eqb dt dt_cv) eqn:Heqb; [| discriminate].
      intros H; inversion H; subst ec; clear H.
      apply dtyp_eqb_eq in Heqb; subst dt.
      apply const_to_lit_exp_sound, Elit.
    - intros H; inversion H; subst ec; clear H.
      etransitivity; [apply denote_mk_copy_exp |].
      apply const_to_lit_exp_sound, Elit.
  Qed.

  Lemma eval_const_iop_same_sound (sz : positive) (iop : ibinop)
    (x y r : @bit_int sz) :
    eval_const_iop_same sz iop x y = Some r ->
    @eval_int_op Pa (@bit_int sz) _ _ iop x y = raise_ret (@DVALUE_I Pa sz r).
  Proof using.
    destruct iop as [nuw nsw | nuw nsw | nuw nsw | nuw nsw | ex | ex | ex | ex | | | | b |];
      cbn [eval_const_iop_same eval_int_op
           VellvmIntegers.mequ VellvmIntegers.madd VellvmIntegers.madd_carry VellvmIntegers.madd_overflow
           VellvmIntegers.msub VellvmIntegers.msub_borrow VellvmIntegers.msub_overflow
           VellvmIntegers.mmul VellvmIntegers.mdivu VellvmIntegers.mdivs VellvmIntegers.mmodu VellvmIntegers.mmods
           VellvmIntegers.mshl VellvmIntegers.mshr VellvmIntegers.mshru VellvmIntegers.mnegative
           VellvmIntegers.mand VellvmIntegers.mor VellvmIntegers.mxor
           VellvmIntegers.mbitwidth VellvmIntegers.mzero VellvmIntegers.mone
           VellvmIntegers.mmin_signed VellvmIntegers.mmax_signed VellvmIntegers.munsigned VellvmIntegers.msigned
           VellvmIntegers.mdtyp_of_int
           VellvmIntegers.VIntVMemInt VellvmIntegers.VInt_Bounded
           VellvmIntegers.equ VellvmIntegers.add VellvmIntegers.add_carry VellvmIntegers.add_overflow
           VellvmIntegers.sub VellvmIntegers.sub_borrow VellvmIntegers.sub_overflow
           VellvmIntegers.mul VellvmIntegers.divu VellvmIntegers.divs VellvmIntegers.modu VellvmIntegers.mods
           VellvmIntegers.shl VellvmIntegers.shr VellvmIntegers.shru VellvmIntegers.negative
           VellvmIntegers.and VellvmIntegers.or VellvmIntegers.xor
           VellvmIntegers.bitwidth VellvmIntegers.zero VellvmIntegers.one
           VellvmIntegers.min_signed VellvmIntegers.max_signed VellvmIntegers.unsigned VellvmIntegers.signed
           dvp option_pred from_option liftM Functor.fmap Functor_Monad EOU_monad Monad_option
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret tdb ToDvalue_Int
           dtyp_base_eqb dtyp_base_eq_dec negb].
    - match goal with |- context [if orb ?a ?b then _ else _] => destruct (orb a b) end;
        [discriminate | intros H; inversion H; reflexivity].
    - match goal with |- context [if orb ?a ?b then _ else _] => destruct (orb a b) end;
        [discriminate | intros H; inversion H; reflexivity].
    - destruct (Pos.eqb sz 1); [intros H; inversion H; reflexivity |].
      match goal with |- context [if orb ?a ?b then _ else _] => destruct (orb a b) end;
        [discriminate | intros H; inversion H; reflexivity].
    - destruct (@Integers.unsigned sz y >=? Z.pos sz)%Z; [discriminate |].
      destruct (andb nuw _); [discriminate |].
      destruct nsw.
      + destruct (negb _); [discriminate | intros H; inversion H; reflexivity].
      + intros H; inversion H; reflexivity.
    - destruct (@Integers.unsigned sz y =? 0)%Z; [discriminate |].
      destruct (andb ex _); [discriminate | intros H; inversion H; reflexivity].
    - destruct (@Integers.signed sz y =? 0)%Z; [discriminate |].
      destruct ((_ =? _)%Z && (_ =? _)%Z)%bool; [discriminate |].
      destruct (andb ex _); [discriminate | intros H; inversion H; reflexivity].
    - rewrite Bool.andb_true_r.
      destruct (@Integers.unsigned sz y >=? Z.pos sz)%Z; [discriminate |].
      destruct (andb ex _); [discriminate | intros H; inversion H; reflexivity].
    - destruct (@Integers.unsigned sz y >=? Z.pos sz)%Z; [discriminate |].
      destruct (andb ex _); [discriminate | intros H; inversion H; reflexivity].
    - destruct (@Integers.unsigned sz y =? 0)%Z; [discriminate | intros H; inversion H; reflexivity].
    - destruct (@Integers.signed sz y =? 0)%Z; [discriminate |].
      destruct ((_ =? _)%Z && (_ =? _)%Z)%bool; [discriminate | intros H; inversion H; reflexivity].
    - intros H; inversion H; reflexivity.
    - destruct b.
      + destruct (@Integers.eq sz _ _); [intros H; inversion H; reflexivity | discriminate].
      + intros H; inversion H; reflexivity.
    - intros H; inversion H; reflexivity.
  Qed.

  Lemma eval_const_iop_sound (iop : ibinop) (c1 c2 cr : const_val) :
    eval_const_iop iop c1 c2 = Some cr ->
    @eval_iop Pa iop (const_to_dvalue c1) (const_to_dvalue c2) =
    raise_ret (const_to_dvalue cr).
  Proof using.
    destruct c1 as [sz1 x], c2 as [sz2 y]; cbn [eval_const_iop].
    destruct (Pos.eq_dec sz2 sz1) as [<- | _]; [| discriminate].
    cbn [eq_rect const_to_dvalue].
    destruct (eval_const_iop_same sz2 iop x y) as [r |] eqn:Er; [| discriminate].
    intros H; inversion H; subst cr; clear H.
    unfold eval_iop, eval_iop_integer_base.
    rewrite sccp_pos_eq_dec_refl; cbn [eq_rec_r eq_rec eq_rect eq_sym].
    rewrite (eval_const_iop_same_sound sz2 iop x y r Er); reflexivity.
  Qed.

  Lemma eval_const_icmp_sound (samesign_f : bool) (cmp_op : icmp)
    (c1 c2 cr : const_val) :
    eval_const_icmp samesign_f cmp_op c1 c2 = Some cr ->
    @eval_icmp Pa samesign_f cmp_op (const_to_dvalue c1) (const_to_dvalue c2) =
    raise_ret (const_to_dvalue cr).
  Proof using.
    destruct c1 as [sz1 x], c2 as [sz2 y]; cbn [eval_const_icmp].
    destruct (Pos.eq_dec sz2 sz1) as [<- | _]; [| discriminate].
    unfold eval_const_icmp_same; cbn [eq_rect const_to_dvalue]; intros H.
    destruct (samesign_f && negb (@VellvmIntegers.samesign (@bit_int sz2) (VellvmIntegers.VInt_Bounded sz2) x y))%bool
      eqn:Hss; [discriminate H |].
    inversion H; subst cr; clear H.
    unfold eval_icmp, eval_icmp_base.
    rewrite sccp_pos_eq_dec_refl; cbn [eq_rec_r eq_rec eq_rect eq_sym].
    destruct cmp_op;
      cbn [eval_int_icmp VellvmIntegers.mcmp VellvmIntegers.mcmpu VellvmIntegers.msamesign VellvmIntegers.mdtyp_of_int
           VellvmIntegers.VIntVMemInt VellvmIntegers.VInt_Bounded
           VellvmIntegers.cmp VellvmIntegers.cmpu Integers.cmp Integers.cmpu dtyp_base_eq_dec
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad liftM Functor.fmap Functor_Monad
           const_to_dvalue VellvmIntegers.one VellvmIntegers.zero];
      rewrite Hss; cbn iota;
      match goal with
      | |- context [if ?b then @DVALUE_I _ _ _ else @DVALUE_I _ _ _] => destruct b
      end;
      reflexivity.
  Qed.

  Lemma eval_const_pconv_sound (pconv : pure_conversion) (dt_from : dtyp)
    (c1 : const_val) (dt_to : dtyp) (cr : const_val) :
    eval_const_pconv pconv dt_from c1 dt_to = Some cr ->
    @convert_pure Pa pconv dt_from (const_to_dvalue c1) dt_to =
    raise_ret (const_to_dvalue cr).
  Proof using.
    destruct c1 as [sz_from i1]; cbn [eval_const_pconv].
    destruct dt_from as [b_from | |]; [| discriminate | discriminate].
    destruct b_from; try discriminate.
    destruct dt_to as [b_to | |]; [| discriminate | discriminate].
    destruct b_to; try discriminate.
    destruct pconv; try discriminate.
    - destruct (Pos.eqb _ sz_from && (_ <? sz_from)%positive)%bool eqn:Hok;
        [| discriminate].
      cbn [const_to_dvalue convert_pure get_base_conversion_type convert_pure_base].
      rewrite Hok.
      destruct (_ || _)%bool; [discriminate |].
      intros H; inversion H; subst cr; reflexivity.
    - destruct (Pos.eqb _ sz_from && (sz_from <? _)%positive)%bool eqn:Hok;
        [| discriminate].
      cbn [const_to_dvalue convert_pure get_base_conversion_type convert_pure_base].
      rewrite Hok.
      destruct (_ && (@Integers.signed sz_from i1 <? 0)%Z)%bool; [discriminate |].
      intros H; inversion H; subst cr; reflexivity.
    - destruct (Pos.eqb _ sz_from && (sz_from <? _)%positive)%bool eqn:Hok;
        [| discriminate].
      cbn [const_to_dvalue convert_pure get_base_conversion_type convert_pure_base].
      rewrite Hok.
      intros H; inversion H; subst cr; reflexivity.
  Qed.

End ConstEvalSound.


(** * 5. Local-Environment Simulation Primitives and Expression Soundness *)

Section SCCPSimulation.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Hint Resolve cfg_local_sim__mon : paco.

  Lemma sccp_dvalue_ind (P : @dvalue PaV -> Prop)
    (HBase : forall db : @dvalue_base PaV, P (DVALUE_Base db))
    (HStruct : forall (p : bool) (fs : list (@dvalue PaV)),
        Forall P fs -> P (DVALUE_Struct p fs))
    (HArray : forall (v : bool) (es : list (@dvalue PaV)),
        Forall P es -> P (DVALUE_Array v es)) :
    forall dv : @dvalue PaV, P dv.
  Proof using.
    exact
      (fix IH (dv : @dvalue PaV) {struct dv} : P dv :=
         let fix go (l : list (@dvalue PaV)) {struct l} : Forall P l :=
           match l with
           | [] => Forall_nil _
           | x :: xs => @Forall_cons (@dvalue PaV) P x xs (IH x) (go xs)
           end
         in
         match dv with
         | DVALUE_Base db => HBase db
         | DVALUE_Struct p fs => HStruct p fs (go fs)
         | DVALUE_Array v es => HArray v es (go es)
         end).
  Qed.

  (** ** [withCall] Equations and [cfg_local_sim] Combinators *)

  Lemma withCall_ret {R : Type} (x : R) :
    @withCall PaV R (Ret x) ≅ Ret x.
  Proof using.
    unfold withCall; apply translate_ret.
  Qed.

  Lemma withCall_bind {R S : Type}
    (t : @MCFGtop PaV R) (k : R -> @MCFGtop PaV S) :
    @withCall PaV S (ITree.bind t k) ≅
    ITree.bind (@withCall PaV R t) (fun x => @withCall PaV S (k x)).
  Proof using.
    unfold withCall; apply translate_bind.
  Qed.

  Lemma withCall_lread_bind {R : Type} (x : local_id)
    (k : @dvalue PaV -> @CFGtop PaV R) :
    ITree.bind (@withCall PaV (@dvalue PaV) (lread x)) k ≅
    ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k.
  Proof using.
    unfold withCall, lread, ITree.trigger.
    pstep; red; repeat (rewrite observe_bind || rewrite observe_translate); cbn.
    constructor; intros v; left.
    change (paco2 (eqit_ eq false false id) bot2
              (ITree.bind (translate inr1 (Ret v)) k) (ITree.bind (Ret v) k))
      with (ITree.bind (translate inr1 (Ret v)) k ≅ ITree.bind (Ret v) k).
    rewrite translate_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma withCall_lread (x : local_id) :
    @withCall PaV (@dvalue PaV) (lread x) ≅
    ITree.bind (ITree.trigger (subevent _ (LocalRead x))) (fun v => Ret v).
  Proof using.
    rewrite <- (Eqit.bind_ret_r (@withCall PaV (@dvalue PaV) (lread x))).
    apply withCall_lread_bind.
  Qed.

  Lemma cfg_local_sim_withCall_ret {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (r1 : R1) (r2 : R2) :
    RR env1 env2 r1 r2 ->
    cfg_local_sim RR env1 env2 (@withCall PaV R1 (Ret r1)) (@withCall PaV R2 (Ret r2)).
  Proof using.
    intros HRR.
    eapply cfg_local_sim_obs_eq;
      [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
    apply cfg_local_sim_ret, HRR.
  Qed.

  Lemma cfg_local_sim_withCall_bind {R1 R2 S1 S2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (RS : @local_env PaV -> @local_env PaV -> S1 -> S2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @MCFGtop PaV R1) (t2 : @MCFGtop PaV R2)
    (k1 : R1 -> @MCFGtop PaV S1) (k2 : R2 -> @MCFGtop PaV S2)
    (Ht : cfg_local_sim RR env1 env2 (@withCall PaV R1 t1) (@withCall PaV R2 t2))
    (Hk : forall e1' e2' r1 r2,
            RR e1' e2' r1 r2 ->
            cfg_local_sim RS e1' e2' (@withCall PaV S1 (k1 r1)) (@withCall PaV S2 (k2 r2))) :
    cfg_local_sim RS env1 env2
      (@withCall PaV S1 (ITree.bind t1 k1))
      (@withCall PaV S2 (ITree.bind t2 k2)).
  Proof using.
    eapply cfg_local_sim_obs_eq;
      [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
    eapply cfg_local_sim_bind; [exact Ht | exact Hk].
  Qed.

  Lemma cfg_local_sim_trigger_sync {R : Type}
    (env1 env2 : @local_env PaV) (e : @CFGEtop PaV R)
    (Hsync : sync_non_local_cfg e = true) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (ITree.trigger e) (ITree.trigger e).
  Proof using.
    pstep; apply CLS_Step; unfold cls_step_body, ITree.trigger; cbn [observe].
    right; left; split; [exact Hsync | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_raise_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) :
    cfg_local_sim RR env1 env2 (raise msg) (raise msg).
  Proof using.
    unfold raise, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_withCall_raise_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) :
    cfg_local_sim RR env1 env2 (@withCall PaV R1 (raise msg)) (@withCall PaV R2 (raise msg)).
  Proof using.
    unfold withCall, raise, trigger_cast, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    repeat (rewrite observe_bind || rewrite observe_translate); cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_raiseUB_cut {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) (t2 : @CFGtop PaV R2) :
    cfg_local_sim RR env1 env2 (raiseUB msg) t2.
  Proof using.
    unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    left; reflexivity.
  Qed.

  Lemma cfg_local_sim_raiseLLVM_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (ex : @exc PaV) :
    cfg_local_sim RR env1 env2 (raiseLLVM ex) (raiseLLVM ex).
  Proof using.
    unfold raiseLLVM, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_EOU_ret_sync {R : Type}
    (env1 env2 : @local_env PaV) (m : EOU R) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ m = raise_ret r1)
      env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply cfg_local_sim_raise_sync.
    - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
      right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
    - apply cfg_local_sim_raiseUB_cut.
    - apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_EOU_sync {R : Type}
    (env1 env2 : @local_env PaV) (m : EOU R) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    eapply cfg_local_sim_weaken; [| apply cfg_local_sim_EOU_ret_sync].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_EOU_sync {R : Type}
    (env1 env2 : @local_env PaV) (m : EOU R) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV R (EOU_to_itree m)) (@withCall PaV R (EOU_to_itree m)).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply cfg_local_sim_withCall_raise_sync.
    - unfold withCall, raiseOOM, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
        unfold cls_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn.
      right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
    - unfold withCall, raiseUB, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
        unfold cls_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
    - apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_gread_sync
    (env1 env2 : @local_env PaV) (id : raw_id) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (gread id) (gread id).
  Proof using.
    unfold gread; apply cfg_local_sim_trigger_sync; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_gread_sync
    (env1 env2 : @local_env PaV) (id : raw_id) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (gread id))
                (@withCall PaV (@dvalue PaV) (gread id)).
  Proof using.
    unfold withCall, gread, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_lread_sync
    (env1 env2 : @local_env PaV) (x : local_id) :
    Maps.lookup x env1 = Maps.lookup x env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (lread x))
                (@withCall PaV (@dvalue PaV) (lread x)).
  Proof using.
    intros Hlk.
    unfold withCall, lread, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate;
      cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1].
    right; right.
    split; [reflexivity | split; [exact Hlk |]].
    intros v _; left.
    apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_lwrite_both
    (env1 env2 : @local_env PaV) (id : local_id) (v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = Maps.add id v env1 /\ e2' = Maps.add id v env2 /\ r1 = r2)
      env1 env2 (lwrite id v) (lwrite id v).
  Proof using.
    pstep; eapply CLS_WriteL; [symmetry; apply Eqit.bind_ret_r |].
    eapply CLS_WriteR; [symmetry; apply Eqit.bind_ret_r |].
    apply CLS_Step; cbn; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_draw_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (draw dt))
                (@withCall PaV (@dvalue PaV) (draw dt)).
  Proof using.
    unfold withCall, draw, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate;
      cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1].
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_conv_sync
    (env1 env2 : @local_env PaV)
    (ic : impure_conversion) (dt_from : dtyp) (dv : @dvalue PaV) (dt_to : dtyp) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (conv ic dt_from dv dt_to))
                (@withCall PaV (@dvalue PaV) (conv ic dt_from dv dt_to)).
  Proof using.
    unfold withCall, conv, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_convert_sync
    (env1 env2 : @local_env PaV)
    (ct : conversion_type) (dt_from : dtyp) (dv : @dvalue PaV) (dt_to : dtyp) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (convert ct dt_from dv dt_to))
                (@withCall PaV (@dvalue PaV) (convert ct dt_from dv dt_to)).
  Proof using.
    destruct ct as [| pconv | ic]; cbn [convert].
    - destruct (dtyp_eqb dt_from dt_to).
      + cbn [ExtLib.Structures.Monad.ret Monad_itree].
        apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
      + destruct (bit_sizeof_dtyp dt_from =? bit_sizeof_dtyp dt_to)%N.
        * apply cfg_local_sim_withCall_EOU_sync.
        * apply cfg_local_sim_withCall_raise_sync.
    - apply cfg_local_sim_withCall_EOU_sync.
    - apply cfg_local_sim_withCall_conv_sync.
  Qed.

  Lemma withCall_fmap_ret {A B : Type} (f : A -> B) (x : A) :
    @withCall PaV B (f <$> ret x) ≅ Ret (f x).
  Proof using.
    change (ret x) with (Ret x : @MCFGtop PaV A).
    unfold withCall; pstep; red; rewrite !observe_translate;
      unfold Functor.fmap, Functor_itree, ITree.map;
      rewrite ?observe_bind; cbn; constructor; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_freeze_sync
    (dv : @dvalue PaV) :
    forall (dt : dtyp) (env1 env2 : @local_env PaV),
      cfg_local_sim
        (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
        env1 env2 (@withCall PaV (@dvalue PaV) (freeze dt dv))
                  (@withCall PaV (@dvalue PaV) (freeze dt dv)).
  Proof using.
    induction dv as [db | p fs IHfs | v es IHes] using sccp_dvalue_ind;
      intros dt env1 env2.
    - cbn [freeze].
      destruct db as [pt | sz i | ip | d | f | | | bsz bv]; cbn [freeze_base];
        lazymatch goal with
        | |- cfg_local_sim _ _ _ (withCall (_ <$> ret _)) (withCall (_ <$> ret _)) =>
            eapply cfg_local_sim_obs_eq;
              [symmetry; apply withCall_fmap_ret | symmetry; apply withCall_fmap_ret |];
            apply cfg_local_sim_ret; repeat split; reflexivity
        | _ => idtac
        end.
      + apply cfg_local_sim_withCall_draw_sync.
      + destruct bv as [bp bidx | bi | bits]; cbn [freeze_base];
          lazymatch goal with
          | |- cfg_local_sim _ _ _ (withCall (_ <$> ret _)) (withCall (_ <$> ret _)) =>
              eapply cfg_local_sim_obs_eq;
                [symmetry; apply withCall_fmap_ret | symmetry; apply withCall_fmap_ret |];
              apply cfg_local_sim_ret; repeat split; reflexivity
          | _ => idtac
          end.
        destruct (existsb is_poison_bit bits).
        * eapply cfg_local_sim_withCall_bind; [apply cfg_local_sim_withCall_draw_sync |].
          intros ? ? x _ (-> & -> & <-).
          cbn [ExtLib.Structures.Monad.ret Monad_itree].
          apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_fmap_ret | symmetry; apply withCall_fmap_ret |].
          apply cfg_local_sim_ret; repeat split; reflexivity.
    - destruct dt as [| p' dts |];
        [cbn [freeze]; apply cfg_local_sim_withCall_raise_sync
        |
        | cbn [freeze]; apply cfg_local_sim_withCall_raise_sync].
      cbn [freeze].
      eapply cfg_local_sim_withCall_bind with
        (RR := fun e1' e2' (r1 r2 : list (@dvalue PaV)) => e1' = env1 /\ e2' = env2 /\ r1 = r2).
      + lazymatch goal with
        | |- cfg_local_sim ?R ?e1 ?e2 (withCall (?go ?flds dts [])) (withCall (?go ?flds dts [])) =>
            cut (forall acc : list (@dvalue PaV),
                    cfg_local_sim R e1 e2 (withCall (go flds dts acc)) (withCall (go flds dts acc)));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert dts env1 env2;
          induction IHfs as [| fv fvs Hfv _ IH];
          intros [| t ts] env1 env2 acc;
          [| apply cfg_local_sim_withCall_raise_sync
           | apply cfg_local_sim_withCall_raise_sync |].
        * apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
        * eapply cfg_local_sim_withCall_bind; [apply (Hfv t env1 env2) |].
          intros ? ? v' _ (-> & -> & <-); apply IH.
      + intros ? ? val _ (-> & -> & <-).
        apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - destruct dt as [| | v' sz t];
        [cbn [freeze]; apply cfg_local_sim_withCall_raise_sync
        | cbn [freeze]; apply cfg_local_sim_withCall_raise_sync |].
      cbn [freeze].
      eapply cfg_local_sim_withCall_bind with
        (RR := fun e1' e2' (r1 r2 : list (@dvalue PaV)) => e1' = env1 /\ e2' = env2 /\ r1 = r2).
      + lazymatch goal with
        | |- cfg_local_sim ?R ?e1 ?e2 (withCall (?go ?els [])) (withCall (?go ?els [])) =>
            cut (forall acc : list (@dvalue PaV),
                    cfg_local_sim R e1 e2 (withCall (go els acc)) (withCall (go els acc)));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert env1 env2;
          induction IHes as [| ev evs Hev _ IH];
          intros env1 env2 acc.
        * apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
        * eapply cfg_local_sim_withCall_bind; [apply (Hev t env1 env2) |].
          intros ? ? v'' _ (-> & -> & <-); apply IH.
      + intros ? ? val _ (-> & -> & <-).
        apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_assert_dereferenceable_sync
    (env1 env2 : @local_env PaV)
    (or_null : bool) (n : N) (v : @dvalue PaV) (msg : string) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (assert_dereferenceable or_null n v msg)
                (assert_dereferenceable or_null n v msg).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [db | |];
      [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
    destruct db as [p | | | | | | |];
      [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
       | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
       | | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
    - destruct (_ || _).
      + apply cfg_local_sim_ret; repeat split; reflexivity.
      + eapply cfg_local_sim_bind.
        * unfold load; apply cfg_local_sim_trigger_sync; reflexivity.
        * intros ? ? _ _ (-> & -> & _); apply cfg_local_sim_ret; repeat split; reflexivity.
    - apply cfg_local_sim_raiseUB_cut.
  Qed.

  Lemma cfg_local_sim_apply_attrs_sync
    (env1 env2 : @local_env PaV)
    (attrs : list param_attr) (msg : string) (v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (apply_attrs attrs msg v) (apply_attrs attrs msg v).
  Proof using.
    unfold apply_attrs.
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? v' _ (-> & -> & <-).
    eapply cfg_local_sim_bind with
      (RR := fun e1' e2' (r1 r2 : unit) => e1' = env1 /\ e2' = env2 /\ r1 = r2).
    - unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[or_null n] |];
        [| apply cfg_local_sim_ret; repeat split; reflexivity].
      destruct v' as [db | |];
        [destruct db;
         [apply cfg_local_sim_assert_dereferenceable_sync | .. ] | |];
        apply cfg_local_sim_ret; repeat split; reflexivity.
    - intros ? ? _ _ (-> & -> & _); apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_check_call_return_sync
    (env1 env2 : @local_env PaV)
    (fattrs : list fn_attr) (rattrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list (@dvalue PaV)) (res : @exc PaV + @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (check_call_return fattrs rattrs ranges loc args res)
                (check_call_return fattrs rattrs ranges loc args res).
  Proof using.
    unfold check_call_return.
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? _ _ (-> & -> & _).
    destruct res as [ex | v].
    - apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_bind; [apply cfg_local_sim_apply_attrs_sync |].
      intros ? ? v' _ (-> & -> & <-); apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_assume_check_sync
    (env1 env2 : @local_env PaV)
    (f : exp dtyp) (tag loc : string) (vs : list (@dvalue PaV))
    (chk : @assume_bundle_check PaV CFGEtop) :
    bundle_check f tag = Some chk ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (chk loc vs) (chk loc vs).
  Proof using.
    unfold bundle_check; intros Hb.
    destruct (is_llvm_assume f); [| discriminate Hb].
    cbn [assume_bundle_checks List.find] in Hb.
    repeat match goal with
           | H : context [if String.eqb ?a ?b then _ else _] |- _ =>
               destruct (String.eqb a b)
           end;
      cbn [option_map snd] in Hb; try discriminate Hb;
      inversion Hb; subst chk; clear Hb.
    - unfold assume_nonnull, assume_violated, assume_malformed.
      destruct vs as [| p [| ? ?]];
        [apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync].
      destruct (dvalue_ptr_address p) as [a |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (a =? 0)%Z;
        [apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_ret; repeat split; reflexivity].
    - unfold assume_noundef, assume_violated, assume_malformed.
      destruct vs as [| v [| ? ?]];
        [apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync].
      destruct (dvalue_well_defined v);
        [apply cfg_local_sim_ret; repeat split; reflexivity | apply cfg_local_sim_raiseUB_cut].
    - unfold assume_align, assume_violated, assume_malformed.
      destruct vs as [| p [| al off]];
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync |].
      cbv zeta.
      destruct (dvalue_ptr_address p) as [a |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (bundle_uint al) as [n |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end) as [o |];
        [| apply cfg_local_sim_raiseUB_cut].
      destruct (if is_power_of_two n then ((a - o) mod n =? 0)%Z else (a =? 0)%Z);
        [apply cfg_local_sim_ret; repeat split; reflexivity | apply cfg_local_sim_raiseUB_cut].
    - unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]];
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync].
      destruct (dvalue_ptr_address p), (bundle_uint sz);
        [| apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_raiseUB_cut].
      destruct (_ =? 0)%Z;
        [apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_assert_dereferenceable_sync].
    - unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]];
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync].
      destruct (dvalue_ptr_address p), (bundle_uint sz);
        [| apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_raiseUB_cut].
      destruct (_ =? 0)%Z;
        [apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_assert_dereferenceable_sync].
  Qed.


  (** ** Deterministic Local-Read Evaluation and Certificate Matching *)

  Inductive evals_local_to {R : Type} (env : @local_env PaV)
    : @CFGtop PaV R -> R -> Prop :=
  | ELT_Ret t r :
      t ≅ Ret r ->
      evals_local_to env t r
  | ELT_Read t x v k r :
      t ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k ->
      Maps.lookup x env = Some v ->
      evals_local_to env (k v) r ->
      evals_local_to env t r.

  Lemma evals_local_to_obs_eq {R : Type} (env : @local_env PaV)
    (t t' : @CFGtop PaV R) (r : R) :
    t ≅ t' ->
    evals_local_to env t r ->
    evals_local_to env t' r.
  Proof using.
    intros Heq Ht; revert t' Heq;
      destruct Ht as [t0 r0 Hr | t0 x v k r0 Hrd Hlk Hk]; intros t' Heq.
    - apply ELT_Ret; rewrite <- Heq; exact Hr.
    - eapply ELT_Read; [rewrite <- Heq; exact Hrd | exact Hlk | exact Hk].
  Qed.

  Lemma evals_local_to_bind {R S : Type} (env : @local_env PaV)
    (t : @CFGtop PaV R) (r : R)
    (k : R -> @CFGtop PaV S) (s : S) :
    evals_local_to env t r ->
    evals_local_to env (k r) s ->
    evals_local_to env (ITree.bind t k) s.
  Proof using.
    intros Ht Hk; induction Ht as [t0 r0 Hr | t0 x v k0 r0 Hrd Hlk Hrest IH].
    - eapply evals_local_to_obs_eq; [| exact Hk].
      symmetry; rewrite Hr, Eqit.bind_ret_l; reflexivity.
    - eapply ELT_Read; [rewrite Hrd, Eqit.bind_bind; reflexivity | exact Hlk | apply IH, Hk].
  Qed.

  Lemma evals_local_to_withCall_ret {R : Type}
    (env : @local_env PaV) (r : R) :
    evals_local_to env (@withCall PaV R (Ret r)) r.
  Proof using.
    apply ELT_Ret, withCall_ret.
  Qed.

  Lemma evals_local_to_withCall_bind {R S : Type}
    (env : @local_env PaV)
    (t : @MCFGtop PaV R) (r : R)
    (k : R -> @MCFGtop PaV S) (s : S) :
    evals_local_to env (@withCall PaV R t) r ->
    evals_local_to env (@withCall PaV S (k r)) s ->
    evals_local_to env (@withCall PaV S (ITree.bind t k)) s.
  Proof using.
    intros Ht Hk.
    eapply evals_local_to_obs_eq; [symmetry; apply withCall_bind |].
    eapply evals_local_to_bind; [exact Ht | exact Hk].
  Qed.

  Lemma evals_local_to_withCall_lread
    (env : @local_env PaV) (x : local_id) (v : @dvalue PaV) :
    Maps.lookup x env = Some v ->
    evals_local_to env (@withCall PaV (@dvalue PaV) (lread x)) v.
  Proof using.
    intros Hlk.
    eapply ELT_Read; [apply withCall_lread | exact Hlk | apply ELT_Ret; reflexivity].
  Qed.

  Lemma evals_local_to_sim_l {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @CFGtop PaV R1) (r1 : R1) (t2 : @CFGtop PaV R2) :
    evals_local_to env1 t1 r1 ->
    cfg_local_sim RR env1 env2 (Ret r1) t2 ->
    cfg_local_sim RR env1 env2 t1 t2.
  Proof using.
    intros H1; revert t2;
      induction H1 as [t0 r0 Hr | t0 x v k r0 Hrd Hlk Hrest IH]; intros t2 Hsim.
    - eapply cfg_local_sim_obs_eq; [symmetry; exact Hr | reflexivity | exact Hsim].
    - specialize (IH t2 Hsim); punfold IH; pstep.
      eapply CLS_ReadL; [exact Hrd | exact Hlk | exact IH].
  Qed.

  Lemma evals_local_to_sim_r {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @CFGtop PaV R1) (t2 : @CFGtop PaV R2) (r2 : R2) :
    evals_local_to env2 t2 r2 ->
    cfg_local_sim RR env1 env2 t1 (Ret r2) ->
    cfg_local_sim RR env1 env2 t1 t2.
  Proof using.
    intros H2; revert t1;
      induction H2 as [t0 r0 Hr | t0 x v k r0 Hrd Hlk Hrest IH]; intros t1 Hsim.
    - eapply cfg_local_sim_obs_eq; [reflexivity | symmetry; exact Hr | exact Hsim].
    - specialize (IH t1 Hsim); punfold IH; pstep.
      eapply CLS_ReadR; [exact Hrd | exact Hlk | exact IH].
  Qed.

  Lemma evals_local_to_sim_both {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @CFGtop PaV R1) (r1 : R1)
    (t2 : @CFGtop PaV R2) (r2 : R2) :
    evals_local_to env1 t1 r1 ->
    evals_local_to env2 t2 r2 ->
    RR env1 env2 r1 r2 ->
    cfg_local_sim RR env1 env2 t1 t2.
  Proof using.
    intros H1 H2 HRR.
    eapply evals_local_to_sim_l; [exact H1 |].
    eapply evals_local_to_sim_r; [exact H2 |].
    apply cfg_local_sim_ret, HRR.
  Qed.

  Lemma evals_local_to_bind_sim_l {R1 R2 S1 : Type}
    (RR : @local_env PaV -> @local_env PaV -> S1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @CFGtop PaV R1) (r1 : R1)
    (k1 : R1 -> @CFGtop PaV S1) (t2 : @CFGtop PaV R2) :
    evals_local_to env1 t1 r1 ->
    cfg_local_sim RR env1 env2 (k1 r1) t2 ->
    cfg_local_sim RR env1 env2 (ITree.bind t1 k1) t2.
  Proof using.
    intros H1; revert t2;
      induction H1 as [t0 r0 Hr | t0 x v k0 r0 Hrd Hlk Hrest IH]; intros t2 Hsim.
    - eapply cfg_local_sim_obs_eq; [| reflexivity | exact Hsim].
      symmetry; rewrite Hr, Eqit.bind_ret_l; reflexivity.
    - specialize (IH t2 Hsim); punfold IH; pstep.
      eapply CLS_ReadL; [rewrite Hrd, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
  Qed.

  (** Environment invariant for verified constant certificates. *)
  Definition env_matches_cert (cm : rmap const_val) (defs : list raw_id)
    (env : @local_env PaV) : Prop :=
    forall y : raw_id,
      In y defs ->
      (exists v, Maps.lookup y env = Some v) /\
      (forall cv, RM.find y cm = Some cv ->
                  Maps.lookup y env = Some (@const_to_dvalue PaV cv)).

  Lemma env_matches_cert_nil (cm : rmap const_val) (env : @local_env PaV) :
    env_matches_cert cm [] env.
  Proof using.
    intros y Hy; inversion Hy.
  Qed.

  Lemma env_matches_cert_incl (cm : rmap const_val) (ds1 ds2 : list raw_id)
    (env : @local_env PaV) :
    sccp_incl_ids ds1 ds2 = true ->
    env_matches_cert cm ds2 env ->
    env_matches_cert cm ds1 env.
  Proof using.
    intros Hincl H2 y Hy.
    apply H2, (sccp_incl_ids_spec ds1 ds2 Hincl y Hy).
  Qed.

  Lemma env_matches_cert_add_const (cm : rmap const_val) (defs : list raw_id)
    (x : raw_id) (cv : const_val) (env : @local_env PaV) :
    RM.find x cm = Some cv ->
    env_matches_cert cm defs env ->
    env_matches_cert cm (x :: defs) (Maps.add x (@const_to_dvalue PaV cv) env).
  Proof using.
    intros Hfx Henv y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_eq_o by reflexivity.
      split; [eexists; reflexivity |].
      intros cv' Hfx'; rewrite Hfx in Hfx'; inversion Hfx'; reflexivity.
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne.
      destruct Hy as [Heq | Hy']; [exfalso; apply Hne, Heq |].
      destruct (Henv y Hy') as [Hv Hcv]; cbn [Maps.lookup Map_rmap] in Hv, Hcv; exact (conj Hv Hcv).
  Qed.

  Lemma env_matches_cert_add_none_cons (cm : rmap const_val) (defs : list raw_id)
    (x : raw_id) (v : @dvalue PaV) (env : @local_env PaV) :
    RM.find x cm = None ->
    env_matches_cert cm defs env ->
    env_matches_cert cm (x :: defs) (Maps.add x v env).
  Proof using.
    intros Hfx Henv y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_eq_o by reflexivity.
      split; [exists v; reflexivity | intros cv Hc; rewrite Hfx in Hc; discriminate Hc].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne.
      destruct Hy as [Heq | Hy']; [exfalso; apply Hne, Heq |].
      destruct (Henv y Hy') as [Hv Hcv]; cbn [Maps.lookup Map_rmap] in Hv, Hcv; exact (conj Hv Hcv).
  Qed.

  Lemma env_matches_cert_add_none_keep (cm : rmap const_val) (defs : list raw_id)
    (x : raw_id) (v : @dvalue PaV) (env : @local_env PaV) :
    RM.find x cm = None ->
    env_matches_cert cm defs env ->
    env_matches_cert cm defs (Maps.add x v env).
  Proof using.
    intros Hfx Henv y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_eq_o by reflexivity.
      split; [exists v; reflexivity | intros cv Hc; rewrite Hfx in Hc; discriminate Hc].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne.
      destruct (Henv y Hy) as [Hv Hcv]; cbn [Maps.lookup Map_rmap] in Hv, Hcv; exact (conj Hv Hcv).
  Qed.

  Lemma env_matches_cert_fargs_init (cm : rmap const_val) (fargs : list local_id)
    (env : @local_env PaV) :
    (forall x, In x fargs -> RM.find x cm = None) ->
    (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
    env_matches_cert cm fargs env.
  Proof using.
    intros Hnone Hlk y Hy.
    split; [apply Hlk, Hy |].
    intros cv Hc; rewrite (Hnone y Hy) in Hc; discriminate Hc.
  Qed.

  Lemma env_matches_cert_fargs_add (cm : rmap const_val) (fargs : list local_id)
    (z : raw_id) (v : @dvalue PaV) (env : @local_env PaV) :
    (forall x, In x fargs -> RM.find x cm = None) ->
    env_matches_cert cm fargs env ->
    env_matches_cert cm fargs (Maps.add z v env).
  Proof using.
    intros Hnone Henv y Hy.
    destruct (RawIDOrd.eq_dec z y) as [<- | Hne].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_eq_o by reflexivity.
      split; [exists v; reflexivity |].
      intros cv Hc; rewrite (Hnone z Hy) in Hc; discriminate Hc.
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne.
      destruct (Henv y Hy) as [Hv Hcv]; cbn [Maps.lookup Map_rmap] in Hv, Hcv; exact (conj Hv Hcv).
  Qed.

  (** ** Soundness of [sccp_safe_atom], [eval_cert_exp], and [subst_exp_at] *)

  Lemma sccp_safe_atom_sound (cm : rmap const_val) (defs : list raw_id)
    (env : @local_env PaV) (dt : dtyp) (e : exp dtyp) :
    env_matches_cert cm defs env ->
    sccp_safe_atom defs dt e = true ->
    exists v : @dvalue PaV, evals_local_to env (denote_exp' (Some dt) e) v.
  Proof using.
    intros Henv Hsafe.
    destruct e; cbn [sccp_safe_atom] in Hsafe; try discriminate Hsafe.
    - destruct id as [gid | y]; [discriminate Hsafe |].
      apply in_raw_ids_spec in Hsafe.
      destruct (Henv y Hsafe) as [[v Hlk] _].
      exists v; cbn [denote_exp' denote_exp lookup_id].
      apply evals_local_to_withCall_lread, Hlk.
    - destruct dt as [b | |]; try discriminate Hsafe.
      destruct b; try discriminate Hsafe.
      eexists;
        cbn [denote_exp' denote_exp denote_int_syntax_as_int coerce_integer_to_int
             ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad EOU_to_itree].
      apply evals_local_to_withCall_ret.
    - destruct b; eexists; cbn [denote_exp' denote_exp]; apply evals_local_to_withCall_ret.
    - eexists; cbn [denote_exp' denote_exp]; apply evals_local_to_withCall_ret.
    - eexists; cbn [denote_exp' denote_exp]; apply evals_local_to_withCall_ret.
    - eexists; cbn [denote_exp' denote_exp]; apply evals_local_to_withCall_ret.
  Qed.

  Lemma eval_cert_exp_sound (cm : rmap const_val) (defs : list raw_id)
    (env : @local_env PaV) (Henv : env_matches_cert cm defs env) :
    forall (e : exp dtyp) (top : option dtyp) (cv : const_val),
      eval_cert_exp cm defs top e = Some cv ->
      evals_local_to env (denote_exp' top e) (@const_to_dvalue PaV cv).
  Proof using.
    apply (@exp_ind dtyp
             (fun e => forall top cv,
                eval_cert_exp cm defs top e = Some cv ->
                evals_local_to env (denote_exp' top e) (@const_to_dvalue PaV cv)));
      try (intros; discriminate).
    - (* EXP_Ident *)
      intros [gid | y] top cv H; [discriminate H |].
      cbn [eval_cert_exp] in H.
      destruct (in_raw_ids y defs) eqn:Hin; [| discriminate H].
      apply in_raw_ids_spec in Hin.
      destruct (Henv y Hin) as [_ Hcv].
      cbn [denote_exp' denote_exp lookup_id].
      apply evals_local_to_withCall_lread, Hcv, H.
    - (* EXP_Integer *)
      intros lit [dt |] cv H; [| discriminate H].
      cbn [eval_cert_exp] in H.
      destruct dt as [b | |]; try discriminate H.
      destruct b; try discriminate H.
      inversion H; subst cv; clear H.
      cbn [denote_exp' denote_exp denote_int_syntax_as_int coerce_integer_to_int
           VellvmIntegers.repr VellvmIntegers.VInt_Bounded ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad
           EOU_to_itree const_to_dvalue].
      apply evals_local_to_withCall_ret.
    - (* EXP_Bool *)
      intros b top cv H; cbn [eval_cert_exp] in H; inversion H; subst cv; clear H.
      destruct b;
        cbn [denote_exp' denote_exp VellvmIntegers.one VellvmIntegers.zero VellvmIntegers.VInt_Bounded const_to_dvalue];
        apply evals_local_to_withCall_ret.
    - (* OP_IBinop *)
      intros iop dt e1 e2 IH1 IH2 top cv H; cbn [eval_cert_exp] in H.
      destruct (eval_cert_exp cm defs (Some dt) e1) as [c1 |] eqn:E1; [| discriminate H].
      destruct (eval_cert_exp cm defs (Some dt) e2) as [c2 |] eqn:E2; [| discriminate H].
      cbn [denote_exp' denote_exp].
      eapply evals_local_to_withCall_bind; [apply (IH1 (Some dt) c1 E1) |].
      eapply evals_local_to_withCall_bind; [apply (IH2 (Some dt) c2 E2) |].
      rewrite (@eval_const_iop_sound PaV iop c1 c2 cv H); cbn [EOU_to_itree].
      apply evals_local_to_withCall_ret.
    - (* OP_ICmp *)
      intros ss cmp_op dt e1 e2 IH1 IH2 top cv H; cbn [eval_cert_exp] in H.
      destruct (eval_cert_exp cm defs (Some dt) e1) as [c1 |] eqn:E1; [| discriminate H].
      destruct (eval_cert_exp cm defs (Some dt) e2) as [c2 |] eqn:E2; [| discriminate H].
      cbn [denote_exp' denote_exp].
      eapply evals_local_to_withCall_bind; [apply (IH1 (Some dt) c1 E1) |].
      eapply evals_local_to_withCall_bind; [apply (IH2 (Some dt) c2 E2) |].
      rewrite (@eval_const_icmp_sound PaV ss cmp_op c1 c2 cv H); cbn [EOU_to_itree].
      apply evals_local_to_withCall_ret.
    - (* OP_Conversion *)
      intros ct dt_from e1 dt_to IH1 top cv H; cbn [eval_cert_exp] in H.
      destruct (eval_cert_exp cm defs (Some dt_from) e1) as [c1 |] eqn:E1; [| discriminate H].
      cbn [denote_exp' denote_exp].
      eapply evals_local_to_withCall_bind; [apply (IH1 (Some dt_from) c1 E1) |].
      destruct ct as [| pconv | ic]; [| | discriminate H].
      + destruct (dtyp_eqb dt_from dt_to) eqn:Heqb; [| discriminate H].
        inversion H; subst c1; clear H.
        cbn [convert]; rewrite Heqb.
        cbn [ExtLib.Structures.Monad.ret Monad_itree]; apply evals_local_to_withCall_ret.
      + cbn [convert]; rewrite (@eval_const_pconv_sound PaV pconv dt_from c1 dt_to cv H).
        cbn [EOU_to_itree]; apply evals_local_to_withCall_ret.
    - (* OP_Select *)
      intros fm [dt_c cnd] [dt1 op1] [dt2 op2] IHc IH1 IH2 top cv H.
      cbn [snd] in IHc, IH1, IH2; cbn [eval_cert_exp] in H.
      destruct (eval_cert_exp cm defs (Some dt_c) cnd) as [[sz_c vc] |] eqn:Ec; [| discriminate H].
      destruct (Pos.eq_dec sz_c 1%positive) as [Heq | _]; [| discriminate H].
      revert H; rewrite <- (sccp_eq_sym_involutive Heq).
      revert vc Ec; generalize (Logic.eq_sym Heq); clear Heq; intros p; destruct p; intros vc Ec H.
      cbn [eq_rect eq_sym] in H.
      cbn [denote_exp' denote_exp].
      eapply evals_local_to_withCall_bind; [apply (IHc (Some dt_c) (CInt 1 vc) Ec) |].
      destruct (@Integers.unsigned 1 vc =? 1)%Z eqn:Econd.
      + assert (Hop2 : exists v2, evals_local_to env (denote_exp' (Some dt2) op2) v2).
        { destruct (eval_cert_exp cm defs (Some dt2) op2) as [c2 |] eqn:E2.
          - exists (@const_to_dvalue PaV c2); apply (IH2 (Some dt2) c2 E2).
          - destruct (sccp_safe_atom defs dt2 op2) eqn:Hsafe2; [| discriminate H].
            eapply sccp_safe_atom_sound; [exact Henv | exact Hsafe2]. }
        assert (E1 : eval_cert_exp cm defs (Some dt1) op1 = Some cv).
        { destruct (eval_cert_exp cm defs (Some dt2) op2);
            [exact H | destruct (sccp_safe_atom defs dt2 op2); [exact H | discriminate H]]. }
        destruct Hop2 as [v2 Hv2].
        eapply evals_local_to_withCall_bind; [apply (IH1 (Some dt1) cv E1) |].
        eapply evals_local_to_withCall_bind; [exact Hv2 |].
        cbn [const_to_dvalue eval_select eval_select_base_dvalue].
        rewrite Econd; cbn [ExtLib.Structures.Monad.ret EOU_monad EOU_to_itree]; apply evals_local_to_withCall_ret.
      + assert (Hop1 : exists v1, evals_local_to env (denote_exp' (Some dt1) op1) v1).
        { destruct (eval_cert_exp cm defs (Some dt1) op1) as [c1 |] eqn:E1.
          - exists (@const_to_dvalue PaV c1); apply (IH1 (Some dt1) c1 E1).
          - destruct (sccp_safe_atom defs dt1 op1) eqn:Hsafe1; [| discriminate H].
            eapply sccp_safe_atom_sound; [exact Henv | exact Hsafe1]. }
        assert (E2 : eval_cert_exp cm defs (Some dt2) op2 = Some cv).
        { destruct (eval_cert_exp cm defs (Some dt1) op1);
            [exact H | destruct (sccp_safe_atom defs dt1 op1); [exact H | discriminate H]]. }
        destruct Hop1 as [v1 Hv1].
        eapply evals_local_to_withCall_bind; [exact Hv1 |].
        eapply evals_local_to_withCall_bind; [apply (IH2 (Some dt2) cv E2) |].
        cbn [const_to_dvalue eval_select eval_select_base_dvalue].
        rewrite Econd; cbn [ExtLib.Structures.Monad.ret EOU_monad EOU_to_itree]; apply evals_local_to_withCall_ret.
    - (* EXP_Metadata *)
      intros md IHm top cv H; cbn [eval_cert_exp] in H.
      destruct md as [| | [dt ex] | | | |]; try discriminate H.
      cbn [denote_exp' denote_exp]; apply (IHm dt ex Logic.eq_refl (Some dt) cv H).
  Qed.

  Lemma eval_cert_exp_subst_sim (cm : rmap const_val) (defs : list raw_id)
    (env : @local_env PaV) (top : option dtyp) (e : exp dtyp) (cv : const_val) :
    env_matches_cert cm defs env ->
    eval_cert_exp cm defs top e = Some cv ->
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env /\ e2' = env /\ r1 = @const_to_dvalue PaV cv /\ r2 = @const_to_dvalue PaV cv)
      env env
      (denote_exp' top e)
      (denote_exp' top (subst_exp_at cm defs top e)).
  Proof using.
    intros Henv Hev.
    pose proof (eval_cert_exp_subst cm defs e top cv Hev) as Hev'.
    eapply evals_local_to_sim_both;
      [apply (eval_cert_exp_sound cm defs env Henv e top cv Hev)
      | apply (eval_cert_exp_sound cm defs env Henv _ top cv Hev')
      | repeat split; reflexivity].
  Qed.

  Lemma subst_texp_list_sim (cm : rmap const_val) (defs : list raw_id)
    (env : @local_env PaV)
    (es : list (dtyp * exp dtyp))
    (IH : forall p, In p es ->
            forall top,
              cfg_local_sim
                (fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2)
                env env
                (denote_exp' top (snd p))
                (denote_exp' top (subst_exp_at cm defs top (snd p)))) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2)
      env env
      (@withCall PaV (list (@dvalue PaV))
         (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) es))
      (@withCall PaV (list (@dvalue PaV))
         (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex)
            ((fix go (l : list (dtyp * exp dtyp)) : list (dtyp * exp dtyp) :=
                match l with
                | [] => []
                | (dt, ex) :: rest => (dt, subst_exp_at cm defs (Some dt) ex) :: go rest
                end) es))).
  Proof using.
    induction es as [| [dt ex] rest IHr]; cbn [map_monad].
    - apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_withCall_bind;
        [apply (IH (dt, ex) (or_introl Logic.eq_refl) (Some dt)) |].
      intros ? ? v _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind.
      + apply IHr; intros p Hp; apply (IH p (or_intror Hp)).
      + intros ? ? vs _ (-> & -> & <-).
        apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
  Qed.

  Lemma subst_exp_at_sim (cm : rmap const_val) (defs : list raw_id)
    (env : @local_env PaV) (Henv : env_matches_cert cm defs env) :
    forall (e : exp dtyp) (top : option dtyp),
      cfg_local_sim
        (fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2)
        env env
        (denote_exp' top e)
        (denote_exp' top (subst_exp_at cm defs top e)).
  Proof using.
    apply (@exp_ind dtyp
             (fun e => forall top,
                cfg_local_sim
                  (fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2)
                  env env
                  (denote_exp' top e)
                  (denote_exp' top (subst_exp_at cm defs top e)))).
    - (* EXP_Ident *)
      intros [gid | y] top.
      + cbn [subst_exp_at denote_exp' denote_exp lookup_id]; apply cfg_local_sim_withCall_gread_sync.
      + cbn [subst_exp_at].
        destruct (in_raw_ids y defs) eqn:Hin.
        * destruct (RM.find y cm) as [cv |] eqn:Ef.
          -- destruct (const_to_exp_at cv top) as [ec |] eqn:Eec.
             ++ apply in_raw_ids_spec in Hin.
                destruct (Henv y Hin) as [_ Hcv].
                eapply evals_local_to_sim_both.
                ** cbn [denote_exp' denote_exp lookup_id].
                   apply evals_local_to_withCall_lread, (Hcv cv Ef).
                ** apply ELT_Ret.
                   unfold denote_exp', withCall.
                   rewrite (@const_to_exp_at_sound PaV cv top ec Eec), translate_ret.
                   reflexivity.
                ** repeat split; reflexivity.
             ++ cbn [denote_exp' denote_exp lookup_id]; apply cfg_local_sim_withCall_lread_sync; reflexivity.
          -- cbn [denote_exp' denote_exp lookup_id]; apply cfg_local_sim_withCall_lread_sync; reflexivity.
        * cbn [denote_exp' denote_exp lookup_id]; apply cfg_local_sim_withCall_lread_sync; reflexivity.
    - (* EXP_Integer *)
      intros x [t |]; cbn [subst_exp_at denote_exp' denote_exp];
        [apply cfg_local_sim_withCall_EOU_sync | apply cfg_local_sim_withCall_raise_sync].
    - (* EXP_Float *)
      intros f [t |]; cbn [subst_exp_at denote_exp' denote_exp];
        [apply cfg_local_sim_withCall_EOU_sync | apply cfg_local_sim_withCall_raise_sync].
    - (* EXP_Bool *)
      intros b top; cbn [subst_exp_at denote_exp' denote_exp].
      destruct b; apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_Null *)
      intros top; cbn [subst_exp_at denote_exp' denote_exp];
        apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_Zero_initializer *)
      intros [t |]; cbn [subst_exp_at denote_exp' denote_exp];
        [apply cfg_local_sim_withCall_EOU_sync | apply cfg_local_sim_withCall_raise_sync].
    - (* EXP_Cstring *)
      intros elts IH top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (subst_texp_list_sim cm defs env elts IH) |].
      intros ? ? vs _ (-> & -> & <-); apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_Undef *)
      intros top; cbn [subst_exp_at denote_exp' denote_exp];
        apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_Poison *)
      intros top; cbn [subst_exp_at denote_exp' denote_exp];
        apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_Struct *)
      intros fields IH top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (subst_texp_list_sim cm defs env fields IH) |].
      intros ? ? vs _ (-> & -> & <-); apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_Packed_struct *)
      intros fields IH top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply cfg_local_sim_withCall_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_withCall_bind; [apply (subst_texp_list_sim cm defs env fields IH) |].
      intros ? ? vs _ (-> & -> & <-); apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_Array *)
      intros elts IH top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (subst_texp_list_sim cm defs env elts IH) |].
      intros ? ? vs _ (-> & -> & <-); apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_Vector *)
      intros elts IH top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (subst_texp_list_sim cm defs env elts IH) |].
      intros ? ? vs _ (-> & -> & <-); apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* OP_IBinop *)
      intros iop dt e1 e2 IH1 IH2 top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt)) |].
      intros ? ? v1 _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt)) |].
      intros ? ? v2 _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_Fneg *)
      intros fm [dt e1] IH1 top; cbn [snd] in IH1; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt)) |].
      intros ? ? v1 _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_ICmp *)
      intros ss cmp_op dt e1 e2 IH1 IH2 top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt)) |].
      intros ? ? v1 _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt)) |].
      intros ? ? v2 _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_FBinop *)
      intros fop fm dt e1 e2 IH1 IH2 top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt)) |].
      intros ? ? v1 _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt)) |].
      intros ? ? v2 _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_FCmp *)
      intros fcmp_op fm dt e1 e2 IH1 IH2 top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt)) |].
      intros ? ? v1 _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt)) |].
      intros ? ? v2 _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_Conversion *)
      intros ct dt_from e1 dt_to IH1 top; cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt_from)) |].
      intros ? ? v1 _ (-> & -> & <-); apply cfg_local_sim_withCall_convert_sync.
    - (* OP_GetElementPtr *)
      intros flags dt1 [dt2 ep] idxs IHp IHi top; cbn [snd] in IHp;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IHp (Some dt2)) |].
      intros ? ? vptr _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (subst_texp_list_sim cm defs env idxs IHi) |].
      intros ? ? vs _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_ExtractElement *)
      intros [dt1 e1] [dt2 e2] IH1 IH2 top; cbn [snd] in *;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt1)) |].
      intros ? ? vec _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt2)) |].
      intros ? ? idx _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_InsertElement *)
      intros [dt1 e1] [dt2 e2] [dt3 e3] IH1 IH2 IH3 top; cbn [snd] in *;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt1)) |].
      intros ? ? vec _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind.
      + eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt2)) |].
        intros ? ? x _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
      + intros ? ? elt _ (-> & -> & <-).
        eapply cfg_local_sim_withCall_bind; [apply (IH3 (Some dt3)) |].
        intros ? ? idx _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_ShuffleVector *)
      intros [dt1 e1] [dt2 e2] [dt3 e3] IH1 IH2 IH3 top; cbn [snd] in *;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt1)) |].
      intros ? ? vec1 _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt2)) |].
      intros ? ? vec2 _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH3 (Some dt3)) |].
      intros ? ? mask _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_ExtractValue *)
      intros [dt1 e1] idxs IH1 top; cbn [snd] in IH1;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt1)) |].
      intros ? ? str _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_InsertValue *)
      intros [dt1 e1] [dt2 e2] idxs IH1 IH2 top; cbn [snd] in *;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt1)) |].
      intros ? ? str _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt2)) |].
      intros ? ? elt _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_Select *)
      intros fm [dtc ec] [dt1 e1] [dt2 e2] IHc IH1 IH2 top; cbn [snd] in *;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IHc (Some dtc)) |].
      intros ? ? dc _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt1)) |].
      intros ? ? v1 _ (-> & -> & <-).
      eapply cfg_local_sim_withCall_bind; [apply (IH2 (Some dt2)) |].
      intros ? ? v2 _ (-> & -> & <-); apply cfg_local_sim_withCall_EOU_sync.
    - (* OP_Freeze *)
      intros [dt e1] IH1 top; cbn [snd] in IH1;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt)) |].
      intros ? ? dv _ (-> & -> & <-); apply cfg_local_sim_withCall_freeze_sync.
    - (* EXP_Asm *)
      intros se al idia uw tmpl cstr top; cbn [subst_exp_at denote_exp' denote_exp];
        apply cfg_local_sim_withCall_raise_sync.
    - (* EXP_Metadata *)
      intros md IHm top; destruct md as [| | [dt ex] | | | |];
        try (cbn [subst_exp_at denote_exp' denote_exp];
             apply cfg_local_sim_withCall_ret; repeat split; reflexivity).
      cbn [subst_exp_at denote_exp' denote_exp]; apply (IHm dt ex Logic.eq_refl (Some dt)).
    - (* EXP_Splat *)
      intros [dt e1] IH1 top; cbn [snd] in IH1;
        cbn [subst_exp_at denote_exp' denote_exp].
      eapply cfg_local_sim_withCall_bind; [apply cfg_local_sim_withCall_EOU_sync |].
      intros e1' e2' [sz t] [sz' t'] Heq;
        destruct Heq as (-> & -> & Heq); inversion Heq; subst sz' t'; clear Heq.
      eapply cfg_local_sim_withCall_bind; [apply (IH1 (Some dt)) |].
      intros ? ? v _ (-> & -> & <-); apply cfg_local_sim_withCall_ret; repeat split; reflexivity.
    - (* EXP_BlockAddress *)
      intros fn blk top; cbn [subst_exp_at denote_exp' denote_exp];
        apply cfg_local_sim_withCall_gread_sync.
  Qed.

  Lemma denote_exp'_refl_sim (env : @local_env PaV) (top : option dtyp) (e : exp dtyp) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2)
      env env
      (denote_exp' top e)
      (denote_exp' top e).
  Proof using.
    pose proof (subst_exp_at_sim (RM.empty const_val) [] env (env_matches_cert_nil _ _) e top) as H.
    rewrite subst_exp_at_empty in H; exact H.
  Qed.


  (** ** Instruction, Code, and Phi-Node Simulation *)

  Definition fargs_preserved (cm : rmap const_val)
    (env env' : @local_env PaV) : Prop :=
    forall fargs : list local_id,
      (forall x, In x fargs -> RM.find x cm = None) ->
      env_matches_cert cm fargs env ->
      env_matches_cert cm fargs env'.

  Lemma fargs_preserved_refl (cm : rmap const_val) (env : @local_env PaV) :
    fargs_preserved cm env env.
  Proof using.
    intros fargs _ H; exact H.
  Qed.

  Lemma fargs_preserved_trans (cm : rmap const_val)
    (e1 e2 e3 : @local_env PaV) :
    fargs_preserved cm e1 e2 ->
    fargs_preserved cm e2 e3 ->
    fargs_preserved cm e1 e3.
  Proof using.
    intros H12 H23 fargs Hnone Hf.
    apply (H23 fargs Hnone (H12 fargs Hnone Hf)).
  Qed.

  Lemma fargs_preserved_add (cm : rmap const_val)
    (z : raw_id) (v : @dvalue PaV) (env : @local_env PaV) :
    fargs_preserved cm env (Maps.add z v env).
  Proof using.
    intros fargs Hnone Hf.
    apply (env_matches_cert_fargs_add cm fargs z v env Hnone Hf).
  Qed.

  Lemma cfg_local_sim_bind_raiseUB_cut {R1 S1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> S1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string)
    (k1 : R1 -> @CFGtop PaV S1) (t2 : @CFGtop PaV R2) :
    cfg_local_sim RR env1 env2 (ITree.bind (raiseUB msg) k1) t2.
  Proof using.
    unfold raiseUB, trigger_cast, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body; rewrite observe_bind; cbn.
    left; reflexivity.
  Qed.

  Lemma cfg_local_sim_load_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (a : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (load dt a) (load dt a).
  Proof using.
    unfold load; apply cfg_local_sim_trigger_sync; reflexivity.
  Qed.

  Lemma cfg_local_sim_store_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (a v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (store dt a v) (store dt a v).
  Proof using.
    unfold store; apply cfg_local_sim_trigger_sync; reflexivity.
  Qed.

  Lemma cfg_local_sim_alloca_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (n : N) (al : option N) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (alloca dt n al) (alloca dt n al).
  Proof using.
    unfold alloca; apply cfg_local_sim_trigger_sync; reflexivity.
  Qed.

  Lemma cfg_local_sim_call_sync
    (env1 env2 : @local_env PaV)
    (dt : dtyp) (cc : cconv) (fv : @dvalue PaV) (vs : list (@dvalue PaV)) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (call dt cc fv vs) (call dt cc fv vs).
  Proof using.
    unfold call; apply cfg_local_sim_trigger_sync; reflexivity.
  Qed.

  Lemma cfg_local_sim_intrinsic_sync
    (env1 env2 : @local_env PaV)
    (dt : dtyp) (s : string) (vs : list (@dvalue PaV)) (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (intrinsic dt s vs va) (intrinsic dt s vs va).
  Proof using.
    unfold intrinsic; apply cfg_local_sim_trigger_sync; reflexivity.
  Qed.

  Lemma cfg_local_sim_stack_get_exc_sync
    (env1 env2 : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 stack_get_exc stack_get_exc.
  Proof using.
    unfold stack_get_exc; apply cfg_local_sim_trigger_sync; reflexivity.
  Qed.

  Lemma cfg_local_sim_stack_raise_sync
    (env1 env2 : @local_env PaV) (exn : @exc PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (stack_raise exn) (stack_raise exn).
  Proof using.
    unfold stack_raise; apply cfg_local_sim_trigger_sync; reflexivity.
  Qed.

  Lemma cfg_local_sim_assert_load_dereferenceable_sync
    (env1 env2 : @local_env PaV)
    (md : list (metadata dtyp)) (v : @dvalue PaV) (msg : string) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (assert_load_dereferenceable md v msg)
                (assert_load_dereferenceable md v msg).
  Proof using.
    unfold assert_load_dereferenceable.
    destruct (load_metadata_dereferenceable md) as [[or_null n] |];
      [apply cfg_local_sim_assert_dereferenceable_sync
      | apply cfg_local_sim_ret; repeat split; reflexivity].
  Qed.

  Lemma cfg_local_sim_atomic_rmw_op
    (env1 env2 : @local_env PaV)
    (a_op : atomic_rmw_operation) (pv val : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (denote_atomic_rmw_operation a_op pv val)
                (denote_atomic_rmw_operation a_op pv val).
  Proof using.
    destruct a_op; cbn [denote_atomic_rmw_operation];
      try apply cfg_local_sim_EOU_sync;
      try apply cfg_local_sim_raise_sync.
    - apply cfg_local_sim_ret; repeat split; reflexivity.
    - destruct val as [db | |]; try apply cfg_local_sim_raise_sync.
      destruct db as [| sz i | | | | | |]; try apply cfg_local_sim_raise_sync.
      apply cfg_local_sim_EOU_sync.
  Qed.

  Lemma denote_call_args_sim (cm : rmap const_val) (defs : list raw_id)
    (env : @local_env PaV) (Henv : env_matches_cert cm defs env)
    (args : list (texp dtyp * list param_attr)) (msg : string) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2)
      env env
      (denote_call_args args msg)
      (denote_call_args (sccp_rewrite_call_args cm defs args) msg).
  Proof using.
    unfold denote_call_args, sccp_rewrite_call_args.
    induction args as [| [[t op] attrs] rest IH]; cbn [List.map map_monad].
    - apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_bind;
          [apply (subst_exp_at_sim cm defs env Henv op (Some t)) |].
        intros ? ? v _ (-> & -> & <-).
        apply cfg_local_sim_apply_attrs_sync.
      + intros ? ? v' _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [exact IH |].
        intros ? ? vs _ (-> & -> & <-).
        apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma denote_operand_bundles_sim (cm : rmap const_val) (defs : list raw_id)
    (env : @local_env PaV) (Henv : env_matches_cert cm defs env)
    (loc : string) (f : exp dtyp) (obs : list (@operand_bundle dtyp)) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2)
      env env
      (denote_operand_bundles loc f obs)
      (denote_operand_bundles loc f (List.map (sccp_rewrite_ob cm defs) obs)).
  Proof using.
    unfold denote_operand_bundles.
    eapply cfg_local_sim_bind with
      (RR := fun e1' e2' (r1 r2 : list unit) => e1' = env /\ e2' = env /\ r1 = r2).
    - induction obs as [| ob rest IH]; cbn [List.map map_monad].
      + apply cfg_local_sim_ret; repeat split; reflexivity.
      + eapply cfg_local_sim_bind with
          (RR := fun e1' e2' (r1 r2 : unit) => e1' = env /\ e2' = env /\ r1 = r2).
        * cbn [sccp_rewrite_ob ob_ops ob_tag].
          eapply cfg_local_sim_bind with
            (RR := fun e1' e2' (r1 r2 : list (@dvalue PaV)) => e1' = env /\ e2' = env /\ r1 = r2).
          -- induction (ob_ops ob) as [| [[t ex] | ms] r_ops IHo]; cbn [List.map map_monad].
             ++ apply cfg_local_sim_ret; repeat split; reflexivity.
             ++ eapply cfg_local_sim_bind;
                  [apply (subst_exp_at_sim cm defs env Henv ex (Some t)) |].
                intros ? ? v _ (-> & -> & <-).
                eapply cfg_local_sim_bind; [exact IHo |].
                intros ? ? vs _ (-> & -> & <-);
                  apply cfg_local_sim_ret; repeat split; reflexivity.
             ++ eapply cfg_local_sim_bind;
                  [apply cfg_local_sim_ret;
                   instantiate (1 := fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2);
                   repeat split; reflexivity |].
                intros ? ? v _ (-> & -> & <-).
                eapply cfg_local_sim_bind; [exact IHo |].
                intros ? ? vs _ (-> & -> & <-);
                  apply cfg_local_sim_ret; repeat split; reflexivity.
          -- intros ? ? vs _ (-> & -> & <-).
             destruct (bundle_check f (ob_tag ob)) as [chk |] eqn:Echk.
             ++ eapply cfg_local_sim_assume_check_sync, Echk.
             ++ apply cfg_local_sim_ret; repeat split; reflexivity.
        * intros ? ? u _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [exact IH |].
          intros ? ? us _ (-> & -> & <-);
            apply cfg_local_sim_ret; repeat split; reflexivity.
    - intros ? ? _ _ (-> & -> & _); apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma denote_instr_sim (cm : rmap const_val) (cur_defs : list raw_id)
    (ii : instr_id * instr dtyp * list (metadata dtyp))
    (va : option (@ptr (@PROV PaV) (@PTR PaV))) (env : @local_env PaV) :
    let '(iid, ins, md) := ii in
    check_sccp_instr cm cur_defs ii = true ->
    env_matches_cert cm cur_defs env ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         e1' = e2' /\
         env_matches_cert cm (sccp_instr_defs ii ++ cur_defs) e1' /\
         fargs_preserved cm env e1')
      env env
      (denote_instr ii va)
      (denote_instr (iid, sccp_rewrite_instr cm cur_defs ins, md) va).
  Proof using.
    destruct ii as [[iid ins] md].
    intros Hchk Henv.
    destruct ins as [msg | op | [dt f] args anns obs | dt anns | dt [du ptr] anns
                     | [dt val] [du ptr] anns | sc ord | cpx | armw | [t ptr_exp] argty
                     | rty cl cs].
    - (* INSTR_Comment *)
      destruct iid as [id | vid]; cbn [denote_instr sccp_rewrite_instr sccp_instr_defs app].
      + apply cfg_local_sim_raise_sync.
      + apply cfg_local_sim_ret;
          split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]].
    - (* INSTR_Op *)
      destruct iid as [id | vid]; cbn [denote_instr sccp_rewrite_instr sccp_instr_defs app];
        [| apply cfg_local_sim_raise_sync].
      cbn [check_sccp_instr] in Hchk.
      destruct (RM.find id cm) as [cv |] eqn:Ef.
      + destruct (eval_cert_exp cm cur_defs None op) as [cv' |] eqn:Eev; [| discriminate Hchk].
        apply const_val_eqb_spec in Hchk; subst cv'.
        eapply cfg_local_sim_bind;
          [apply (eval_cert_exp_subst_sim cm cur_defs env None op cv Henv Eev) |].
        intros ? ? ? ? (-> & -> & -> & ->).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
        intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret; split; [reflexivity |].
        split; [apply (env_matches_cert_add_const cm cur_defs id cv env Ef Henv)
               | apply fargs_preserved_add].
      + eapply cfg_local_sim_bind;
          [apply (subst_exp_at_sim cm cur_defs env Henv op None) |].
        intros ? ? uv _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
        intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret; split; [reflexivity |].
        split; [apply (env_matches_cert_add_none_cons cm cur_defs id uv env Ef Henv)
               | apply fargs_preserved_add].
    - (* INSTR_Call *)
      destruct iid as [id | vid];
        cbn [sccp_rewrite_instr]; unfold denote_instr; cbv beta iota zeta;
        (eapply cfg_local_sim_bind;
           [apply (denote_call_args_sim cm cur_defs env Henv args _) |];
         intros ? ? vs _ (-> & -> & <-);
         eapply cfg_local_sim_bind;
           [apply (denote_operand_bundles_sim cm cur_defs env Henv _ f obs) |];
         intros ? ? _ _ (-> & -> & _);
         eapply cfg_local_sim_bind with
           (RR := fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2);
         [ destruct (intrinsic_exp f) as [s |];
           [ apply cfg_local_sim_intrinsic_sync
           | eapply cfg_local_sim_bind; [apply denote_exp'_refl_sim |];
             intros ? ? fv _ (-> & -> & <-); apply cfg_local_sim_call_sync ]
         | intros ? ? res _ (-> & -> & <-);
           eapply cfg_local_sim_bind; [apply cfg_local_sim_check_call_return_sync |];
           intros ? ? res' _ (-> & -> & <-);
           destruct res' as [exc | dv];
           [ eapply cfg_local_sim_bind;
               [apply cfg_local_sim_raiseLLVM_sync with
                  (RR := fun _ _ (_ _ : @dvalue PaV) => False) |];
             intros ? ? ? ? []
           | eapply cfg_local_sim_bind;
               [apply cfg_local_sim_ret;
                instantiate (1 := fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = dv /\ r2 = dv);
                repeat split; reflexivity |];
             intros ? ? ? ? (-> & -> & -> & ->) ] ]).
      + cbn [sccp_instr_defs app check_sccp_instr] in Hchk |- *.
        destruct (RM.find id cm) eqn:Ef; [discriminate Hchk |].
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
        intros ? ? _ _ (-> & -> & _); split; [reflexivity |].
        split; [apply (env_matches_cert_add_none_cons cm cur_defs id dv env Ef Henv)
               | apply fargs_preserved_add].
      + cbn [sccp_instr_defs app].
        apply cfg_local_sim_ret;
          split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]].
    - (* INSTR_Alloca *)
      destruct iid as [id | vid]; cbn [sccp_rewrite_instr sccp_instr_defs app];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [check_sccp_instr] in Hchk.
      destruct (RM.find id cm) eqn:Ef; [discriminate Hchk |].
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' _ _ =>
                 e1' = e2' /\
                 env_matches_cert cm (id :: cur_defs) e1' /\
                 fargs_preserved cm env e1').
      + destruct (find_option ann_num_elements anns) as [[t num_exp] |].
        * eapply cfg_local_sim_bind; [apply denote_exp'_refl_sim |].
          intros ? ? n _ (-> & -> & <-).
          destruct (dvalue_is_poison n); [apply cfg_local_sim_raiseUB_cut |].
          eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
          intros ? ? n' _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [apply cfg_local_sim_alloca_sync |].
          intros ? ? v _ (-> & -> & <-).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); split; [reflexivity |].
          split; [apply (env_matches_cert_add_none_cons cm cur_defs id v env Ef Henv)
                 | apply fargs_preserved_add].
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_alloca_sync |].
          intros ? ? v _ (-> & -> & <-).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); split; [reflexivity |].
          split; [apply (env_matches_cert_add_none_cons cm cur_defs id v env Ef Henv)
                 | apply fargs_preserved_add].
      + intros ? ? _ _ (<- & Henv' & Hfp);
          apply cfg_local_sim_ret; split; [reflexivity | exact (conj Henv' Hfp)].
    - (* INSTR_Load *)
      destruct iid as [id | vid]; cbn [sccp_rewrite_instr sccp_instr_defs app];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [check_sccp_instr] in Hchk.
      destruct (RM.find id cm) eqn:Ef; [discriminate Hchk |].
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm cur_defs env Henv ptr (Some du)) |].
      intros ? ? a _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
      intros ? ? v _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? v' _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_assert_load_dereferenceable_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
      intros ? ? _ _ (-> & -> & _); split; [reflexivity |].
      split; [apply (env_matches_cert_add_none_cons cm cur_defs id v' env Ef Henv)
             | apply fargs_preserved_add].
    - (* INSTR_Store *)
      destruct iid as [id | vid]; cbn [sccp_rewrite_instr sccp_instr_defs app];
        [unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync |].
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm cur_defs env Henv val (Some dt)) |].
      intros ? ? v _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm cur_defs env Henv ptr (Some du)) |].
      intros ? ? a _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      destruct a as [db | |].
      + destruct db; cbn [ExtLib.Structures.Monad.bind Monad_itree];
          lazymatch goal with
          | |- cfg_local_sim _ _ _ (ITree.bind (raiseUB _) _) _ =>
              apply cfg_local_sim_bind_raiseUB_cut
          | _ =>
              eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |];
              intros ? ? _ _ (-> & -> & _);
              apply cfg_local_sim_ret;
              split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]]
          end.
      + eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _);
          apply cfg_local_sim_ret;
          split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]].
      + eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _);
          apply cfg_local_sim_ret;
          split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]].
    - (* INSTR_Fence *)
      destruct iid as [id | vid]; cbn [denote_instr sccp_rewrite_instr sccp_instr_defs app];
        apply cfg_local_sim_ret;
        (split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]]).
    - (* INSTR_AtomicCmpXchg *)
      destruct iid as [id | vid];
        [| cbn [sccp_rewrite_instr]; destruct (c_ptr cpx), (c_cmp cpx), (c_new cpx);
           unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [check_sccp_instr] in Hchk.
      destruct (RM.find id cm) eqn:Ef; [discriminate Hchk |].
      destruct cpx as [cw cv_f [ptr_ty ptr_val] [cmp_ty cmp_val] [new_ty new_val] cs_o cso cfo cal].
      cbn [sccp_rewrite_instr sccp_instr_defs app denote_instr denote_cmpxchg
           c_ptr c_cmp c_new c_align].
      destruct (dtyp_eq_dec cmp_ty new_ty) as [<- | _]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm cur_defs env Henv ptr_val (Some ptr_ty)) |].
      intros ? ? ptr_v _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm cur_defs env Henv cmp_val (Some cmp_ty)) |].
      intros ? ? cmp_v _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm cur_defs env Henv new_val (Some cmp_ty)) |].
      intros ? ? new_v _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
      intros ? ? loaded_v _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? dv _ (-> & -> & <-).
      destruct dv as [db | |];
        [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
      destruct db as [| sz cb | | | | | |];
        [apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync
        | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
        | | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
      + destruct sz as [p | p |];
          [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync |].
        match goal with |- context [if ?b then _ else _] => destruct b end.
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
          intros ? ? _ _ (-> & -> & _).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); split; [reflexivity |].
          split; [apply (env_matches_cert_add_none_cons cm cur_defs id _ env Ef Henv)
                 | apply fargs_preserved_add].
        * eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); split; [reflexivity |].
          split; [apply (env_matches_cert_add_none_cons cm cur_defs id _ env Ef Henv)
                 | apply fargs_preserved_add].
      + apply cfg_local_sim_raiseUB_cut.
    - (* INSTR_AtomicRMW *)
      destruct iid as [id | vid];
        [| cbn [sccp_rewrite_instr]; destruct (a_ptr armw), (a_val armw);
           unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [check_sccp_instr] in Hchk.
      destruct (RM.find id cm) eqn:Ef; [discriminate Hchk |].
      destruct armw as [av aop [ptr_ty ptr_val] [a_ty a_val_e] as_o aord aal].
      cbn [sccp_rewrite_instr sccp_instr_defs app denote_instr denote_atomicrmw
           a_ptr a_val a_operation a_align].
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm cur_defs env Henv ptr_val (Some ptr_ty)) |].
      intros ? ? ptr_v _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm cur_defs env Henv a_val_e (Some a_ty)) |].
      intros ? ? a_v _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
      intros ? ? loaded_v _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_atomic_rmw_op |].
      intros ? ? stored_v _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
      intros ? ? _ _ (-> & -> & _).
      apply cfg_local_sim_ret; split; [reflexivity |].
      split; [apply (env_matches_cert_add_none_cons cm cur_defs id loaded_v env Ef Henv)
             | apply fargs_preserved_add].
    - (* INSTR_VAArg *)
      destruct iid as [id | vid].
      + cbn [check_sccp_instr] in Hchk.
        destruct (RM.find id cm) eqn:Ef; [discriminate Hchk |].
        cbn [sccp_rewrite_instr sccp_instr_defs app];
          unfold denote_instr; cbv beta iota zeta;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply cfg_local_sim_bind;
          [apply (subst_exp_at_sim cm cur_defs env Henv ptr_exp
                    (Some (DTYPE_Base DTYPE_Pointer))) |].
        intros ? ? ptr_to_args _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? vargs _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? retv _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? ix _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? args' _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _).
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
        intros ? ? _ _ (-> & -> & _); split; [reflexivity |].
        split; [apply (env_matches_cert_add_none_cons cm cur_defs id retv env Ef Henv)
               | apply fargs_preserved_add].
      + cbn [sccp_rewrite_instr sccp_instr_defs app];
          unfold denote_instr; cbv beta iota zeta;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply cfg_local_sim_bind;
          [apply (subst_exp_at_sim cm cur_defs env Henv ptr_exp
                    (Some (DTYPE_Base DTYPE_Pointer))) |].
        intros ? ? ptr_to_args _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? vargs _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? retv _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? ix _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? args' _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret;
          split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]].
    - (* INSTR_LandingPad *)
      destruct iid as [id | vid]; cbn [sccp_rewrite_instr sccp_instr_defs app];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [check_sccp_instr] in Hchk.
      destruct (RM.find id cm) eqn:Ef; [discriminate Hchk |].
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind; [apply cfg_local_sim_stack_get_exc_sync |].
      intros ? ? oe _ (-> & -> & <-).
      destruct oe as [e |]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
      intros ? ? _ _ (-> & -> & _); split; [reflexivity |].
      split; [apply (env_matches_cert_add_none_cons cm cur_defs id e env Ef Henv)
             | apply fargs_preserved_add].
  Qed.

  Lemma denote_code_sim (cm : rmap const_val) (cd : code dtyp)
    (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    forall (cur_defs : list raw_id) (env : @local_env PaV),
      check_sccp_code cm cur_defs cd = true ->
      env_matches_cert cm cur_defs env ->
      cfg_local_sim
        (fun e1' e2' _ _ =>
           e1' = e2' /\
           env_matches_cert cm (sccp_code_defs_end cur_defs cd) e1' /\
           fargs_preserved cm env e1')
        env env
        (denote_code cd va)
        (denote_code (sccp_rewrite_code cm cur_defs cd) va).
  Proof using.
    induction cd as [| [[iid ins] md] rest IH]; intros cur_defs env Hchk Henv.
    - cbn [sccp_rewrite_code sccp_code_defs_end].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_nil | symmetry; apply denote_code_nil |].
      apply cfg_local_sim_ret;
        split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]].
    - cbn [check_sccp_code] in Hchk.
      apply Bool.andb_true_iff in Hchk as [Hi Hrest].
      cbn [sccp_rewrite_code sccp_code_defs_end].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_cons | symmetry; apply denote_code_cons |].
      eapply cfg_local_sim_bind;
        [apply (denote_instr_sim cm cur_defs (iid, ins, md) va env Hi Henv) |].
      intros e1' e2' _ _ (<- & Henv' & Hfp1).
      eapply cfg_local_sim_weaken;
        [| apply (IH (sccp_instr_defs (iid, ins, md) ++ cur_defs) e1' Hrest Henv')].
      intros e1'' e2'' _ _ (<- & Henv'' & Hfp2).
      split; [reflexivity | split; [exact Henv'' | eapply fargs_preserved_trans; eassumption]].
  Qed.

  Inductive phi_eval_results (cm : rmap const_val)
    : list (local_id * phi dtyp * list (metadata dtyp)) ->
      list (local_id * @dvalue PaV) -> Prop :=
  | PER_nil :
      phi_eval_results cm [] []
  | PER_cons_const x ph md cv ps dvs :
      RM.find x cm = Some cv ->
      phi_eval_results cm ps dvs ->
      phi_eval_results cm ((x, ph, md) :: ps) ((x, @const_to_dvalue PaV cv) :: dvs)
  | PER_cons_none x ph md v ps dvs :
      RM.find x cm = None ->
      phi_eval_results cm ps dvs ->
      phi_eval_results cm ((x, ph, md) :: ps) ((x, v) :: dvs).

  Lemma denote_phis_eval_sim (fargs : list local_id) (c : CFG.cfg dtyp)
    (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
    (bid_from bid_src : block_id)
    (Hedge_in : sccp_in_edges (bid_from, bid_src) exec_edges = true)
    (env : @local_env PaV)
    (Hedge_env : env_matches_cert cm (sccp_edge_defs fargs c md_in bid_from bid_src) env)
    (phis : list (local_id * phi dtyp * list (metadata dtyp))) :
    forallb (check_sccp_phi cm (sccp_edge_defs fargs c md_in bid_from bid_src) bid_from) phis = true ->
    cfg_local_sim
      (fun e1' e2' dvs1 dvs2 =>
         e1' = env /\ e2' = env /\ dvs1 = dvs2 /\ phi_eval_results cm phis dvs1)
      env env
      (map_monad (denote_phi bid_from) phis)
      (map_monad (denote_phi bid_from)
         (sccp_rewrite_phis fargs c exec_edges md_in cm bid_src phis)).
  Proof using.
    set (edge_d := sccp_edge_defs fargs c md_in bid_from bid_src) in *.
    induction phis as [| [[x [fm dt args]] md] rest IH]; intros Hchk.
    - cbn [sccp_rewrite_phis List.map map_monad].
      apply cfg_local_sim_ret;
        split; [reflexivity | split; [reflexivity | split; [reflexivity | constructor]]].
    - cbn [forallb] in Hchk; apply Bool.andb_true_iff in Hchk as [Hp Hrest].
      cbn [sccp_rewrite_phis List.map map_monad].
      assert (Hassoc :
        assoc bid_from (sccp_rewrite_phi_args fargs c exec_edges md_in cm bid_src dt args) =
        option_map (subst_exp_at cm edge_d (Some dt)) (assoc bid_from args)).
      { clear Hp Hrest; induction args as [| [pred0 op0] r_args IHa]; [reflexivity |].
        cbn [sccp_rewrite_phi_args List.map].
        destruct (RawIDOrd.eq_dec bid_from pred0) as [<- | Hne].
        - destruct (sccp_in_edges (bid_from, bid_src) exec_edges) eqn:Ein;
            rewrite !assoc_hd; [reflexivity | discriminate Hedge_in].
        - destruct (sccp_in_edges (pred0, bid_src) exec_edges);
            rewrite !assoc_tl by exact Hne; exact IHa. }
      cbn [check_sccp_phi] in Hp.
      destruct (RM.find x cm) as [cv |] eqn:Ef.
      + destruct (assoc bid_from args) as [op |] eqn:Eop; [| discriminate Hp].
        destruct (eval_cert_exp cm edge_d (Some dt) op) as [cv' |] eqn:Eev; [| discriminate Hp].
        apply const_val_eqb_spec in Hp; subst cv'.
        eapply cfg_local_sim_bind with
          (RR := fun e1' e2' p1 p2 =>
                   e1' = env /\ e2' = env /\
                   p1 = (x, @const_to_dvalue PaV cv) /\
                   p2 = (x, @const_to_dvalue PaV cv)).
        * unfold denote_phi; cbv beta iota zeta.
          rewrite Eop, Hassoc; cbn [option_map].
          eapply cfg_local_sim_bind;
            [apply (eval_cert_exp_subst_sim cm edge_d env (Some dt) op cv Hedge_env Eev) |].
          intros ? ? ? ? (-> & -> & -> & ->).
          apply cfg_local_sim_ret; repeat split; reflexivity.
        * intros ? ? ? ? (-> & -> & -> & ->).
          eapply cfg_local_sim_bind; [exact (IH Hrest) |].
          intros ? ? dvs1 _ (-> & -> & <- & Hper).
          apply cfg_local_sim_ret;
            split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
          eapply PER_cons_const; [exact Ef | exact Hper].
      + eapply cfg_local_sim_bind with
          (RR := fun e1' e2' p1 p2 =>
                   e1' = env /\ e2' = env /\ p1 = p2 /\ exists uv, p1 = (x, uv)).
        * unfold denote_phi; cbv beta iota zeta.
          rewrite Hassoc.
          destruct (assoc bid_from args) as [op |]; cbn [option_map];
            [| apply cfg_local_sim_raise_sync].
          eapply cfg_local_sim_bind;
            [apply (subst_exp_at_sim cm edge_d env Hedge_env op (Some dt)) |].
          intros ? ? uv _ (-> & -> & <-).
          apply cfg_local_sim_ret;
            split; [reflexivity | split; [reflexivity | split; [reflexivity | exists uv; reflexivity]]].
        * intros ? ? ? _ (-> & -> & <- & uv & ->).
          eapply cfg_local_sim_bind; [exact (IH Hrest) |].
          intros ? ? dvs1 _ (-> & -> & <- & Hper).
          apply cfg_local_sim_ret;
            split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
          eapply PER_cons_none; [exact Ef | exact Hper].
  Qed.

  Lemma denote_phis_write_sim (cm : rmap const_val)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (dvs : list (local_id * @dvalue PaV))
    (Hper : phi_eval_results cm phis dvs) :
    forall (cur_defs : list raw_id) (env : @local_env PaV),
      env_matches_cert cm cur_defs env ->
      cfg_local_sim
        (fun e1' e2' _ _ =>
           e1' = e2' /\
           env_matches_cert cm (sccp_phis_defs_end cur_defs phis) e1' /\
           fargs_preserved cm env e1')
        env env
        (map_monad (fun '(id, dv) => lwrite id dv) dvs)
        (map_monad (fun '(id, dv) => lwrite id dv) dvs).
  Proof using.
    induction Hper as [| x ph md cv ps dvs' Ef Hper IH | x ph md v ps dvs' Ef Hper IH];
      intros cur_defs env Henv; cbn [map_monad sccp_phis_defs_end].
    - apply cfg_local_sim_ret;
        split; [reflexivity | split; [exact Henv | apply fargs_preserved_refl]].
    - eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
      intros ? ? [] [] (-> & -> & _).
      eapply cfg_local_sim_bind;
        [apply (IH (x :: cur_defs) (Maps.add x (@const_to_dvalue PaV cv) env)
                   (env_matches_cert_add_const cm cur_defs x cv env Ef Henv)) |].
      intros e1'' e2'' l1 l2 (<- & Henv'' & Hfp).
      apply cfg_local_sim_ret; split; [reflexivity |].
      split; [exact Henv'' | eapply fargs_preserved_trans; [apply fargs_preserved_add | exact Hfp]].
    - eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
      intros ? ? [] [] (-> & -> & _).
      eapply cfg_local_sim_bind;
        [apply (IH (x :: cur_defs) (Maps.add x v env)
                   (env_matches_cert_add_none_cons cm cur_defs x v env Ef Henv)) |].
      intros e1'' e2'' l1 l2 (<- & Henv'' & Hfp).
      apply cfg_local_sim_ret; split; [reflexivity |].
      split; [exact Henv'' | eapply fargs_preserved_trans; [apply fargs_preserved_add | exact Hfp]].
  Qed.

  Lemma denote_phis_sim (fargs : list local_id) (c : CFG.cfg dtyp)
    (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
    (bid_from bid_src : block_id)
    (Hedge_in : sccp_in_edges (bid_from, bid_src) exec_edges = true)
    (defs_in : list raw_id) (env : @local_env PaV)
    (Hedge_env : env_matches_cert cm (sccp_edge_defs fargs c md_in bid_from bid_src) env)
    (Hdefs_in : env_matches_cert cm defs_in env)
    (phis : list (local_id * phi dtyp * list (metadata dtyp))) :
    forallb (check_sccp_phi cm (sccp_edge_defs fargs c md_in bid_from bid_src) bid_from) phis = true ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         e1' = e2' /\
         env_matches_cert cm (sccp_phis_defs_end defs_in phis) e1' /\
         fargs_preserved cm env e1')
      env env
      (denote_phis bid_from phis)
      (denote_phis bid_from (sccp_rewrite_phis fargs c exec_edges md_in cm bid_src phis)).
  Proof using.
    intros Hchk; unfold denote_phis.
    eapply cfg_local_sim_bind;
      [apply (denote_phis_eval_sim fargs c exec_edges md_in cm bid_from bid_src
                Hedge_in env Hedge_env phis Hchk) |].
    intros ? ? dvs _ (-> & -> & <- & Hper).
    eapply cfg_local_sim_bind;
      [apply (denote_phis_write_sim cm phis dvs Hper defs_in env Hdefs_in) |].
    intros e1' e2' _ _ (<- & Henv' & Hfp).
    apply cfg_local_sim_ret; exact (conj Logic.eq_refl (conj Henv' Hfp)).
  Qed.


  (** ** Terminator, Block, and Whole-CFG Simulation *)

  Lemma sccp_select_switch_in
    (selector : @dvalue PaV) (default_br : block_id)
    (switches : list (@dvalue PaV * block_id)) (bid : block_id) :
    @select_switch PaV selector default_br switches = raise_ret bid ->
    bid = default_br \/ In bid (List.map snd switches).
  Proof using.
    induction switches as [| [v id] rest IH]; cbn [select_switch].
    - intros H; inversion H; left; reflexivity.
    - destruct selector as [db1 | |]; try discriminate.
      destruct db1 as [| sz1 i1 | | | | | |]; try discriminate.
      destruct v as [db2 | |]; try discriminate.
      destruct db2 as [| sz2 i2 | | | | | |]; try discriminate.
      destruct (Pos.eq_dec sz1 sz2) as [<- | _]; [| discriminate].
      cbn [eq_rec_r eq_rec eq_rect eq_rect_r eq_sym
           VellvmIntegers.cmp VellvmIntegers.VInt_Bounded
           ExtLib.Structures.Monad.ret EOU_monad List.map snd].
      destruct (@Integers.cmp sz1 Ceq i1 i2).
      + intros H; inversion H; subst bid; right; left; reflexivity.
      + intros H; destruct (IH H) as [-> | Hin];
          [left; reflexivity | right; right; exact Hin].
  Qed.

  Lemma sccp_map_monad_switch_dests_snd
    (dests : list (tint_literal * block_id))
    (switches : list (@dvalue PaV * block_id)) :
    map_monad
      (fun '((TInt_Literal sz x), id) =>
         s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
         ret (DVALUE_Base s, id))
      dests = raise_ret switches ->
    List.map snd switches = List.map snd dests.
  Proof using.
    set (f := fun '((TInt_Literal sz x), id) =>
                s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
                (ret (DVALUE_Base s, id) : EOU (@dvalue PaV * block_id))).
    change (map_monad f dests = raise_ret switches ->
            List.map snd switches = List.map snd dests).
    revert switches; induction dests as [| [[sz x] id] rest IH];
      intros switches H; cbn [map_monad List.map snd] in *.
    - inversion H; reflexivity.
    - unfold f at 1 in H.
      destruct (@coerce_integer_to_int PaV (Some sz) (denote_int_syntax x))
        as [| | | s]; try discriminate H.
      cbn [ExtLib.Structures.Monad.bind EOU_monad] in H.
      destruct (map_monad f rest) as [| | | sws]; try discriminate H.
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad] in H.
      inversion H; subst switches; cbn [List.map snd].
      f_equal; apply IH; reflexivity.
  Qed.

  Lemma sccp_switch_eou_in
    (selector : @dvalue PaV) (default_br : block_id)
    (dests : list (tint_literal * block_id)) (bid : block_id) :
    (switches <- map_monad
                   (fun '((TInt_Literal sz x), id) =>
                      s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
                      ret (DVALUE_Base s, id))
                   dests ;;
     @select_switch PaV selector default_br switches) = raise_ret bid ->
    In bid (default_br :: List.map snd dests).
  Proof using.
    set (f := fun '((TInt_Literal sz x), id) =>
                s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
                (ret (DVALUE_Base s, id) : EOU (@dvalue PaV * block_id))).
    change ((switches <- map_monad f dests ;; @select_switch PaV selector default_br switches) =
            raise_ret bid ->
            In bid (default_br :: List.map snd dests)).
    destruct (map_monad f dests) as [| | | switches] eqn:Esw; try discriminate.
    cbn [ExtLib.Structures.Monad.bind EOU_monad]; intros Hsel.
    rewrite <- (sccp_map_monad_switch_dests_snd dests switches Esw).
    destruct (sccp_select_switch_in selector default_br switches bid Hsel) as [-> | Hin];
      [left; reflexivity | right; exact Hin].
  Qed.

  Lemma denote_indirectbr_addrs_sim
    (env : @local_env PaV) (f : function_id) (brs : list block_id) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env /\ e2' = env /\ r1 = r2)
      env env
      (map_monad (fun b => ba <- gread (blockaddress_id f b) ;; ret (dvalue_ptr_address ba)) brs)
      (map_monad (fun b => ba <- gread (blockaddress_id f b) ;; ret (dvalue_ptr_address ba)) brs).
  Proof using.
    induction brs as [| b rest IH]; cbn [map_monad].
    - apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_bind with
        (RR := fun e1' e2' (r1 r2 : option Z) => e1' = env /\ e2' = env /\ r1 = r2).
      + eapply cfg_local_sim_bind; [apply cfg_local_sim_gread_sync |].
        intros ? ? ba _ (-> & -> & <-);
          apply cfg_local_sim_ret; repeat split; reflexivity.
      + intros ? ? addr _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [exact IH |].
        intros ? ? addrs _ (-> & -> & <-);
          apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma denote_term_gen_sim (allow_fold : bool)
    (exec_edges : list cfg_edge) (cm : rmap const_val)
    (defs_end : list raw_id) (bid_src : block_id)
    (trm : instr_id * terminator dtyp * list (metadata dtyp))
    (env : @local_env PaV) :
    let '(tiid, tm, tmd) := trm in
    (match tiid with IId tx => RM.find tx cm = None | IVoid _ => True end) ->
    env_matches_cert cm defs_end env ->
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = e2' /\
         r1 = r2 /\
         env_matches_cert cm defs_end e1' /\
         fargs_preserved cm env e1' /\
         match r1 with
         | inl bid_tgt =>
             allow_fold = true ->
             check_sccp_term exec_edges cm defs_end bid_src trm = true ->
             sccp_in_edges (bid_src, bid_tgt) exec_edges = true
         | inr _ => True
         end)
      env env
      (denote_terminator trm)
      (denote_terminator (tiid, sccp_rewrite_term allow_fold cm defs_end tm, tmd)).
  Proof using.
    destruct trm as [[tiid tm] tmd].
    intros Htid Henv.
    destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt ex] def_br dests
                    | [dt ex] brs fn | [dt ex] | [dt fnptrval] args to_lbl unwind_lbl anns obs |].
    - (* TERM_Ret *)
      cbn [sccp_rewrite_term]; unfold denote_terminator; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm defs_end env Henv op (Some dt)) |].
      intros ? ? dv _ (-> & -> & <-).
      apply cfg_local_sim_ret;
        split; [reflexivity | split; [reflexivity |
                split; [exact Henv | split; [apply fargs_preserved_refl | exact I]]]].
    - (* TERM_Ret_void *)
      cbn [sccp_rewrite_term]; unfold denote_terminator; cbv beta iota zeta.
      apply cfg_local_sim_ret;
        split; [reflexivity | split; [reflexivity |
                split; [exact Henv | split; [apply fargs_preserved_refl | exact I]]]].
    - (* TERM_Br *)
      cbn [sccp_rewrite_term].
      destruct allow_fold.
      + destruct (sccp_branch_target cm defs_end dt op br1 br2) as [taken |] eqn:Etgt.
        * pose proof Etgt as Etgt0.
          unfold sccp_branch_target in Etgt; cbn zeta in Etgt.
          destruct (eval_cert_exp cm defs_end (Some dt) op) as [[sz vc] |] eqn:Eev;
            [| discriminate Etgt].
          destruct (Pos.eq_dec sz 1%positive) as [Heq | _]; [| discriminate Etgt].
          revert Etgt; rewrite <- (sccp_eq_sym_involutive Heq).
          revert vc Eev; generalize (Logic.eq_sym Heq); clear Heq; intros p; destruct p; intros vc Eev Etgt.
          cbn [eq_rect eq_sym] in Etgt; inversion Etgt; subst taken; clear Etgt.
          unfold denote_terminator; cbv beta iota zeta.
          eapply evals_local_to_bind_sim_l;
            [apply (eval_cert_exp_sound cm defs_end env Henv op (Some dt) (CInt 1 vc) Eev) |].
          cbn [const_to_dvalue VellvmIntegers.equ VellvmIntegers.one VellvmIntegers.VInt_Bounded].
          destruct (@Integers.eq 1 vc (@Integers.one 1));
            apply cfg_local_sim_ret;
            (split; [reflexivity | split; [reflexivity |
                     split; [exact Henv | split; [apply fargs_preserved_refl |]]]]);
            (intros _ Hchk; cbn [check_sccp_term] in Hchk; rewrite Etgt0 in Hchk;
             apply Bool.andb_true_iff in Hchk as [_ Hsucc]; exact Hsucc).
        * unfold denote_terminator; cbv beta iota zeta.
          eapply cfg_local_sim_bind;
            [apply (subst_exp_at_sim cm defs_end env Henv op (Some dt)) |].
          intros ? ? v _ (-> & -> & <-).
          destruct v as [db | |];
            [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
          destruct db as [| sz cb | | | | | |];
            [apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync
            | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
            | | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
          -- destruct sz as [p | p |];
               [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync |].
             match goal with |- context [if ?b then _ else _] => destruct b end.
             ++ apply cfg_local_sim_ret;
                  split; [reflexivity | split; [reflexivity |
                          split; [exact Henv | split; [apply fargs_preserved_refl |]]]].
                intros _ Hchk; cbn [check_sccp_term] in Hchk; rewrite Etgt in Hchk.
                apply Bool.andb_true_iff in Hchk as [_ Hsucc].
                apply Bool.andb_true_iff in Hsucc as [Hb1 _]; exact Hb1.
             ++ apply cfg_local_sim_ret;
                  split; [reflexivity | split; [reflexivity |
                          split; [exact Henv | split; [apply fargs_preserved_refl |]]]].
                intros _ Hchk; cbn [check_sccp_term] in Hchk; rewrite Etgt in Hchk.
                apply Bool.andb_true_iff in Hchk as [_ Hsucc].
                apply Bool.andb_true_iff in Hsucc as [_ Hb2]; exact Hb2.
          -- apply cfg_local_sim_raiseUB_cut.
      + unfold denote_terminator; cbv beta iota zeta.
        eapply cfg_local_sim_bind;
          [apply (subst_exp_at_sim cm defs_end env Henv op (Some dt)) |].
        intros ? ? v _ (-> & -> & <-).
        destruct v as [db | |];
          [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
        destruct db as [| sz cb | | | | | |];
          [apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync
          | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
          | | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
        * destruct sz as [p | p |];
            [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync |].
          match goal with |- context [if ?b then _ else _] => destruct b end;
            apply cfg_local_sim_ret;
            (split; [reflexivity | split; [reflexivity |
                     split; [exact Henv | split; [apply fargs_preserved_refl
                                                 | intros Hf; discriminate Hf]]]]).
        * apply cfg_local_sim_raiseUB_cut.
    - (* TERM_Br_1 *)
      cbn [sccp_rewrite_term]; unfold denote_terminator; cbv beta iota zeta.
      apply cfg_local_sim_ret;
        split; [reflexivity | split; [reflexivity |
                split; [exact Henv | split; [apply fargs_preserved_refl |]]]].
      intros _ Hchk; cbn [check_sccp_term sccp_term_succs forallb] in Hchk.
      apply Bool.andb_true_iff in Hchk as [_ Hsucc].
      apply Bool.andb_true_iff in Hsucc as [Hbr _]; exact Hbr.
    - (* TERM_Switch *)
      cbn [sccp_rewrite_term]; unfold denote_terminator; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm defs_end env Henv ex (Some dt)) |].
      intros ? ? selector _ (-> & -> & <-).
      destruct (dvalue_is_poison selector); [apply cfg_local_sim_raiseUB_cut |].
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_ret_sync |].
      intros ? ? bid _ (-> & -> & <- & Ebid).
      apply sccp_switch_eou_in in Ebid.
      apply cfg_local_sim_ret;
        split; [reflexivity | split; [reflexivity |
                split; [exact Henv | split; [apply fargs_preserved_refl |]]]].
      intros _ Hchk; cbn [check_sccp_term sccp_term_succs] in Hchk.
      apply Bool.andb_true_iff in Hchk as [_ Hall].
      rewrite forallb_forall in Hall; apply Hall, Ebid.
    - (* TERM_IndirectBr *)
      cbn [sccp_rewrite_term]; unfold denote_terminator; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm defs_end env Henv ex (Some dt)) |].
      intros ? ? a _ (-> & -> & <-).
      destruct (dvalue_is_poison a); [apply cfg_local_sim_raiseUB_cut |].
      destruct fn as [f |]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_bind; [apply denote_indirectbr_addrs_sim |].
      intros ? ? addrs _ (-> & -> & <-).
      destruct (dvalue_ptr_address a) as [z |]; [| apply cfg_local_sim_raise_sync].
      destruct (indirectbr_target z (combine brs addrs)) as [b |] eqn:Etgt;
        [| apply cfg_local_sim_raiseUB_cut].
      assert (Hin_b : In b brs) by (eapply indirectbr_target_In; exact Etgt).
      apply cfg_local_sim_ret;
        split; [reflexivity | split; [reflexivity |
                split; [exact Henv | split; [apply fargs_preserved_refl |]]]].
      intros _ Hchk; cbn [check_sccp_term sccp_term_succs] in Hchk.
      apply Bool.andb_true_iff in Hchk as [_ Hall].
      rewrite forallb_forall in Hall; apply Hall, Hin_b.
    - (* TERM_Resume *)
      cbn [sccp_rewrite_term]; unfold denote_terminator; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [apply (subst_exp_at_sim cm defs_end env Henv ex (Some dt)) |].
      intros ? ? exn _ (-> & -> & <-); apply cfg_local_sim_raiseLLVM_sync.
    - (* TERM_Invoke *)
      cbn [sccp_rewrite_term]; unfold denote_terminator; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [apply (denote_call_args_sim cm defs_end env Henv args _) |].
      intros ? ? uvs _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply (denote_operand_bundles_sim cm defs_end env Henv _ fnptrval obs) |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind; [apply denote_exp'_refl_sim |].
      intros ? ? fv _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_call_sync |].
      intros ? ? rv _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_check_call_return_sync |].
      intros ? ? rv' _ (-> & -> & <-).
      destruct rv' as [exn | ret_val].
      + eapply cfg_local_sim_bind; [apply cfg_local_sim_stack_raise_sync |].
        intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret;
          split; [reflexivity | split; [reflexivity |
                  split; [exact Henv | split; [apply fargs_preserved_refl |]]]].
        intros _ Hchk; cbn [check_sccp_term sccp_term_succs forallb] in Hchk.
        apply Bool.andb_true_iff in Hchk as [_ Hsucc].
        apply Bool.andb_true_iff in Hsucc as [_ Hsucc].
        apply Bool.andb_true_iff in Hsucc as [Hunw _]; exact Hunw.
      + destruct tiid as [tx | vid].
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
          intros ? ? [] [] (-> & -> & _).
          apply cfg_local_sim_ret;
            split; [reflexivity | split; [reflexivity |
                    split; [apply (env_matches_cert_add_none_keep cm defs_end tx ret_val env Htid Henv)
                           | split; [apply fargs_preserved_add |]]]].
          intros _ Hchk; cbn [check_sccp_term sccp_term_succs forallb] in Hchk.
          apply Bool.andb_true_iff in Hchk as [_ Hsucc].
          apply Bool.andb_true_iff in Hsucc as [Hto _]; exact Hto.
        * eapply cfg_local_sim_bind;
            [apply cfg_local_sim_ret;
             instantiate (1 := fun e1' e2' _ _ => e1' = env /\ e2' = env);
             split; reflexivity |].
          intros ? ? _ _ (-> & ->).
          apply cfg_local_sim_ret;
            split; [reflexivity | split; [reflexivity |
                    split; [exact Henv | split; [apply fargs_preserved_refl |]]]].
          intros _ Hchk; cbn [check_sccp_term sccp_term_succs forallb] in Hchk.
          apply Bool.andb_true_iff in Hchk as [_ Hsucc].
          apply Bool.andb_true_iff in Hsucc as [Hto _]; exact Hto.
    - (* TERM_Unreachable *)
      cbn [sccp_rewrite_term]; unfold denote_terminator; cbv beta iota zeta.
      apply cfg_local_sim_raiseUB_cut.
  Qed.

  Lemma denote_term_refl_sim
    (trm : instr_id * terminator dtyp * list (metadata dtyp))
    (env : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2)
      env env
      (denote_terminator trm)
      (denote_terminator trm).
  Proof using.
    destruct trm as [[tiid tm] tmd].
    assert (Htid : match tiid with IId tx => RM.find tx (RM.empty const_val) = None | IVoid _ => True end).
    { destruct tiid as [tx | vid]; [apply RMF.F.empty_o | exact I]. }
    pose proof (denote_term_gen_sim false [] (RM.empty const_val) [] (Anon 0%Z)
                  (tiid, tm, tmd) env Htid (env_matches_cert_nil _ _)) as H.
    rewrite sccp_rewrite_term_empty in H.
    eapply cfg_local_sim_weaken; [| exact H].
    intros ? ? ? ? (<- & <- & _); split; reflexivity.
  Qed.

  Lemma denote_instr_refl_sim
    (ii : instr_id * instr dtyp * list (metadata dtyp))
    (va : option (@ptr (@PROV PaV) (@PTR PaV))) (env : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2)
      env env
      (denote_instr ii va)
      (denote_instr ii va).
  Proof using.
    destruct ii as [[iid ins] md].
    assert (Hchk : check_sccp_instr (RM.empty const_val) [] (iid, ins, md) = true).
    { destruct iid as [id | vid]; cbn [check_sccp_instr]; [| reflexivity].
      rewrite RMF.F.empty_o; destruct ins; reflexivity. }
    pose proof (denote_instr_sim (RM.empty const_val) [] (iid, ins, md) va env
                  Hchk (env_matches_cert_nil _ _)) as H.
    rewrite sccp_rewrite_instr_empty in H.
    eapply cfg_local_sim_weaken; [| exact H].
    intros ? ? [] [] (<- & _); split; reflexivity.
  Qed.

  Lemma denote_code_refl_sim
    (cd : code dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV))) (env : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2)
      env env
      (denote_code cd va)
      (denote_code cd va).
  Proof using.
    revert env; induction cd as [| ii rest IH]; intros env.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_nil | symmetry; apply denote_code_nil |].
      apply cfg_local_sim_ret; split; reflexivity.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_cons | symmetry; apply denote_code_cons |].
      eapply cfg_local_sim_bind; [apply denote_instr_refl_sim |].
      intros e1' e2' _ _ [<- _]; apply IH.
  Qed.

  Lemma denote_phis_refl_sim
    (bid_from : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (env : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2)
      env env
      (denote_phis bid_from phis)
      (denote_phis bid_from phis).
  Proof using.
    unfold denote_phis.
    eapply cfg_local_sim_bind with
      (RR := fun e1' e2' dvs1 dvs2 => e1' = env /\ e2' = env /\ dvs1 = dvs2).
    - induction phis as [| [[x [fm dt args]] md] rest IH]; cbn [map_monad].
      + apply cfg_local_sim_ret; repeat split; reflexivity.
      + eapply cfg_local_sim_bind with
          (RR := fun e1' e2' p1 p2 => e1' = env /\ e2' = env /\ p1 = p2).
        * unfold denote_phi; cbv beta iota zeta.
          destruct (assoc bid_from args) as [op |]; [| apply cfg_local_sim_raise_sync].
          eapply cfg_local_sim_bind; [apply denote_exp'_refl_sim |].
          intros ? ? uv _ (-> & -> & <-);
            apply cfg_local_sim_ret; repeat split; reflexivity.
        * intros ? ? p _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [exact IH |].
          intros ? ? dvs _ (-> & -> & <-);
            apply cfg_local_sim_ret; repeat split; reflexivity.
    - intros ? ? dvs _ (-> & -> & <-).
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2).
      + revert env; induction dvs as [| [id dv] rest IH]; intros env; cbn [map_monad].
        * apply cfg_local_sim_ret; split; reflexivity.
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
          intros ? ? [] [] (-> & -> & _).
          eapply cfg_local_sim_bind; [apply IH |].
          intros e1' e2' l1 l2 [<- <-]; apply cfg_local_sim_ret; split; reflexivity.
      + intros e1' e2' l1 l2 [<- <-]; apply cfg_local_sim_ret; split; reflexivity.
  Qed.

  Lemma denote_cfg_refl_sim
    (c : CFG.cfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV))) (env : @local_env PaV) :
    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
      env env (denote_cfg c va) (denote_cfg c va).
  Proof using.
    unfold denote_cfg, denote_cfg_map, denote_ocfg_map.
    eapply cfg_local_sim_bind.
    - eapply (cfg_local_sim_iter
                (fun e1 e2 (s1 s2 : block_id * block_id) => e1 = e2 /\ s1 = s2)
                (fun _ _ r1 r2 => r1 = r2));
        [| split; reflexivity].
      intros env1 env2 [bid_from bid_src] s2 [<- <-].
      destruct (RM.find bid_src (ocfg_map (blks c))) as [bk_src |].
      + eapply cfg_local_sim_bind with
          (RR := fun e1' e2' bd1 bd2 => e1' = e2' /\ bd1 = bd2).
        * unfold denote_block.
          eapply cfg_local_sim_bind; [apply denote_phis_refl_sim |].
          intros e1' e2' _ _ [<- _].
          eapply cfg_local_sim_bind; [apply denote_code_refl_sim |].
          intros e1'' e2'' _ _ [<- _].
          apply denote_term_refl_sim.
        * intros e1' e2' [bid_tgt | dv] _ [<- <-];
            apply cfg_local_sim_ret; cbn [iter_step_rel]; auto.
      + apply cfg_local_sim_ret; cbn [iter_step_rel]; reflexivity.
    - intros ? ? [bid | uv] _ <-;
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_ret; reflexivity].
  Qed.

  Definition sccp_iter_inv (fargs : list local_id) (c : CFG.cfg dtyp)
    (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
    (env1 env2 : @local_env PaV) (s1 s2 : block_id * block_id) : Prop :=
    s1 = s2 /\
    env1 = env2 /\
    sccp_in_edges s1 exec_edges = true /\
    env_matches_cert cm fargs env1 /\
    env_matches_cert cm (sccp_edge_defs fargs c md_in (fst s1) (snd s1)) env1.

  Lemma denote_cfg_sccp_valid_sim
    (fargs : list local_id) (c : CFG.cfg dtyp)
    (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
    (env : @local_env PaV) (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    check_sccp_valid fargs c exec_edges md_in cm = true ->
    (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
      env env
      (denote_cfg c va)
      (denote_cfg
         {| init := init c;
            blks := List.map (sccp_rewrite_block fargs c exec_edges md_in cm) (blks c);
            args := args c |} va).
  Proof using.
    intros Hvalid Hfargs_lk.
    unfold check_sccp_valid in Hvalid.
    apply Bool.andb_true_iff in Hvalid as [Hv1 Hedges_b].
    apply Bool.andb_true_iff in Hv1 as [Hinit_edge Hfargs_b].
    assert (Hfargs_none : forall x, In x fargs -> RM.find x cm = None).
    { intros x Hx; rewrite forallb_forall in Hfargs_b.
      specialize (Hfargs_b x Hx).
      destruct (RM.find x cm); [discriminate Hfargs_b | reflexivity]. }
    rewrite forallb_forall in Hedges_b.
    unfold denote_cfg, denote_cfg_map, denote_ocfg_map; cbn [init blks].
    eapply cfg_local_sim_bind.
    - eapply (cfg_local_sim_iter
                (sccp_iter_inv fargs c exec_edges md_in cm)
                (fun _ _ r1 r2 => r1 = r2)).
      + (* Loop body *)
        intros env1 env2 [bid_from bid_src] s2
          (<- & <- & Hedge_in & Hfargs_env & Hedge_env).
        cbn [fst snd] in Hedge_env.
        rewrite !(@ocfg_map_find_block dtyp).
        rewrite (sccp_find_block_map_preserve
                   (sccp_rewrite_block fargs c exec_edges md_in cm)
                   (sccp_rewrite_block_id fargs c exec_edges md_in cm)
                   (blks c) bid_src).
        destruct (find_block (blks c) bid_src) as [b |] eqn:Efind; cbn [option_map].
        * pose proof (sccp_find_block_some_id (blks c) bid_src b Efind) as Hbid.
          subst bid_src.
          pose proof (sccp_is_reachable_from_edge exec_edges bid_from (blk_id b) Hedge_in)
            as Hreach.
          pose proof (Hedges_b (bid_from, blk_id b)
                        (proj1 (sccp_in_edges_spec _ _) Hedge_in)) as Hedge_ok.
          cbn [check_sccp_edge] in Hedge_ok; rewrite Efind in Hedge_ok.
          apply Bool.andb_true_iff in Hedge_ok as [Hok1 Hterm_ok].
          apply Bool.andb_true_iff in Hok1 as [Hok2 Hcode_ok].
          apply Bool.andb_true_iff in Hok2 as [Hincl Hphis_ok].
          set (defs_in := sccp_lookup_defs (blk_id b) md_in) in *.
          set (defs_phis := sccp_phis_defs_end defs_in (blk_phis b)) in *.
          set (defs_end := sccp_block_defs_end defs_in b) in *.
          assert (Hdefs_in : env_matches_cert cm defs_in env1)
            by exact (env_matches_cert_incl cm defs_in _ env1 Hincl Hedge_env).
          unfold sccp_rewrite_block; cbn zeta; rewrite Hreach.
          destruct (blk_term b) as [[tiid tm] tmd] eqn:Eterm.
          assert (Htid : match tiid with IId tx => RM.find tx cm = None | IVoid _ => True end).
          { pose proof Hterm_ok as Htid_chk.
            cbn [check_sccp_term] in Htid_chk.
            apply Bool.andb_true_iff in Htid_chk as [Htid_b _].
            destruct tiid as [tx | vid]; [| exact I].
            destruct (RM.find tx cm); [discriminate Htid_b | reflexivity]. }
          eapply cfg_local_sim_bind with
            (RR := fun e1_t e2_t bd1 bd2 =>
                     e1_t = e2_t /\
                     bd1 = bd2 /\
                     env_matches_cert cm defs_end e1_t /\
                     fargs_preserved cm env1 e1_t /\
                     match bd1 with
                     | inl bid_tgt => sccp_in_edges (blk_id b, bid_tgt) exec_edges = true
                     | inr _ => True
                     end).
          -- unfold denote_block; cbn [blk_phis blk_code blk_term].
             rewrite Eterm.
             eapply cfg_local_sim_bind;
               [apply (denote_phis_sim fargs c exec_edges md_in cm bid_from (blk_id b)
                         Hedge_in defs_in env1 Hedge_env Hdefs_in (blk_phis b) Hphis_ok) |].
             intros e1_p e2_p _ _ (<- & Henv_p & Hfp_p).
             eapply cfg_local_sim_bind;
               [apply (denote_code_sim cm (blk_code b) va defs_phis e1_p Hcode_ok Henv_p) |].
             intros e1_c e2_c _ _ (<- & Henv_c & Hfp_c).
             change (sccp_code_defs_end defs_phis (blk_code b)) with defs_end in Henv_c.
             eapply cfg_local_sim_weaken;
               [| apply (denote_term_gen_sim true exec_edges cm defs_end (blk_id b)
                           (tiid, tm, tmd) e1_c Htid Henv_c)].
             intros e1_t e2_t bd1 bd2 (<- & <- & Henv_t & Hfp_t & Hbd).
             split; [reflexivity | split; [reflexivity | split; [exact Henv_t |]]].
             split.
             ++ eapply fargs_preserved_trans; [exact Hfp_p |].
                eapply fargs_preserved_trans; [exact Hfp_c | exact Hfp_t].
             ++ destruct bd1 as [bid_tgt | dv]; [| exact I].
                exact (Hbd Logic.eq_refl Hterm_ok).
          -- intros e1_t e2_t [bid_tgt | dv] _ (<- & <- & Henv_t & Hfp_all & Hnext).
             ++ apply cfg_local_sim_ret; cbn [iter_step_rel]; unfold sccp_iter_inv; cbn [fst snd].
                pose proof (Hfp_all fargs Hfargs_none Hfargs_env) as Hfargs_t.
                split; [reflexivity | split; [reflexivity | split; [exact Hnext |]]].
                split; [exact Hfargs_t |].
                unfold sccp_edge_defs.
                destruct (raw_id_eqb (blk_id b) (init c) && raw_id_eqb bid_tgt (init c)).
                ** exact Hfargs_t.
                ** rewrite Efind; exact Henv_t.
             ++ apply cfg_local_sim_ret; cbn [iter_step_rel]; reflexivity.
        * apply cfg_local_sim_ret; cbn [iter_step_rel]; reflexivity.
      + (* Initial state *)
        unfold sccp_iter_inv; cbn [fst snd].
        pose proof (env_matches_cert_fargs_init cm fargs env Hfargs_none Hfargs_lk) as Hfargs0.
        split; [reflexivity | split; [reflexivity | split; [exact Hinit_edge |]]].
        split; [exact Hfargs0 |].
        unfold sccp_edge_defs; rewrite !raw_id_eqb_refl; cbn [andb]; exact Hfargs0.
    - intros ? ? [bid | uv] _ <-;
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_ret; reflexivity].
  Qed.

  Lemma sccp_cfg_sim
    (fargs : list local_id) (c : CFG.cfg dtyp)
    (env : @local_env PaV) (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
      env env (denote_cfg c va) (denote_cfg (sccp_cfg fargs c) va).
  Proof using.
    intros Hfargs_lk; unfold sccp_cfg; cbn zeta.
    destruct (sccp_check_guards fargs c); [| apply denote_cfg_refl_sim].
    destruct (sccp_solve fargs c) as [exec_edges lm].
    set (md_in := sccp_compute_must_def fargs c exec_edges).
    set (cm := sccp_build_cert fargs c exec_edges md_in lm).
    destruct (check_sccp_valid fargs c exec_edges md_in cm) eqn:Hvalid;
      [| apply denote_cfg_refl_sim].
    apply (denote_cfg_sccp_valid_sim fargs c exec_edges md_in cm env va Hvalid Hfargs_lk).
  Qed.

End SCCPSimulation.

(** * 6. Whole-Module Refinement Theorem *)

Theorem sccp_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (sccp_mcfg M).
Proof.
  intros IP IPT M.
  exact (@lift_cfg_with_args_local_pass IP IPT
           sccp_cfg
           sccp_cfg_block_addresses
           (@sccp_cfg_sim IP IPT)
           M).
Qed.
