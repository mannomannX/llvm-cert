(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * CFG DAG Summarization & Block UB Extraction ([CertValidator.CertValCfgSum])

    Purpose:
      Defines acyclic CFG-to-[cfg_dag] summarization ([summarize_ocfg_dag],
      [summarize_cfg_dag_with_uas]), block UB assumption lookup ([block_uas_for]),
      and well-formedness plus source/target operational soundness theorems.

    Trust Contract & Fail-Closed Boundary:
      Fail-closed CFG summarizer ([summarize_src_dag_sound],
      [summarize_tgt_dag_sound]); cycles (exhausted fuel), unsupported terminators,
      or reification errors yield [None], never dropping CFG paths.

    Assumptions:
      Depends on Stdlib, [Paco], [ITree], [ExtLib], [Vellvm], [Diag], and
      [CertFormat]/[AigLrat]/[AlgRules]/[CfgDag]/[CertVal*]; zero custom axioms.

    Section Outline:
      Single section defining [try_const_i1], [block_uas_for],
      [summarize_ocfg_dag]/[summarize_cfg_dag_with_uas], WF, and src/tgt soundness. *)

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
  CertValExpReify
  CertValCfgDag.

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

Definition try_const_i1 (ce : cert_expr) : option bool :=
  match normalize_cert_expr [] ce with
  | CE_BvConst 1%positive v =>
      Some (@Integers.unsigned 1 (@Integers.repr 1 (Z.of_N v)) =? 1)%Z
  | _ => None
  end.

Lemma try_const_i1_sound {Pa : Params} :
  forall (ce : cert_expr) (penv : param_env Pa) (foracle : freeze_oracle) (b : bool),
    wt_cert_expr [] ce = true ->
    is_let_free_expr ce = true ->
    wf_param_env_for (collect_free_vars [] ce) penv ->
    try_const_i1 ce = Some b ->
    exists cbit : @Integers.bit_int 1,
      eval_closed_cert_expr penv foracle ce =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) /\
      (@Integers.unsigned 1 cbit =? 1)%Z = b.
Proof.
  intros ce penv foracle b Hwt Hlf Hpenv Htc.
  unfold try_const_i1 in Htc.
  pose proof (normalize_cert_expr_eval [] ce penv foracle Hwt Hlf Hpenv (Forall_nil _)) as Heq.
  destruct (normalize_cert_expr [] ce) as [w v | | | | | | | |] eqn:En; try discriminate Htc.
  destruct w as [| |]; try discriminate Htc.
  inversion Htc; subst b; clear Htc.
  cbn [eval_closed_cert_expr eval_cert_expr] in Heq.
  destruct (eval_closed_cert_expr penv foracle ce) as [| | | dv]; try contradiction Heq.
  cbn [equiv_eou_dvalue] in Heq; subst dv; exists (@Integers.repr 1 (Z.of_N v)); split; reflexivity.
Qed.

Definition strip_leading_percent (s : string) : string :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 37%nat then rest else s
  | EmptyString => EmptyString
  end.

Definition cert_block_matches_id (bname : string) (bid : block_id) : bool :=
  String.eqb (strip_leading_percent bname) (cert_raw_id_bare bid).

Definition block_uas_for
  (entry_bid : block_id) (bcs : list block_certificate) (bid : block_id)
  : list ub_assumption :=
  List.flat_map (fun bc =>
    let matched :=
      cert_block_matches_id (bc_src_block bc) bid ||
      match bc_kind bc with
      | BCK_Entry => raw_id_eqb bid entry_bid
      | _ => false
      end in
    if matched then bc_ub_assumptions bc else []) bcs.

Definition default_cfg_dag_fuel (G : CFG.cfg dtyp) : nat :=
  S (17 * List.length (blks G)).

Fixpoint summarize_ocfg_dag
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
  {struct fuel} : option cfg_dag :=
  match fuel with
  | O => None
  | S fuel' =>
      match RM.find bid_cur bmap with
      | None => None
      | Some b =>
          if is_entry && negb (list_empty_b (blk_phis b)) then None
          else
            match reify_phi_evals uf params src_pnames defs smap bid_from seen (blk_phis b) with
            | None => None
            | Some (pevals, seen_p) =>
                let smap_p := apply_phi_smap smap pevals in
                match reify_code uf params src_pnames defs smap_p seen_p (blk_code b) with
                | None => None
                | Some (cevals, smap_c, seen_c) =>
                    let opt_d_term :=
                      match blk_term b with
                      | (_, TERM_Unreachable, _) =>
                          Some CD_Unreachable
                      | (_, TERM_Ret_void, _) =>
                          Some CD_RetVoid
                      | (_, TERM_Ret (DTYPE_Base (DTYPE_I w), op), _) =>
                          match reify_exp uf params src_pnames defs smap_c seen_c
                                  (Some (DTYPE_Base (DTYPE_I w))) op with
                          | Some (_, ce_ret, _) =>
                              Some (CD_RetScalar w ce_ret)
                          | None => None
                          end
                      | (_, TERM_Br_1 br, _) =>
                          summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                            false bid_cur br smap_c seen_c
                      | (_, TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2, _) =>
                          match reify_exp uf params src_pnames defs smap_c seen_c
                                  (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
                          | Some (_, ce_cond, seen_br) =>
                              match try_const_i1 ce_cond with
                              | Some true =>
                                  match summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br1 smap_c seen_br with
                                  | Some d_t => Some (CD_Eval 1%positive ce_cond d_t)
                                  | None => None
                                  end
                              | Some false =>
                                  match summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br2 smap_c seen_br with
                                  | Some d_f => Some (CD_Eval 1%positive ce_cond d_f)
                                  | None => None
                                  end
                              | None =>
                                  match summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br1 smap_c seen_br,
                                        summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br2 smap_c seen_br with
                                  | Some d_t, Some d_f =>
                                      Some (CD_Branch ce_cond d_t d_f)
                                  | _, _ => None
                                  end
                              end
                          | None => None
                          end
                      | _ => None
                      end in
                    match opt_d_term with
                    | Some d_term =>
                        Some (CD_BlockAssume (blk_uas bid_cur)
                                (wrap_phi_evals pevals (wrap_evals cevals d_term)))
                    | None => None
                    end
                end
            end
      end
  end.

Definition summarize_cfg_dag_with_uas
  (blk_uas : block_id -> list ub_assumption)
  (uf : bool) (G : CFG.cfg dtyp) (src_pnames : list string) : option cfg_dag :=
  summarize_ocfg_dag
    (default_cfg_dag_fuel G)
    blk_uas
    uf
    (args G)
    src_pnames
    (defined_ids_of_cfg G)
    (ocfg_map (blks G))
    true
    (init G)
    (init G)
    (RM.empty _)
    [].

Definition summarize_cfg_dag
  (uf : bool) (G : CFG.cfg dtyp) (src_pnames : list string) : option cfg_dag :=
  summarize_cfg_dag_with_uas (fun _ => []) uf G src_pnames.

Lemma block_param_uses_phi_in :
  forall params defs b id fm dt pargs md bid_from op u,
    In (id, Phi fm dt pargs, md) (blk_phis b) ->
    In (bid_from, op) pargs ->
    In u (exp_param_uses params defs (Some dt) op) ->
    In u (block_param_uses params defs b).
Proof.
  intros params defs b id fm dt pargs md bid_from op u Hphi Hparg Hu.
  unfold block_param_uses; apply in_app_iff; left.
  apply in_flat_map; exists (id, Phi fm dt pargs, md); split; [exact Hphi |].
  apply in_flat_map; exists (bid_from, op); split; assumption.
Qed.

Lemma block_param_uses_code_in :
  forall params defs b iid ins md u,
    In (iid, ins, md) (blk_code b) ->
    In u (instr_param_uses params defs ins) ->
    In u (block_param_uses params defs b).
Proof.
  intros params defs b iid ins md u Hc Hu.
  unfold block_param_uses; apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists (iid, ins, md); split; assumption.
Qed.

Lemma block_param_uses_ret_in :
  forall params defs b iid dt op md u,
    blk_term b = (iid, TERM_Ret (dt, op), md) ->
    In u (exp_param_uses params defs (Some dt) op) ->
    In u (block_param_uses params defs b).
Proof.
  intros params defs b iid dt op md u Ht Hu.
  unfold block_param_uses; apply in_app_iff; right; apply in_app_iff; right.
  rewrite Ht; exact Hu.
Qed.

Lemma block_param_uses_br_in :
  forall params defs b iid dt op br1 br2 md u,
    blk_term b = (iid, TERM_Br (dt, op) br1 br2, md) ->
    In u (exp_param_uses params defs (Some dt) op) ->
    In u (block_param_uses params defs b).
Proof.
  intros params defs b iid dt op br1 br2 md u Ht Hu.
  unfold block_param_uses; apply in_app_iff; right; apply in_app_iff; right.
  rewrite Ht; exact Hu.
Qed.

Lemma summarize_ocfg_dag_wf :
  forall fuel blk_uas uf G src_pnames allowed is_entry bid_from bid_cur smap seen d,
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg G) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    wf_smap_entries allowed (defined_ids_of_cfg G) seen uf smap ->
    summarize_ocfg_dag fuel blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
      (ocfg_map (blks G)) is_entry bid_from bid_cur smap seen = Some d ->
    wf_cfg_dag allowed d = true.
Proof.
  induction fuel as [| fuel' IH];
    intros blk_uas uf G src_pnames allowed is_entry bid_from bid_cur smap seen d Hpu_cfg Hsmap Hr;
    cbn [summarize_ocfg_dag] in Hr; [discriminate |].
  destruct (RM.find bid_cur (ocfg_map (blks G))) as [b |] eqn:Hfb; [| discriminate].
  pose proof (ocfg_map_in (blks G) bid_cur b Hfb) as Hb_in.
  destruct (is_entry && negb (list_empty_b (blk_phis b))); [discriminate |].
  destruct (reify_phi_evals uf (args G) src_pnames (defined_ids_of_cfg G) smap bid_from seen (blk_phis b))
    as [[pevals seen_p] |] eqn:Hr_phis; [| discriminate].
  destruct (reify_phi_evals_typing (blk_phis b) uf (args G) src_pnames (defined_ids_of_cfg G) allowed
              smap bid_from seen pevals seen_p Hsmap
              (fun id fm dt pargs md op idx w0 pnm Hphi Hparg Hu Hpnm =>
                 Hpu_cfg idx w0 pnm
                   (proj2 (in_flat_map _ (blks G) _)
                     (ex_intro _ b (conj Hb_in (block_param_uses_phi_in _ _ b id fm dt pargs md bid_from op _ Hphi Hparg Hu))))
                   Hpnm)
              Hr_phis)
    as [Hinc_sp Hfa_p].
  pose proof (apply_phi_smap_wf allowed (defined_ids_of_cfg G) seen_p uf pevals smap
                (wf_smap_entries_seen_mono _ _ _ _ _ _ Hinc_sp Hsmap) Hfa_p) as Hsmap_p.
  destruct (reify_code uf (args G) src_pnames (defined_ids_of_cfg G) (apply_phi_smap smap pevals) seen_p (blk_code b))
    as [[[cevals smap_c] seen_c] |] eqn:Hr_code; [| discriminate].
  destruct (reify_code_typing (blk_code b) uf (args G) src_pnames (defined_ids_of_cfg G) allowed
              (apply_phi_smap smap pevals) seen_p cevals smap_c seen_c Hsmap_p
              (fun iid ins md idx w0 pnm Hc Hu Hpnm =>
                 Hpu_cfg idx w0 pnm
                   (proj2 (in_flat_map _ (blks G) _)
                     (ex_intro _ b (conj Hb_in (block_param_uses_code_in _ _ b iid ins md _ Hc Hu))))
                   Hpnm)
              Hr_code)
    as (_ & Hsmap_c & Hwrap_c).
  cbn zeta in Hr.
  match type of Hr with
  | match ?ot with Some _ => _ | None => _ end = Some _ =>
      destruct ot as [d_term |] eqn:Hopt; [| discriminate Hr]
  end.
  inversion Hr; subst d; clear Hr.
  cbn [wf_cfg_dag]; apply (wrap_phi_evals_wf _ _ _ _ _ _ Hfa_p); apply Hwrap_c.
  destruct (blk_term b) as [[tiid tm] tmd] eqn:Htm.
  destruct tm; try discriminate Hopt.
  - (* TERM_Ret *)
    destruct v as [dt op].
    destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [w | | | | | | | | | |]; try discriminate Hopt.
    destruct (reify_exp uf (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate Hopt].
    inversion Hopt; subst d_term; clear Hopt.
    destruct (reify_exp_typing op uf (args G) src_pnames (defined_ids_of_cfg G) allowed smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I w))) w1 ce_ret seen_ret Hsmap_c
                (fun idx w0 pnm Hu Hpnm =>
                   Hpu_cfg idx w0 pnm
                     (proj2 (in_flat_map _ (blks G) _)
                       (ex_intro _ b (conj Hb_in (block_param_uses_ret_in _ _ b tiid _ op tmd _ Htm Hu))))
                     Hpnm)
                Hr_ret)
      as (Hcw & Hwt & Hbw & Hlf & Hfv & _ & _).
    apply check_opt_int_width_some_inv in Hcw; subst w1.
    cbn [wf_cfg_dag].
    rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv); reflexivity.
  - (* TERM_Ret_void *)
    inversion Hopt; subst d_term; reflexivity.
  - (* TERM_Br *)
    destruct v as [dt op].
    destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [wc | | | | | | | | | |]; try discriminate Hopt.
    destruct wc as [| |]; try discriminate Hopt.
    destruct (reify_exp uf (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
      as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate Hopt].
    destruct (reify_exp_typing op uf (args G) src_pnames (defined_ids_of_cfg G) allowed smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I 1%positive))) wc' ce_cond seen_br Hsmap_c
                (fun idx w0 pnm Hu Hpnm =>
                   Hpu_cfg idx w0 pnm
                     (proj2 (in_flat_map _ (blks G) _)
                       (ex_intro _ b (conj Hb_in (block_param_uses_br_in _ _ b tiid _ op br1 br2 tmd _ Htm Hu))))
                     Hpnm)
                Hr_cond)
      as (Hcw & Hwt & Hbw & Hlf & Hfv & Hinc_br & _).
    apply check_opt_int_width_some_inv in Hcw; subst wc'.
    pose proof (wf_smap_entries_seen_mono _ _ _ _ _ _ Hinc_br Hsmap_c) as Hsmap_br.
    destruct (try_const_i1 ce_cond) as [[|] |].
    + destruct (summarize_ocfg_dag fuel' blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
                  (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br)
        as [d_t |] eqn:Hr_t; [| discriminate Hopt].
      inversion Hopt; subst d_term.
      pose proof (IH blk_uas uf G src_pnames allowed false bid_cur br1 smap_c seen_br d_t Hpu_cfg Hsmap_br Hr_t) as Hwft.
      cbn [wf_cfg_dag]; rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), Hwft; reflexivity.
    + destruct (summarize_ocfg_dag fuel' blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
                  (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br)
        as [d_f |] eqn:Hr_f; [| discriminate Hopt].
      inversion Hopt; subst d_term.
      pose proof (IH blk_uas uf G src_pnames allowed false bid_cur br2 smap_c seen_br d_f Hpu_cfg Hsmap_br Hr_f) as Hwff.
      cbn [wf_cfg_dag]; rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), Hwff; reflexivity.
    + destruct (summarize_ocfg_dag fuel' blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
                  (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br)
        as [d_t |] eqn:Hr_t; [| discriminate Hopt].
      destruct (summarize_ocfg_dag fuel' blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
                  (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br)
        as [d_f |] eqn:Hr_f; [| discriminate Hopt].
      inversion Hopt; subst d_term.
      pose proof (IH blk_uas uf G src_pnames allowed false bid_cur br1 smap_c seen_br d_t Hpu_cfg Hsmap_br Hr_t) as Hwft.
      pose proof (IH blk_uas uf G src_pnames allowed false bid_cur br2 smap_c seen_br d_f Hpu_cfg Hsmap_br Hr_f) as Hwff.
      cbn [wf_cfg_dag]; rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), Hwft, Hwff; reflexivity.
  - (* TERM_Br_1 *)
    exact (IH blk_uas uf G src_pnames allowed false bid_cur br smap_c seen_c d_term Hpu_cfg Hsmap_c Hopt).
  - (* TERM_Unreachable *)
    inversion Hopt; subst d_term; reflexivity.
Qed.

Lemma summarize_cfg_dag_with_uas_wf :
  forall blk_uas uf G src_pnames allowed d,
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg G) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    summarize_cfg_dag_with_uas blk_uas uf G src_pnames = Some d ->
    wf_cfg_dag allowed d = true.
Proof.
  intros blk_uas uf G src_pnames allowed d Hpu Hr.
  exact (summarize_ocfg_dag_wf (default_cfg_dag_fuel G) blk_uas uf G src_pnames allowed
           true (init G) (init G) (RM.empty _) [] d Hpu
           (wf_smap_entries_empty allowed (defined_ids_of_cfg G) [] uf) Hr).
Qed.

Lemma summarize_cfg_dag_wf :
  forall uf G src_pnames allowed d,
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg G) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    summarize_cfg_dag uf G src_pnames = Some d ->
    wf_cfg_dag allowed d = true.
Proof.
  intros uf G src_pnames allowed d Hpu Hr.
  exact (summarize_cfg_dag_with_uas_wf (fun _ => []) uf G src_pnames allowed d Hpu Hr).
Qed.

Lemma denote_ocfg_map_step_obs {Pa : Params} :
  forall (bmap : rmap (block dtyp)) (bid_from bid_cur : block_id) (b : block dtyp),
    RM.find bid_cur bmap = Some b ->
    observe (@denote_ocfg_map Pa bmap None (bid_from, bid_cur)) =
    observe (ITree.bind
      (ITree.bind (denote_block b bid_from None)
        (fun bd => match bd with
                   | inr dv => Ret (inr (inr dv))
                   | inl bid_target => Ret (inl (bid_cur, bid_target))
                   end))
      (fun lr => match lr with
                 | inl j => Tau (denote_ocfg_map bmap None j)
                 | inr r => Ret r
                 end)).
Proof.
  intros bmap bid_from bid_cur b Hf.
  unfold denote_ocfg_map; rewrite observe_iter; cbn beta; rewrite Hf; reflexivity.
Qed.

Lemma cfg_param_dtyp_compatible_nth :
  forall G arg_dtys idx dt,
    cfg_param_dtyp_compatible G arg_dtys = true ->
    In (idx, dt) (param_idx_uses_cfg G) ->
    nth_error arg_dtys idx = Some dt.
Proof.
  intros G arg_dtys idx dt Hcomp Hin.
  unfold cfg_param_dtyp_compatible in Hcomp; rewrite forallb_forall in Hcomp.
  pose proof (Hcomp (idx, dt) Hin) as Hidx.
  cbn zeta iota in Hidx.
  destruct (nth_error arg_dtys idx) as [dt_a |] eqn:Hnth; [| discriminate Hidx].
  apply dtyp_eqb_dec_eq in Hidx; subst dt_a; reflexivity.
Qed.

Lemma summarize_ocfg_src_sound {Pa : Params} :
  forall fuel blk_uas G src_pnames allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) is_entry bid_from bid_cur
         smap (env : rmap (@dvalue Pa)) seen d,
    NoDup src_pnames ->
    List.length (args G) = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
    wf_smap_entries allowed (defined_ids_of_cfg G) seen false smap ->
    env_matches_smap (defined_ids_of_cfg G) (build_param_env src_pnames vs) foracle smap env ->
    summarize_ocfg_dag fuel blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
      (ocfg_map (blks G)) is_entry bid_from bid_cur smap seen = Some d ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s,
           cfg_steps_to_ub (chain_draws draws tail_s) env
             (denote_ocfg_map (ocfg_map (blks G)) None (bid_from, bid_cur))) /\
        eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_UB) \/
       (exists env_out dv,
          eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_Ret dv /\
          (forall tail_s,
             cfg_steps_to_ret (chain_draws draws tail_s) env
               (denote_ocfg_map (ocfg_map (blks G)) None (bid_from, bid_cur))
               tail_s env_out (inr dv)))).
Proof.
  induction fuel as [| fuel' IH];
    intros blk_uas G src_pnames allowed arg_dtys vs foracle is_entry bid_from bid_cur smap env seen d
           Hnd Hlp Hls Hla Hcomp Hvs Hpe Hwfs Henv Hr;
    cbn [summarize_ocfg_dag] in Hr; [discriminate |].
  destruct (RM.find bid_cur (ocfg_map (blks G))) as [b |] eqn:Hfb; [| discriminate].
  pose proof (ocfg_map_in (blks G) bid_cur b Hfb) as Hb_in.
  destruct (is_entry && negb (list_empty_b (blk_phis b))); [discriminate |].
  destruct (reify_phi_evals false (args G) src_pnames (defined_ids_of_cfg G) smap bid_from seen (blk_phis b))
    as [[pevals seen_p] |] eqn:Hr_phis; [| discriminate].
  destruct (reify_code false (args G) src_pnames (defined_ids_of_cfg G)
              (apply_phi_smap smap pevals) seen_p (blk_code b))
    as [[[cevals smap_c] seen_c] |] eqn:Hr_code; [| discriminate].
  cbn zeta in Hr.
  match type of Hr with
  | match ?ot with Some _ => _ | None => _ end = Some _ =>
      destruct ot as [d_term |] eqn:Hopt; [| discriminate Hr]
  end.
  inversion Hr; subst d; clear Hr.
  destruct (eval_reified_phi_map_src (blk_phis b) (args G) src_pnames (defined_ids_of_cfg G)
              allowed arg_dtys vs foracle smap env bid_from seen pevals seen_p
              Hnd Hlp Hls Hla Hvs
              (fun id fm dt pargs md op idx dt_u Hphi Hparg Hu =>
                 cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                   (proj2 (in_flat_map _ (blks G) _)
                     (ex_intro _ b (conj Hb_in (block_param_uses_phi_in _ _ b id fm dt pargs md bid_from op _ Hphi Hparg Hu)))))
              Hpe Hwfs Henv Hr_phis)
    as (draws_p & Hfa_dp & [[Hub_p Hev_ub_p] | (dvs_p & Hpm_p & Hev_kp & Hst_p)]).
  - exists draws_p; split; [exact Hfa_dp | left; split].
    + intros tail_s.
      eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
      unfold denote_block, denote_phis.
      apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
      exact (Hub_p tail_s).
    + cbn [eval_cfg_dag]; exact (Hev_ub_p (wrap_evals cevals d_term)).
  - destruct (reify_phi_evals_wf_smap (blk_phis b) false (args G) src_pnames (defined_ids_of_cfg G)
                allowed smap bid_from seen pevals seen_p Hwfs Hr_phis)
      as (ext_p & _ & Hfa_wf_p & Hwfs_p).
    pose proof (apply_phi_env_matches ext_p (defined_ids_of_cfg G) seen_p false
                  (build_param_env src_pnames vs) foracle smap env pevals dvs_p
                  Henv Hfa_wf_p Hpm_p) as Henv_p.
    assert (Hpe_p : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r (apply_phi_env env dvs_p) = Some dv).
    { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
      exists dv; split; [exact Hv |].
      rewrite (apply_phi_env_preserves_nondefs ext_p (defined_ids_of_cfg G) seen_p false
                 (build_param_env src_pnames vs) foracle env pevals dvs_p r Hfa_wf_p Hpm_p Hnin);
        exact Hfe. }
    assert (Hphis_step : forall tail_s,
      cfg_steps_to_ret (chain_draws draws_p tail_s) env
        (denote_phis bid_from (blk_phis b)) tail_s (apply_phi_env env dvs_p) tt).
    { intros tail_s; unfold denote_phis.
      eapply cfg_steps_to_ret_bind; [exact (Hst_p tail_s) |].
      eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite_list | apply CSR_Ret; reflexivity]. }
    destruct (eval_reified_code_src (blk_code b) (args G) src_pnames (defined_ids_of_cfg G)
                ext_p arg_dtys vs foracle (apply_phi_smap smap pevals) (apply_phi_env env dvs_p)
                seen_p cevals smap_c seen_c Hnd Hlp Hls Hla Hvs
                (fun iid ins md idx dt_u Hc Hu =>
                   cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                     (proj2 (in_flat_map _ (blks G) _)
                       (ex_intro _ b (conj Hb_in (block_param_uses_code_in _ _ b iid ins md _ Hc Hu)))))
                Hpe_p Hwfs_p Henv_p Hr_code)
      as (draws_c & Hfa_dc & [[Hub_c Hev_ub_c] | (env_c & Hpe_c & Henv_c & Hev_kc & Hst_c)]).
    + exists (draws_p ++ draws_c); split; [apply Forall_app; split; assumption | left; split].
      * intros tail_s; rewrite chain_draws_app.
        eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
        unfold denote_block.
        apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
        eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c tail_s)) |].
        apply cfg_steps_to_ub_bind_l; exact (Hub_c tail_s).
      * cbn [eval_cfg_dag]; rewrite Hev_kp; exact (Hev_ub_c d_term).
    + destruct (reify_code_wf_smap (blk_code b) false (args G) src_pnames (defined_ids_of_cfg G)
                  ext_p (apply_phi_smap smap pevals) seen_p cevals smap_c seen_c Hwfs_p Hr_code)
        as (ext_c & _ & Hwfs_c).
      destruct (blk_term b) as [[tiid tm] tmd] eqn:Htm.
      destruct tm; try discriminate Hopt.
      * (* TERM_Ret *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [w | | | | | | | | | |]; try discriminate Hopt.
        destruct (reify_exp false (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) op)
          as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate Hopt].
        inversion Hopt; subst d_term; clear Hopt.
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_ret)) as ->.
        destruct (eval_reified_exp_src op (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c arg_dtys vs foracle smap_c env_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) w ce_ret seen_ret
                    Hnd Hlp Hls Hla Hvs
                    (fun idx dt_u Hu =>
                       cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                         (proj2 (in_flat_map _ (blks G) _)
                           (ex_intro _ b (conj Hb_in (block_param_uses_ret_in _ _ b tiid _ op tmd _ Htm Hu)))))
                    Hpe_c Hwfs_c Henv_c Hr_ret)
          as (draws_r & Hfa_dr & [[Hub_r [msg_r Hev_r]] | [dv_r [Hev_r [_ Hst_r]]]]).
        -- exists ((draws_p ++ draws_c) ++ draws_r).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dr] | left; split].
           ++ intros tail_s; rewrite !chain_draws_app.
              eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
              eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_r tail_s))) |].
              eapply cfg_steps_to_ub_bind_r; [exact (Hst_c (chain_draws draws_r tail_s)) |].
              cbn [denote_terminator]; unfold denote_exp'.
              apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_r tail_s).
           ++ cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
        -- exists ((draws_p ++ draws_c) ++ draws_r).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dr] | right].
           exists env_c, dv_r; split.
           ++ cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
           ++ intros tail_s; rewrite !chain_draws_app.
              eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_r tail_s))) |].
                     eapply cfg_steps_to_ret_bind; [exact (Hst_c (chain_draws draws_r tail_s)) |].
                     cbn [denote_terminator]; unfold denote_exp'.
                     eapply cfg_steps_to_ret_bind;
                       [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_r tail_s)) | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** apply CSR_Ret; reflexivity.
      * (* TERM_Ret_void *)
        inversion Hopt; subst d_term; clear Hopt.
        exists (draws_p ++ draws_c); split; [apply Forall_app; split; assumption | right].
        exists env_c, NONE; split; [cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; reflexivity |].
        intros tail_s; rewrite chain_draws_app.
        eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
        unfold denote_block; rewrite Htm.
        eapply cfg_steps_to_ret_bind.
        -- eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind; [exact (Hphis_step (chain_draws draws_c tail_s)) |].
              eapply cfg_steps_to_ret_bind; [exact (Hst_c tail_s) | apply CSR_Ret; reflexivity].
           ++ apply CSR_Ret; reflexivity.
        -- apply CSR_Ret; reflexivity.
      * (* TERM_Br *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [wc | | | | | | | | | |]; try discriminate Hopt.
        destruct wc as [| |]; try discriminate Hopt.
        destruct (reify_exp false (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
          as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate Hopt].
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_cond)) as ->.
        destruct (reify_exp_wt_lf op false (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c smap_c seen_c (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hwfs_c Hr_cond) as [Hwt_cond Hlf_cond].
        pose proof (wf_smap_entries_false_seen ext_c (defined_ids_of_cfg G) seen_c seen_br smap_c Hwfs_c) as Hwfs_br.
        destruct (eval_reified_exp_src op (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c arg_dtys vs foracle smap_c env_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hnd Hlp Hls Hla Hvs
                    (fun idx dt_u Hu =>
                       cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                         (proj2 (in_flat_map _ (blks G) _)
                           (ex_intro _ b (conj Hb_in (block_param_uses_br_in _ _ b tiid _ op br1 br2 tmd _ Htm Hu)))))
                    Hpe_c Hwfs_c Henv_c Hr_cond)
          as (draws_br & Hfa_dbr & [[Hub_br [msg_br Hev_br]] | [dv_br [Hev_br [Hsc_br Hst_br]]]]).
        -- exists ((draws_p ++ draws_c) ++ draws_br).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | left; split].
           ++ intros tail_s; rewrite !chain_draws_app.
              eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
              eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br tail_s))) |].
              eapply cfg_steps_to_ub_bind_r; [exact (Hst_c (chain_draws draws_br tail_s)) |].
              cbn [denote_terminator]; unfold denote_exp'.
              apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_br tail_s).
           ++ cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc.
              destruct (try_const_i1 ce_cond) as [[|] |].
              ** destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
                 inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
              ** destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
                 inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
              ** destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
                 destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
                 inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
        -- pose proof (eval_closed_lf_ret_wf_param_env ce_cond (build_param_env src_pnames vs)
                         foracle dv_br Hlf_cond Hev_br) as Hp_cond.
           destruct Hsc_br as [-> | [cbit ->]].
           ++ exists ((draws_p ++ draws_c) ++ draws_br).
              split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | left; split].
              ** intros tail_s; rewrite !chain_draws_app.
                 eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                 unfold denote_block; rewrite Htm.
                 apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
                 eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br tail_s))) |].
                 eapply cfg_steps_to_ub_bind_r; [exact (Hst_c (chain_draws draws_br tail_s)) |].
                 cbn [denote_terminator]; unfold denote_exp'.
                 eapply cfg_steps_to_ub_bind_r;
                   [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br tail_s)) | apply cfg_steps_raiseUB].
              ** destruct (try_const_i1 ce_cond) as [b_tc |] eqn:Etc.
                 --- destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                                 foracle b_tc Hwt_cond Hlf_cond Hp_cond Etc) as [cbit_tc [Hev_tc _]].
                     congruence.
                 --- destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
                     destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
                     inversion Hopt; subst d_term.
                     cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ set (br_tgt := if (@Integers.unsigned 1 cbit =? 1)%Z then br1 else br2).
              assert (Hnext_br :
                exists d_next,
                  summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br_tgt smap_c seen_br = Some d_next /\
                  eval_cfg_dag (build_param_env src_pnames vs) foracle d_term =
                  eval_cfg_dag (build_param_env src_pnames vs) foracle d_next).
              { destruct (try_const_i1 ce_cond) as [[|] |] eqn:Etc.
                - destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                              foracle true Hwt_cond Hlf_cond Hp_cond Etc) as [cbit' [Hev_tc Ecbit']].
                  rewrite Hev_br in Hev_tc.
                  pose proof (eou_dvalue_I_same_sz_inj 1 cbit cbit' Hev_tc) as <-.
                  destruct (summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br) as [d_t |] eqn:Hr_t;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term; exists d_t; unfold br_tgt; rewrite Ecbit'; split; [exact Hr_t |].
                  cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
                - destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                              foracle false Hwt_cond Hlf_cond Hp_cond Etc) as [cbit' [Hev_tc Ecbit']].
                  rewrite Hev_br in Hev_tc.
                  pose proof (eou_dvalue_I_same_sz_inj 1 cbit cbit' Hev_tc) as <-.
                  destruct (summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br) as [d_f |] eqn:Hr_f;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term; exists d_f; unfold br_tgt; rewrite Ecbit'; split; [exact Hr_f |].
                  cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
                - destruct (summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br) as [d_t |] eqn:Hr_t;
                    [| discriminate Hopt].
                  destruct (summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br) as [d_f |] eqn:Hr_f;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term.
                  exists (if (@Integers.unsigned 1 cbit =? 1)%Z then d_t else d_f); split.
                  + unfold br_tgt; destruct (@Integers.unsigned 1 cbit =? 1)%Z; [exact Hr_t | exact Hr_f].
                  + cbn [eval_cfg_dag]; rewrite Hev_br; destruct (@Integers.unsigned 1 cbit =? 1)%Z; reflexivity. }
              destruct Hnext_br as [d_next [Hr_next Hev_term]].
              destruct (IH blk_uas G src_pnames ext_c arg_dtys vs foracle false bid_cur br_tgt
                          smap_c env_c seen_br d_next
                          Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfs_br Henv_c Hr_next)
                as (draws_n & Hfa_dn & [[Hub_n Hev_ub_n] | [env_out [dv_out [Hev_out Hst_n]]]]).
              ** exists (((draws_p ++ draws_c) ++ draws_br) ++ draws_n).
                 split;
                   [apply Forall_app; split;
                      [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | exact Hfa_dn]
                   | left; split].
                 --- intros tail_s; rewrite !chain_draws_app.
                     eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                     unfold denote_block; rewrite Htm.
                     eapply cfg_steps_to_ub_bind_r.
                     +++ eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind;
                               [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br (chain_draws draws_n tail_s)))) |].
                             eapply cfg_steps_to_ret_bind;
                               [exact (Hst_c (chain_draws draws_br (chain_draws draws_n tail_s))) |].
                             cbn [denote_terminator]; unfold denote_exp'.
                             eapply cfg_steps_to_ret_bind;
                               [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br (chain_draws draws_n tail_s))) |].
                             cbn iota beta; rewrite bit_int_1_equ_one_eq_unsigned; unfold br_tgt.
                             destruct (@Integers.unsigned 1 cbit =? 1)%Z; apply CSR_Ret; reflexivity.
                         *** apply CSR_Ret; reflexivity.
                     +++ eapply CSU_Tau; [reflexivity | exact (Hub_n tail_s)].
                 --- cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc, Hev_term; exact Hev_ub_n.
              ** exists (((draws_p ++ draws_c) ++ draws_br) ++ draws_n).
                 split;
                   [apply Forall_app; split;
                      [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | exact Hfa_dn]
                   | right; exists env_out, dv_out; split].
                 --- cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc, Hev_term; exact Hev_out.
                 --- intros tail_s; rewrite !chain_draws_app.
                     eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                     unfold denote_block; rewrite Htm.
                     eapply cfg_steps_to_ret_bind.
                     +++ eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind;
                               [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br (chain_draws draws_n tail_s)))) |].
                             eapply cfg_steps_to_ret_bind;
                               [exact (Hst_c (chain_draws draws_br (chain_draws draws_n tail_s))) |].
                             cbn [denote_terminator]; unfold denote_exp'.
                             eapply cfg_steps_to_ret_bind;
                               [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br (chain_draws draws_n tail_s))) |].
                             cbn iota beta; rewrite bit_int_1_equ_one_eq_unsigned; unfold br_tgt.
                             destruct (@Integers.unsigned 1 cbit =? 1)%Z; apply CSR_Ret; reflexivity.
                         *** apply CSR_Ret; reflexivity.
                     +++ eapply CSR_Tau; [reflexivity | exact (Hst_n tail_s)].
      * (* TERM_Br_1 *)
        destruct (IH blk_uas G src_pnames ext_c arg_dtys vs foracle false bid_cur br smap_c env_c seen_c d_term
                    Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfs_c Henv_c Hopt)
          as (draws_n & Hfa_dn & [[Hub_n Hev_ub_n] | [env_out [dv_out [Hev_out Hst_n]]]]).
        -- exists ((draws_p ++ draws_c) ++ draws_n).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dn] | left; split].
           ++ intros tail_s; rewrite !chain_draws_app.
              eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ub_bind_r.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_n tail_s))) |].
                     eapply cfg_steps_to_ret_bind; [exact (Hst_c (chain_draws draws_n tail_s)) | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** eapply CSU_Tau; [reflexivity | exact (Hub_n tail_s)].
           ++ cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; exact Hev_ub_n.
        -- exists ((draws_p ++ draws_c) ++ draws_n).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dn] | right].
           exists env_out, dv_out; split; [cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; exact Hev_out |].
           intros tail_s; rewrite !chain_draws_app.
           eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
           unfold denote_block; rewrite Htm.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_n tail_s))) |].
                 eapply cfg_steps_to_ret_bind; [exact (Hst_c (chain_draws draws_n tail_s)) | apply CSR_Ret; reflexivity].
              ** apply CSR_Ret; reflexivity.
           ++ eapply CSR_Tau; [reflexivity | exact (Hst_n tail_s)].
      * (* TERM_Unreachable *)
        inversion Hopt; subst d_term; clear Hopt.
        exists (draws_p ++ draws_c); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app.
           eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
           unfold denote_block; rewrite Htm.
           apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
           eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c tail_s)) |].
           eapply cfg_steps_to_ub_bind_r; [exact (Hst_c tail_s) | apply cfg_steps_raiseUB].
        -- cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; reflexivity.
Qed.

Lemma summarize_src_dag_with_uas_sound {Pa : Params} :
  forall blk_uas G src_pnames arg_dtys (vs : list (@dvalue Pa)) (foracle : freeze_oracle) d,
    NoDup (args G) ->
    NoDup src_pnames ->
    List.length src_pnames = List.length (args G) ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    summarize_cfg_dag_with_uas blk_uas false G src_pnames = Some d ->
    exists sigma_src : @draw_strat Pa,
      wf_draw_strat sigma_src /\
      ((cfg_steps_to_ub sigma_src (init_cfg_locals (args G) vs) (denote_cfg G None) /\
        eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_UB) \/
       (exists sigma_src' env_out dv,
          eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_Ret dv /\
          cfg_steps_to_ret sigma_src (init_cfg_locals (args G) vs) (denote_cfg G None)
            sigma_src' env_out dv)).
Proof.
  intros blk_uas G src_pnames arg_dtys vs foracle d Hnd_p Hnd_s Hlen_sp Hlen_da Hcomp Hvs Hr.
  assert (Hlen_vs : List.length vs = List.length arg_dtys) by exact (Forall2_length Hvs).
  assert (Hlp : List.length (args G) = List.length vs) by lia.
  assert (Hls : List.length src_pnames = List.length vs) by lia.
  assert (Hpe0 : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
    exists dv, nth_error vs idx = Some dv /\ RM.find r (init_cfg_locals (args G) vs) = Some dv).
  { intros idx r Hnth _; exact (init_cfg_locals_nth (args G) vs idx r Hnd_p Hlp Hnth). }
  destruct (summarize_ocfg_src_sound (default_cfg_dag_fuel G) blk_uas G src_pnames [] arg_dtys vs foracle
              true (init G) (init G) (RM.empty _) (init_cfg_locals (args G) vs) [] d
              Hnd_s Hlp Hls Hlen_da Hcomp Hvs Hpe0
              (wf_smap_entries_empty [] (defined_ids_of_cfg G) [] false)
              (env_matches_smap_empty (defined_ids_of_cfg G) (build_param_env src_pnames vs)
                 foracle (init_cfg_locals (args G) vs))
              Hr)
    as (draws & Hfa & [[Hub Hev_ub] | [env_out [dv [Hev_ret Hst_ret]]]]).
  - exists (chain_draws draws default_draw_strat).
    split; [exact (chain_draws_wf draws default_draw_strat Hfa default_draw_strat_wf) | left; split; [| exact Hev_ub]].
    unfold denote_cfg, denote_cfg_map; apply cfg_steps_to_ub_bind_l; exact (Hub default_draw_strat).
  - exists (chain_draws draws default_draw_strat).
    split; [exact (chain_draws_wf draws default_draw_strat Hfa default_draw_strat_wf) | right].
    exists default_draw_strat, env_out, dv; split; [exact Hev_ret |].
    unfold denote_cfg, denote_cfg_map.
    eapply cfg_steps_to_ret_bind; [exact (Hst_ret default_draw_strat) | apply CSR_Ret; reflexivity].
Qed.

Lemma summarize_src_dag_sound {Pa : Params} :
  forall G src_pnames arg_dtys (vs : list (@dvalue Pa)) (foracle : freeze_oracle) d,
    NoDup (args G) ->
    NoDup src_pnames ->
    List.length src_pnames = List.length (args G) ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    summarize_cfg_dag false G src_pnames = Some d ->
    exists sigma_src : @draw_strat Pa,
      wf_draw_strat sigma_src /\
      ((cfg_steps_to_ub sigma_src (init_cfg_locals (args G) vs) (denote_cfg G None) /\
        eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_UB) \/
       (exists sigma_src' env_out dv,
          eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_Ret dv /\
          cfg_steps_to_ret sigma_src (init_cfg_locals (args G) vs) (denote_cfg G None)
            sigma_src' env_out dv)).
Proof.
  intros G src_pnames arg_dtys vs foracle d.
  exact (summarize_src_dag_with_uas_sound (fun _ => []) G src_pnames arg_dtys vs foracle d).
Qed.

Lemma summarize_ocfg_tgt_sound {Pa : Params} :
  forall fuel blk_uas G src_pnames allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         is_entry bid_from bid_cur smap (env : rmap (@dvalue Pa)) seen0 d,
    NoDup src_pnames ->
    List.length (args G) = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed (defined_ids_of_cfg G) seen0 true smap ->
    env_matches_smap (defined_ids_of_cfg G) (build_param_env src_pnames vs)
      (oracle_of_fmap fmap0) smap env ->
    summarize_ocfg_dag fuel blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
      (ocfg_map (blks G)) is_entry bid_from bid_cur smap seen0 = Some d ->
    exists added : list (freeze_key * Z),
      (forall key z, In (key, z) added -> ~ In key seen0) /\
      (eval_cfg_dag (build_param_env src_pnames vs) (oracle_of_fmap (added ++ fmap0)) d = DO_UB \/
       (exists sigma_out env_out dv,
          wf_draw_strat sigma_out /\
          eval_cfg_dag (build_param_env src_pnames vs) (oracle_of_fmap (added ++ fmap0)) d = DO_Ret dv /\
          cfg_steps_to_ret sigma0 env
            (denote_ocfg_map (ocfg_map (blks G)) None (bid_from, bid_cur))
            sigma_out env_out (inr dv))).
Proof.
  induction fuel as [| fuel' IH];
    intros blk_uas G src_pnames allowed arg_dtys vs sigma0 fmap0 is_entry bid_from bid_cur smap env seen0 d
           Hnd Hlp Hls Hla Hcomp Hvs Hpe Hwfd0 Hwfs0 Henv0 Hr;
    cbn [summarize_ocfg_dag] in Hr; [discriminate |].
  destruct (RM.find bid_cur (ocfg_map (blks G))) as [b |] eqn:Hfb; [| discriminate].
  pose proof (ocfg_map_in (blks G) bid_cur b Hfb) as Hb_in.
  destruct (is_entry && negb (list_empty_b (blk_phis b))); [discriminate |].
  destruct (reify_phi_evals true (args G) src_pnames (defined_ids_of_cfg G) smap bid_from seen0 (blk_phis b))
    as [[pevals seen_p] |] eqn:Hr_phis; [| discriminate].
  destruct (reify_code true (args G) src_pnames (defined_ids_of_cfg G)
              (apply_phi_smap smap pevals) seen_p (blk_code b))
    as [[[cevals smap_c] seen_c] |] eqn:Hr_code; [| discriminate].
  cbn zeta in Hr.
  match type of Hr with
  | match ?ot with Some _ => _ | None => _ end = Some _ =>
      destruct ot as [d_term |] eqn:Hopt; [| discriminate Hr]
  end.
  inversion Hr; subst d; clear Hr.
  destruct (reify_phi_evals_wf_smap (blk_phis b) true (args G) src_pnames (defined_ids_of_cfg G)
              allowed smap bid_from seen0 pevals seen_p Hwfs0 Hr_phis)
    as (ext_p & Hinc0p & Hfa_wf_p & Hwfs_p).
  destruct (reify_code_wf_smap (blk_code b) true (args G) src_pnames (defined_ids_of_cfg G)
              ext_p (apply_phi_smap smap pevals) seen_p cevals smap_c seen_c Hwfs_p Hr_code)
    as (ext_c & Hinc_pc & Hwfs_c).
  destruct (eval_reified_phi_map_tgt (blk_phis b) (args G) src_pnames (defined_ids_of_cfg G)
              allowed arg_dtys vs sigma0 fmap0 smap env bid_from seen0 pevals seen_p
              Hnd Hlp Hls Hla Hvs
              (fun id fm dt pargs md op idx dt_u Hphi Hparg Hu =>
                 cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                   (proj2 (in_flat_map _ (blks G) _)
                     (ex_intro _ b (conj Hb_in (block_param_uses_phi_in _ _ b id fm dt pargs md bid_from op _ Hphi Hparg Hu)))))
              Hpe Hwfd0 Hwfs0 Henv0 Hr_phis)
    as (added_p & Had_p & [Hev_ub_p | (sigma_p & dvs_p & Hwfd_p & Hpm_p & Hev_kp & Hst_p)]).
  - exists added_p; split; [intros k z H; exact (proj2 (Had_p k z H)) | left].
    cbn [eval_cfg_dag]; exact (Hev_ub_p (wrap_evals cevals d_term)).
  - pose proof (env_matches_smap_oracle_prepend allowed (defined_ids_of_cfg G) seen0 added_p fmap0
                  (build_param_env src_pnames vs) smap env Hwfs0
                  (fun k z H => proj2 (Had_p k z H)) Henv0) as Henv0'.
    pose proof (apply_phi_env_matches ext_p (defined_ids_of_cfg G) seen_p true
                  (build_param_env src_pnames vs) (oracle_of_fmap (added_p ++ fmap0))
                  smap env pevals dvs_p Henv0' Hfa_wf_p Hpm_p) as Henv_p.
    assert (Hpe_p : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r (apply_phi_env env dvs_p) = Some dv).
    { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
      exists dv; split; [exact Hv |].
      rewrite (apply_phi_env_preserves_nondefs ext_p (defined_ids_of_cfg G) seen_p true
                 (build_param_env src_pnames vs) (oracle_of_fmap (added_p ++ fmap0))
                 env pevals dvs_p r Hfa_wf_p Hpm_p Hnin);
        exact Hfe. }
    assert (Hphis_step : cfg_steps_to_ret sigma0 env (denote_phis bid_from (blk_phis b))
                           sigma_p (apply_phi_env env dvs_p) tt).
    { unfold denote_phis.
      eapply cfg_steps_to_ret_bind; [exact Hst_p |].
      eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite_list | apply CSR_Ret; reflexivity]. }
    destruct (eval_reified_code_tgt (blk_code b) (args G) src_pnames (defined_ids_of_cfg G)
                ext_p arg_dtys vs sigma_p (added_p ++ fmap0)
                (apply_phi_smap smap pevals) (apply_phi_env env dvs_p)
                seen_p cevals smap_c seen_c Hnd Hlp Hls Hla Hvs
                (fun iid ins md idx dt_u Hc Hu =>
                   cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                     (proj2 (in_flat_map _ (blks G) _)
                       (ex_intro _ b (conj Hb_in (block_param_uses_code_in _ _ b iid ins md _ Hc Hu)))))
                Hpe_p Hwfd_p Hwfs_p Henv_p Hr_code)
      as (added_c & Had_c & [Hev_ub_c | (sigma_c & env_c & Hwfd_c & Hpe_c & Henv_c & Hev_kc & Hst_c)]).
    + exists (added_c ++ added_p).
      assert (Hdisj_cp : forall k z, In (k, z) (added_c ++ added_p) -> ~ In k seen0).
      { intros k z Hkz; apply in_app_iff in Hkz as [Hc | Hp].
        - intros Hs0; exact (proj2 (Had_c k z Hc) (Hinc0p k Hs0)).
        - exact (proj2 (Had_p k z Hp)). }
      split; [exact Hdisj_cp | left].
      cbn [eval_cfg_dag]; rewrite <- app_assoc.
      rewrite (Hev_kp added_c (wrap_evals cevals d_term) (fun q z H => proj2 (Had_c q z H))).
      exact (Hev_ub_c d_term).
    + assert (Hstrip_blk : forall added_t dt_k,
        (forall k z, In (k, z) added_t -> ~ In k seen_c) ->
        eval_cfg_dag (build_param_env src_pnames vs)
          (oracle_of_fmap ((added_t ++ added_c ++ added_p) ++ fmap0))
          (wrap_phi_evals pevals (wrap_evals cevals dt_k)) =
        eval_cfg_dag (build_param_env src_pnames vs)
          (oracle_of_fmap (added_t ++ added_c ++ added_p ++ fmap0)) dt_k).
      { intros added_t dt_k Hdisj_t.
        assert (Hdisj_tc_p : forall k z, In (k, z) (added_t ++ added_c) -> ~ In k seen_p).
        { intros k z Hkz; apply in_app_iff in Hkz as [Ht | Hc].
          - intros Hsp; exact (Hdisj_t k z Ht (Hinc_pc k Hsp)).
          - exact (proj2 (Had_c k z Hc)). }
        replace ((added_t ++ added_c ++ added_p) ++ fmap0)
          with ((added_t ++ added_c) ++ added_p ++ fmap0)
          by (rewrite !app_assoc; reflexivity).
        rewrite (Hev_kp (added_t ++ added_c) (wrap_evals cevals dt_k) Hdisj_tc_p).
        replace ((added_t ++ added_c) ++ added_p ++ fmap0)
          with (added_t ++ added_c ++ added_p ++ fmap0)
          by (rewrite !app_assoc; reflexivity).
        exact (Hev_kc added_t dt_k Hdisj_t). }
      assert (Hdisj_all : forall added_t,
        (forall k z, In (k, z) added_t -> ~ In k seen_c) ->
        forall k z, In (k, z) (added_t ++ added_c ++ added_p) -> ~ In k seen0).
      { intros added_t Hdt k z Hkz; apply in_app_iff in Hkz as [Ht | Hcp].
        - intros Hs0; exact (Hdt k z Ht (Hinc_pc k (Hinc0p k Hs0))).
        - apply in_app_iff in Hcp as [Hc | Hp].
          + intros Hs0; exact (proj2 (Had_c k z Hc) (Hinc0p k Hs0)).
          + exact (proj2 (Had_p k z Hp)). }
      destruct (blk_term b) as [[tiid tm] tmd] eqn:Htm.
      destruct tm; try discriminate Hopt.
      * (* TERM_Ret *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [w | | | | | | | | | |]; try discriminate Hopt.
        destruct (reify_exp true (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) op)
          as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate Hopt].
        inversion Hopt; subst d_term; clear Hopt.
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_ret)) as ->.
        destruct (eval_reified_exp_tgt op (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c arg_dtys vs sigma_c (added_c ++ added_p ++ fmap0) smap_c env_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) w ce_ret seen_ret
                    Hnd Hlp Hls Hla Hvs
                    (fun idx dt_u Hu =>
                       cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                         (proj2 (in_flat_map _ (blks G) _)
                           (ex_intro _ b (conj Hb_in (block_param_uses_ret_in _ _ b tiid _ op tmd _ Htm Hu)))))
                    Hpe_c Hwfd_c Hwfs_c Henv_c Hr_ret)
          as (added_r & Had_r & [[msg_r Hev_r] | (sigma_r & dv_r & Hwfd_r & Hev_r & _ & Hst_r)]).
        -- exists (added_r ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_r (fun k z H => proj2 (Had_r k z H))) | left].
           cbn [eval_cfg_dag].
           rewrite (Hstrip_blk added_r (CD_RetScalar w ce_ret) (fun k z H => proj2 (Had_r k z H))).
           cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
        -- exists (added_r ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_r (fun k z H => proj2 (Had_r k z H))) | right].
           exists sigma_r, env_c, dv_r; split; [exact Hwfd_r | split].
           ++ cbn [eval_cfg_dag].
              rewrite (Hstrip_blk added_r (CD_RetScalar w ce_ret) (fun k z H => proj2 (Had_r k z H))).
              cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
           ++ eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                     eapply cfg_steps_to_ret_bind; [exact Hst_c |].
                     cbn [denote_terminator]; unfold denote_exp'.
                     eapply cfg_steps_to_ret_bind;
                       [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst_r) | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** apply CSR_Ret; reflexivity.
      * (* TERM_Ret_void *)
        inversion Hopt; subst d_term; clear Hopt.
        exists ([] ++ added_c ++ added_p).
        split; [exact (Hdisj_all [] (fun _ _ H => False_ind _ H)) | right].
        exists sigma_c, env_c, NONE; split; [exact Hwfd_c | split].
        -- cbn [eval_cfg_dag]; rewrite (Hstrip_blk [] CD_RetVoid (fun _ _ H => False_ind _ H)); reflexivity.
        -- eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
           unfold denote_block; rewrite Htm.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                 eapply cfg_steps_to_ret_bind; [exact Hst_c | apply CSR_Ret; reflexivity].
              ** apply CSR_Ret; reflexivity.
           ++ apply CSR_Ret; reflexivity.
      * (* TERM_Br *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [wc | | | | | | | | | |]; try discriminate Hopt.
        destruct wc as [| |]; try discriminate Hopt.
        destruct (reify_exp true (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
          as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate Hopt].
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_cond)) as ->.
        destruct (reify_exp_wt_lf op true (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c smap_c seen_c (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hwfs_c Hr_cond) as [Hwt_cond _].
        destruct (reify_exp_freeze_props op true (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c smap_c seen_c (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hwfs_c Hr_cond)
          as (Hlf_cond & Hinc_cbr & Hfk_cond).
        pose proof (wf_smap_entries_seen_mono ext_c (defined_ids_of_cfg G) seen_c seen_br true smap_c Hinc_cbr Hwfs_c)
          as Hwfs_br.
        destruct (eval_reified_exp_tgt op (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c arg_dtys vs sigma_c (added_c ++ added_p ++ fmap0) smap_c env_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hnd Hlp Hls Hla Hvs
                    (fun idx dt_u Hu =>
                       cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                         (proj2 (in_flat_map _ (blks G) _)
                           (ex_intro _ b (conj Hb_in (block_param_uses_br_in _ _ b tiid _ op br1 br2 tmd _ Htm Hu)))))
                    Hpe_c Hwfd_c Hwfs_c Henv_c Hr_cond)
          as (added_br & Had_br & [[msg_br Hev_br] | (sigma_br & dv_br & Hwfd_br & Hev_br & Hsc_br & Hst_br)]).
        -- exists (added_br ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_br (fun k z H => proj2 (Had_br k z H))) | left].
           cbn [eval_cfg_dag]; rewrite (Hstrip_blk added_br d_term (fun k z H => proj2 (Had_br k z H))).
           destruct (try_const_i1 ce_cond) as [[|] |].
           ++ destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
              inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
              inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
              destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
              inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
        -- pose proof (eval_closed_lf_ret_wf_param_env ce_cond (build_param_env src_pnames vs)
                         (oracle_of_fmap (added_br ++ added_c ++ added_p ++ fmap0))
                         dv_br Hlf_cond Hev_br) as Hp_cond.
           destruct Hsc_br as [-> | [cbit ->]].
           ++ exists (added_br ++ added_c ++ added_p).
              split; [exact (Hdisj_all added_br (fun k z H => proj2 (Had_br k z H))) | left].
              destruct (try_const_i1 ce_cond) as [b_tc |] eqn:Etc.
              ** destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                             (oracle_of_fmap (added_br ++ added_c ++ added_p ++ fmap0))
                             b_tc Hwt_cond Hlf_cond Hp_cond Etc) as [cbit_tc [Hev_tc _]].
                 congruence.
              ** destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
                 destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
                 inversion Hopt; subst d_term.
                 cbn [eval_cfg_dag]; rewrite (Hstrip_blk added_br _ (fun k z H => proj2 (Had_br k z H))).
                 cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ pose proof (env_matches_smap_oracle_prepend ext_c (defined_ids_of_cfg G) seen_c
                            added_br (added_c ++ added_p ++ fmap0)
                            (build_param_env src_pnames vs) smap_c env_c Hwfs_c
                            (fun k z H => proj2 (Had_br k z H)) Henv_c) as Henv_br.
              set (br_tgt := if (@Integers.unsigned 1 cbit =? 1)%Z then br1 else br2).
              assert (Hnext_br :
                exists d_next,
                  summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br_tgt smap_c seen_br = Some d_next /\
                  (forall fo,
                     eval_closed_cert_expr (build_param_env src_pnames vs) fo ce_cond =
                       raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) ->
                     eval_cfg_dag (build_param_env src_pnames vs) fo d_term =
                     eval_cfg_dag (build_param_env src_pnames vs) fo d_next)).
              { destruct (try_const_i1 ce_cond) as [[|] |] eqn:Etc.
                - destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                              (oracle_of_fmap (added_br ++ added_c ++ added_p ++ fmap0))
                              true Hwt_cond Hlf_cond Hp_cond Etc) as [cbit' [Hev_tc Ecbit']].
                  rewrite Hev_br in Hev_tc.
                  pose proof (eou_dvalue_I_same_sz_inj 1 cbit cbit' Hev_tc) as <-.
                  destruct (summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br) as [d_t |] eqn:Hr_t;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term; exists d_t; unfold br_tgt; rewrite Ecbit'; split; [exact Hr_t |].
                  intros fo Hfo; cbn [eval_cfg_dag]; rewrite Hfo; reflexivity.
                - destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                              (oracle_of_fmap (added_br ++ added_c ++ added_p ++ fmap0))
                              false Hwt_cond Hlf_cond Hp_cond Etc) as [cbit' [Hev_tc Ecbit']].
                  rewrite Hev_br in Hev_tc.
                  pose proof (eou_dvalue_I_same_sz_inj 1 cbit cbit' Hev_tc) as <-.
                  destruct (summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br) as [d_f |] eqn:Hr_f;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term; exists d_f; unfold br_tgt; rewrite Ecbit'; split; [exact Hr_f |].
                  intros fo Hfo; cbn [eval_cfg_dag]; rewrite Hfo; reflexivity.
                - destruct (summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br) as [d_t |] eqn:Hr_t;
                    [| discriminate Hopt].
                  destruct (summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br) as [d_f |] eqn:Hr_f;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term.
                  exists (if (@Integers.unsigned 1 cbit =? 1)%Z then d_t else d_f); split.
                  + unfold br_tgt; destruct (@Integers.unsigned 1 cbit =? 1)%Z; [exact Hr_t | exact Hr_f].
                  + intros fo Hfo; cbn [eval_cfg_dag]; rewrite Hfo; destruct (@Integers.unsigned 1 cbit =? 1)%Z; reflexivity. }
              destruct Hnext_br as [d_next [Hr_next Hev_term]].
              destruct (IH blk_uas G src_pnames ext_c arg_dtys vs sigma_br
                          (added_br ++ added_c ++ added_p ++ fmap0)
                          false bid_cur br_tgt smap_c env_c seen_br d_next
                          Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfd_br Hwfs_br Henv_br Hr_next)
                as (added_n & Had_n & [Hev_ub_n | (sigma_out & env_out & dv_out & Hwfd_out & Hev_out & Hst_n)]).
              ** assert (Hdisj_nbr : forall k z, In (k, z) (added_n ++ added_br) -> ~ In k seen_c).
                 { intros k z Hkz; apply in_app_iff in Hkz as [Hn | Hb0].
                   - intros Hsc0; exact (Had_n k z Hn (Hinc_cbr k Hsc0)).
                   - exact (proj2 (Had_br k z Hb0)). }
                 exists ((added_n ++ added_br) ++ added_c ++ added_p).
                 split; [exact (Hdisj_all (added_n ++ added_br) Hdisj_nbr) | left].
                 cbn [eval_cfg_dag]; rewrite (Hstrip_blk (added_n ++ added_br) d_term Hdisj_nbr).
                 replace ((added_n ++ added_br) ++ added_c ++ added_p ++ fmap0)
                   with (added_n ++ added_br ++ added_c ++ added_p ++ fmap0)
                   by (rewrite !app_assoc; reflexivity).
                 pose proof (eval_let_free_prepend_fmap ce_cond (build_param_env src_pnames vs)
                               added_n (added_br ++ added_c ++ added_p ++ fmap0) seen_br
                               Hlf_cond (Hfk_cond eq_refl) Had_n) as Hev_br'.
                 rewrite Hev_br in Hev_br'.
                 rewrite (Hev_term _ Hev_br'); exact Hev_ub_n.
              ** assert (Hdisj_nbr : forall k z, In (k, z) (added_n ++ added_br) -> ~ In k seen_c).
                 { intros k z Hkz; apply in_app_iff in Hkz as [Hn | Hb0].
                   - intros Hsc0; exact (Had_n k z Hn (Hinc_cbr k Hsc0)).
                   - exact (proj2 (Had_br k z Hb0)). }
                 exists ((added_n ++ added_br) ++ added_c ++ added_p).
                 split; [exact (Hdisj_all (added_n ++ added_br) Hdisj_nbr) | right].
                 exists sigma_out, env_out, dv_out; split; [exact Hwfd_out | split].
                 --- cbn [eval_cfg_dag]; rewrite (Hstrip_blk (added_n ++ added_br) d_term Hdisj_nbr).
                     replace ((added_n ++ added_br) ++ added_c ++ added_p ++ fmap0)
                       with (added_n ++ added_br ++ added_c ++ added_p ++ fmap0)
                       by (rewrite !app_assoc; reflexivity).
                     pose proof (eval_let_free_prepend_fmap ce_cond (build_param_env src_pnames vs)
                                   added_n (added_br ++ added_c ++ added_p ++ fmap0) seen_br
                                   Hlf_cond (Hfk_cond eq_refl) Had_n) as Hev_br'.
                     rewrite Hev_br in Hev_br'.
                     rewrite (Hev_term _ Hev_br'); exact Hev_out.
                 --- eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                     unfold denote_block; rewrite Htm.
                     eapply cfg_steps_to_ret_bind.
                     +++ eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                             eapply cfg_steps_to_ret_bind; [exact Hst_c |].
                             cbn [denote_terminator]; unfold denote_exp'.
                             eapply cfg_steps_to_ret_bind;
                               [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst_br) |].
                             cbn iota beta; rewrite bit_int_1_equ_one_eq_unsigned; unfold br_tgt.
                             destruct (@Integers.unsigned 1 cbit =? 1)%Z; apply CSR_Ret; reflexivity.
                         *** apply CSR_Ret; reflexivity.
                     +++ eapply CSR_Tau; [reflexivity | exact Hst_n].
      * (* TERM_Br_1 *)
        destruct (IH blk_uas G src_pnames ext_c arg_dtys vs sigma_c (added_c ++ added_p ++ fmap0)
                    false bid_cur br smap_c env_c seen_c d_term
                    Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfd_c Hwfs_c Henv_c Hopt)
          as (added_n & Had_n & [Hev_ub_n | (sigma_out & env_out & dv_out & Hwfd_out & Hev_out & Hst_n)]).
        -- exists (added_n ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_n Had_n) | left].
           cbn [eval_cfg_dag]; rewrite (Hstrip_blk added_n d_term Had_n); exact Hev_ub_n.
        -- exists (added_n ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_n Had_n) | right].
           exists sigma_out, env_out, dv_out; split; [exact Hwfd_out | split].
           ++ cbn [eval_cfg_dag]; rewrite (Hstrip_blk added_n d_term Had_n); exact Hev_out.
           ++ eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                     eapply cfg_steps_to_ret_bind; [exact Hst_c | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** eapply CSR_Tau; [reflexivity | exact Hst_n].
      * (* TERM_Unreachable *)
        inversion Hopt; subst d_term; clear Hopt.
        exists ([] ++ added_c ++ added_p).
        split; [exact (Hdisj_all [] (fun _ _ H => False_ind _ H)) | left].
        cbn [eval_cfg_dag]; rewrite (Hstrip_blk [] CD_Unreachable (fun _ _ H => False_ind _ H)); reflexivity.
Qed.

Lemma summarize_tgt_dag_sound {Pa : Params} :
  forall G src_pnames arg_dtys (vs : list (@dvalue Pa)) (sigma_tgt : @draw_strat Pa) d,
    NoDup (args G) ->
    NoDup src_pnames ->
    List.length src_pnames = List.length (args G) ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    wf_draw_strat sigma_tgt ->
    summarize_cfg_dag true G src_pnames = Some d ->
    exists fmap_tgt : list (freeze_key * Z),
      eval_cfg_dag (build_param_env src_pnames vs) (oracle_of_fmap fmap_tgt) d = DO_UB \/
      (exists sigma_tgt' env_out dv,
         eval_cfg_dag (build_param_env src_pnames vs) (oracle_of_fmap fmap_tgt) d = DO_Ret dv /\
         cfg_steps_to_ret sigma_tgt (init_cfg_locals (args G) vs) (denote_cfg G None)
           sigma_tgt' env_out dv).
Proof.
  intros G src_pnames arg_dtys vs sigma_tgt d Hnd_p Hnd_s Hlen_sp Hlen_da Hcomp Hvs Hwfd Hr.
  assert (Hlen_vs : List.length vs = List.length arg_dtys) by exact (Forall2_length Hvs).
  assert (Hlp : List.length (args G) = List.length vs) by lia.
  assert (Hls : List.length src_pnames = List.length vs) by lia.
  assert (Hpe0 : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
    exists dv, nth_error vs idx = Some dv /\ RM.find r (init_cfg_locals (args G) vs) = Some dv).
  { intros idx r Hnth _; exact (init_cfg_locals_nth (args G) vs idx r Hnd_p Hlp Hnth). }
  destruct (summarize_ocfg_tgt_sound (default_cfg_dag_fuel G) (fun _ => []) G src_pnames [] arg_dtys vs
              sigma_tgt [] true (init G) (init G) (RM.empty _) (init_cfg_locals (args G) vs) [] d
              Hnd_s Hlp Hls Hlen_da Hcomp Hvs Hpe0 Hwfd
              (wf_smap_entries_empty [] (defined_ids_of_cfg G) [] true)
              (env_matches_smap_empty (defined_ids_of_cfg G) (build_param_env src_pnames vs)
                 (oracle_of_fmap []) (init_cfg_locals (args G) vs))
              Hr)
    as (fmap_tgt & _ & [Hev_ub | (sigma_out & env_out & dv & _ & Hev_ret & Hst_ret)]).
  - exists (fmap_tgt ++ []); left; exact Hev_ub.
  - exists (fmap_tgt ++ []); right; exists sigma_out, env_out, dv; split; [exact Hev_ret |].
    unfold denote_cfg, denote_cfg_map.
    eapply cfg_steps_to_ret_bind; [exact Hst_ret | apply CSR_Ret; reflexivity].
Qed.


