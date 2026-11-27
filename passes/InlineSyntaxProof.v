(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Interprocedural Function Inlining Pass — Syntax Proofs ([CertPasses.InlineSyntaxProof])

    Freshness partition lemmas, finder inversion, block lookup, hygiene validator
    soundness, and global-environment construction preservation. *)

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

From CertPasses Require Import InlineSpec.

(** * 5. Freshness Partition, Finder Inversion, Block Lookup & Validator Soundness *)

Lemma is_empty_list_spec {A : Type} (xs : list A) :
  is_empty_list xs = true <-> xs = [].
Proof.
  destruct xs; cbn [is_empty_list]; split; intros H;
    try reflexivity; discriminate.
Qed.

Lemma inl_firstn_length {A : Type} :
  forall (n : nat) (xs : list A),
    (n <= List.length xs)%nat ->
    List.length (firstn n xs) = n.
Proof.
  induction n as [| n' IH]; intros [| x xs'] Hle; cbn in *; try reflexivity; try lia.
  f_equal; apply IH; lia.
Qed.

Lemma inl_skipn_length {A : Type} :
  forall (n : nat) (xs : list A),
    List.length (skipn n xs) = (List.length xs - n)%nat.
Proof.
  induction n as [| n' IH]; intros [| x xs']; cbn; try reflexivity.
  apply IH.
Qed.

Lemma inl_firstn_skipn {A : Type} :
  forall (n : nat) (xs : list A),
    firstn n xs ++ skipn n xs = xs.
Proof.
  induction n as [| n' IH]; intros [| x xs']; cbn; try reflexivity.
  f_equal; apply IH.
Qed.

Lemma inl_skipn_add {A : Type} :
  forall (a b : nat) (xs : list A),
    skipn (a + b) xs = skipn b (skipn a xs).
Proof.
  induction a as [| a' IH]; intros b [| x xs']; cbn; try reflexivity.
  - destruct b; reflexivity.
  - apply IH.
Qed.

Lemma inl_firstn_all {A : Type} :
  forall (n : nat) (xs : list A),
    List.length xs = n ->
    firstn n xs = xs.
Proof.
  induction n as [| n' IH]; intros [| x xs'] Hlen; cbn in *; try discriminate; [reflexivity |].
  injection Hlen as Hlen; f_equal; apply IH, Hlen.
Qed.

Lemma inl_nodup_app_l {A : Type} :
  forall (xs ys : list A),
    NoDup (xs ++ ys) -> NoDup xs.
Proof.
  induction xs as [| x xs' IH]; intros ys Hnd; cbn in *.
  - constructor.
  - inversion Hnd as [| ? ? Hnin Hnd']; subst.
    constructor.
    + intros Hx; apply Hnin, in_or_app; left; exact Hx.
    + eapply IH, Hnd'.
Qed.

Lemma inl_nodup_app_r {A : Type} :
  forall (xs ys : list A),
    NoDup (xs ++ ys) -> NoDup ys.
Proof.
  induction xs as [| x xs' IH]; intros ys Hnd; cbn in *.
  - exact Hnd.
  - inversion Hnd; subst; eapply IH; eassumption.
Qed.

Lemma inl_nodup_app_disj {A : Type} :
  forall (xs ys : list A),
    NoDup (xs ++ ys) ->
    forall x, In x xs -> ~ In x ys.
Proof.
  induction xs as [| a xs' IH]; intros ys Hnd x Hx Hy; [contradiction |].
  cbn in Hnd; inversion Hnd as [| ? ? Hnin Hnd']; subst.
  destruct Hx as [<- | Hx].
  - apply Hnin, in_or_app; right; exact Hy.
  - eapply IH; [exact Hnd' | exact Hx | exact Hy].
Qed.

Lemma all_fresh_partition (used_ids : list raw_id) (n_loc n_blk n_ret : nat) :
  let all_fresh := fresh_names "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids in
  let post_bid  := hd (Name "inl_post"%string) all_fresh in
  let va_tmp_id := hd (Name "inl_va"%string) (skipn 1 all_fresh) in
  let l_fresh   := firstn n_loc (skipn 2 all_fresh) in
  let b_fresh   := firstn n_blk (skipn (2 + n_loc)%nat all_fresh) in
  let ret_tmps  := firstn n_ret (skipn (2 + n_loc + n_blk)%nat all_fresh) in
  all_fresh = post_bid :: va_tmp_id :: l_fresh ++ b_fresh ++ ret_tmps /\
  List.length l_fresh = n_loc /\
  List.length b_fresh = n_blk /\
  List.length ret_tmps = n_ret /\
  NoDup all_fresh /\
  (forall x, In x all_fresh -> ~ In x used_ids).
Proof.
  intros all_fresh post_bid va_tmp_id l_fresh b_fresh ret_tmps.
  pose proof (fresh_names_length "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids) as Hlen.
  pose proof (fresh_names_nodup "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids) as Hnd.
  pose proof (fresh_names_disjoint "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids) as Hdisj.
  fold all_fresh in Hlen, Hnd, Hdisj.
  destruct all_fresh as [| f0 [| f1 rest2]] eqn:Eaf; cbn [List.length] in Hlen; try lia.
  assert (Hpb : post_bid = f0) by reflexivity.
  assert (Hva : va_tmp_id = f1) by reflexivity.
  assert (Hsk2 : skipn 2 (f0 :: f1 :: rest2) = rest2) by reflexivity.
  assert (Hlen2 : List.length rest2 = (n_loc + n_blk + n_ret)%nat) by lia.
  assert (Hsk_loc : skipn (2 + n_loc)%nat (f0 :: f1 :: rest2) = skipn n_loc rest2).
  { rewrite (inl_skipn_add 2 n_loc (f0 :: f1 :: rest2)), Hsk2; reflexivity. }
  assert (Hsk_blk : skipn (2 + n_loc + n_blk)%nat (f0 :: f1 :: rest2) =
                    skipn n_blk (skipn n_loc rest2)).
  { rewrite (inl_skipn_add (2 + n_loc)%nat n_blk (f0 :: f1 :: rest2)), Hsk_loc; reflexivity. }
  unfold l_fresh, b_fresh, ret_tmps; rewrite Hpb, Hva, Hsk2, Hsk_loc, Hsk_blk.
  set (rest3 := skipn n_loc rest2).
  assert (Hlen3 : List.length rest3 = (n_blk + n_ret)%nat).
  { unfold rest3; rewrite inl_skipn_length; lia. }
  set (rest4 := skipn n_blk rest3).
  assert (Hlen4 : List.length rest4 = n_ret).
  { unfold rest4; rewrite inl_skipn_length; lia. }
  assert (Hfn4 : firstn n_ret rest4 = rest4) by (apply inl_firstn_all, Hlen4).
  split.
  - f_equal; f_equal.
    rewrite Hfn4; unfold rest4.
    rewrite inl_firstn_skipn; unfold rest3.
    symmetry; apply inl_firstn_skipn.
  - split; [apply inl_firstn_length; lia |].
    split; [apply inl_firstn_length; lia |].
    split; [rewrite Hfn4; exact Hlen4 |].
    split; [exact Hnd | exact Hdisj].
Qed.

(** *** Membership in [defn_all_ids], [callee_local_ids], and [callee_block_ids] *)

Lemma defn_all_ids_dc_name {T : Set} (df : definition T (CFG.cfg T)) :
  In (dc_name (df_prototype df)) (defn_all_ids df).
Proof.
  left; reflexivity.
Qed.

Lemma defn_all_ids_arg {T : Set} (df : definition T (CFG.cfg T)) (x : raw_id) :
  In x (df_args df) -> In x (defn_all_ids df).
Proof.
  intros Hx; right; apply in_or_app; left; exact Hx.
Qed.

Lemma defn_all_ids_cfg {T : Set} (df : definition T (CFG.cfg T)) (x : raw_id) :
  In x (cfg_all_ids (df_instrs df)) -> In x (defn_all_ids df).
Proof.
  intros Hx; right; apply in_or_app; right; apply in_or_app; left; exact Hx.
Qed.

Lemma defn_all_ids_init {T : Set} (df : definition T (CFG.cfg T)) :
  In (init (df_instrs df)) (defn_all_ids df).
Proof.
  apply defn_all_ids_cfg; left; reflexivity.
Qed.

Lemma defn_all_ids_blk_id {T : Set} (df : definition T (CFG.cfg T)) (bk : block T) :
  In bk (blks (df_instrs df)) -> In (blk_id bk) (defn_all_ids df).
Proof.
  intros Hbk; apply defn_all_ids_cfg; right; apply in_or_app; right; apply in_or_app; left.
  apply in_map, Hbk.
Qed.

Lemma defn_all_ids_block_defs {T : Set} (df : definition T (CFG.cfg T)) (bk : block T) (x : raw_id) :
  In bk (blks (df_instrs df)) -> In x (full_block_defs bk) -> In x (defn_all_ids df).
Proof.
  intros Hbk Hx; apply defn_all_ids_cfg.
  right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
  apply in_flat_map; exists bk; split; assumption.
Qed.

Lemma defn_all_ids_block_uses {T : Set} (df : definition T (CFG.cfg T)) (bk : block T) (x : raw_id) :
  In bk (blks (df_instrs df)) -> In x (full_block_uses bk) -> In x (defn_all_ids df).
Proof.
  intros Hbk Hx; apply defn_all_ids_cfg.
  right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
  apply in_flat_map; exists bk; split; assumption.
Qed.

Lemma defn_all_ids_label_ids {T : Set} (df : definition T (CFG.cfg T)) (bk : block T) (b : raw_id) :
  In bk (blks (df_instrs df)) -> In b (block_all_label_ids bk) -> In b (defn_all_ids df).
Proof.
  intros Hbk Hb; right; apply in_or_app; right; apply in_or_app; right.
  apply in_flat_map; exists bk; split; assumption.
Qed.

Lemma callee_local_ids_arg (callee_df : definition dtyp (CFG.cfg dtyp)) (x : raw_id) :
  In x (df_args callee_df) -> In x (callee_local_ids callee_df).
Proof.
  intros Hx; unfold callee_local_ids; apply dedup_raw_ids_in.
  apply in_or_app; left; exact Hx.
Qed.

Lemma callee_local_ids_defs (callee_df : definition dtyp (CFG.cfg dtyp)) (bk : block dtyp) (x : raw_id) :
  In bk (blks (df_instrs callee_df)) ->
  In x (full_block_defs bk) ->
  In x (callee_local_ids callee_df).
Proof.
  intros Hbk Hx; unfold callee_local_ids; apply dedup_raw_ids_in.
  apply in_or_app; right; apply in_or_app; left.
  apply in_flat_map; exists bk; split; assumption.
Qed.

Lemma callee_local_ids_uses (callee_df : definition dtyp (CFG.cfg dtyp)) (bk : block dtyp) (x : raw_id) :
  In bk (blks (df_instrs callee_df)) ->
  In x (full_block_uses bk) ->
  In x (callee_local_ids callee_df).
Proof.
  intros Hbk Hx; unfold callee_local_ids; apply dedup_raw_ids_in.
  apply in_or_app; right; apply in_or_app; right.
  apply in_flat_map; exists bk; split; assumption.
Qed.

Lemma callee_local_ids_sub_defn (callee_df : definition dtyp (CFG.cfg dtyp)) (x : raw_id) :
  In x (callee_local_ids callee_df) -> In x (defn_all_ids callee_df).
Proof.
  unfold callee_local_ids; rewrite dedup_raw_ids_in, !in_app_iff, !in_flat_map.
  intros [Hx | [[bk [Hbk Hx]] | [bk [Hbk Hx]]]].
  - apply defn_all_ids_arg, Hx.
  - eapply defn_all_ids_block_defs; eassumption.
  - eapply defn_all_ids_block_uses; eassumption.
Qed.

Lemma callee_block_ids_init (callee_df : definition dtyp (CFG.cfg dtyp)) :
  In (init (df_instrs callee_df)) (callee_block_ids callee_df).
Proof.
  unfold callee_block_ids; apply dedup_raw_ids_in; left; reflexivity.
Qed.

Lemma callee_block_ids_label (callee_df : definition dtyp (CFG.cfg dtyp)) (bk : block dtyp) (b : raw_id) :
  In bk (blks (df_instrs callee_df)) ->
  In b (block_all_label_ids bk) ->
  In b (callee_block_ids callee_df).
Proof.
  intros Hbk Hb; unfold callee_block_ids; apply dedup_raw_ids_in; right.
  apply in_flat_map; exists bk; split; assumption.
Qed.

Lemma callee_block_ids_blk_id (callee_df : definition dtyp (CFG.cfg dtyp)) (bk : block dtyp) :
  In bk (blks (df_instrs callee_df)) ->
  In (blk_id bk) (callee_block_ids callee_df).
Proof.
  intros Hbk; eapply callee_block_ids_label; [exact Hbk | left; reflexivity].
Qed.

Lemma callee_block_ids_sub_defn (callee_df : definition dtyp (CFG.cfg dtyp)) (b : raw_id) :
  In b (callee_block_ids callee_df) -> In b (defn_all_ids callee_df).
Proof.
  unfold callee_block_ids; rewrite dedup_raw_ids_in; cbn [In]; rewrite in_flat_map.
  intros [<- | [bk [Hbk Hb]]].
  - apply defn_all_ids_init.
  - eapply defn_all_ids_label_ids; eassumption.
Qed.

(** *** Finder Inversion Lemmas *)

Lemma find_defn_by_gid_in (gid : function_id) (defs : list (definition dtyp (CFG.cfg dtyp)))
  (df : definition dtyp (CFG.cfg dtyp)) :
  find_defn_by_gid gid defs = Some df ->
  In df defs /\ dc_name (df_prototype df) = gid.
Proof.
  induction defs as [| d rest IH]; cbn [find_defn_by_gid]; [discriminate |].
  destruct (raw_id_eqb (dc_name (df_prototype d)) gid) eqn:E.
  - intros H; injection H as <-.
    apply raw_id_eqb_spec in E; split; [left; reflexivity | exact E].
  - intros H; apply IH in H as [Hin Hnm]; split; [right; exact Hin | exact Hnm].
Qed.

Lemma find_call_in_code_inv
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  (caller_gid : function_id)
  (acc_pre cd pre_cd post_cd : code dtyp)
  (im : instr_id * instr dtyp * list (metadata dtyp))
  (callee_df : definition dtyp (CFG.cfg dtyp))
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (call_anns : list (annotation dtyp)) :
  find_call_in_code defs caller_gid acc_pre cd =
    Some (pre_cd, im, post_cd, callee_df, ret_dt, call_args, call_anns) ->
  List.rev acc_pre ++ cd = pre_cd ++ im :: post_cd /\
  match_inlinable_call_instr defs caller_gid im =
    Some (callee_df, ret_dt, call_args, call_anns).
Proof.
  revert acc_pre; induction cd as [| hd rest IH]; intros acc_pre; cbn [find_call_in_code]; [discriminate |].
  destruct (match_inlinable_call_instr defs caller_gid hd)
    as [[[[cdf rdt] cargs] canns] |] eqn:Em.
  - intros H; injection H as <- <- <- <- <- <- <-.
    split; [reflexivity | exact Em].
  - intros H; apply IH in H as [Heq Hmatch].
    cbn [List.rev] in Heq; rewrite <- app_assoc in Heq; cbn [app] in Heq.
    split; [exact Heq | exact Hmatch].
Qed.

Lemma find_call_in_blks_inv
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  (caller_gid : function_id)
  (all_caller_bks acc_pre bks pre_blks post_blks : ocfg dtyp)
  (b_call : block dtyp)
  (pre_cd post_cd : code dtyp)
  (im : instr_id * instr dtyp * list (metadata dtyp))
  (callee_df : definition dtyp (CFG.cfg dtyp))
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (call_anns : list (annotation dtyp)) :
  find_call_in_blks defs caller_gid all_caller_bks acc_pre bks =
    Some (pre_blks, b_call, post_blks, pre_cd, im, post_cd, callee_df, ret_dt, call_args, call_anns) ->
  List.rev acc_pre ++ bks = pre_blks ++ b_call :: post_blks /\
  blk_code b_call = pre_cd ++ im :: post_cd /\
  match_inlinable_call_instr defs caller_gid im =
    Some (callee_df, ret_dt, call_args, call_anns).
Proof.
  revert acc_pre; induction bks as [| bk rest IH]; intros acc_pre; cbn [find_call_in_blks]; [discriminate |].
  destruct (block_in_cfg_loop all_caller_bks bk).
  - intros H; apply IH in H as (Hbks & Hcd & Hmatch).
    cbn [List.rev] in Hbks; rewrite <- app_assoc in Hbks; cbn [app] in Hbks.
    split; [exact Hbks | split; [exact Hcd | exact Hmatch]].
  - destruct (find_call_in_code defs caller_gid [] (blk_code bk))
      as [[[[[[[pcd im0] pscd] cdf] rdt] cargs] canns] |] eqn:Ec.
    + intros H; injection H as <- <- <- <- <- <- <- <- <- <-.
      apply find_call_in_code_inv in Ec as [Hcd Hmatch]; cbn [List.rev app] in Hcd.
      split; [reflexivity | split; [exact Hcd | exact Hmatch]].
    + intros H; apply IH in H as (Hbks & Hcd & Hmatch).
      cbn [List.rev] in Hbks; rewrite <- app_assoc in Hbks; cbn [app] in Hbks.
      split; [exact Hbks | split; [exact Hcd | exact Hmatch]].
Qed.

Lemma inline_first_in_defs_inv
  (all_defs rem_defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
  inline_first_in_defs all_defs rem_defs = Some defs' ->
  exists pre_defs caller_df post_defs
         pre_blks b_call post_blks
         pre_cd call_iid ins call_md post_cd
         callee_df ret_dt call_args call_anns,
    rem_defs = pre_defs ++ caller_df :: post_defs /\
    defs' =
      pre_defs
      ++ inline_site_in_caller caller_df callee_df pre_blks post_blks
           b_call pre_cd post_cd call_iid ret_dt call_args
      :: post_defs /\
    is_inlinable_caller caller_df = true /\
    blks (df_instrs caller_df) = pre_blks ++ b_call :: post_blks /\
    blk_code b_call = pre_cd ++ (call_iid, ins, call_md) :: post_cd /\
    match_inlinable_call_instr all_defs (dc_name (df_prototype caller_df))
      (call_iid, ins, call_md) =
      Some (callee_df, ret_dt, call_args, call_anns).
Proof.
  revert defs'; induction rem_defs as [| caller_df rest_defs IH]; intros defs';
    cbn [inline_first_in_defs]; [discriminate |].
  destruct (is_inlinable_caller caller_df) eqn:Ecaller.
  - destruct (find_call_in_blks all_defs (dc_name (df_prototype caller_df))
                (blks (df_instrs caller_df)) [] (blks (df_instrs caller_df)))
      as [[[[[[[[[[pre_blks b_call] post_blks] pre_cd] [[call_iid ins] call_md]] post_cd]
               callee_df] ret_dt] call_args] call_anns] |] eqn:Efind.
    + intros H; injection H as <-.
      apply find_call_in_blks_inv in Efind as (Hbks & Hcd & Hmatch).
      cbn [List.rev app] in Hbks.
      exists [], caller_df, rest_defs,
             pre_blks, b_call, post_blks,
             pre_cd, call_iid, ins, call_md, post_cd,
             callee_df, ret_dt, call_args, call_anns.
      repeat split; assumption.
    + destruct (inline_first_in_defs all_defs rest_defs) as [rest' |] eqn:Erec;
        cbn [option_map]; [| discriminate].
      intros H; injection H as <-.
      destruct (IH rest' Logic.eq_refl)
        as (pre_defs & cdf & post_defs & pre_blks & b_call & post_blks &
            pre_cd & call_iid & ins & call_md & post_cd &
            callee_df & ret_dt & call_args & call_anns &
            -> & -> & H1 & H2 & H3 & H4).
      exists (caller_df :: pre_defs), cdf, post_defs,
             pre_blks, b_call, post_blks,
             pre_cd, call_iid, ins, call_md, post_cd,
             callee_df, ret_dt, call_args, call_anns.
      cbn [app]; repeat split; assumption.
  - destruct (inline_first_in_defs all_defs rest_defs) as [rest' |] eqn:Erec;
      cbn [option_map]; [| discriminate].
    intros H; injection H as <-.
    destruct (IH rest' Logic.eq_refl)
      as (pre_defs & cdf & post_defs & pre_blks & b_call & post_blks &
          pre_cd & call_iid & ins & call_md & post_cd &
          callee_df & ret_dt & call_args & call_anns &
          -> & -> & H1 & H2 & H3 & H4).
    exists (caller_df :: pre_defs), cdf, post_defs,
           pre_blks, b_call, post_blks,
           pre_cd, call_iid, ins, call_md, post_cd,
           callee_df, ret_dt, call_args, call_anns.
    cbn [app]; repeat split; assumption.
Qed.

(** *** [find_block] and [assoc] Lemmas for Split Caller & Renamed Callee *)

Lemma inl_find_block_not_in {T : Set} :
  forall (bks : ocfg T) (b : block_id),
    ~ In b (List.map blk_id bks) ->
    find_block bks b = None.
Proof.
  induction bks as [| bk rest IH]; intros b Hnin; [reflexivity |].
  cbn [List.map In] in Hnin.
  destruct (RawIDOrd.eq_dec (blk_id bk) b) as [Heq | Hne].
  - exfalso; apply Hnin; left; exact Heq.
  - rewrite find_block_ineq by exact Hne.
    apply IH; intros Hb; apply Hnin; right; exact Hb.
Qed.

Lemma inl_find_block_nodup_in {T : Set} :
  forall (bks : ocfg T) (bk : block T),
    NoDup (List.map blk_id bks) ->
    In bk bks ->
    find_block bks (blk_id bk) = Some bk.
Proof.
  induction bks as [| hd rest IH]; intros bk Hnd Hin; [contradiction |].
  cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd']; subst.
  destruct Hin as [-> | Hin].
  - apply find_block_eq; reflexivity.
  - destruct (RawIDOrd.eq_dec (blk_id hd) (blk_id bk)) as [Heq | Hne].
    + exfalso; apply Hnin; rewrite Heq; apply in_map, Hin.
    + rewrite find_block_ineq by exact Hne.
      apply IH; assumption.
Qed.

Lemma map_blk_id_remap {T : Set} (old_bid new_bid : block_id) (bks : ocfg T) :
  List.map blk_id (List.map (remap_block_phis old_bid new_bid) bks) =
  List.map blk_id bks.
Proof.
  rewrite map_map; reflexivity.
Qed.

Lemma map_blk_id_transform_callee
  (ren_l ren_b : raw_id -> raw_id) (post_bid : block_id)
  (bks : ocfg dtyp) (rtmps : list raw_id)
  (Hlen : List.length rtmps = List.length bks) :
  List.map blk_id
    (List.map (transform_callee_block ren_l ren_b post_bid) (combine bks rtmps)) =
  List.map (fun bk => ren_b (blk_id bk)) bks.
Proof.
  revert rtmps Hlen; induction bks as [| bk rest IH]; intros [| r rs] Hlen;
    try discriminate Hlen; [reflexivity |].
  cbn [List.length] in Hlen; injection Hlen as Hlen.
  cbn [combine List.map].
  unfold transform_callee_block at 1.
  destruct (blk_term bk) as [[tiid tm] tmd].
  destruct tm as [[dt op] | | [dt op] b1 b2 | b | [dt op] db brs | ? ? ? | ? | ? ? ? ? ? ? | ];
    cbn [blk_id]; f_equal; apply IH, Hlen.
Qed.

Lemma inl_nodup_app_intro {A : Type} :
  forall (xs ys : list A),
    NoDup xs ->
    NoDup ys ->
    (forall x, In x xs -> ~ In x ys) ->
    NoDup (xs ++ ys).
Proof.
  induction xs as [| x xs' IH]; intros ys Hx Hy Hdisj; cbn [app].
  - exact Hy.
  - inversion Hx as [| ? ? Hnin Hx']; subst.
    constructor.
    + intros Hin; apply in_app_or in Hin as [Hin | Hin].
      * contradiction.
      * eapply Hdisj; [left; reflexivity | exact Hin].
    + apply IH; [exact Hx' | exact Hy | intros z Hz; apply Hdisj; right; exact Hz].
Qed.

Lemma nodup_map_inj_on {A B : Type} (f : A -> B) (xs : list A)
  (Hnd : NoDup xs)
  (Hinj : forall x1 x2, In x1 xs -> In x2 xs -> f x1 = f x2 -> x1 = x2) :
  NoDup (List.map f xs).
Proof.
  induction Hnd as [| x xs' Hnin Hnd' IH]; cbn [List.map].
  - constructor.
  - constructor.
    + intros Hin; apply in_map_iff in Hin as [x' [Heq Hx']].
      assert (Hx_eq : x' = x).
      { apply Hinj; [right; exact Hx' | left; reflexivity | exact Heq]. }
      subst x'; contradiction.
    + apply IH; intros x1 x2 H1 H2 Heq.
      apply Hinj; [right; exact H1 | right; exact H2 | exact Heq].
Qed.

Lemma inline_new_blks_nodup
  (caller_df callee_df : definition dtyp (CFG.cfg dtyp))
  (pre_blks post_blks : ocfg dtyp)
  (b_call : block dtyp)
  (pre_code post_code : code dtyp)
  (call_iid : instr_id)
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (Hcaller_nd : NoDup (List.map blk_id (blks (df_instrs caller_df))))
  (Hcaller_split : blks (df_instrs caller_df) = pre_blks ++ b_call :: post_blks)
  (Hcallee_nd : NoDup (List.map blk_id (blks (df_instrs callee_df)))) :
  NoDup (List.map blk_id
           (blks (df_instrs
                    (inline_site_in_caller caller_df callee_df pre_blks post_blks
                       b_call pre_code post_code call_iid ret_dt call_args)))).
Proof.
  unfold inline_site_in_caller; cbn [df_instrs blks].
  set (caller_cfg := df_instrs caller_df).
  set (callee_cfg := df_instrs callee_df).
  set (used_ids := defn_all_ids caller_df ++ defn_all_ids callee_df).
  set (l_origs := callee_local_ids callee_df).
  set (b_origs := callee_block_ids callee_df).
  set (n_loc := List.length l_origs).
  set (n_blk := List.length b_origs).
  set (n_ret := List.length (blks callee_cfg)).
  pose proof (all_fresh_partition used_ids n_loc n_blk n_ret)
    as (Eaf & Hlen_l & Hlen_b & Hlen_r & Hnd_af & Hdisj_used).
  set (all_fresh := fresh_names "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids) in *.
  set (post_bid := hd (Name "inl_post"%string) all_fresh) in *.
  set (va_tmp_id := hd (Name "inl_va"%string) (skipn 1 all_fresh)) in *.
  set (l_fresh := firstn n_loc (skipn 2 all_fresh)) in *.
  set (b_fresh := firstn n_blk (skipn (2 + n_loc)%nat all_fresh)) in *.
  set (ret_tmps := firstn n_ret (skipn (2 + n_loc + n_blk)%nat all_fresh)) in *.
  set (ren_l := lookup_ren (combine l_origs l_fresh)).
  set (ren_b := lookup_ren (combine b_origs b_fresh)).
  rewrite !map_app; cbn [List.map blk_id]; rewrite !map_app; cbn [List.map blk_id].
  rewrite !map_blk_id_remap.
  rewrite map_blk_id_transform_callee by exact Hlen_r.
  assert (Hcaller_in_used : forall x, In x (List.map blk_id (blks caller_cfg)) -> In x used_ids).
  { intros x Hx; apply in_map_iff in Hx as [bk [<- Hbk]].
    unfold used_ids; apply in_or_app; left; apply defn_all_ids_blk_id, Hbk. }
  rewrite Hcaller_split, map_app in Hcaller_nd; cbn [List.map] in Hcaller_nd.
  pose proof (inl_nodup_app_l _ _ Hcaller_nd) as Hnd_pre.
  pose proof (inl_nodup_app_r _ _ Hcaller_nd) as Hnd_call_post.
  pose proof (inl_nodup_app_disj _ _ Hcaller_nd) as Hdisj_pre_rest.
  inversion Hnd_call_post as [| ? ? Hnin_call_post Hnd_post]; subst.
  rewrite Eaf in Hnd_af.
  inversion Hnd_af as [| ? ? Hnin_pb Hnd_af1]; subst.
  inversion Hnd_af1 as [| ? ? _ Hnd_lbr]; subst.
  pose proof (inl_nodup_app_r _ _ Hnd_lbr) as Hnd_br.
  pose proof (inl_nodup_app_l _ _ Hnd_br) as Hnd_bf.
  assert (Hbf_in_af : forall x, In x b_fresh -> In x all_fresh).
  { intros x Hx; rewrite Eaf; right; right; apply in_or_app; right; apply in_or_app; left; exact Hx. }
  assert (Hpb_in_af : In post_bid all_fresh) by (rewrite Eaf; left; reflexivity).
  assert (Hpb_not_bf : ~ In post_bid b_fresh).
  { intros Hin; apply Hnin_pb; right; apply in_or_app; right; apply in_or_app; left; exact Hin. }
  assert (Hren_in_bf : forall x, In x (List.map (fun bk => ren_b (blk_id bk)) (blks callee_cfg)) -> In x b_fresh).
  { intros x Hx; apply in_map_iff in Hx as [bk [<- Hbk]].
    unfold ren_b; apply lookup_ren_in_dom; [symmetry; exact Hlen_b |].
    apply callee_block_ids_blk_id, Hbk. }
  assert (Hnd_callee_ren : NoDup (List.map (fun bk => ren_b (blk_id bk)) (blks callee_cfg))).
  { rewrite <- (map_map blk_id ren_b).
    apply nodup_map_inj_on; [exact Hcallee_nd |].
    intros b1 b2 Hb1 Hb2 Heq.
    apply in_map_iff in Hb1 as [bk1 [<- Hbk1]].
    apply in_map_iff in Hb2 as [bk2 [<- Hbk2]].
    unfold ren_b in Heq; eapply lookup_ren_inj_on;
      [symmetry; exact Hlen_b | exact Hnd_bf
      | apply callee_block_ids_blk_id, Hbk1
      | apply callee_block_ids_blk_id, Hbk2
      | exact Heq]. }
  assert (Hpre_used : forall x, In x (List.map blk_id pre_blks) -> In x used_ids).
  { intros x Hx; apply Hcaller_in_used; unfold caller_cfg; rewrite Hcaller_split, map_app; apply in_or_app; left; exact Hx. }
  assert (Hcall_used : In (blk_id b_call) used_ids).
  { apply Hcaller_in_used; unfold caller_cfg; rewrite Hcaller_split, map_app; apply in_or_app; right; left; reflexivity. }
  assert (Hpost_used : forall x, In x (List.map blk_id post_blks) -> In x used_ids).
  { intros x Hx; apply Hcaller_in_used; unfold caller_cfg; rewrite Hcaller_split, map_app; apply in_or_app; right; right; exact Hx. }
  apply inl_nodup_app_intro; [exact Hnd_pre | |].
  - constructor.
    + intros Hin; apply in_app_or in Hin as [Hin | [Heq | Hin]].
      * eapply Hdisj_used; [apply Hbf_in_af, Hren_in_bf, Hin | exact Hcall_used].
      * rewrite <- Heq in Hcall_used; eapply Hdisj_used; [exact Hpb_in_af | exact Hcall_used].
      * contradiction.
    + apply inl_nodup_app_intro; [exact Hnd_callee_ren | |].
      * constructor; [| exact Hnd_post].
        intros Hin; eapply Hdisj_used; [exact Hpb_in_af | apply Hpost_used, Hin].
      * intros x Hx [Heq | Hy].
        -- rewrite <- Heq in Hx; apply Hpb_not_bf, Hren_in_bf, Hx.
        -- eapply Hdisj_used; [apply Hbf_in_af, Hren_in_bf, Hx | apply Hpost_used, Hy].
  - intros x Hx Hin.
    cbn [In] in Hin; destruct Hin as [Heq | Hin].
    + rewrite <- Heq in Hx; eapply Hdisj_pre_rest; [exact Hx | left; reflexivity].
    + apply in_app_or in Hin as [Hin | [Heq | Hin]].
      * eapply Hdisj_used; [apply Hbf_in_af, Hren_in_bf, Hin | apply Hpre_used, Hx].
      * rewrite <- Heq in Hx; eapply Hdisj_used; [exact Hpb_in_af | apply Hpre_used, Hx].
      * eapply Hdisj_pre_rest; [exact Hx | right; exact Hin].
Qed.

Lemma find_block_new_call_bid
  (caller_df callee_df : definition dtyp (CFG.cfg dtyp))
  (pre_blks post_blks : ocfg dtyp)
  (b_call : block dtyp)
  (pre_code post_code : code dtyp)
  (call_iid : instr_id)
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (Hcaller_nd : NoDup (List.map blk_id (blks (df_instrs caller_df))))
  (Hcaller_split : blks (df_instrs caller_df) = pre_blks ++ b_call :: post_blks)
  (Hcallee_nd : NoDup (List.map blk_id (blks (df_instrs callee_df)))) :
  let used_ids := defn_all_ids caller_df ++ defn_all_ids callee_df in
  let l_origs := callee_local_ids callee_df in
  let n_loc := List.length l_origs in
  let n_blk := List.length (callee_block_ids callee_df) in
  let n_ret := List.length (blks (df_instrs callee_df)) in
  let all_fresh := fresh_names "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids in
  let post_bid  := hd (Name "inl_post"%string) all_fresh in
  let va_tmp_id := hd (Name "inl_va"%string) (skipn 1 all_fresh) in
  let l_fresh   := firstn n_loc (skipn 2 all_fresh) in
  let b_fresh   := firstn n_blk (skipn (2 + n_loc)%nat all_fresh) in
  let ren_l     := lookup_ren (combine l_origs l_fresh) in
  let ren_b     := lookup_ren (combine (callee_block_ids callee_df) b_fresh) in
  find_block
    (blks (df_instrs
             (inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args)))
    (blk_id b_call) =
  Some
    {| blk_id       := blk_id b_call;
       blk_phis     := remap_phis_pred (blk_id b_call) post_bid (blk_phis b_call);
       blk_code     := pre_code
                       ++ build_param_copies ren_l (df_args callee_df) call_args
                       ++ [(IId va_tmp_id, INSTR_Alloca (DTYPE_Struct true []) [], [])];
       blk_term     := (IVoid 0%Z, TERM_Br_1 (ren_b (init (df_instrs callee_df))), []);
       blk_comments := blk_comments b_call |}.
Proof.
  intros used_ids l_origs n_loc n_blk n_ret all_fresh post_bid va_tmp_id l_fresh b_fresh ren_l ren_b.
  pose proof (inline_new_blks_nodup caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args
                Hcaller_nd Hcaller_split Hcallee_nd) as Hnd.
  set (b_pre :=
    {| blk_id       := blk_id b_call;
       blk_phis     := remap_phis_pred (blk_id b_call) post_bid (blk_phis b_call);
       blk_code     := pre_code
                       ++ build_param_copies ren_l (df_args callee_df) call_args
                       ++ [(IId va_tmp_id, INSTR_Alloca (DTYPE_Struct true []) [], [])];
       blk_term     := (IVoid 0%Z, TERM_Br_1 (ren_b (init (df_instrs callee_df))), []);
       blk_comments := blk_comments b_call |}).
  assert (Hin : In b_pre
    (blks (df_instrs
             (inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args)))).
  { unfold inline_site_in_caller; cbn [df_instrs blks].
    apply in_or_app; right; left; reflexivity. }
  exact (inl_find_block_nodup_in _ b_pre Hnd Hin).
Qed.

Lemma find_block_new_post_bid
  (caller_df callee_df : definition dtyp (CFG.cfg dtyp))
  (pre_blks post_blks : ocfg dtyp)
  (b_call : block dtyp)
  (pre_code post_code : code dtyp)
  (call_iid : instr_id)
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (Hcaller_nd : NoDup (List.map blk_id (blks (df_instrs caller_df))))
  (Hcaller_split : blks (df_instrs caller_df) = pre_blks ++ b_call :: post_blks)
  (Hcallee_nd : NoDup (List.map blk_id (blks (df_instrs callee_df)))) :
  let used_ids := defn_all_ids caller_df ++ defn_all_ids callee_df in
  let l_origs := callee_local_ids callee_df in
  let b_origs := callee_block_ids callee_df in
  let n_loc := List.length l_origs in
  let n_blk := List.length b_origs in
  let n_ret := List.length (blks (df_instrs callee_df)) in
  let all_fresh := fresh_names "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids in
  let post_bid  := hd (Name "inl_post"%string) all_fresh in
  let b_fresh   := firstn n_blk (skipn (2 + n_loc)%nat all_fresh) in
  let ret_tmps  := firstn n_ret (skipn (2 + n_loc + n_blk)%nat all_fresh) in
  let ren_b     := lookup_ren (combine b_origs b_fresh) in
  let ret_in    := collect_ret_phi_incoming ren_b (combine (blks (df_instrs callee_df)) ret_tmps) in
  let post_phis :=
    match call_iid with
    | IId res_id => [(res_id, Phi [] ret_dt ret_in, [])]
    | IVoid _ => []
    end
  in
  find_block
    (blks (df_instrs
             (inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args)))
    post_bid =
  Some
    {| blk_id       := post_bid;
       blk_phis     := post_phis;
       blk_code     := post_code;
       blk_term     := blk_term b_call;
       blk_comments := None |}.
Proof.
  intros used_ids l_origs b_origs n_loc n_blk n_ret all_fresh post_bid b_fresh ret_tmps ren_b ret_in post_phis.
  pose proof (inline_new_blks_nodup caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args
                Hcaller_nd Hcaller_split Hcallee_nd) as Hnd.
  set (b_post :=
    {| blk_id       := post_bid;
       blk_phis     := post_phis;
       blk_code     := post_code;
       blk_term     := blk_term b_call;
       blk_comments := None |}).
  assert (Hin : In b_post
    (blks (df_instrs
             (inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args)))).
  { unfold inline_site_in_caller; cbn [df_instrs blks].
    apply in_or_app; right; right; apply in_or_app; right; left; reflexivity. }
  exact (inl_find_block_nodup_in _ b_post Hnd Hin).
Qed.

Lemma find_block_new_callee
  (caller_df callee_df : definition dtyp (CFG.cfg dtyp))
  (pre_blks post_blks : ocfg dtyp)
  (b_call : block dtyp)
  (pre_code post_code : code dtyp)
  (call_iid : instr_id)
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (bk : block dtyp) (rtmp : raw_id)
  (Hcaller_nd : NoDup (List.map blk_id (blks (df_instrs caller_df))))
  (Hcaller_split : blks (df_instrs caller_df) = pre_blks ++ b_call :: post_blks)
  (Hcallee_nd : NoDup (List.map blk_id (blks (df_instrs callee_df)))) :
  let used_ids := defn_all_ids caller_df ++ defn_all_ids callee_df in
  let l_origs := callee_local_ids callee_df in
  let b_origs := callee_block_ids callee_df in
  let n_loc := List.length l_origs in
  let n_blk := List.length b_origs in
  let n_ret := List.length (blks (df_instrs callee_df)) in
  let all_fresh := fresh_names "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids in
  let post_bid  := hd (Name "inl_post"%string) all_fresh in
  let l_fresh   := firstn n_loc (skipn 2 all_fresh) in
  let b_fresh   := firstn n_blk (skipn (2 + n_loc)%nat all_fresh) in
  let ret_tmps  := firstn n_ret (skipn (2 + n_loc + n_blk)%nat all_fresh) in
  let ren_l     := lookup_ren (combine l_origs l_fresh) in
  let ren_b     := lookup_ren (combine b_origs b_fresh) in
  In (bk, rtmp) (combine (blks (df_instrs callee_df)) ret_tmps) ->
  find_block
    (blks (df_instrs
             (inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args)))
    (ren_b (blk_id bk)) =
  Some (transform_callee_block ren_l ren_b post_bid (bk, rtmp)).
Proof.
  intros used_ids l_origs b_origs n_loc n_blk n_ret all_fresh post_bid l_fresh b_fresh ret_tmps ren_l ren_b Hin.
  pose proof (inline_new_blks_nodup caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args
                Hcaller_nd Hcaller_split Hcallee_nd) as Hnd.
  set (tbk := transform_callee_block ren_l ren_b post_bid (bk, rtmp)).
  assert (Hid : blk_id tbk = ren_b (blk_id bk)).
  { unfold tbk, transform_callee_block; destruct (blk_term bk) as [[? tm] ?];
      destruct tm as [[? ?] | | [? ?] ? ? | ? | [? ?] ? ? | ? ? ? | ? | ? ? ? ? ? ? | ]; reflexivity. }
  rewrite <- Hid.
  eapply (inl_find_block_nodup_in _ _ Hnd).
  unfold inline_site_in_caller; cbn [df_instrs blks].
  apply in_or_app; right; right; apply in_or_app; left.
  apply in_map, Hin.
Qed.

Lemma find_block_new_caller_other
  (caller_df callee_df : definition dtyp (CFG.cfg dtyp))
  (pre_blks post_blks : ocfg dtyp)
  (b_call : block dtyp)
  (pre_code post_code : code dtyp)
  (call_iid : instr_id)
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (bid : block_id)
  (Hcaller_nd : NoDup (List.map blk_id (blks (df_instrs caller_df))))
  (Hcaller_split : blks (df_instrs caller_df) = pre_blks ++ b_call :: post_blks)
  (Hcallee_nd : NoDup (List.map blk_id (blks (df_instrs callee_df)))) :
  let used_ids := defn_all_ids caller_df ++ defn_all_ids callee_df in
  let l_origs := callee_local_ids callee_df in
  let b_origs := callee_block_ids callee_df in
  let n_loc := List.length l_origs in
  let n_blk := List.length b_origs in
  let n_ret := List.length (blks (df_instrs callee_df)) in
  let all_fresh := fresh_names "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids in
  let post_bid  := hd (Name "inl_post"%string) all_fresh in
  let b_fresh   := firstn n_blk (skipn (2 + n_loc)%nat all_fresh) in
  bid <> blk_id b_call ->
  bid <> post_bid ->
  ~ In bid b_fresh ->
  find_block
    (blks (df_instrs
             (inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args)))
    bid =
  option_map (remap_block_phis (blk_id b_call) post_bid)
    (find_block (blks (df_instrs caller_df)) bid).
Proof.
  intros used_ids l_origs b_origs n_loc n_blk n_ret all_fresh post_bid b_fresh Hne_call Hne_post Hnin_bf.
  pose proof (inline_new_blks_nodup caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args
                Hcaller_nd Hcaller_split Hcallee_nd) as Hnd.
  destruct (find_block (blks (df_instrs caller_df)) bid) as [bk |] eqn:Efb; cbn [option_map].
  - pose proof (find_block_has_id _ _ Efb) as Hid; symmetry in Hid.
    pose proof (find_block_In' _ _ Efb) as Hbk_in.
    rewrite Hcaller_split in Hbk_in; apply in_app_or in Hbk_in as [Hbk_pre | [<- | Hbk_post]].
    + set (rbk := remap_block_phis (blk_id b_call) post_bid bk).
      replace bid with (blk_id rbk) by (cbn; exact Hid).
      eapply (inl_find_block_nodup_in _ _ Hnd).
      unfold inline_site_in_caller; cbn [df_instrs blks].
      apply in_or_app; left; apply in_map, Hbk_pre.
    + symmetry in Hid; contradiction.
    + set (rbk := remap_block_phis (blk_id b_call) post_bid bk).
      replace bid with (blk_id rbk) by (cbn; exact Hid).
      eapply (inl_find_block_nodup_in _ _ Hnd).
      unfold inline_site_in_caller; cbn [df_instrs blks].
      apply in_or_app; right; right; apply in_or_app; right; right; apply in_map, Hbk_post.
  - apply inl_find_block_not_in.
    pose proof (all_fresh_partition used_ids n_loc n_blk n_ret)
      as (_ & _ & Hlen_b & Hlen_r & _ & _).
    unfold inline_site_in_caller; cbn [df_instrs blks].
    rewrite !map_app; cbn [List.map blk_id]; rewrite !map_app; cbn [List.map blk_id].
    rewrite !map_blk_id_remap.
    rewrite map_blk_id_transform_callee by exact Hlen_r.
    intros Hin.
    assert (Hnot_caller : ~ In bid (List.map blk_id (blks (df_instrs caller_df)))).
    { intros Hc; apply in_map_iff in Hc as [bk [<- Hbk]].
      destruct (In_find_block _ _ Hbk) as [bk' Efb']; congruence. }
    apply in_app_or in Hin as [Hin | [Heq | Hin]].
    + apply Hnot_caller; rewrite Hcaller_split, map_app; apply in_or_app; left; exact Hin.
    + symmetry in Heq; contradiction.
    + apply in_app_or in Hin as [Hin | [Heq | Hin]].
      * apply in_map_iff in Hin as [bk [<- Hbk]].
        apply Hnin_bf; apply lookup_ren_in_dom; [symmetry; exact Hlen_b | apply callee_block_ids_blk_id, Hbk].
      * symmetry in Heq; contradiction.
      * apply Hnot_caller; rewrite Hcaller_split, map_app; apply in_or_app; right; right; exact Hin.
Qed.

Lemma remap_pred_id_inj_not_new (old_bid new_bid b1 b2 : block_id)
  (Hold_new : old_bid <> new_bid)
  (Hb1 : b1 <> new_bid)
  (Hb2 : b2 <> new_bid) :
  remap_pred_id old_bid new_bid b1 = remap_pred_id old_bid new_bid b2 ->
  b1 = b2.
Proof.
  unfold remap_pred_id.
  destruct (raw_id_eqb b1 old_bid) eqn:E1, (raw_id_eqb b2 old_bid) eqn:E2.
  - apply raw_id_eqb_spec in E1; apply raw_id_eqb_spec in E2; congruence.
  - intros Heq; symmetry in Heq; contradiction.
  - intros Heq; contradiction.
  - intros Heq; exact Heq.
Qed.

Lemma assoc_remap_pred_id {B : Type} (old_bid new_bid b_from : block_id)
  (pargs : list (block_id * B))
  (Hold_new : old_bid <> new_bid)
  (Hfrom : b_from <> new_bid)
  (Hpargs : ~ In new_bid (List.map fst pargs)) :
  assoc (remap_pred_id old_bid new_bid b_from)
    (List.map (fun '(b, ex) => (remap_pred_id old_bid new_bid b, ex)) pargs) =
  assoc b_from pargs.
Proof.
  induction pargs as [| [b ex] rest IH]; [reflexivity |].
  cbn [List.map In fst] in *.
  assert (Hb_not_new : b <> new_bid) by (intros ->; apply Hpargs; left; reflexivity).
  assert (Hrest : ~ In new_bid (List.map fst rest)) by (intros H; apply Hpargs; right; exact H).
  destruct (RawIDOrd.eq_dec b_from b) as [<- | Hne].
  - rewrite !assoc_hd; reflexivity.
  - rewrite assoc_tl.
    + rewrite assoc_tl by exact Hne; apply IH, Hrest.
    + intros Heq; apply Hne;
        exact (remap_pred_id_inj_not_new old_bid new_bid b_from b Hold_new Hfrom Hb_not_new Heq).
Qed.

Lemma assoc_ren_phi {B C : Type} (ren_b : block_id -> block_id) (f : B -> C)
  (b_dom : list block_id) (b_from : block_id) (pargs : list (block_id * B))
  (Hinj : forall b1 b2, In b1 b_dom -> In b2 b_dom -> ren_b b1 = ren_b b2 -> b1 = b2)
  (Hfrom : In b_from b_dom)
  (Hpargs : incl (List.map fst pargs) b_dom) :
  assoc (ren_b b_from) (List.map (fun '(b, ex) => (ren_b b, f ex)) pargs) =
  option_map f (assoc b_from pargs).
Proof.
  induction pargs as [| [b ex] rest IH]; [reflexivity |].
  cbn [List.map].
  assert (Hb_dom : In b b_dom) by (apply Hpargs; left; reflexivity).
  assert (Hrest : incl (List.map fst rest) b_dom).
  { intros z Hz; apply Hpargs; right; exact Hz. }
  destruct (RawIDOrd.eq_dec b_from b) as [<- | Hne].
  - rewrite !assoc_hd; reflexivity.
  - rewrite assoc_tl.
    + rewrite assoc_tl by exact Hne; apply IH, Hrest.
    + intros Heq; apply Hne; apply Hinj; assumption.
Qed.

Lemma in_combine_same_length {A B : Type} :
  forall (xs : list A) (ys : list B),
    List.length ys = List.length xs ->
    forall x, In x xs -> exists y, In (x, y) (combine xs ys).
Proof.
  induction xs as [| a xs' IH]; intros [| b ys'] Hlen x Hx;
    try discriminate Hlen; [contradiction |].
  cbn [List.length] in Hlen; injection Hlen as Hlen.
  destruct Hx as [<- | Hx].
  - exists b; left; reflexivity.
  - destruct (IH ys' Hlen x Hx) as [y Hy]; exists y; right; exact Hy.
Qed.

Lemma assoc_collect_ret_phi_incoming
  (ren_b : raw_id -> raw_id) (b_dom : list raw_id)
  (bks : ocfg dtyp) (rtmps : list raw_id)
  (bk : block dtyp) (rtmp : raw_id) (rpair : texp dtyp)
  (Hnd : NoDup (List.map blk_id bks))
  (Hinj : forall b1 b2, In b1 b_dom -> In b2 b_dom -> ren_b b1 = ren_b b2 -> b1 = b2)
  (Hbks_dom : incl (List.map blk_id bks) b_dom)
  (Hin : In (bk, rtmp) (combine bks rtmps))
  (Hret : snd (fst (blk_term bk)) = TERM_Ret rpair) :
  assoc (ren_b (blk_id bk)) (collect_ret_phi_incoming ren_b (combine bks rtmps)) =
  Some (EXP_Ident (ID_Local rtmp)).
Proof.
  revert rtmps Hnd Hbks_dom Hin.
  induction bks as [| hd rest IH]; intros [| r rs] Hnd Hbks_dom Hin;
    cbn [combine collect_ret_phi_incoming flat_map] in *; try contradiction.
  cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin_hd Hnd_rest]; subst.
  assert (Hhd_dom : In (blk_id hd) b_dom) by (apply Hbks_dom; left; reflexivity).
  assert (Hrest_dom : incl (List.map blk_id rest) b_dom).
  { intros z Hz; apply Hbks_dom; right; exact Hz. }
  destruct Hin as [Heq | Hin].
  - injection Heq as -> ->.
    rewrite Hret; cbn [app]; apply assoc_hd.
  - assert (Hbk_in_rest : In bk rest) by (eapply in_combine_l, Hin).
    assert (Hbk_dom : In (blk_id bk) b_dom) by (apply Hrest_dom, in_map, Hbk_in_rest).
    assert (Hne_id : blk_id bk <> blk_id hd).
    { intros Heq; apply Hnin_hd; rewrite <- Heq; apply in_map, Hbk_in_rest. }
    destruct (snd (fst (blk_term hd)));
      cbn [app];
      try (eapply IH; eassumption).
    rewrite assoc_tl.
    + eapply IH; eassumption.
    + intros Heq; apply Hne_id; apply Hinj; assumption.
Qed.

(** *** Soundness of the Callee Definite-Initialization Validator *)

Lemma check_code_defs_inv {T : Set} (cur : list raw_id)
  (iid : instr_id) (ins : instr T) (md : list (metadata T))
  (rest : list (instr_id * instr T * list (metadata T))) (d_out : list raw_id) :
  check_code_defs cur ((iid, ins, md) :: rest) = Some d_out ->
  incl (full_instr_uses ins ++ flat_map full_metadata_uses md) cur /\
  check_code_defs (cur ++ instr_id_defs iid) rest = Some d_out.
Proof.
  cbn [check_code_defs].
  destruct (incl_raw_ids (full_instr_uses ins ++ flat_map full_metadata_uses md) cur) eqn:E;
    [| discriminate].
  apply incl_raw_ids_spec in E; intros H; split; assumption.
Qed.

Lemma check_code_defs_incl {T : Set} :
  forall (cd : list (instr_id * instr T * list (metadata T))) (cur d_out : list raw_id),
    check_code_defs cur cd = Some d_out ->
    incl cur d_out.
Proof.
  induction cd as [| [[iid ins] md] rest IH]; intros cur d_out Hchk.
  - cbn [check_code_defs] in Hchk; injection Hchk as <-; apply incl_refl.
  - apply check_code_defs_inv in Hchk as [_ Hrest].
    specialize (IH _ _ Hrest).
    intros x Hx; apply IH, in_or_app; left; exact Hx.
Qed.

Lemma verify_def_map_init {T : Set} (fargs : list raw_id) (c : CFG.cfg T)
  (in_map : list (block_id * list raw_id)) :
  verify_def_map fargs c in_map = true ->
  incl (lookup_def_set in_map (init c)) fargs.
Proof.
  unfold verify_def_map; rewrite andb_true_iff, incl_raw_ids_spec; intros [H _]; exact H.
Qed.

Lemma verify_def_map_block {T : Set} (fargs : list raw_id) (c : CFG.cfg T)
  (in_map : list (block_id * list raw_id)) (bk : block T) :
  verify_def_map fargs c in_map = true ->
  In bk (blks c) ->
  verify_block_defs (blks c) in_map bk = true.
Proof.
  unfold verify_def_map; rewrite andb_true_iff, forallb_forall.
  intros [_ Hall] Hbk; apply Hall, Hbk.
Qed.

Lemma check_succ_edge_inv {T : Set} (bks : ocfg T)
  (in_map : list (block_id * list raw_id))
  (src_bid : block_id) (d_out : list raw_id) (succ_bid : block_id) :
  check_succ_edge bks in_map src_bid d_out succ_bid = true ->
  exists b_succ,
    find_block bks succ_bid = Some b_succ /\
    incl (lookup_def_set in_map succ_bid) d_out /\
    Forall
      (fun '(_, Phi _ _ pargs, md) =>
         exists op,
           assoc src_bid pargs = Some op /\
           incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_out)
      (blk_phis b_succ).
Proof.
  unfold check_succ_edge.
  destruct (find_block bks succ_bid) as [b_succ |] eqn:Efb; [| discriminate].
  rewrite andb_true_iff, incl_raw_ids_spec, forallb_forall.
  intros [Hincl Hphis].
  exists b_succ; split; [reflexivity | split; [exact Hincl |]].
  apply Forall_forall; intros [[x [fm dt pargs]] md] Hin.
  specialize (Hphis _ Hin); cbv beta iota in Hphis.
  destruct (assoc src_bid pargs) as [op |] eqn:Eop; [| discriminate].
  apply incl_raw_ids_spec in Hphis.
  exists op; split; [reflexivity | exact Hphis].
Qed.

Lemma verify_block_defs_inv {T : Set} (bks : ocfg T)
  (in_map : list (block_id * list raw_id)) (bk : block T) :
  verify_block_defs bks in_map bk = true ->
  exists d_out,
    check_code_defs
      (lookup_def_set in_map (blk_id bk) ++ List.map (fun '(x, _, _) => x) (blk_phis bk))
      (blk_code bk) = Some d_out /\
    incl (full_term_uses (snd (fst (blk_term bk))) ++ flat_map full_metadata_uses (snd (blk_term bk))) d_out /\
    (forall succ_bid,
       In succ_bid (term_succ_bids (snd (fst (blk_term bk)))) ->
       check_succ_edge bks in_map (blk_id bk) d_out succ_bid = true).
Proof.
  unfold verify_block_defs.
  destruct (check_code_defs
              (lookup_def_set in_map (blk_id bk) ++ List.map (fun '(x, _, _) => x) (blk_phis bk))
              (blk_code bk)) as [d_out |] eqn:Echk; [| discriminate].
  destruct (blk_term bk) as [[tiid tm] tmd]; cbn [fst snd].
  rewrite andb_true_iff, incl_raw_ids_spec, forallb_forall.
  intros [Htm Hsuccs].
  exists d_out; split; [reflexivity | split; assumption].
Qed.

(** * 6. Preservation of [mcfg_block_addresses] and [build_global_environment] *)

Lemma exp_block_addresses_ren_exp {T : Set} (ren_l : raw_id -> raw_id) :
  forall (e : exp T),
    exp_block_addresses (ren_exp ren_l e) = exp_block_addresses e.
Proof.
  assert (Hlist :
    forall (elts : list (T * exp T)),
      (forall p, In p elts -> exp_block_addresses (ren_exp ren_l (snd p)) = exp_block_addresses (snd p)) ->
      flat_map (fun x => exp_block_addresses (snd x))
        ((fix go (l : list (T * exp T)) : list (T * exp T) :=
            match l with
            | [] => []
            | (t, ex) :: rest => (t, ren_exp ren_l ex) :: go rest
            end) elts) =
      flat_map (fun x => exp_block_addresses (snd x)) elts).
  { induction elts as [| [t ex] rest IHl]; intros Hall; [reflexivity |].
    cbn -[ren_exp exp_block_addresses].
    pose proof (Hall (t, ex) (or_introl Logic.eq_refl)) as Hhd.
    cbn [snd] in Hhd; rewrite Hhd.
    f_equal; apply IHl; intros p Hp; apply Hall; right; exact Hp. }
  apply (@AstLib.exp_ind T (fun e => exp_block_addresses (ren_exp ren_l e) = exp_block_addresses e));
    intros;
    repeat match goal with
           | p : T * exp T |- _ => destruct p as [? ?]
           end;
    cbn [ren_exp exp_block_addresses snd] in *;
    try reflexivity;
    try (apply Hlist; assumption);
    try congruence.
  - (* OP_GetElementPtr *)
    rewrite H, (Hlist idxs H0); reflexivity.
Qed.

Lemma block_block_addresses_remap {T : Set} (old_bid new_bid : block_id) (bk : block T) :
  block_block_addresses (remap_block_phis old_bid new_bid bk) =
  block_block_addresses bk.
Proof.
  unfold block_block_addresses, remap_block_phis, remap_phis_pred; cbn [blk_phis blk_code blk_term].
  f_equal.
  induction (blk_phis bk) as [| [[x [fm dt pargs]] md] rest IH]; [reflexivity |].
  cbn [List.map flat_map].
  f_equal; [| exact IH].
  induction pargs as [| [b ex] prest IHp]; [reflexivity |].
  cbn [List.map flat_map snd]; f_equal; exact IHp.
Qed.

Lemma block_block_addresses_nil_in {T : Set} (bks : ocfg T) (bk : block T) :
  flat_map block_block_addresses bks = [] ->
  In bk bks ->
  block_block_addresses bk = [].
Proof.
  intros Hnil Hin.
  destruct (block_block_addresses bk) as [| fb rest] eqn:E; [reflexivity |].
  exfalso.
  assert (Hfb : In fb (flat_map block_block_addresses bks)).
  { apply in_flat_map; exists bk; split; [exact Hin | rewrite E; left; reflexivity]. }
  rewrite Hnil in Hfb; exact Hfb.
Qed.

Lemma block_block_addresses_transform_callee
  (ren_l ren_b : raw_id -> raw_id) (post_bid : block_id)
  (bk : block dtyp) (rtmp : raw_id) :
  block_block_addresses bk = [] ->
  block_block_addresses (transform_callee_block ren_l ren_b post_bid (bk, rtmp)) = [].
Proof.
  unfold block_block_addresses, transform_callee_block.
  destruct (blk_term bk) as [[tiid tm] tmd].
  intros Hnil.
  apply app_eq_nil in Hnil as [Hphis Hrest].
  apply app_eq_nil in Hrest as [Hcode Hterm].
  assert (Hphis' :
    flat_map (fun '(_, Phi _ _ args, _) => flat_map (fun x => exp_block_addresses (snd x)) args)
      (List.map (ren_phi_entry ren_l ren_b) (blk_phis bk)) = []).
  { clear -Hphis.
    induction (blk_phis bk) as [| [[x [fm dt pargs]] md] rest IH]; [reflexivity |].
    cbn [flat_map List.map ren_phi_entry] in *.
    apply app_eq_nil in Hphis as [Hp Hrest].
    rewrite (IH Hrest), app_nil_r.
    induction pargs as [| [b ex] prest IHp]; [reflexivity |].
    cbn [List.map flat_map snd] in *.
    apply app_eq_nil in Hp as [Hex Hprest].
    rewrite exp_block_addresses_ren_exp, Hex, (IHp Hprest); reflexivity. }
  assert (Hcode' :
    flat_map (fun '(_, i, _) => instr_block_addresses i)
      (List.map (ren_code_entry ren_l) (blk_code bk)) = []).
  { clear -Hcode.
    induction (blk_code bk) as [| [[iid ins] md] rest IH]; [reflexivity |].
    cbn [flat_map List.map ren_code_entry] in *.
    apply app_eq_nil in Hcode as [Hi Hrest].
    rewrite (IH Hrest), app_nil_r.
    destruct ins as [? | op | ? ? ? ? | ? ? | ? [du ptr] ? | [dt val] [du ptr] ? | ? ? | ? | ? | ? ? | ? ? ?];
      cbn [ren_leaf_instr instr_block_addresses texps_block_addresses flat_map snd] in *;
      try exact Hi.
    - rewrite exp_block_addresses_ren_exp; exact Hi.
    - rewrite exp_block_addresses_ren_exp; exact Hi.
    - rewrite !exp_block_addresses_ren_exp; exact Hi. }
  destruct tm as [[dt op] | | [dt op] b1 b2 | b | [dt op] db brs | ? ? ? | ? | ? ? ? ? ? ? | ];
    cbn [blk_phis blk_code blk_term term_block_addresses texps_block_addresses flat_map snd] in *;
    rewrite ?Hphis', ?flat_map_app, ?Hcode'; cbn [app flat_map instr_block_addresses mk_copy_exp exp_block_addresses];
    try rewrite exp_block_addresses_ren_exp;
    try exact Hterm;
    try (rewrite app_nil_r in Hterm; rewrite Hterm; reflexivity).
Qed.

Lemma build_param_copies_block_addresses
  (ren_l : raw_id -> raw_id) :
  forall (params : list local_id) (call_args : list (texp dtyp * list param_attr)),
    texps_block_addresses (List.map fst call_args) = [] ->
    flat_map (fun '(_, i, _) => instr_block_addresses i)
      (build_param_copies ren_l params call_args) = [].
Proof.
  induction params as [| p ps IH]; intros [| [[arg_dt arg_e] pattrs] rest] Hargs;
    cbn [build_param_copies List.map texps_block_addresses flat_map fst snd] in *;
    try reflexivity.
  apply app_eq_nil in Hargs as [He Hrest].
  cbn [instr_block_addresses mk_copy_exp exp_block_addresses app].
  rewrite He, app_nil_r; apply IH, Hrest.
Qed.

Lemma collect_ret_phi_block_addresses
  (ren_b : raw_id -> raw_id) (bk_rtmps : list (block dtyp * raw_id)) :
  flat_map (fun x => exp_block_addresses (snd x))
    (collect_ret_phi_incoming ren_b bk_rtmps) = [].
Proof.
  induction bk_rtmps as [| [bk rtmp] rest IH]; [reflexivity |].
  cbn [collect_ret_phi_incoming flat_map].
  destruct (snd (fst (blk_term bk))); cbn [flat_map app snd exp_block_addresses]; exact IH.
Qed.

Lemma remap_phis_pred_block_addresses {T : Set} (old_b new_b : block_id)
  (phis : list (local_id * phi T * list (metadata T))) :
  flat_map (fun '(_, Phi _ _ args, _) => flat_map (fun x => exp_block_addresses (snd x)) args)
    (remap_phis_pred old_b new_b phis) =
  flat_map (fun '(_, Phi _ _ args, _) => flat_map (fun x => exp_block_addresses (snd x)) args)
    phis.
Proof.
  induction phis as [| [[x [fm dt pargs]] md] rest IH]; [reflexivity |].
  cbn [remap_phis_pred List.map flat_map]; f_equal; [| exact IH].
  induction pargs as [| [b ex] pr IHpr]; [reflexivity |].
  cbn [List.map flat_map snd]; f_equal; exact IHpr.
Qed.

Lemma inline_site_block_addresses
  (caller_df callee_df : definition dtyp (CFG.cfg dtyp))
  (pre_blks post_blks : ocfg dtyp)
  (b_call : block dtyp)
  (pre_code post_code : code dtyp)
  (call_iid : instr_id) (ins : instr dtyp) (call_md : list (metadata dtyp))
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (Hcaller_ba : cfg_no_block_addresses (df_instrs caller_df) = true)
  (Hcallee_ba : cfg_no_block_addresses (df_instrs callee_df) = true)
  (Hcaller_split : blks (df_instrs caller_df) = pre_blks ++ b_call :: post_blks)
  (Hcode_split : blk_code b_call = pre_code ++ (call_iid, ins, call_md) :: post_code)
  (Hins_ba : texps_block_addresses (List.map fst call_args) = []) :
  flat_map block_block_addresses
    (blks (df_instrs
             (inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_code post_code call_iid ret_dt call_args))) = [].
Proof.
  apply cfg_no_block_addresses_nil in Hcaller_ba.
  apply cfg_no_block_addresses_nil in Hcallee_ba.
  rewrite Hcaller_split, flat_map_app in Hcaller_ba; cbn [flat_map] in Hcaller_ba.
  apply app_eq_nil in Hcaller_ba as [Hpre_ba Hcall_post_ba].
  apply app_eq_nil in Hcall_post_ba as [Hbcall_ba Hpost_ba].
  unfold block_block_addresses in Hbcall_ba.
  rewrite Hcode_split, flat_map_app in Hbcall_ba; cbn [flat_map] in Hbcall_ba.
  apply app_eq_nil in Hbcall_ba as [Hbcall_phis Hrest1].
  apply app_eq_nil in Hrest1 as [Hpre_cd_rest Hbcall_term].
  apply app_eq_nil in Hpre_cd_rest as [Hpre_cd Hcall_post_cd].
  apply app_eq_nil in Hcall_post_cd as [_ Hpost_cd].
  unfold inline_site_in_caller; cbn [df_instrs blks].
  rewrite !flat_map_app; cbn [flat_map]; rewrite !flat_map_app; cbn [flat_map].
  assert (Hremap_nil :
    forall old_b new_b (bs : ocfg dtyp),
      flat_map block_block_addresses bs = [] ->
      flat_map block_block_addresses (List.map (remap_block_phis old_b new_b) bs) = []).
  { intros old_b new_b bs Hbs.
    induction bs as [| hd tl IHbs]; [reflexivity |].
    cbn [List.map flat_map] in *; apply app_eq_nil in Hbs as [Hhd Htl].
    rewrite block_block_addresses_remap, Hhd, (IHbs Htl); reflexivity. }
  rewrite (Hremap_nil _ _ pre_blks Hpre_ba), (Hremap_nil _ _ post_blks Hpost_ba).
  cbn [app]; rewrite app_nil_r.
  unfold block_block_addresses at 1.
  cbn [blk_phis blk_code blk_term term_block_addresses].
  rewrite remap_phis_pred_block_addresses, Hbcall_phis, !flat_map_app, Hpre_cd,
          build_param_copies_block_addresses by exact Hins_ba.
  cbn [app flat_map instr_block_addresses].
  assert (Hinl_ba :
    forall ren_l ren_b post_bid (bks : ocfg dtyp) (rtmps : list raw_id),
      flat_map block_block_addresses bks = [] ->
      flat_map block_block_addresses
        (List.map (transform_callee_block ren_l ren_b post_bid) (combine bks rtmps)) = []).
  { intros ren_l ren_b post_bid bks rtmps Hbks.
    revert rtmps; induction bks as [| bk tl IHbks]; intros [| r rs]; try reflexivity.
    cbn [combine List.map flat_map] in *.
    apply app_eq_nil in Hbks as [Hbk Htl].
    rewrite block_block_addresses_transform_callee by exact Hbk.
    cbn [app]; apply IHbks, Htl. }
  rewrite Hinl_ba by exact Hcallee_ba; cbn [app].
  unfold block_block_addresses; cbn [blk_phis blk_code blk_term].
  rewrite Hpost_cd, Hbcall_term; cbn [app].
  destruct call_iid as [res_id | vn]; cbn [flat_map app]; [| reflexivity].
  rewrite collect_ret_phi_block_addresses; reflexivity.
Qed.

Lemma inline_one_site_prototypes (M : CFG.mcfg dtyp) :
  List.map df_prototype (m_definitions (inline_one_site_mcfg M)) =
  List.map df_prototype (m_definitions M).
Proof.
  unfold inline_one_site_mcfg.
  destruct (is_hygienic_module M) eqn:Ehyg; [| reflexivity].
  destruct (inline_first_in_defs (m_definitions M) (m_definitions M)) as [defs' |] eqn:Efind;
    [| reflexivity].
  cbn [m_definitions].
  apply inline_first_in_defs_inv in Efind
    as (pre_defs & caller_df & post_defs & pre_blks & b_call & post_blks &
        pre_cd & call_iid & ins & call_md & post_cd &
        callee_df & ret_dt & call_args & call_anns &
        Edefs & -> & _).
  rewrite Edefs, !map_app; cbn [List.map inline_site_in_caller df_prototype]; reflexivity.
Qed.

Lemma match_inlinable_call_instr_inv
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  (caller_gid : function_id)
  (call_iid : instr_id) (ins : instr dtyp) (call_md : list (metadata dtyp))
  (callee_df : definition dtyp (CFG.cfg dtyp))
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  (call_anns : list (annotation dtyp)) :
  match_inlinable_call_instr defs caller_gid (call_iid, ins, call_md) =
    Some (callee_df, ret_dt, call_args, call_anns) ->
  let opt_ret_dt := match call_iid with IId _ => Some ret_dt | IVoid _ => None end in
  exists callee_gid,
    ins = INSTR_Call (ret_dt, EXP_Ident (ID_Global callee_gid)) call_args call_anns [] /\
    caller_gid <> callee_gid /\
    find_defn_by_gid callee_gid defs = Some callee_df /\
    (match call_iid with IId _ => ret_dt <> DTYPE_Void | IVoid _ => True end) /\
    List.length call_args = List.length (df_args callee_df) /\
    (forall te pattrs, In (te, pattrs) call_args -> pattrs = []) /\
    cconv_eqb (anns_cconv call_anns) (anns_cconv (dc_annotations (df_prototype callee_df))) = true /\
    ann_ret_attributes call_anns = [] /\
    forallb is_safe_fn_attr (ann_fun_attributes call_anns) = true /\
    metadata_range call_md = None /\
    is_inlinable_callee opt_ret_dt callee_df = true.
Proof.
  unfold match_inlinable_call_instr.
  destruct ins as [? | ? | [fn_dt fn_e] cargs canns cobs | ? ? | ? ? ? | ? ? ? | ? ? | ? | ? | ? ? | ? ? ?];
    try discriminate.
  destruct fn_e; try discriminate.
  match goal with i : ident |- _ => destruct i as [callee_gid |]; try discriminate end.
  destruct cobs; try discriminate.
  destruct (raw_id_eqb caller_gid callee_gid) eqn:Eself; [discriminate |].
  apply raw_id_eqb_neq in Eself.
  destruct (find_defn_by_gid callee_gid defs) as [cdf |] eqn:Efdf; [| discriminate].
  destruct (_ && is_inlinable_callee _ cdf)%bool eqn:Eok; [| discriminate].
  intros H; injection H as -> -> -> ->.
  repeat match goal with
         | H0 : (_ && _)%bool = true |- _ => apply andb_prop in H0 as [H0 ?]
         end.
  exists callee_gid.
  split; [reflexivity |].
  split; [exact Eself |].
  split; [exact Efdf |].
  split.
  - destruct call_iid as [? | ?]; [| exact I].
    intros ->.
    match goal with Hnv : negb (dtyp_eqb _ _) = true |- _ =>
      rewrite dtyp_eqb_refl in Hnv; discriminate Hnv
    end.
  - split; [apply Nat.eqb_eq; assumption |].
    split.
    + intros te pattrs Hin.
      match goal with Hfa : forallb _ call_args = true |- _ =>
        rewrite forallb_forall in Hfa; specialize (Hfa (te, pattrs) Hin);
        apply is_empty_list_spec in Hfa; exact Hfa
      end.
    + split; [assumption |].
      split; [apply is_empty_list_spec; assumption |].
      split; [assumption |].
      split; [destruct (metadata_range call_md); [discriminate | reflexivity] |].
      assumption.
Qed.

Lemma inline_one_site_block_addresses (M : CFG.mcfg dtyp) :
  mcfg_block_addresses (inline_one_site_mcfg M) = mcfg_block_addresses M.
Proof.
  unfold inline_one_site_mcfg.
  destruct (is_hygienic_module M) eqn:Ehyg; [| reflexivity].
  destruct (inline_first_in_defs (m_definitions M) (m_definitions M)) as [defs' |] eqn:Efind;
    [| reflexivity].
  unfold mcfg_block_addresses; cbn [m_globals m_definitions].
  f_equal.
  apply inline_first_in_defs_inv in Efind
    as (pre_defs & caller_df & post_defs & pre_blks & b_call & post_blks &
        pre_cd & call_iid & ins & call_md & post_cd &
        callee_df & ret_dt & call_args & call_anns &
        Edefs & -> & Hcaller & Hsplit & Hcd & Hmatch).
  unfold is_inlinable_caller in Hcaller.
  apply andb_prop in Hcaller as [_ Hcaller_ba].
  apply match_inlinable_call_instr_inv in Hmatch
    as (callee_gid & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcallee).
  unfold is_inlinable_callee in Hcallee.
  repeat match goal with
         | H : (_ && _)%bool = true |- _ => apply andb_prop in H as [H ?]
         end.
  assert (Hcargs_ba : texps_block_addresses (List.map fst call_args) = []).
  { pose proof Hcaller_ba as Hcba; apply cfg_no_block_addresses_nil in Hcba.
    assert (Hbcall_in : In b_call (blks (df_instrs caller_df))).
    { rewrite Hsplit; apply in_or_app; right; left; reflexivity. }
    pose proof (block_block_addresses_nil_in _ _ Hcba Hbcall_in) as Hb0.
    unfold block_block_addresses in Hb0; rewrite Hcd, flat_map_app in Hb0; cbn [flat_map] in Hb0.
    apply app_eq_nil in Hb0 as [_ Hb1]; apply app_eq_nil in Hb1 as [Hb2 _].
    apply app_eq_nil in Hb2 as [_ Hb3]; apply app_eq_nil in Hb3 as [Hb4 _].
    cbn [instr_block_addresses texps_block_addresses flat_map snd exp_block_addresses app] in Hb4.
    exact Hb4. }
  rewrite Edefs, !flat_map_app; cbn [flat_map].
  f_equal; f_equal.
  pose proof Hcaller_ba as Hcba; apply cfg_no_block_addresses_nil in Hcba; rewrite Hcba; cbn [app].
  erewrite inline_site_block_addresses; eauto.
Qed.

Lemma inline_one_site_build_global_env {Pa : Params} (M : CFG.mcfg dtyp) :
  @build_global_environment Pa (inline_one_site_mcfg M) =
  @build_global_environment Pa M.
Proof.
  unfold build_global_environment.
  rewrite inline_one_site_prototypes, inline_one_site_block_addresses.
  unfold inline_one_site_mcfg.
  destruct (is_hygienic_module M); [| reflexivity].
  destruct (inline_first_in_defs (m_definitions M) (m_definitions M)); reflexivity.
Qed.

