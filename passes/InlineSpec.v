(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Interprocedural Function Inlining Pass — Syntax & Specification ([CertPasses.InlineSpec])

    Computable ID sets, hygienic renaming maps, block splitting, and the
    single-site / iterated module inlining transformation ([inline_mcfg], [inline_mcfg_typ]). *)

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

(** * 1. Computable ID Sets, Deduplication, and Renaming Maps *)

Fixpoint nodup_raw_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: xs' => negb (in_raw_ids x xs') && nodup_raw_ids xs'
  end.

Lemma nodup_raw_ids_spec (xs : list raw_id) :
  nodup_raw_ids xs = true <-> NoDup xs.
Proof.
  induction xs as [| x xs' IH]; cbn [nodup_raw_ids].
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite andb_true_iff, negb_true_iff, in_raw_ids_false, IH.
    split.
    + intros [Hnin Hnd]; constructor; assumption.
    + intros Hnd; inversion Hnd; subst; split; assumption.
Qed.

Definition disjoint_raw_ids (xs ys : list raw_id) : bool :=
  forallb (fun x => negb (in_raw_ids x ys)) xs.

Lemma disjoint_raw_ids_spec (xs ys : list raw_id) :
  disjoint_raw_ids xs ys = true <-> (forall x, In x xs -> ~ In x ys).
Proof.
  unfold disjoint_raw_ids; rewrite forallb_forall.
  split; intros H x Hx; specialize (H x Hx);
    rewrite negb_true_iff, in_raw_ids_false in *; exact H.
Qed.

Definition incl_raw_ids (xs ys : list raw_id) : bool :=
  forallb (fun x => in_raw_ids x ys) xs.

Lemma incl_raw_ids_spec (xs ys : list raw_id) :
  incl_raw_ids xs ys = true <-> incl xs ys.
Proof.
  unfold incl_raw_ids, incl; rewrite forallb_forall.
  split; intros H x Hx; specialize (H x Hx);
    rewrite in_raw_ids_spec in *; exact H.
Qed.

Definition add_unique_id (x : raw_id) (xs : list raw_id) : list raw_id :=
  if in_raw_ids x xs then xs else x :: xs.

Definition dedup_raw_ids (xs : list raw_id) : list raw_id :=
  fold_right add_unique_id [] xs.

Lemma dedup_raw_ids_in (x : raw_id) (xs : list raw_id) :
  In x (dedup_raw_ids xs) <-> In x xs.
Proof.
  induction xs as [| y ys IH]; cbn [dedup_raw_ids fold_right].
  - tauto.
  - change (fold_right add_unique_id [] ys) with (dedup_raw_ids ys); unfold add_unique_id.
    destruct (in_raw_ids y (dedup_raw_ids ys)) eqn:Ein.
    + apply in_raw_ids_spec in Ein.
      split; [intros H; right; apply IH; exact H | intros [<- | H]; [exact Ein | apply IH; exact H]].
    + cbn [In]; rewrite IH; tauto.
Qed.

Lemma dedup_raw_ids_nodup (xs : list raw_id) :
  NoDup (dedup_raw_ids xs).
Proof.
  induction xs as [| y ys IH]; cbn [dedup_raw_ids fold_right].
  - constructor.
  - change (fold_right add_unique_id [] ys) with (dedup_raw_ids ys); unfold add_unique_id.
    destruct (in_raw_ids y (dedup_raw_ids ys)) eqn:Ein.
    + exact IH.
    + apply in_raw_ids_false in Ein; constructor; assumption.
Qed.

Fixpoint lookup_ren (ren : list (raw_id * raw_id)) (x : raw_id) : raw_id :=
  match ren with
  | [] => x
  | (k, v) :: rest => if raw_id_eqb x k then v else lookup_ren rest x
  end.

Lemma lookup_ren_in_dom (xs ys : list raw_id) (x : raw_id)
  (Hlen : List.length xs = List.length ys)
  (Hx : In x xs) :
  In (lookup_ren (combine xs ys) x) ys.
Proof.
  revert ys Hlen; induction xs as [| a xs' IH]; intros [| b ys'] Hlen;
    try discriminate Hlen; [contradiction |].
  cbn [List.length] in Hlen; injection Hlen as Hlen.
  cbn [combine lookup_ren].
  destruct (raw_id_eqb x a) eqn:E.
  - left; reflexivity.
  - apply raw_id_eqb_neq in E.
    destruct Hx as [Heq | Hx]; [ symmetry in Heq; contradiction |].
    right; apply IH; assumption.
Qed.

Lemma lookup_ren_not_in_dom (xs ys : list raw_id) (x : raw_id)
  (Hnin : ~ In x xs) :
  lookup_ren (combine xs ys) x = x.
Proof.
  revert ys; induction xs as [| a xs' IH]; intros [| b ys']; try reflexivity.
  cbn [combine lookup_ren].
  destruct (raw_id_eqb x a) eqn:E.
  - apply raw_id_eqb_spec in E; subst a.
    exfalso; apply Hnin; left; reflexivity.
  - apply IH; intros Hx; apply Hnin; right; exact Hx.
Qed.

Lemma lookup_ren_inj_on (xs ys : list raw_id)
  (Hlen : List.length xs = List.length ys)
  (Hnd_y : NoDup ys) :
  forall x1 x2,
    In x1 xs ->
    In x2 xs ->
    lookup_ren (combine xs ys) x1 = lookup_ren (combine xs ys) x2 ->
    x1 = x2.
Proof.
  revert ys Hlen Hnd_y.
  induction xs as [| a xs' IH]; intros [| b ys'] Hlen Hnd_y x1 x2 H1 H2 Heq;
    try discriminate Hlen; [contradiction |].
  cbn [List.length] in Hlen; injection Hlen as Hlen.
  inversion Hnd_y as [| ? ? Hnin_b Hnd_ys']; subst.
  cbn [combine lookup_ren] in Heq.
  destruct (raw_id_eqb x1 a) eqn:E1, (raw_id_eqb x2 a) eqn:E2.
  - apply raw_id_eqb_spec in E1; apply raw_id_eqb_spec in E2; congruence.
  - apply raw_id_eqb_neq in E2.
    destruct H2 as [Ha2 | H2]; [symmetry in Ha2; contradiction |].
    subst b.
    exfalso; apply Hnin_b.
    eapply lookup_ren_in_dom; eassumption.
  - apply raw_id_eqb_neq in E1.
    destruct H1 as [Ha1 | H1]; [symmetry in Ha1; contradiction |].
    exfalso; apply Hnin_b; rewrite <- Heq.
    eapply lookup_ren_in_dom; eassumption.
  - apply raw_id_eqb_neq in E1; apply raw_id_eqb_neq in E2.
    destruct H1 as [Ha1 | H1]; [symmetry in Ha1; contradiction |].
    destruct H2 as [Ha2 | H2]; [symmetry in Ha2; contradiction |].
    eapply IH; eassumption.
Qed.

(** * 2. AST Alpha-Renaming & Predecessor Remapping *)

Definition ren_ident (ren_l : raw_id -> raw_id) (id : ident) : ident :=
  match id with
  | ID_Local x => ID_Local (ren_l x)
  | ID_Global g => ID_Global g
  end.

Fixpoint ren_exp {T : Set} (ren_l : raw_id -> raw_id) (e : exp T) : exp T :=
  let ren_texp_list :=
    fix go (l : list (T * exp T)) : list (T * exp T) :=
      match l with
      | [] => []
      | (t, ex) :: rest => (t, ren_exp ren_l ex) :: go rest
      end
  in
  match e with
  | EXP_Ident id => EXP_Ident (ren_ident ren_l id)
  | EXP_Integer x => EXP_Integer x
  | EXP_Float f => EXP_Float f
  | EXP_Bool b => EXP_Bool b
  | EXP_Null => EXP_Null
  | EXP_Zero_initializer => EXP_Zero_initializer
  | EXP_Undef => EXP_Undef
  | EXP_Poison => EXP_Poison
  | EXP_Asm s1 s2 s3 s4 s5 s6 => EXP_Asm s1 s2 s3 s4 s5 s6
  | EXP_BlockAddress fn b => EXP_BlockAddress fn b
  | EXP_Cstring elts => EXP_Cstring (ren_texp_list elts)
  | EXP_Struct elts => EXP_Struct (ren_texp_list elts)
  | EXP_Packed_struct elts => EXP_Packed_struct (ren_texp_list elts)
  | EXP_Array elts => EXP_Array (ren_texp_list elts)
  | EXP_Vector elts => EXP_Vector (ren_texp_list elts)
  | OP_IBinop iop t e1 e2 =>
      OP_IBinop iop t (ren_exp ren_l e1) (ren_exp ren_l e2)
  | OP_ICmp ss cmp t e1 e2 =>
      OP_ICmp ss cmp t (ren_exp ren_l e1) (ren_exp ren_l e2)
  | OP_FBinop fop fm t e1 e2 =>
      OP_FBinop fop fm t (ren_exp ren_l e1) (ren_exp ren_l e2)
  | OP_Fneg fm (t, e1) =>
      OP_Fneg fm (t, ren_exp ren_l e1)
  | OP_FCmp cmp fm t e1 e2 =>
      OP_FCmp cmp fm t (ren_exp ren_l e1) (ren_exp ren_l e2)
  | OP_Conversion ct tf e1 tt0 =>
      OP_Conversion ct tf (ren_exp ren_l e1) tt0
  | OP_GetElementPtr flags t (tp, ep) idxs =>
      OP_GetElementPtr flags t (tp, ren_exp ren_l ep) (ren_texp_list idxs)
  | OP_ExtractElement (t1, e1) (t2, e2) =>
      OP_ExtractElement (t1, ren_exp ren_l e1) (t2, ren_exp ren_l e2)
  | OP_InsertElement (t1, e1) (t2, e2) (t3, e3) =>
      OP_InsertElement (t1, ren_exp ren_l e1) (t2, ren_exp ren_l e2) (t3, ren_exp ren_l e3)
  | OP_ShuffleVector (t1, e1) (t2, e2) (t3, e3) =>
      OP_ShuffleVector (t1, ren_exp ren_l e1) (t2, ren_exp ren_l e2) (t3, ren_exp ren_l e3)
  | OP_ExtractValue (t1, e1) idxs =>
      OP_ExtractValue (t1, ren_exp ren_l e1) idxs
  | OP_InsertValue (t1, e1) (t2, e2) idxs =>
      OP_InsertValue (t1, ren_exp ren_l e1) (t2, ren_exp ren_l e2) idxs
  | OP_Select fm (t1, e1) (t2, e2) (t3, e3) =>
      OP_Select fm (t1, ren_exp ren_l e1) (t2, ren_exp ren_l e2) (t3, ren_exp ren_l e3)
  | OP_Freeze (t1, e1) =>
      OP_Freeze (t1, ren_exp ren_l e1)
  | EXP_Metadata md =>
      EXP_Metadata (ren_metadata ren_l md)
  | EXP_Splat (t1, e1) =>
      EXP_Splat (t1, ren_exp ren_l e1)
  end
with ren_metadata {T : Set} (ren_l : raw_id -> raw_id) (md : metadata T) : metadata T :=
  let ren_md_list :=
    fix go_md (l : list (metadata T)) : list (metadata T) :=
      match l with
      | [] => []
      | m :: rest => ren_metadata ren_l m :: go_md rest
      end
  in
  match md with
  | METADATA_Null => METADATA_Null
  | METADATA_Id id => METADATA_Id id
  | METADATA_Const (t, ex) => METADATA_Const (t, ren_exp ren_l ex)
  | METADATA_Node mds => METADATA_Node (ren_md_list mds)
  | METADATA_Pair m1 m2 => METADATA_Pair (ren_metadata ren_l m1) (ren_metadata ren_l m2)
  | METADATA_Debug s1 s2 => METADATA_Debug s1 s2
  | METADATA_File_info fi => METADATA_File_info fi
  end.

Definition ren_instr_id (ren_l : raw_id -> raw_id) (iid : instr_id) : instr_id :=
  match iid with
  | IId x => IId (ren_l x)
  | IVoid n => IVoid n
  end.

Definition ren_leaf_instr {T : Set} (ren_l : raw_id -> raw_id) (ins : instr T) : instr T :=
  match ins with
  | INSTR_Op op => INSTR_Op (ren_exp ren_l op)
  | INSTR_Load dt (du, ptr) anns => INSTR_Load dt (du, ren_exp ren_l ptr) anns
  | INSTR_Store (dt, val) (du, ptr) anns =>
      INSTR_Store (dt, ren_exp ren_l val) (du, ren_exp ren_l ptr) anns
  | _ => ins
  end.

Definition ren_code_entry {T : Set} (ren_l : raw_id -> raw_id)
  (im : instr_id * instr T * list (metadata T)) : instr_id * instr T * list (metadata T) :=
  let '(iid, ins, md) := im in
  (ren_instr_id ren_l iid, ren_leaf_instr ren_l ins, md).

Definition ren_phi_entry {T : Set} (ren_l ren_b : raw_id -> raw_id)
  (pm : local_id * phi T * list (metadata T)) : local_id * phi T * list (metadata T) :=
  let '(x, Phi fm dt pargs, md) := pm in
  (ren_l x, Phi fm dt (List.map (fun '(b, ex) => (ren_b b, ren_exp ren_l ex)) pargs), md).

Definition remap_pred_id (old_bid new_bid b : block_id) : block_id :=
  if raw_id_eqb b old_bid then new_bid else b.

Definition remap_phis_pred {T : Set} (old_bid new_bid : block_id)
  (phis : list (local_id * phi T * list (metadata T)))
  : list (local_id * phi T * list (metadata T)) :=
  List.map
    (fun '(x, Phi fm dt pargs, md) =>
       (x, Phi fm dt (List.map (fun '(b, ex) => (remap_pred_id old_bid new_bid b, ex)) pargs), md))
    phis.

Definition remap_block_phis {T : Set} (old_bid new_bid : block_id) (bk : block T) : block T :=
  {| blk_id       := blk_id bk;
     blk_phis     := remap_phis_pred old_bid new_bid (blk_phis bk);
     blk_code     := blk_code bk;
     blk_term     := blk_term bk;
     blk_comments := blk_comments bk |}.

(** * 3. Callee Definite-Initialization Analysis & Validator *)

Definition term_succ_bids {T : Set} (tm : terminator T) : list block_id :=
  match tm with
  | TERM_Br _ b1 b2 => [b1; b2]
  | TERM_Br_1 b => [b]
  | TERM_Switch _ d brs => d :: List.map snd brs
  | TERM_IndirectBr _ brs _ => brs
  | TERM_Invoke _ _ b1 b2 _ _ => [b1; b2]
  | _ => []
  end.

Definition block_all_label_ids {T : Set} (bk : block T) : list raw_id :=
  blk_id bk
  :: flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) (blk_phis bk)
  ++ term_succ_bids (snd (fst (blk_term bk))).

Definition defn_all_ids {T : Set} (df : definition T (CFG.cfg T)) : list raw_id :=
  dc_name (df_prototype df)
  :: df_args df
  ++ cfg_all_ids (df_instrs df)
  ++ flat_map block_all_label_ids (blks (df_instrs df)).

Definition lookup_def_set (m : list (block_id * list raw_id)) (b : block_id) : list raw_id :=
  match assoc b m with
  | Some ds => ds
  | None => []
  end.

Definition intersect_raw_ids (xs ys : list raw_id) : list raw_id :=
  List.filter (fun x => in_raw_ids x ys) xs.

Definition block_local_defs {T : Set} (bk : block T) : list raw_id :=
  List.map (fun '(x, _, _) => x) (blk_phis bk)
  ++ flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk).

Definition step_def_map {T : Set} (fargs all_defs : list raw_id) (c : CFG.cfg T)
  (cur : list (block_id * list raw_id)) : list (block_id * list raw_id) :=
  List.map
    (fun bk =>
       let bid := blk_id bk in
       let base := if raw_id_eqb bid (init c) then fargs else all_defs in
       let preds_in :=
         fold_left
           (fun acc pred_bk =>
              if in_raw_ids bid (term_succ_bids (snd (fst (blk_term pred_bk))))
              then intersect_raw_ids acc
                     (dedup_raw_ids (lookup_def_set cur (blk_id pred_bk)
                                     ++ block_local_defs pred_bk))
              else acc)
           (blks c) base
       in
       (bid, preds_in))
    (blks c).

Fixpoint iter_def_map {T : Set} (fuel : nat) (fargs all_defs : list raw_id) (c : CFG.cfg T)
  (cur : list (block_id * list raw_id)) : list (block_id * list raw_id) :=
  match fuel with
  | O => cur
  | S fuel' => iter_def_map fuel' fargs all_defs c (step_def_map fargs all_defs c cur)
  end.

Definition compute_def_map {T : Set} (fargs : list raw_id) (c : CFG.cfg T)
  : list (block_id * list raw_id) :=
  let all_defs := dedup_raw_ids (fargs ++ flat_map block_local_defs (blks c)) in
  let init_map :=
    List.map
      (fun bk =>
         (blk_id bk, if raw_id_eqb (blk_id bk) (init c) then fargs else all_defs))
      (blks c)
  in
  iter_def_map (S (List.length (blks c))) fargs all_defs c init_map.

Fixpoint check_code_defs {T : Set} (cur : list raw_id)
  (cd : list (instr_id * instr T * list (metadata T))) : option (list raw_id) :=
  match cd with
  | [] => Some cur
  | (iid, ins, md) :: rest =>
      if incl_raw_ids (full_instr_uses ins ++ flat_map full_metadata_uses md) cur
      then check_code_defs (cur ++ instr_id_defs iid) rest
      else None
  end.

Definition check_succ_edge {T : Set} (bks : ocfg T)
  (in_map : list (block_id * list raw_id))
  (src_bid : block_id) (d_out : list raw_id) (succ_bid : block_id) : bool :=
  match find_block bks succ_bid with
  | None => false
  | Some b_succ =>
      incl_raw_ids (lookup_def_set in_map succ_bid) d_out &&
      forallb
        (fun '(_, Phi _ _ pargs, md) =>
           match assoc src_bid pargs with
           | None => false
           | Some op =>
               incl_raw_ids (full_exp_uses op ++ flat_map full_metadata_uses md) d_out
           end)
        (blk_phis b_succ)
  end.

Definition verify_block_defs {T : Set} (bks : ocfg T)
  (in_map : list (block_id * list raw_id)) (bk : block T) : bool :=
  let d0 := lookup_def_set in_map (blk_id bk) in
  let d_phi := d0 ++ List.map (fun '(x, _, _) => x) (blk_phis bk) in
  match check_code_defs d_phi (blk_code bk) with
  | None => false
  | Some d_out =>
      let '(_, tm, tmd) := blk_term bk in
      incl_raw_ids (full_term_uses tm ++ flat_map full_metadata_uses tmd) d_out &&
      forallb (check_succ_edge bks in_map (blk_id bk) d_out) (term_succ_bids tm)
  end.

Definition verify_def_map {T : Set} (fargs : list raw_id) (c : CFG.cfg T)
  (in_map : list (block_id * list raw_id)) : bool :=
  incl_raw_ids (lookup_def_set in_map (init c)) fargs &&
  forallb (verify_block_defs (blks c) in_map) (blks c).

Definition check_cfg_def_before_use {T : Set} (fargs : list raw_id) (c : CFG.cfg T) : bool :=
  verify_def_map fargs c (compute_def_map fargs c).

(** * 4. Eligibility Guards & Single-Site Inlining Transformation *)

Definition is_empty_list {A : Type} (xs : list A) : bool :=
  match xs with
  | [] => true
  | _ :: _ => false
  end.

Definition is_safe_fn_attr (fa : fn_attr) : bool :=
  negb (fn_attr_is_noreturn fa) && negb (fn_attr_is_nocreateundeforpoison fa).

Definition is_zero_vararg_alloca (dt : dtyp) (anns : list (annotation dtyp)) : bool :=
  dtyp_eqb dt (DTYPE_Struct true []) && is_empty_list anns.

Definition is_leaf_instr_entry (im : instr_id * instr dtyp * list (metadata dtyp)) : bool :=
  let '(iid, ins, md) := im in
  is_empty_list (flat_map full_metadata_uses md) &&
  match iid, ins with
  | IId _, INSTR_Op _ => true
  | IId _, INSTR_Alloca dt anns => is_zero_vararg_alloca dt anns
  | IId _, INSTR_Load _ _ anns => is_empty_list (flat_map full_ann_uses anns)
  | IVoid _, INSTR_Store _ _ anns => is_empty_list (flat_map full_ann_uses anns)
  | IVoid _, INSTR_Comment _ => true
  | IVoid _, INSTR_Fence _ _ => true
  | _, _ => false
  end.

Definition is_leaf_term_entry (opt_ret_dt : option dtyp)
  (tm_entry : instr_id * terminator dtyp * list (metadata dtyp)) : bool :=
  let '(_, tm, tmd) := tm_entry in
  is_empty_list (flat_map full_metadata_uses tmd) &&
  match tm with
  | TERM_Ret (dt, _) =>
      match opt_ret_dt with
      | Some ret_dt => dtyp_eqb dt ret_dt
      | None => true
      end
  | TERM_Ret_void =>
      match opt_ret_dt with
      | Some _ => false
      | None => true
      end
  | TERM_Br _ _ _ => true
  | TERM_Br_1 _ => true
  | TERM_Switch _ _ _ => true
  | TERM_Unreachable => true
  | _ => false
  end.

Definition is_leaf_block (opt_ret_dt : option dtyp) (bk : block dtyp) : bool :=
  forallb (fun '(_, _, md) => is_empty_list (flat_map full_metadata_uses md)) (blk_phis bk) &&
  forallb is_leaf_instr_entry (blk_code bk) &&
  is_leaf_term_entry opt_ret_dt (blk_term bk).

Definition cfg_entry_has_no_phis {T : Set} (c : CFG.cfg T) : bool :=
  match find_block (blks c) (init c) with
  | Some b0 => is_empty_list (blk_phis b0)
  | None => false
  end.

Definition is_hygienic_module (M : CFG.mcfg dtyp) : bool :=
  let decl_names :=
    List.map dc_name (m_declarations M ++ List.map df_prototype (m_definitions M))
  in
  let ba_names :=
    List.map (fun '(f, b) => blockaddress_id f b) (mcfg_block_addresses M)
  in
  let glob_names := List.map g_ident (m_globals M) in
  nodup_raw_ids (decl_names ++ ba_names ++ glob_names).

Definition is_non_interposable_linkage (lnk : linkage) : bool :=
  match lnk with
  | LINKAGE_Weak
  | LINKAGE_Weak_odr
  | LINKAGE_Linkonce
  | LINKAGE_Linkonce_odr
  | LINKAGE_Extern_weak
  | LINKAGE_Common
  | LINKAGE_Appending => false
  | LINKAGE_Private
  | LINKAGE_Internal
  | LINKAGE_Available_externally
  | LINKAGE_External => true
  end.

Definition is_inlinable_decl_ann {T : Set} (a : annotation T) : bool :=
  match a with
  | ANN_linkage lnk => is_non_interposable_linkage lnk
  | ANN_preemption_specifier PREEMPTION_Dso_preemptable => false
  | ANN_section _ => false
  | _ => true
  end.

Definition is_inlinable_fn_attr (fa : fn_attr) : bool :=
  match fa with
  | FNATTR_Noinline
  | FNATTR_Optnone
  | FNATTR_Naked
  | FNATTR_Returns_twice
  | FNATTR_Strictfp
  | FNATTR_Null_pointer_is_valid
  | FNATTR_Attr_grp _ => false
  | _ => true
  end.

Definition ocfg_succs_of {T : Set} (bks : ocfg T) (bid : block_id) : list block_id :=
  match find_block bks bid with
  | Some bk => term_succ_bids (snd (fst (blk_term bk)))
  | None => []
  end.

Fixpoint can_reach_bid_in {T : Set} (fuel : nat) (bks : ocfg T)
  (frontier : list block_id) (target : block_id) : bool :=
  in_raw_ids target frontier ||
  match fuel with
  | O => false
  | S fuel' =>
      let next := dedup_raw_ids (flat_map (ocfg_succs_of bks) frontier) in
      can_reach_bid_in fuel' bks next target
  end.

(** True iff [bk] lies on a CFG cycle (self-loop or backedge) in [bks].
    Rejecting call sites in loop blocks ensures the synthetic 0-byte varargs
    [INSTR_Alloca <{}>] emitted per inlined site cannot grow the caller's stack
    frame across loop iterations. *)
Definition block_in_cfg_loop {T : Set} (bks : ocfg T) (bk : block T) : bool :=
  let succs := term_succ_bids (snd (fst (blk_term bk))) in
  can_reach_bid_in (List.length bks) bks succs (blk_id bk).

Definition is_inlinable_callee (opt_ret_dt : option dtyp)
  (callee_df : definition dtyp (CFG.cfg dtyp)) : bool :=
  let proto := df_prototype callee_df in
  let gid := dc_name proto in
  let c := df_instrs callee_df in
  match lookup_intrinsic_declaration gid with
  | Some _ => false
  | None => true
  end &&
  negb (raw_id_eqb gid (Name "puts"%string)) &&
  negb (raw_id_eqb gid (Name "putchar"%string)) &&
  forallb is_inlinable_fn_attr (dc_attrs proto) &&
  forallb is_inlinable_decl_ann (dc_annotations proto) &&
  is_empty_list (fst (dc_param_attrs proto)) &&
  forallb is_empty_list (snd (dc_param_attrs proto)) &&
  forallb is_safe_fn_attr (dc_attrs proto) &&
  nodup_raw_ids (df_args callee_df) &&
  nodup_raw_ids (List.map blk_id (blks c)) &&
  cfg_entry_has_no_phis c &&
  cfg_no_block_addresses c &&
  forallb (is_leaf_block opt_ret_dt) (blks c) &&
  (match opt_ret_dt with
   | None => true
   | Some _ =>
       existsb
         (fun bk =>
            match snd (fst (blk_term bk)) with
            | TERM_Ret _ => true
            | _ => false
            end)
         (blks c)
   end) &&
  check_cfg_def_before_use (df_args callee_df) c.

Fixpoint find_defn_by_gid (gid : function_id)
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  : option (definition dtyp (CFG.cfg dtyp)) :=
  match defs with
  | [] => None
  | df :: rest =>
      if raw_id_eqb (dc_name (df_prototype df)) gid
      then Some df
      else find_defn_by_gid gid rest
  end.

Definition is_inlinable_caller (caller_df : definition dtyp (CFG.cfg dtyp)) : bool :=
  let c := df_instrs caller_df in
  nodup_raw_ids (List.map blk_id (blks c)) &&
  cfg_entry_has_no_phis c &&
  cfg_no_block_addresses c.

Definition match_inlinable_call_instr
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  (caller_gid : function_id)
  (im : instr_id * instr dtyp * list (metadata dtyp))
  : option (definition dtyp (CFG.cfg dtyp) * dtyp *
            list (texp dtyp * list param_attr) * list (annotation dtyp)) :=
  let '(call_iid, ins, call_md) := im in
  match ins with
  | INSTR_Call (ret_dt, EXP_Ident (ID_Global callee_gid)) call_args call_anns [] =>
      if raw_id_eqb caller_gid callee_gid then None
      else
        let opt_ret_dt :=
          match call_iid with
          | IId _ => Some ret_dt
          | IVoid _ => None
          end
        in
        let ret_non_void_ok :=
          match call_iid with
          | IId _ => negb (dtyp_eqb ret_dt DTYPE_Void)
          | IVoid _ => true
          end
        in
        match find_defn_by_gid callee_gid defs with
        | None => None
        | Some callee_df =>
            let proto := df_prototype callee_df in
            if ret_non_void_ok &&
               Nat.eqb (List.length call_args) (List.length (df_args callee_df)) &&
               forallb (fun '(_, pattrs) => is_empty_list pattrs) call_args &&
               cconv_eqb (anns_cconv call_anns) (anns_cconv (dc_annotations proto)) &&
               is_empty_list (ann_ret_attributes call_anns) &&
               forallb is_inlinable_fn_attr (ann_fun_attributes call_anns) &&
               forallb is_safe_fn_attr (ann_fun_attributes call_anns) &&
               match metadata_range call_md with None => true | Some _ => false end &&
               is_inlinable_callee opt_ret_dt callee_df
            then Some (callee_df, ret_dt, call_args, call_anns)
            else None
        end
  | _ => None
  end.

Definition callee_local_ids (callee_df : definition dtyp (CFG.cfg dtyp)) : list raw_id :=
  dedup_raw_ids
    (df_args callee_df
     ++ flat_map full_block_defs (blks (df_instrs callee_df))
     ++ flat_map full_block_uses (blks (df_instrs callee_df))).

Definition callee_block_ids (callee_df : definition dtyp (CFG.cfg dtyp)) : list raw_id :=
  dedup_raw_ids
    (init (df_instrs callee_df)
     :: flat_map block_all_label_ids (blks (df_instrs callee_df))).

Fixpoint build_param_copies (ren_l : raw_id -> raw_id)
  (params : list local_id) (call_args : list (texp dtyp * list param_attr))
  : code dtyp :=
  match params, call_args with
  | p :: ps, ((arg_dt, arg_e), _) :: rest =>
      (IId (ren_l p), INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) arg_dt arg_e), [])
      :: build_param_copies ren_l ps rest
  | _, _ => []
  end.

Definition transform_callee_block
  (ren_l ren_b : raw_id -> raw_id) (post_bid : block_id)
  (bk_rtmp : block dtyp * raw_id) : block dtyp :=
  let '(bk, rtmp) := bk_rtmp in
  let base_code := List.map (ren_code_entry ren_l) (blk_code bk) in
  let '(tiid, tm, tmd) := blk_term bk in
  let '(new_code, new_term) :=
    match tm with
    | TERM_Ret (dt, op) =>
        (base_code ++ [(IId rtmp, INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt (ren_exp ren_l op)), [])],
         (IVoid 0%Z, TERM_Br_1 post_bid, []))
    | TERM_Ret_void =>
        (base_code, (IVoid 0%Z, TERM_Br_1 post_bid, []))
    | TERM_Br (dt, op) b1 b2 =>
        (base_code, (tiid, TERM_Br (dt, ren_exp ren_l op) (ren_b b1) (ren_b b2), tmd))
    | TERM_Br_1 b =>
        (base_code, (tiid, TERM_Br_1 (ren_b b), tmd))
    | TERM_Switch (dt, op) def_b brs =>
        (base_code,
         (tiid,
          TERM_Switch (dt, ren_exp ren_l op) (ren_b def_b)
            (List.map (fun '(lit, b) => (lit, ren_b b)) brs),
          tmd))
    | _ =>
        (base_code, (tiid, tm, tmd))
    end
  in
  {| blk_id       := ren_b (blk_id bk);
     blk_phis     := List.map (ren_phi_entry ren_l ren_b) (blk_phis bk);
     blk_code     := new_code;
     blk_term     := new_term;
     blk_comments := blk_comments bk |}.

Definition collect_ret_phi_incoming
  (ren_b : raw_id -> raw_id)
  (bk_rtmps : list (block dtyp * raw_id)) : list (block_id * exp dtyp) :=
  flat_map
    (fun '(bk, rtmp) =>
       match snd (fst (blk_term bk)) with
       | TERM_Ret _ => [(ren_b (blk_id bk), EXP_Ident (ID_Local rtmp))]
       | _ => []
       end)
    bk_rtmps.

Definition inline_site_in_caller
  (caller_df callee_df : definition dtyp (CFG.cfg dtyp))
  (pre_blks post_blks : ocfg dtyp)
  (b_call : block dtyp)
  (pre_code post_code : code dtyp)
  (call_iid : instr_id)
  (ret_dt : dtyp)
  (call_args : list (texp dtyp * list param_attr))
  : definition dtyp (CFG.cfg dtyp) :=
  let caller_cfg := df_instrs caller_df in
  let callee_cfg := df_instrs callee_df in
  let used_ids := defn_all_ids caller_df ++ defn_all_ids callee_df in
  let l_origs := callee_local_ids callee_df in
  let b_origs := callee_block_ids callee_df in
  let n_loc := List.length l_origs in
  let n_blk := List.length b_origs in
  let n_ret := List.length (blks callee_cfg) in
  let all_fresh := fresh_names "inl"%string (2 + n_loc + n_blk + n_ret)%nat used_ids in
  let post_bid  := hd (Name "inl_post"%string) all_fresh in
  let va_tmp_id := hd (Name "inl_va"%string) (skipn 1 all_fresh) in
  let l_fresh   := firstn n_loc (skipn 2 all_fresh) in
  let b_fresh   := firstn n_blk (skipn (2 + n_loc)%nat all_fresh) in
  let ret_tmps  := firstn n_ret (skipn (2 + n_loc + n_blk)%nat all_fresh) in
  let ren_l     := lookup_ren (combine l_origs l_fresh) in
  let ren_b     := lookup_ren (combine b_origs b_fresh) in
  let call_bid  := blk_id b_call in
  let bk_rtmps  := combine (blks callee_cfg) ret_tmps in
  let inl_blks  := List.map (transform_callee_block ren_l ren_b post_bid) bk_rtmps in
  let ret_in    := collect_ret_phi_incoming ren_b bk_rtmps in
  let b_pre :=
    {| blk_id       := call_bid;
       blk_phis     := remap_phis_pred call_bid post_bid (blk_phis b_call);
       blk_code     := pre_code
                       ++ build_param_copies ren_l (df_args callee_df) call_args
                       ++ [(IId va_tmp_id, INSTR_Alloca (DTYPE_Struct true []) [], [])];
       blk_term     := (IVoid 0%Z, TERM_Br_1 (ren_b (init callee_cfg)), []);
       blk_comments := blk_comments b_call |}
  in
  let post_phis :=
    match call_iid with
    | IId res_id => [(res_id, Phi [] ret_dt ret_in, [])]
    | IVoid _ => []
    end
  in
  let b_post :=
    {| blk_id       := post_bid;
       blk_phis     := post_phis;
       blk_code     := post_code;
       blk_term     := blk_term b_call;
       blk_comments := None |}
  in
  let new_blks :=
    List.map (remap_block_phis call_bid post_bid) pre_blks
    ++ b_pre :: inl_blks
    ++ b_post :: List.map (remap_block_phis call_bid post_bid) post_blks
  in
  {| df_prototype := df_prototype caller_df;
     df_args      := df_args caller_df;
     df_instrs    := {| init := init caller_cfg;
                        blks := new_blks;
                        args := args caller_cfg |} |}.

Fixpoint find_call_in_code
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  (caller_gid : function_id)
  (acc_pre : code dtyp)
  (cd : code dtyp)
  : option (code dtyp * (instr_id * instr dtyp * list (metadata dtyp)) * code dtyp *
            definition dtyp (CFG.cfg dtyp) * dtyp *
            list (texp dtyp * list param_attr) * list (annotation dtyp)) :=
  match cd with
  | [] => None
  | im :: rest =>
      match match_inlinable_call_instr defs caller_gid im with
      | Some (callee_df, ret_dt, call_args, call_anns) =>
          Some (List.rev acc_pre, im, rest, callee_df, ret_dt, call_args, call_anns)
      | None =>
          find_call_in_code defs caller_gid (im :: acc_pre) rest
      end
  end.

Fixpoint find_call_in_blks
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  (caller_gid : function_id)
  (all_caller_bks : ocfg dtyp)
  (acc_pre_blks : ocfg dtyp)
  (bks : ocfg dtyp)
  : option (ocfg dtyp * block dtyp * ocfg dtyp *
            code dtyp * (instr_id * instr dtyp * list (metadata dtyp)) * code dtyp *
            definition dtyp (CFG.cfg dtyp) * dtyp *
            list (texp dtyp * list param_attr) * list (annotation dtyp)) :=
  match bks with
  | [] => None
  | bk :: rest_blks =>
      if block_in_cfg_loop all_caller_bks bk then
        find_call_in_blks defs caller_gid all_caller_bks (bk :: acc_pre_blks) rest_blks
      else
        match find_call_in_code defs caller_gid [] (blk_code bk) with
        | Some (pre_cd, im, post_cd, callee_df, ret_dt, call_args, call_anns) =>
            Some (List.rev acc_pre_blks, bk, rest_blks,
                  pre_cd, im, post_cd, callee_df, ret_dt, call_args, call_anns)
        | None =>
            find_call_in_blks defs caller_gid all_caller_bks (bk :: acc_pre_blks) rest_blks
        end
  end.

Fixpoint inline_first_in_defs
  (all_defs : list (definition dtyp (CFG.cfg dtyp)))
  (rem_defs : list (definition dtyp (CFG.cfg dtyp)))
  : option (list (definition dtyp (CFG.cfg dtyp))) :=
  match rem_defs with
  | [] => None
  | caller_df :: rest_defs =>
      let caller_gid := dc_name (df_prototype caller_df) in
      let caller_bks := blks (df_instrs caller_df) in
      if is_inlinable_caller caller_df then
        match find_call_in_blks all_defs caller_gid caller_bks [] caller_bks with
        | Some (pre_blks, b_call, post_blks,
                pre_cd, (call_iid, _, _), post_cd,
                callee_df, ret_dt, call_args, _) =>
            let caller_df' :=
              inline_site_in_caller caller_df callee_df pre_blks post_blks
                b_call pre_cd post_cd call_iid ret_dt call_args
            in
            Some (caller_df' :: rest_defs)
        | None =>
            option_map (cons caller_df) (inline_first_in_defs all_defs rest_defs)
        end
      else
        option_map (cons caller_df) (inline_first_in_defs all_defs rest_defs)
  end.

Definition inline_one_site_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  if is_hygienic_module M then
    match inline_first_in_defs (m_definitions M) (m_definitions M) with
    | None => M
    | Some defs' =>
        {| m_name         := m_name M;
           m_target       := m_target M;
           m_datalayout   := m_datalayout M;
           m_type_defs    := m_type_defs M;
           m_globals      := m_globals M;
           m_declarations := m_declarations M;
           m_definitions  := defs' |}
    end
  else M.

Fixpoint inline_iter (fuel : nat) (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  match fuel with
  | O => M
  | S fuel' => inline_iter fuel' (inline_one_site_mcfg M)
  end.

Definition inline_default_fuel : nat := 16%nat.

Definition inline_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  inline_iter inline_default_fuel M.

Definition inline_mcfg_typ (M : CFG.mcfg typ) : CFG.mcfg dtyp :=
  inline_mcfg (convert_types M).


