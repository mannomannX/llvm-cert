(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Interprocedural Function Inlining Pass ([CertPasses.Inline])

    Inlines eligible direct calls to non-recursive leaf internal definitions
    across a module ([CFG.mcfg dtyp]) via hygienic fresh [Name] alpha-renaming,
    caller basic-block splitting, and multi-round iteration composed with
    [prog_refines_trans]. *)

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
  induction xs as [| y ys IH]; cbn [dedup_raw_ids fold_right add_unique_id].
  - tauto.
  - destruct (in_raw_ids y (dedup_raw_ids ys)) eqn:Ein.
    + apply in_raw_ids_spec in Ein.
      rewrite IH in *; split; [intros H; right; exact H | intros [<- | H]; assumption].
    + cbn [In]; rewrite IH; tauto.
Qed.

Lemma dedup_raw_ids_nodup (xs : list raw_id) :
  NoDup (dedup_raw_ids xs).
Proof.
  induction xs as [| y ys IH]; cbn [dedup_raw_ids fold_right add_unique_id].
  - constructor.
  - destruct (in_raw_ids y (dedup_raw_ids ys)) eqn:Ein.
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
      (IId (ren_l p), INSTR_Op (mk_copy_exp (DTYPE_I 1) arg_dt arg_e), [])
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
        (base_code ++ [(IId rtmp, INSTR_Op (mk_copy_exp (DTYPE_I 1) dt (ren_exp ren_l op)), [])],
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
  induction n as [| n' IH]; intros [| x xs'] Hle; cbn in *; try lia; [reflexivity |].
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
  rewrite !map_app; cbn [List.map blk_id].
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
    unfold ren_b; apply lookup_ren_in_dom; [exact Hlen_b |].
    apply callee_block_ids_blk_id, Hbk. }
  assert (Hnd_callee_ren : NoDup (List.map (fun bk => ren_b (blk_id bk)) (blks callee_cfg))).
  { rewrite <- (map_map blk_id ren_b).
    apply nodup_map_inj_on; [exact Hcallee_nd |].
    intros b1 b2 Hb1 Hb2 Heq.
    apply in_map_iff in Hb1 as [bk1 [<- Hbk1]].
    apply in_map_iff in Hb2 as [bk2 [<- Hbk2]].
    eapply lookup_ren_inj_on;
      [exact Hlen_b | exact Hnd_bf
      | apply callee_block_ids_blk_id, Hbk1
      | apply callee_block_ids_blk_id, Hbk2
      | exact Heq]. }
  assert (Hpre_used : forall x, In x (List.map blk_id pre_blks) -> In x used_ids).
  { intros x Hx; apply Hcaller_in_used; rewrite Hcaller_split, map_app; apply in_or_app; left; exact Hx. }
  assert (Hcall_used : In (blk_id b_call) used_ids).
  { apply Hcaller_in_used; rewrite Hcaller_split, map_app; apply in_or_app; right; left; reflexivity. }
  assert (Hpost_used : forall x, In x (List.map blk_id post_blks) -> In x used_ids).
  { intros x Hx; apply Hcaller_in_used; rewrite Hcaller_split, map_app; apply in_or_app; right; right; exact Hx. }
  apply inl_nodup_app_intro; [exact Hnd_pre | |].
  - constructor.
    + intros Hin; apply in_app_or in Hin as [Hin | [<- | Hin]].
      * eapply Hdisj_used; [apply Hbf_in_af, Hren_in_bf, Hin | exact Hcall_used].
      * eapply Hdisj_used; [exact Hpb_in_af | exact Hcall_used].
      * contradiction.
    + apply inl_nodup_app_intro; [exact Hnd_callee_ren | |].
      * constructor; [| exact Hnd_post].
        intros Hin; eapply Hdisj_used; [exact Hpb_in_af | apply Hpost_used, Hin].
      * intros x Hx [<- | Hy].
        -- apply Hpb_not_bf, Hren_in_bf, Hx.
        -- eapply Hdisj_used; [apply Hbf_in_af, Hren_in_bf, Hx | apply Hpost_used, Hy].
  - intros x Hx Hin.
    cbn [In] in Hin; destruct Hin as [<- | Hin].
    + eapply Hdisj_pre_rest; [exact Hx | left; reflexivity].
    + apply in_app_or in Hin as [Hin | [<- | Hin]].
      * eapply Hdisj_used; [apply Hbf_in_af, Hren_in_bf, Hin | apply Hpre_used, Hx].
      * eapply Hdisj_used; [exact Hpb_in_af | apply Hpre_used, Hx].
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
  eapply (inl_find_block_nodup_in _ _ Hnd).
  unfold inline_site_in_caller; cbn [df_instrs blks].
  apply in_or_app; right; left; reflexivity.
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
  eapply (inl_find_block_nodup_in _ _ Hnd).
  unfold inline_site_in_caller; cbn [df_instrs blks].
  apply in_or_app; right; right; apply in_or_app; right; left; reflexivity.
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
    + contradiction.
    + set (rbk := remap_block_phis (blk_id b_call) post_bid bk).
      replace bid with (blk_id rbk) by (cbn; exact Hid).
      eapply (inl_find_block_nodup_in _ _ Hnd).
      unfold inline_site_in_caller; cbn [df_instrs blks].
      apply in_or_app; right; right; apply in_or_app; right; right; apply in_map, Hbk_post.
  - apply inl_find_block_not_in.
    pose proof (all_fresh_partition used_ids n_loc n_blk n_ret)
      as (_ & _ & Hlen_b & Hlen_r & _ & _).
    unfold inline_site_in_caller; cbn [df_instrs blks].
    rewrite !map_app; cbn [List.map blk_id].
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
        apply Hnin_bf; apply lookup_ren_in_dom; [exact Hlen_b | apply callee_block_ids_blk_id, Hbk].
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
    + intros Heq; apply Hne; eapply remap_pred_id_inj_not_new; eassumption.
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
  specialize (Hphis _ Hin).
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
    cbn [flat_map snd].
    rewrite (Hall (t, ex) (or_introl Logic.eq_refl)).
    f_equal; apply IHl; intros p Hp; apply Hall; right; exact Hp. }
  apply (AstLib.exp_ind T (fun e => exp_block_addresses (ren_exp ren_l e) = exp_block_addresses e));
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
  rewrite !flat_map_app; cbn [flat_map].
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
    revert rtmps; induction bks as [| bk tl IHbks]; intros [| r rs]; [reflexivity | reflexivity |].
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
  intros H; injection H as <- <- <- <-.
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
    match goal with Hnv : negb (dtyp_eqb DTYPE_Void DTYPE_Void) = true |- _ =>
      rewrite dtyp_eqb_refl in Hnv; discriminate Hnv
    end.
  - split; [apply Nat.eqb_eq; assumption |].
    split.
    + intros te pattrs Hin.
      match goal with Hfa : forallb _ call_args = true |- _ =>
        rewrite forallb_forall in Hfa; specialize (Hfa (te, pattrs) Hin)
      end.
      apply is_empty_list_spec in Hfa; exact Hfa.
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

(** * 7. Model-Semantics Preliminaries, Empty Memory Frame & Global Environment Invariant *)

Section InliningSemantics.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.

  (** ** 7A. Nested Induction Principles for [dvalue] and [exp] *)

  Fixpoint dvalue_ind_nested
    (P : @dvalue PaV -> Prop)
    (Hbase   : forall db, P (DVALUE_Base db))
    (Hstruct : forall pk fs, Forall P fs -> P (DVALUE_Struct pk fs))
    (Harray  : forall vc es, Forall P es -> P (DVALUE_Array vc es))
    (dv : @dvalue PaV) {struct dv} : P dv :=
    let fix list_ind (l : list (@dvalue PaV)) : Forall P l :=
      match l with
      | [] => Forall_nil P
      | x :: xs => Forall_cons x (dvalue_ind_nested P Hbase Hstruct Harray x) (list_ind xs)
      end
    in
    match dv with
    | DVALUE_Base db => Hbase db
    | DVALUE_Struct pk fs => Hstruct pk fs (list_ind fs)
    | DVALUE_Array vc es => Harray vc es (list_ind es)
    end.

  Fixpoint exp_denote_ind {T : Set}
    (P : exp T -> Prop)
    (Hident  : forall id, P (EXP_Ident id))
    (Hint    : forall x, P (EXP_Integer x))
    (Hfloat  : forall f, P (EXP_Float f))
    (Hbool   : forall b, P (EXP_Bool b))
    (Hnull   : P EXP_Null)
    (Hzero   : P EXP_Zero_initializer)
    (Hcstr   : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Cstring es))
    (Hundef  : P EXP_Undef)
    (Hpoison : P EXP_Poison)
    (Hstruct : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Struct es))
    (Hpstr   : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Packed_struct es))
    (Harr    : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Array es))
    (Hvec    : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Vector es))
    (Hibin   : forall iop dt e1 e2, P e1 -> P e2 -> P (OP_IBinop iop dt e1 e2))
    (Hicmp   : forall ss cmp dt e1 e2, P e1 -> P e2 -> P (OP_ICmp ss cmp dt e1 e2))
    (Hfbin   : forall fop fm dt e1 e2, P e1 -> P e2 -> P (OP_FBinop fop fm dt e1 e2))
    (Hfneg   : forall fm dt e1, P e1 -> P (OP_Fneg fm (dt, e1)))
    (Hfcmp   : forall cmp fm dt e1 e2, P e1 -> P e2 -> P (OP_FCmp cmp fm dt e1 e2))
    (Hconv   : forall ct tf e1 tt0, P e1 -> P (OP_Conversion ct tf e1 tt0))
    (Hgep    : forall fl dt1 dt2 ep idxs,
                 P ep -> Forall (fun te => P (snd te)) idxs ->
                 P (OP_GetElementPtr fl dt1 (dt2, ep) idxs))
    (Hextel  : forall t1 e1 t2 e2, P e1 -> P e2 -> P (OP_ExtractElement (t1, e1) (t2, e2)))
    (Hinsel  : forall t1 e1 t2 e2 t3 e3,
                 P e1 -> P e2 -> P e3 -> P (OP_InsertElement (t1, e1) (t2, e2) (t3, e3)))
    (Hshuf   : forall t1 e1 t2 e2 t3 e3,
                 P e1 -> P e2 -> P e3 -> P (OP_ShuffleVector (t1, e1) (t2, e2) (t3, e3)))
    (Hextv   : forall t1 e1 idxs, P e1 -> P (OP_ExtractValue (t1, e1) idxs))
    (Hinsv   : forall t1 e1 t2 e2 idxs,
                 P e1 -> P e2 -> P (OP_InsertValue (t1, e1) (t2, e2) idxs))
    (Hsel    : forall fm t1 e1 t2 e2 t3 e3,
                 P e1 -> P e2 -> P e3 -> P (OP_Select fm (t1, e1) (t2, e2) (t3, e3)))
    (Hfrz    : forall t1 e1, P e1 -> P (OP_Freeze (t1, e1)))
    (Hasm    : forall b1 b2 s1 s2 s3 s4, P (EXP_Asm b1 b2 s1 s2 s3 s4))
    (Hba     : forall f b, P (EXP_BlockAddress f b))
    (Hsplat  : forall t1 e1, P e1 -> P (EXP_Splat (t1, e1)))
    (Hmd_c   : forall t1 e1, P e1 -> P (EXP_Metadata (METADATA_Const (t1, e1))))
    (Hmd_o   : forall md,
                 (forall t1 e1, md <> METADATA_Const (t1, e1)) ->
                 P (EXP_Metadata md))
    (e : exp T) {struct e} : P e :=
    let fix texp_list_ind (l : list (T * exp T)) : Forall (fun te => P (snd te)) l :=
      match l with
      | [] => Forall_nil _
      | (t, ex) :: rest =>
          Forall_cons (t, ex)
            (exp_denote_ind P Hident Hint Hfloat Hbool Hnull Hzero Hcstr Hundef Hpoison
               Hstruct Hpstr Harr Hvec Hibin Hicmp Hfbin Hfneg Hfcmp Hconv Hgep
               Hextel Hinsel Hshuf Hextv Hinsv Hsel Hfrz Hasm Hba Hsplat Hmd_c Hmd_o ex)
            (texp_list_ind rest)
      end
    in
    let rec_e :=
      exp_denote_ind P Hident Hint Hfloat Hbool Hnull Hzero Hcstr Hundef Hpoison
        Hstruct Hpstr Harr Hvec Hibin Hicmp Hfbin Hfneg Hfcmp Hconv Hgep
        Hextel Hinsel Hshuf Hextv Hinsv Hsel Hfrz Hasm Hba Hsplat Hmd_c Hmd_o
    in
    match e with
    | EXP_Ident id => Hident id
    | EXP_Integer x => Hint x
    | EXP_Float f => Hfloat f
    | EXP_Bool b => Hbool b
    | EXP_Null => Hnull
    | EXP_Zero_initializer => Hzero
    | EXP_Cstring es => Hcstr es (texp_list_ind es)
    | EXP_Undef => Hundef
    | EXP_Poison => Hpoison
    | EXP_Struct es => Hstruct es (texp_list_ind es)
    | EXP_Packed_struct es => Hpstr es (texp_list_ind es)
    | EXP_Array es => Harr es (texp_list_ind es)
    | EXP_Vector es => Hvec es (texp_list_ind es)
    | OP_IBinop iop dt e1 e2 => Hibin iop dt e1 e2 (rec_e e1) (rec_e e2)
    | OP_ICmp ss cmp dt e1 e2 => Hicmp ss cmp dt e1 e2 (rec_e e1) (rec_e e2)
    | OP_FBinop fop fm dt e1 e2 => Hfbin fop fm dt e1 e2 (rec_e e1) (rec_e e2)
    | OP_Fneg fm (dt, e1) => Hfneg fm dt e1 (rec_e e1)
    | OP_FCmp cmp fm dt e1 e2 => Hfcmp cmp fm dt e1 e2 (rec_e e1) (rec_e e2)
    | OP_Conversion ct tf e1 tt0 => Hconv ct tf e1 tt0 (rec_e e1)
    | OP_GetElementPtr fl dt1 (dt2, ep) idxs =>
        Hgep fl dt1 dt2 ep idxs (rec_e ep) (texp_list_ind idxs)
    | OP_ExtractElement (t1, e1) (t2, e2) =>
        Hextel t1 e1 t2 e2 (rec_e e1) (rec_e e2)
    | OP_InsertElement (t1, e1) (t2, e2) (t3, e3) =>
        Hinsel t1 e1 t2 e2 t3 e3 (rec_e e1) (rec_e e2) (rec_e e3)
    | OP_ShuffleVector (t1, e1) (t2, e2) (t3, e3) =>
        Hshuf t1 e1 t2 e2 t3 e3 (rec_e e1) (rec_e e2) (rec_e e3)
    | OP_ExtractValue (t1, e1) idxs => Hextv t1 e1 idxs (rec_e e1)
    | OP_InsertValue (t1, e1) (t2, e2) idxs =>
        Hinsv t1 e1 t2 e2 idxs (rec_e e1) (rec_e e2)
    | OP_Select fm (t1, e1) (t2, e2) (t3, e3) =>
        Hsel fm t1 e1 t2 e2 t3 e3 (rec_e e1) (rec_e e2) (rec_e e3)
    | OP_Freeze (t1, e1) => Hfrz t1 e1 (rec_e e1)
    | EXP_Asm b1 b2 s1 s2 s3 s4 => Hasm b1 b2 s1 s2 s3 s4
    | EXP_BlockAddress f b => Hba f b
    | EXP_Splat (t1, e1) => Hsplat t1 e1 (rec_e e1)
    | EXP_Metadata md =>
        match md with
        | METADATA_Const (t1, e1) => Hmd_c t1 e1 (rec_e e1)
        | METADATA_Null => Hmd_o METADATA_Null (fun _ _ H => ltac:(discriminate H))
        | METADATA_Id id => Hmd_o (METADATA_Id id) (fun _ _ H => ltac:(discriminate H))
        | METADATA_Node mds => Hmd_o (METADATA_Node mds) (fun _ _ H => ltac:(discriminate H))
        | METADATA_Pair m1 m2 => Hmd_o (METADATA_Pair m1 m2) (fun _ _ H => ltac:(discriminate H))
        | METADATA_Debug s1 s2 => Hmd_o (METADATA_Debug s1 s2) (fun _ _ H => ltac:(discriminate H))
        | METADATA_File_info fi => Hmd_o (METADATA_File_info fi) (fun _ _ H => ltac:(discriminate H))
        end
    end.

  (** ** 7B. Fused Global Handler, [inl_mrec_ctx], and Attribute Reductions *)

  Lemma fused_global_prov_read_some (k : raw_id) (v : @dvalue PaV) (s : FusedS)
    (Hlk : Maps.lookup k (snd (snd s)) = Some v) :
    fused_global_prov (GlobalRead k) s ≅ Ret (s, v).
  Proof using.
    destruct s as [m [ls g]]; cbn [snd] in Hlk.
    unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref.
    cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
    rewrite Hlk, !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma fused_global_prov_read_none (k : raw_id) (s : FusedS)
    (Hlk : Maps.lookup k (snd (snd s)) = None) :
    exists (u : unit) (kf : void -> itree ProvBotE (FusedS * @dvalue PaV)),
      fused_global_prov (GlobalRead k) s ≅
      Vis (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (Throw u))))))) kf.
  Proof using.
    destruct s as [m [ls g]]; cbn [snd] in Hlk.
    unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref.
    cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
    rewrite Hlk.
    unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
    eexists _, _; rewrite !Eqit.bind_bind.
    cbn [subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    rewrite Eqit.bind_vis, unfold_translate; cbn [observe]; rewrite Eqit.bind_vis; reflexivity.
  Qed.

  Lemma fused_global_prov_write (k : raw_id) (v : @dvalue PaV)
    (m : state) (ls : @stack_frame PaV * stack) (g : global_env) :
    fused_global_prov (GlobalWrite k v) (m, (ls, g)) ≅
    Ret ((m, (ls, Maps.add k v g)), tt).
  Proof using.
    unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref.
    cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
    rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Definition inl_mrec_ctx
    (fundefs : IntMap (@function_denotation PaV))
    : @CallE PaV ~> @CFGtop PaV :=
    fun T call_ev =>
      match call_ev with
      | Call dt cc fv args =>
          @ExtLib.Structures.Monad.bind (@CFGtop PaV) _ _ _ (EOU_to_itree (check_callee fv))
            (fun _ =>
               match lookup_defn fv fundefs with
               | Some f_den => f_den cc args
               | None => Functor.fmap inr (external_call dt fv args)
               end)
      end.

  Lemma denote_mcfg_eq_interp_mrec
    (fundefs : IntMap (@function_denotation PaV))
    (dt : dtyp) (fv : @dvalue PaV) (args : list (@dvalue PaV)) :
    denote_mcfg fundefs dt fv args =
    interp_mrec (inl_mrec_ctx fundefs) (inl_mrec_ctx fundefs _ (Call dt CC_Ccc fv args)).
  Proof using.
    unfold denote_mcfg, mrec; reflexivity.
  Qed.

  Lemma combine_lists_varargs_exact {A B : Type} (xs : list A) (ys : list B) :
    List.length xs = List.length ys ->
    combine_lists_varargs xs ys = raise_ret (combine xs ys, []).
  Proof using.
    revert ys; induction xs as [| x xs' IH]; intros [| y ys'] Hlen; try discriminate Hlen.
    - reflexivity.
    - cbn [List.length] in Hlen; injection Hlen as Hlen.
      cbn [combine_lists_varargs combine]; rewrite (IH ys' Hlen); reflexivity.
  Qed.

  Lemma init_local_env_lookup_in (bs : list (local_id * @dvalue PaV)) (x : local_id) (v : @dvalue PaV) :
    Maps.lookup x (init_local_env bs) = Some v ->
    In (x, v) bs.
  Proof using.
    induction bs as [| [k dv] rest IH]; cbn [init_local_env fold_right].
    - rewrite PassCommon.lookup_empty; discriminate.
    - destruct (RawIDOrd.eq_dec k x) as [-> | Hne].
      + rewrite PassCommon.lookup_add_eq; intros H; injection H as <-; left; reflexivity.
      + rewrite PassCommon.lookup_add_neq by exact Hne; intros H; right; apply IH, H.
  Qed.

  Lemma init_local_env_nodup_lookup (xs : list local_id) (ys : list (@dvalue PaV))
    (x : local_id) (v : @dvalue PaV)
    (Hnd : NoDup xs)
    (Hlen : List.length xs = List.length ys)
    (Hin : In (x, v) (combine xs ys)) :
    Maps.lookup x (init_local_env (combine xs ys)) = Some v.
  Proof using.
    revert ys Hlen Hin; induction Hnd as [| a xs' Hnin _ IH];
      intros [| b ys'] Hlen Hin; try discriminate Hlen; [contradiction |].
    cbn [List.length] in Hlen; injection Hlen as Hlen.
    cbn [combine init_local_env fold_right In] in *.
    destruct Hin as [Heq | Hin].
    - injection Heq as -> ->; apply PassCommon.lookup_add_eq.
    - assert (Hne : a <> x).
      { intros ->; apply Hnin; eapply in_combine_l; exact Hin. }
      rewrite PassCommon.lookup_add_neq by exact Hne.
      apply IH; assumption.
  Qed.

  Lemma existsb_false_forall {A : Type} (p : A -> bool) (xs : list A) :
    (forall x, In x xs -> p x = false) ->
    existsb p xs = false.
  Proof using.
    induction xs as [| x xs' IH]; intros H; [reflexivity |].
    cbn [existsb]; rewrite (H x (or_introl Logic.eq_refl)), IH; [reflexivity |].
    intros y Hy; apply H; right; exact Hy.
  Qed.

  Lemma value_attrs_poison_nil (v : @dvalue PaV) :
    value_attrs_poison [] v = v.
  Proof using.
    unfold value_attrs_poison, value_attr_nofpclass, value_attr_range,
           value_attr_align, value_attr_nonnull.
    destruct v as [[p | | | | | | |] | |]; reflexivity.
  Qed.

  Lemma apply_value_attrs_nil (msg : string) (v : @dvalue PaV) :
    apply_value_attrs [] msg v = raise_ret v.
  Proof using.
    unfold apply_value_attrs; rewrite value_attrs_poison_nil; reflexivity.
  Qed.

  Lemma apply_attrs_nil_eq {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{MemoryE -< E}
    (msg : string) (v : @dvalue PaV) :
    apply_attrs [] msg v ≅ Ret v.
  Proof using.
    unfold apply_attrs, assert_attrs_dereferenceable; rewrite apply_value_attrs_nil.
    cbn [EOU_to_itree find_option ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma apply_args_attrs_all_nil_eq {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{MemoryE -< E}
    (attrss : list (list param_attr)) (msg : string) (args : list (@dvalue PaV))
    (Hnil : forallb is_empty_list attrss = true) :
    apply_args_attrs attrss msg args ≅ Ret args.
  Proof using.
    revert attrss Hnil; induction args as [| v vs IH]; intros attrss Hnil; cbn [apply_args_attrs].
    - reflexivity.
    - destruct attrss as [| a rest].
      + cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        rewrite apply_attrs_nil_eq, Eqit.bind_ret_l, (IH [] Logic.eq_refl), Eqit.bind_ret_l.
        reflexivity.
      + cbn [forallb] in Hnil; apply andb_prop in Hnil as [Ha Hrest].
        apply is_empty_list_spec in Ha; subst a.
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        rewrite apply_attrs_nil_eq, Eqit.bind_ret_l, (IH rest Hrest), Eqit.bind_ret_l.
        reflexivity.
  Qed.

  Lemma check_cconv_eq_true (fcc cc : cconv) (fname : string) :
    cconv_eqb cc fcc = true ->
    @check_cconv PaV fcc cc fname = raise_ret tt.
  Proof using.
    intros H; unfold check_cconv; rewrite H; reflexivity.
  Qed.

  Lemma check_call_result_safe_inr (fattrs : list fn_attr) (msg : string)
    (args : list (@dvalue PaV)) (v : @dvalue PaV)
    (Hsafe : forallb is_safe_fn_attr fattrs = true) :
    check_call_result fattrs msg args (inr v) = raise_ret tt.
  Proof using.
    unfold check_call_result.
    rewrite forallb_forall in Hsafe.
    assert (Hnr : existsb fn_attr_is_noreturn fattrs = false).
    { apply existsb_false_forall; intros fa Hfa.
      specialize (Hsafe fa Hfa); unfold is_safe_fn_attr in Hsafe.
      apply andb_prop in Hsafe as [H1 _]; apply negb_true_iff in H1; exact H1. }
    assert (Hnc : existsb fn_attr_is_nocreateundeforpoison fattrs = false).
    { apply existsb_false_forall; intros fa Hfa.
      specialize (Hsafe fa Hfa); unfold is_safe_fn_attr in Hsafe.
      apply andb_prop in Hsafe as [_ H2]; apply negb_true_iff in H2; exact H2. }
    rewrite Hnr, Hnc; reflexivity.
  Qed.

  Lemma check_call_return_safe_inr_eq {E}
    `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{MemoryE -< E}
    (fattrs : list fn_attr) (loc : string)
    (args : list (@dvalue PaV)) (v : @dvalue PaV)
    (Hsafe : forallb is_safe_fn_attr fattrs = true) :
    check_call_return fattrs [] None loc args (inr v) ≅ Ret (inr v).
  Proof using.
    unfold check_call_return; rewrite (check_call_result_safe_inr fattrs loc args v Hsafe).
    cbn [EOU_to_itree value_metadata_range ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l, apply_attrs_nil_eq, Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma check_callee_nonnull_ptr (p : @ptr PaV)
    (Hnn : (ptr_to_int p > 0)%Z) :
    check_callee (DVALUE_Base (DVALUE_Pointer p)) = raise_ret tt.
  Proof using.
    unfold check_callee.
    assert (Hnull : ptr_to_int (@null PaV) = 0%Z).
    { cbn [ptr_to_int null PointerV fst]; apply to_Z_0. }
    rewrite Hnull.
    destruct (Z.eqb_spec (ptr_to_int p) 0%Z) as [Heq | _]; [lia | reflexivity].
  Qed.

  Lemma intrinsic_exp_global_none (gid : function_id) :
    lookup_intrinsic_declaration gid = None ->
    intrinsic_exp (T := dtyp) (EXP_Ident (ID_Global gid)) = None.
  Proof using.
    intros Hnone; destruct gid as [s | |]; cbn [intrinsic_exp];
      [rewrite Hnone; reflexivity | reflexivity | reflexivity].
  Qed.

  Lemma denote_operand_bundles_nil_eq (loc : string) (f : exp dtyp) :
    @denote_operand_bundles PaV loc f [] ≅ Ret tt.
  Proof using.
    unfold denote_operand_bundles; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma inl_withCall_ret {R : Type} (x : R) :
    @withCall PaV R (Ret x) ≅ Ret x.
  Proof using.
    unfold withCall; apply translate_ret.
  Qed.

  Lemma inl_withCall_bind {A B : Type}
    (t : @MCFGtop PaV A) (k : A -> @MCFGtop PaV B) :
    @withCall PaV B (ITree.bind t k) ≅
    ITree.bind (@withCall PaV A t) (fun x => @withCall PaV B (k x)).
  Proof using.
    unfold withCall; apply translate_bind.
  Qed.

  (** ** 7C. Empty Stack-Frame Memory Simulation ([push_empty_frame]) *)

  Definition push_empty_frame (σ : state) : state :=
    {| state_memory_stack :=
         {| Memory_stack_memory      := σ.(state_memory_stack).(Memory_stack_memory);
            Memory_stack_frame_stack := Snoc σ.(state_memory_stack).(Memory_stack_frame_stack) [];
            Memory_stack_heap        := σ.(state_memory_stack).(Memory_stack_heap) |};
       state_provenance := σ.(state_provenance) |}.

  Lemma mempush_empty_frame (σ : state) :
    memM_interp_prov (handle_memoryM MemPush) σ = Ret (push_empty_frame σ, tt).
  Proof using.
    reflexivity.
  Qed.

  Lemma mempop_empty_frame (σ : state) :
    memM_interp_prov (handle_memoryM MemPop) (push_empty_frame σ) = Ret (σ, tt).
  Proof using.
    destruct σ as [[mem fs hp] pr]; reflexivity.
  Qed.

  Lemma store_zero_struct_noop (varg : @ptr PaV) (σ : state) :
    memM_interp_prov
      (handle_memoryM
         (Store (DTYPE_Struct true [])
            (DVALUE_Base (DVALUE_Pointer varg))
            (DVALUE_Struct true [])))
      σ = Ret (σ, tt).
  Proof using.
    reflexivity.
  Qed.

  Definition is_callee_sync_mem {X : Type} (me : @MemoryE PaV X) : bool :=
    match me with
    | MemPush => false
    | MemPop => false
    | Alloca dt n al =>
        dtyp_eqb dt (DTYPE_Struct true []) && N.eqb n 1%N &&
        match al with None => true | Some _ => false end
    | Load _ _ => true
    | Store _ _ _ => true
    | Conv _ _ _ _ => true
    end.

  Definition inl_mcfg_event_post {X : Type} (e : @MCFGEtop PaV X) (a : X) : Prop :=
    match e in (_ +' _) Y return Y -> Prop with
    | inl1 _ => fun _ => True
    | inr1 e1 =>
        match e1 in (_ +' _) Y return Y -> Prop with
        | inl1 _ => fun _ => True
        | inr1 e2 =>
            match e2 in (_ +' _) Y return Y -> Prop with
            | inl1 _ => fun _ => True
            | inr1 e3 =>
                match e3 in (_ +' _) Y return Y -> Prop with
                | inl1 _ => fun _ => True
                | inr1 e4 =>
                    match e4 in (_ +' _) Y return Y -> Prop with
                    | inl1 me =>
                        match me in MemoryE Y return Y -> Prop with
                        | Alloca _ _ _ =>
                            fun dv => exists p, dv = DVALUE_Base (DVALUE_Pointer p)
                        | _ => fun _ => True
                        end
                    | inr1 _ => fun _ => True
                    end
                end
            end
        end
    end a.

  Definition inl_cfg_event_post {X : Type} (e : @CFGEtop PaV X) (a : X) : Prop :=
    match e in (_ +' _) Y return Y -> Prop with
    | inl1 _ => fun _ => True
    | inr1 m => inl_mcfg_event_post m
    end a.

  Lemma handle_memoryM_inl_post {X : Type} (me : @MemoryE PaV X) :
    memM_all_ret
      (match me in MemoryE Y return Y -> Prop with
       | Alloca _ _ _ => fun dv => exists p, dv = DVALUE_Base (DVALUE_Pointer p)
       | _ => fun _ => True
       end)
      (handle_memoryM me).
  Proof using.
    destruct me as [| | t n al | dt a | dt a v | cv tf v tt0]; cbn [handle_memoryM];
      try apply memM_all_ret_true.
    eapply memM_all_ret_bind; [apply memM_all_ret_true |].
    intros p _; exists p; reflexivity.
  Qed.

  (** Relational lift on [memM] relating execution on [push_empty_frame σ] vs [σ]. *)
  Definition memM_rel_empty {X : Type} (P : X -> Prop)
    (m1 m2 : @memM PaV _ X) : Prop :=
    forall (σ : state) (U : list N),
      refine_prov
        (fun _ '(σ1', r1) '(σ2', r2) =>
           σ1' = push_empty_frame σ2' /\ r1 = r2 /\ P r1)
        U
        (memM_interp_prov m1 (push_empty_frame σ))
        (memM_interp_prov m2 σ).

  Lemma memM_interp_prov_bind_eq {A B : Type}
    (m : @memM PaV _ A) (k : A -> @memM PaV _ B) (σ : state) :
    memM_interp_prov (ExtLib.Structures.Monad.bind m k) σ ≅
    ITree.bind (memM_interp_prov m σ) (fun '(σ', x) => memM_interp_prov (k x) σ').
  Proof using.
    revert σ; induction m as [x | s | s | s | g IH | σ' g IH | c g IH]; intros σ;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind memM_interp_prov].
    - rewrite Eqit.bind_ret_l; reflexivity.
    - unfold raiseOOM, trigger_cast; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    - unfold raiseUB, trigger_cast; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    - unfold raise, trigger_cast; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    - apply IH.
    - exact (IH tt σ').
    - destruct c as [sz al | |]; cbn [memM_interp_prov].
      + apply IH.
      + rewrite Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros p _ <-; apply IH].
      + apply IH.
  Qed.

  Lemma memM_rel_empty_ret {X : Type} (P : X -> Prop) (x : X) (Hx : P x) :
    memM_rel_empty P (ExtLib.Structures.Monad.ret x) (ExtLib.Structures.Monad.ret x).
  Proof using.
    intros σ U; pstep; apply RP_Step; cbn.
    split; [reflexivity | split; [reflexivity | exact Hx]].
  Qed.

  Lemma memM_rel_empty_bind {X Y : Type} (P : X -> Prop) (Q : Y -> Prop)
    (m1 m2 : @memM PaV _ X)
    (f1 f2 : X -> @memM PaV _ Y)
    (Hm : memM_rel_empty P m1 m2)
    (Hf : forall x, P x -> memM_rel_empty Q (f1 x) (f2 x)) :
    memM_rel_empty Q (ExtLib.Structures.Monad.bind m1 f1) (ExtLib.Structures.Monad.bind m2 f2).
  Proof using.
    intros σ U.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind_eq
      | symmetry; apply memM_interp_prov_bind_eq |].
    eapply refine_prov_bind; [apply Hm |].
    intros U' [σ1' x1] [σ2' x2] _ (-> & <- & Hx).
    apply (Hf x1 Hx).
  Qed.

  Lemma memM_rel_empty_lift {X : Type} (e : EOU X) :
    memM_rel_empty (fun _ => True)
      (Vellvm.Semantics.Interfaces.Memory.lift e)
      (Vellvm.Semantics.Interfaces.Memory.lift e).
  Proof using.
    intros σ U; destruct e as [s | s | s | x]; cbn.
    - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn; left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn; left; reflexivity.
    - unfold raise, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn;
        right; right; split; [exact I | intros [] [] _].
    - pstep; apply RP_Step; cbn; auto.
  Qed.

  Lemma memM_rel_empty_mub {X : Type} (P : X -> Prop) (msg : string) :
    memM_rel_empty P (mub msg) (mub msg).
  Proof using.
    intros σ U; cbn; unfold raiseUB, trigger_cast, ITree.trigger.
    pstep; apply RP_Step; cbn; left; reflexivity.
  Qed.

  Lemma memM_rel_empty_merr {X : Type} (P : X -> Prop) (msg : string) :
    memM_rel_empty P (merr msg) (merr msg).
  Proof using.
    intros σ U; cbn; unfold raise, trigger_cast, ITree.trigger.
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma memM_rel_empty_read_byte (p : @ptr PaV) :
    memM_rel_empty (fun _ => True) (read_byte p) (read_byte p).
  Proof using.
    intros σ U; cbn [read_byte MemoryModelPrimitivesV].
    unfold Read_byte, read_byte_raw, get;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
           state_get_memory MemoryModelStateV push_empty_frame Memory_stack_memory].
    destruct (read_byte_raw_mem (Memory_stack_memory (state_memory_stack σ)) (ptr_to_int p))
      as [[b aid] |]; cbn.
    - destruct (access_allowed (ptr_provenance p) aid); cbn.
      + pstep; apply RP_Step; cbn; auto.
      + unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn; left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn; left; reflexivity.
  Qed.

  Lemma memM_rel_empty_write_byte (p : @ptr PaV) (mb : @memory_byte PaV) :
    memM_rel_empty (fun _ => True) (write_byte p mb) (write_byte p mb).
  Proof using.
    intros σ U; cbn [write_byte MemoryModelPrimitivesV].
    unfold Write_byte, read_byte_raw, set_byte_raw, get_mem, upd_mem, app_mem, get, put;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
           state_get_memory MemoryModelStateV push_empty_frame Memory_stack_memory].
    destruct (read_byte_raw_mem (Memory_stack_memory (state_memory_stack σ)) (ptr_to_int p))
      as [[b aid] |]; cbn.
    - destruct (access_allowed (ptr_provenance p) aid); cbn.
      + pstep; apply RP_Step; cbn; unfold push_empty_frame; cbn; auto.
      + unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn; left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn; left; reflexivity.
  Qed.

  Lemma memM_rel_empty_map_monad_acc {A B : Type} (f : A -> @memM PaV _ B) (xs : list A)
    (Hf : forall a, memM_rel_empty (fun _ => True) (f a) (f a)) :
    memM_rel_empty (fun _ => True) (map_monad_acc f xs) (map_monad_acc f xs).
  Proof using.
    unfold map_monad_acc.
    assert (Hgo :
      forall (ys : list A) (acc : list B),
        memM_rel_empty (fun _ => True)
          ((fix loop (acc0 : list B) (l : list A) : @memM PaV _ (list B) :=
              match l with
              | [] => ExtLib.Structures.Monad.ret (rev_append acc0 [])
              | a :: l' => ExtLib.Structures.Monad.bind (f a) (fun b => loop (b :: acc0) l')
              end) acc ys)
          ((fix loop (acc0 : list B) (l : list A) : @memM PaV _ (list B) :=
              match l with
              | [] => ExtLib.Structures.Monad.ret (rev_append acc0 [])
              | a :: l' => ExtLib.Structures.Monad.bind (f a) (fun b => loop (b :: acc0) l')
              end) acc ys)).
    { induction ys as [| a ys' IH]; intros acc.
      - apply memM_rel_empty_ret, I.
      - eapply memM_rel_empty_bind; [apply Hf | intros b _; apply IH]. }
    apply Hgo.
  Qed.

  Lemma memM_rel_empty_map_monad {A B : Type} (f : A -> @memM PaV _ B) (xs : list A)
    (Hf : forall a, memM_rel_empty (fun _ => True) (f a) (f a)) :
    memM_rel_empty (fun _ => True) (map_monad f xs) (map_monad f xs).
  Proof using.
    induction xs as [| a xs' IH]; cbn [map_monad].
    - apply memM_rel_empty_ret, I.
    - eapply memM_rel_empty_bind; [apply Hf | intros b _].
      eapply memM_rel_empty_bind; [exact IH | intros bs _; apply memM_rel_empty_ret, I].
  Qed.

  Lemma memM_rel_empty_loop_monad {A : Type} (f : A -> @memM PaV _ unit) (xs : list A)
    (Hf : forall a, memM_rel_empty (fun _ => True) (f a) (f a)) :
    memM_rel_empty (fun _ => True) (loop_monad f xs) (loop_monad f xs).
  Proof using.
    induction xs as [| a xs' IH]; cbn [loop_monad].
    - apply memM_rel_empty_ret, I.
    - eapply memM_rel_empty_bind; [apply Hf | intros [] _; exact IH].
  Qed.

  Lemma memM_rel_empty_convert_impure_base
    (ct : impure_conversion) (tf : dtyp_base) (dv : @dvalue_base PaV) (tt0 : dtyp_base) :
    memM_rel_empty (fun _ => True)
      (convert_impure_base ct tf dv tt0)
      (convert_impure_base ct tf dv tt0).
  Proof using.
    unfold convert_impure_base.
    destruct ct.
    - eapply memM_rel_empty_bind.
      + unfold assert_inttoptr_types_ok;
          destruct tf, tt0; try apply memM_rel_empty_mub; apply memM_rel_empty_ret, I.
      + intros [] _; destruct dv; apply memM_rel_empty_lift.
    - destruct dv, tt0; try apply memM_rel_empty_mub; apply memM_rel_empty_lift.
    - destruct dv, tt0; try apply memM_rel_empty_mub; apply memM_rel_empty_lift.
    - apply memM_rel_empty_merr.
  Qed.

  Lemma memM_rel_empty_zero_alloca :
    memM_rel_empty
      (fun dv => exists p, dv = DVALUE_Base (DVALUE_Pointer p))
      (handle_memoryM (Alloca (DTYPE_Struct true []) 1%N None))
      (handle_memoryM (Alloca (DTYPE_Struct true []) 1%N None)).
  Proof using.
    cbn [handle_memoryM]; unfold allocate_dtyp.
    change (dtyp_eqb (DTYPE_Struct true []) DTYPE_Void) with false.
    change (concat_acc (repeatN 1%N (generate_poison_bytes (DTYPE_Struct true []))))
      with ([] : list (@memory_byte PaV)).
    set (al := preferred_alignment (dtyp_alignment (DTYPE_Struct true []))).
    eapply memM_rel_empty_bind with (P := fun _ => True);
      [| intros p _; apply memM_rel_empty_ret; exists p; reflexivity].
    intros σ U.
    unfold allocate_bytes, fresh_prov; cbn [allocate_bytes_with_pr MemoryModelPrimitivesV].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind memM_interp_prov].
    pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
    right; right; intros pr _.
    left; eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    change {| state_memory_stack := state_memory_stack (push_empty_frame σ);
              state_provenance   := pr |}
      with (push_empty_frame {| state_memory_stack := state_memory_stack σ;
                                state_provenance   := pr |}).
    set (σ' := {| state_memory_stack := state_memory_stack σ; state_provenance := pr |}).
    unfold Allocate_bytes_with_pr, get_free_block, next_key.
    change (N.length ([] : list (@memory_byte PaV))) with 0%N.
    eapply (memM_rel_empty_bind (fun '(_, ptrs) => ptrs = []) (fun _ => True)).
    - eapply memM_rel_empty_bind with (P := fun _ => True).
      + intros σ0 U0; cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
                           push_empty_frame Memory_stack_memory].
        pstep; apply RP_Step; cbn; auto.
      + intros addr _.
        eapply memM_rel_empty_bind; [apply memM_rel_empty_lift | intros p _].
        change (get_consecutive_ptrs p 0%N) with (@raise_ret (list (@ptr PaV)) []).
        cbn [Vellvm.Semantics.Interfaces.Memory.lift EOU_monad ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret].
        apply memM_rel_empty_ret; reflexivity.
    - intros [p ptrs] ->.
      eapply memM_rel_empty_bind with (P := fun _ => True); [| intros [] _; apply memM_rel_empty_ret, I].
      unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem,
             app_mem_stack, get, put.
      intros σ0 U0; destruct σ0 as [[mem0 fs0 hp0] pr0].
      change (memory_bytes_to_bytes (provenance_to_allocation_id pr) []) with ([] : list byte).
      cbn [add_all_index_acc add_all_to_frame fold_left ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret
           memM_interp_prov push_empty_frame state_get_memory MemoryModelStateV Memory_stack_memory].
      pstep; apply RP_Step; cbn; auto.
  Qed.

  Lemma handle_memoryM_empty_frame {X : Type} (me : @MemoryE PaV X)
    (Hok : is_callee_sync_mem me = true) :
    memM_rel_empty
      (match me in MemoryE Y return Y -> Prop with
       | Alloca _ _ _ => fun dv => exists p, dv = DVALUE_Base (DVALUE_Pointer p)
       | _ => fun _ => True
       end)
      (handle_memoryM me)
      (handle_memoryM me).
  Proof using.
    destruct me as [| | dt n al | dt a | dt a v | ct tf v tt0];
      try discriminate Hok.
    - cbn [is_callee_sync_mem] in Hok.
      apply andb_prop in Hok as [Hok Hal].
      apply andb_prop in Hok as [Hdt Hn].
      apply dtyp_eqb_spec in Hdt; apply N.eqb_eq in Hn.
      destruct al; [discriminate Hal |].
      subst dt n; apply memM_rel_empty_zero_alloca.
    - cbn [handle_memoryM].
      destruct a as [[p | | | | | | |] | |]; try apply memM_rel_empty_mub.
      unfold read_dvalue, read_bytes.
      eapply memM_rel_empty_bind.
      + eapply memM_rel_empty_bind; [apply memM_rel_empty_lift |].
        intros ptrs _; apply memM_rel_empty_map_monad_acc, memM_rel_empty_read_byte.
      + intros bytes _; apply memM_rel_empty_lift.
    - cbn [handle_memoryM].
      destruct a as [[p | | | | | | |] | |]; try apply memM_rel_empty_mub.
      unfold write_dvalue, write_bytes.
      eapply memM_rel_empty_bind; [apply memM_rel_empty_lift |].
      intros bytes _.
      eapply memM_rel_empty_bind; [apply memM_rel_empty_lift |].
      intros ptrs _.
      apply memM_rel_empty_loop_monad.
      intros [p' mb]; apply memM_rel_empty_write_byte.
    - cbn [handle_memoryM]; unfold convert_impure.
      destruct v as [db | pk fs | vc es]; try apply memM_rel_empty_merr.
      + destruct (get_base_conversion_type tf tt0) as [[tf' tt'] |]; [| apply memM_rel_empty_merr].
        cbn [Functor.fmap Functor_Monad].
        eapply memM_rel_empty_bind; [apply memM_rel_empty_convert_impure_base |].
        intros db' _; apply memM_rel_empty_ret, I.
      + destruct vc; [| apply memM_rel_empty_merr].
        destruct (get_vector_conversion_type tf tt0) as [[tf' tt'] |]; [| apply memM_rel_empty_merr].
        eapply memM_rel_empty_bind; [apply memM_rel_empty_lift |].
        intros es' _.
        eapply memM_rel_empty_bind.
        * apply memM_rel_empty_map_monad; intros db'; apply memM_rel_empty_convert_impure_base.
        * intros val _; apply memM_rel_empty_ret, I.
  Qed.

  (** ** 7D. Address Monotonicity & [build_global_environment] Hoare Postcondition *)

  Lemma next_key_with_alignment_ge_1 {A : Type} (m : IntMap A) (align : N) :
    (next_key_with_alignment m align >= 1)%Z.
  Proof using.
    unfold next_key_with_alignment, Vellvm.Semantics.Handlers.Memory.pad_to.
    destruct (IM_greatest_key m) as [gk |]; lia.
  Qed.

  Lemma next_key_with_alignment_gt_in {A : Type} (m : IntMap A) (align : N) (k : Z) :
    IM.In k m ->
    (k < next_key_with_alignment m align)%Z.
  Proof using.
    intros Hin.
    destruct (IM_greatest_key_In' m k Hin) as [gk Hgk].
    pose proof (IM_greatest_key_lt m gk Hgk) as Hlt.
    unfold IM.In in Hin; apply IM.Raw.Proofs.In_alt in Hin.
    red in Hlt; specialize (Hlt k Hin); unfold IM.E.lt in Hlt.
    unfold next_key_with_alignment, Vellvm.Semantics.Handlers.Memory.pad_to.
    rewrite Hgk.
    destruct (Z_le_gt_dec 0 gk) as [Hpos | Hneg].
    - assert (Hz : Z.of_N (1 + Z.to_N gk)%N = (1 + gk)%Z) by (rewrite N2Z.inj_add, Z2N.id; lia).
      lia.
    - assert (Hz : Z.to_N gk = 0%N) by lia.
      rewrite Hz; lia.
  Qed.

  Lemma IM_In_add_all_index_acc {A : Type} (vs : list A) (base k : Z) (m : IntMap A) :
    (IM.In k m \/ (base <= k < base + Z.of_nat (List.length vs))%Z) ->
    IM.In k (add_all_index_acc vs base m).
  Proof using.
    revert base m; induction vs as [| v tl IH]; intros base m Hk; cbn [add_all_index_acc List.length].
    - destruct Hk as [Hin | Hlt]; [exact Hin | lia].
    - apply IH.
      destruct Hk as [Hin | Hlt].
      + left; unfold add; apply IntMaps.IP.F.add_in_iff; right; exact Hin.
      + destruct (Z.eq_dec k base) as [-> | Hne].
        * left; unfold add; apply IntMaps.IP.F.add_in_iff; left; reflexivity.
        * right; lia.
  Qed.

  Definition model_hoare {R : Type} (P : FusedS -> Prop) (u : @MCFGtop PaV R)
    (Q : FusedS -> R -> Prop) : Prop :=
    forall (s : FusedS) (U : list N),
      P s ->
      refine_prov
        (fun _ '(s1, r1) '(s2, r2) => s1 = s2 /\ r1 = r2 /\ Q s1 r1)
        U (interp_mcfg_model u s) (interp_mcfg_model u s).

  Lemma interp_mcfg_model_ret_eq {R : Type} (x : R) (s : FusedS) :
    interp_mcfg_model (Ret x) s ≅ Ret (s, x).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_mcfg_model_bind_eq {A B : Type}
    (t : @MCFGtop PaV A) (k : A -> @MCFGtop PaV B) (s : FusedS) :
    interp_mcfg_model (ITree.bind t k) s ≅
    ITree.bind (interp_mcfg_model t s) (fun '(s', x) => interp_mcfg_model (k x) s').
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_bind, interp_state_bind; reflexivity.
  Qed.

  Lemma interp_mcfg_model_non_intr_eq {X : Type}
    (me : @MCFGEtop PaV X) (s : FusedS)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_mcfg_model (ITree.trigger me) s ≅
    ITree.bind (interp_vellvm_prov_h me s)
      (fun '(s', x) => Tau (Tau (Ret (s', x)))).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics, ITree.trigger.
    rewrite unfold_interp; cbn [_interp observe]; rewrite Hni.
    unfold ITree.trigger; rewrite Eqit.bind_vis, interp_state_vis.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' x] _ <-.
    rewrite Eqit.bind_ret_l, interp_tau, interp_ret, interp_state_tau, interp_state_ret.
    reflexivity.
  Qed.

  Lemma model_hoare_ret {R : Type} (P : FusedS -> Prop) (Q : FusedS -> R -> Prop) (x : R)
    (Hx : forall s, P s -> Q s x) :
    model_hoare P (Ret x) Q.
  Proof using.
    intros s U Hs.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_ret_eq
      | symmetry; apply interp_mcfg_model_ret_eq |].
    pstep; apply RP_Step; cbn; split; [reflexivity | split; [reflexivity | apply Hx, Hs]].
  Qed.

  Lemma model_hoare_bind {A B : Type}
    (P : FusedS -> Prop) (Q : FusedS -> A -> Prop) (R : FusedS -> B -> Prop)
    (t : @MCFGtop PaV A) (k : A -> @MCFGtop PaV B)
    (Ht : model_hoare P t Q)
    (Hk : forall a, model_hoare (fun s => Q s a) (k a) R) :
    model_hoare P (ITree.bind t k) R.
  Proof using.
    intros s U Hs.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq
      | symmetry; apply interp_mcfg_model_bind_eq |].
    eapply refine_prov_bind; [apply Ht, Hs |].
    intros U' [s1 a1] [s2 a2] _ (-> & <- & HQ).
    apply (Hk a1 s2 U' HQ).
  Qed.

  Lemma model_hoare_weaken {R : Type}
    (P P' : FusedS -> Prop) (Q Q' : FusedS -> R -> Prop)
    (u : @MCFGtop PaV R)
    (HP : forall s, P' s -> P s)
    (HQ : forall s r, Q s r -> Q' s r)
    (Hu : model_hoare P u Q) :
    model_hoare P' u Q'.
  Proof using.
    intros s U Hs.
    eapply refine_prov_antitone with (U := U).
    - intros _ _ [s1 r1] [s2 r2] _ (-> & <- & Hq).
      split; [reflexivity | split; [reflexivity | apply HQ, Hq]].
    - apply incl_refl.
    - apply Hu, HP, Hs.
  Qed.

  Lemma model_hoare_loop_monad {A : Type} (I : FusedS -> Prop)
    (f : A -> @MCFGtop PaV unit) (xs : list A)
    (Hf : forall x, In x xs -> model_hoare I (f x) (fun s' _ => I s')) :
    model_hoare I (loop_monad f xs) (fun s' _ => I s').
  Proof using.
    induction xs as [| x xs' IH]; cbn [loop_monad].
    - apply model_hoare_ret; intros s Hs; exact Hs.
    - eapply model_hoare_bind; [apply (Hf x (or_introl Logic.eq_refl)) |].
      intros []; apply IH; intros y Hy; apply Hf; right; exact Hy.
  Qed.

  Lemma model_hoare_map_monad {A B : Type} (I : FusedS -> Prop)
    (f : A -> @MCFGtop PaV B) (xs : list A)
    (Hf : forall x, In x xs -> model_hoare I (f x) (fun s' _ => I s')) :
    model_hoare I (map_monad f xs) (fun s' _ => I s').
  Proof using.
    induction xs as [| x xs' IH]; cbn [map_monad].
    - apply model_hoare_ret; intros s Hs; exact Hs.
    - eapply model_hoare_bind; [apply (Hf x (or_introl Logic.eq_refl)) |].
      intros b; eapply model_hoare_bind.
      + apply IH; intros y Hy; apply Hf; right; exact Hy.
      + intros bs; apply model_hoare_ret; intros s Hs; exact Hs.
  Qed.

  Lemma model_hoare_raise {R : Type} (P : FusedS -> Prop) (Q : FusedS -> R -> Prop) (msg : string) :
    model_hoare P (raise msg) Q.
  Proof using.
    intros s U _; unfold raise, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq | symmetry; apply interp_mcfg_model_bind_eq |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_mcfg_model_non_intr_eq _ s Logic.eq_refl); reflexivity
      | symmetry; rewrite (interp_mcfg_model_non_intr_eq _ s Logic.eq_refl); reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
    right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma model_hoare_raiseUB {R : Type} (P : FusedS -> Prop) (Q : FusedS -> R -> Prop) (msg : string) :
    model_hoare P (raiseUB msg) Q.
  Proof using.
    intros s U _; unfold raiseUB, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_mcfg_model_non_intr_eq _ s Logic.eq_refl); reflexivity
      | reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
  Qed.

  Lemma model_hoare_raiseOOM {R : Type} (P : FusedS -> Prop) (Q : FusedS -> R -> Prop) (msg : string) :
    model_hoare P (raiseOOM msg) Q.
  Proof using.
    intros s U _; unfold raiseOOM, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_mcfg_model_non_intr_eq _ s Logic.eq_refl); reflexivity
      | reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
  Qed.

  Lemma model_hoare_EOU {A : Type} (I : FusedS -> Prop) (m : EOU A) :
    model_hoare I (EOU_to_itree m) (fun s' _ => I s').
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply model_hoare_raiseOOM.
    - apply model_hoare_raiseUB.
    - apply model_hoare_raise.
    - apply model_hoare_ret; intros s Hs; exact Hs.
  Qed.

  Lemma refine_prov_tau2_ret {R1 R2 : Type} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (r1 : R1) (r2 : R2) (H : RR U r1 r2) :
    refine_prov RR U (Tau (Tau (Ret r1))) (Tau (Tau (Ret r2))).
  Proof using.
    pstep; eapply RP_TauL; [reflexivity |]; eapply RP_TauR; [reflexivity |].
    eapply RP_TauL; [reflexivity |]; eapply RP_TauR; [reflexivity |].
    apply RP_Step; cbn; exact H.
  Qed.

  Lemma model_hoare_non_intr_refl_preserve {X : Type}
    (I : FusedS -> Prop) (me : @MCFGEtop PaV X)
    (Hni : interp_intrinsics_h me = ITree.trigger me)
    (Hpres : forall s U,
               I s ->
               refine_prov
                 (fun _ '(s1, r1) '(s2, r2) => s1 = s2 /\ r1 = r2 /\ I s1)
                 U (interp_vellvm_prov_h me s) (interp_vellvm_prov_h me s)) :
    model_hoare I (ITree.trigger me) (fun s' _ => I s').
  Proof using.
    intros s U Hs.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr_eq, Hni
      | symmetry; apply interp_mcfg_model_non_intr_eq, Hni |].
    eapply refine_prov_bind; [apply Hpres, Hs |].
    intros U' [s1 r1] [s2 r2] _ (-> & <- & HI).
    apply refine_prov_tau2_ret; auto.
  Qed.

  Lemma model_hoare_memory_lsg_preserve {X : Type}
    (I : FusedS -> Prop) (me : @MemoryE PaV X)
    (Hlsg : forall m m' lsg, I (m, lsg) -> I (m', lsg)) :
    model_hoare I (ITree.trigger (subevent _ me)) (fun s' _ => I s').
  Proof using.
    apply model_hoare_non_intr_refl_preserve; [reflexivity |].
    intros [m lsg] U HI.
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_bind;
      [apply (memM_interp_prov_post _ (handle_memoryM me) (memM_all_ret_true _)) |].
    intros U' [m1 r1] [m2 r2] _ (-> & <- & _).
    pstep; apply RP_Step; cbn; split; [reflexivity | split; [reflexivity | eapply Hlsg, HI]].
  Qed.

  Lemma model_hoare_gread_preserve (I : FusedS -> Prop) (k : raw_id) :
    model_hoare I (gread k) (fun s' _ => I s').
  Proof using.
    unfold gread, trigger_cast.
    apply model_hoare_non_intr_refl_preserve; [reflexivity |].
    intros s U HI.
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    destruct (Maps.lookup k (snd (snd s))) as [v |] eqn:Elk.
    - eapply refine_prov_obs_eq;
        [symmetry; apply (fused_global_prov_read_some k v s Elk)
        | symmetry; apply (fused_global_prov_read_some k v s Elk) |].
      pstep; apply RP_Step; cbn; auto.
    - destruct (fused_global_prov_read_none k s Elk) as (u & kf & Ef).
      eapply refine_prov_obs_eq; [symmetry; exact Ef | symmetry; exact Ef |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma model_hoare_lread_preserve (I : FusedS -> Prop) (k : raw_id) :
    model_hoare I (lread k) (fun s' _ => I s').
  Proof using.
    unfold lread, trigger_cast.
    apply model_hoare_non_intr_refl_preserve; [reflexivity |].
    intros [m [[sf fstk] g]] U HI.
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    destruct (Maps.lookup k sf.(stack_vars)) as [v |] eqn:Elk.
    - eapply refine_prov_obs_eq;
        [symmetry; apply (fused_local_prov_read_some k v (m, ((sf, fstk), g)) Elk)
        | symmetry; apply (fused_local_prov_read_some k v (m, ((sf, fstk), g)) Elk) |].
      pstep; apply RP_Step; cbn; auto.
    - destruct (fused_local_prov_read_none k (m, ((sf, fstk), g)) Elk) as (msg & kf & Ef).
      eapply refine_prov_obs_eq; [symmetry; exact Ef | symmetry; exact Ef |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma model_hoare_draw_preserve (I : FusedS -> Prop) (dt : dtyp) :
    model_hoare I (draw dt) (fun s' _ => I s').
  Proof using.
    unfold draw, trigger_cast.
    apply model_hoare_non_intr_refl_preserve; [reflexivity |].
    intros s U HI.
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_draw_prov, handle_draw.
    destruct (default_dvalue_of_dtyp dt) as [msg | msg | msg | dv]; cbn [EOU_to_itree].
    - unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
    - unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn.
      right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
        | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
      pstep; apply RP_Step; cbn; auto.
  Qed.

  Lemma model_hoare_gwrite (P : FusedS -> Prop) (k : raw_id) (v : @dvalue PaV)
    (Q : FusedS -> unit -> Prop)
    (HQ : forall m ls g, P (m, (ls, g)) -> Q (m, (ls, Maps.add k v g)) tt) :
    model_hoare P (gwrite k v) Q.
  Proof using.
    intros [m [ls g]] U HP.
    unfold gwrite, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity
      | symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite fused_global_prov_write, Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite fused_global_prov_write, Eqit.bind_ret_l; reflexivity |].
    apply refine_prov_tau2_ret; split; [reflexivity | split; [reflexivity | apply HQ, HP]].
  Qed.

  Lemma model_hoare_freeze_preserve (I : FusedS -> Prop) (dv : @dvalue PaV) :
    forall dt : dtyp,
      model_hoare I (freeze dt dv) (fun s' _ => I s').
  Proof using.
    induction dv as [db | pk fs IHfs | vc es IHes] using dvalue_ind_nested; intros dt;
      unfold freeze.
    - destruct db as [| | | | | | | sz bv];
        try (cbn [Functor.fmap Functor_itree ITree.map ExtLib.Structures.Monad.ret Monad_itree];
             eapply model_hoare_weaken;
             [intros s Hs; exact Hs | intros s _ Hs; exact Hs |];
             intros s U Hs; eapply refine_prov_obs_eq;
             [symmetry; rewrite Eqit.bind_ret_l; apply interp_mcfg_model_ret_eq
             | symmetry; rewrite Eqit.bind_ret_l; apply interp_mcfg_model_ret_eq |];
             pstep; apply RP_Step; cbn; auto).
      + apply model_hoare_draw_preserve.
      + destruct bv as [bi | p ix | bits];
          try (cbn [freeze_base Functor.fmap Functor_itree ITree.map ExtLib.Structures.Monad.ret Monad_itree];
               intros s U Hs; eapply refine_prov_obs_eq;
               [symmetry; rewrite Eqit.bind_ret_l; apply interp_mcfg_model_ret_eq
               | symmetry; rewrite Eqit.bind_ret_l; apply interp_mcfg_model_ret_eq |];
               pstep; apply RP_Step; cbn; auto).
        cbn [freeze_base]; destruct (existsb is_poison_bit bits).
        * eapply model_hoare_bind; [apply model_hoare_draw_preserve |].
          intros x; apply model_hoare_ret; intros s Hs; exact Hs.
        * cbn [Functor.fmap Functor_itree ITree.map ExtLib.Structures.Monad.ret Monad_itree].
          intros s U Hs; eapply refine_prov_obs_eq;
            [symmetry; rewrite Eqit.bind_ret_l; apply interp_mcfg_model_ret_eq
            | symmetry; rewrite Eqit.bind_ret_l; apply interp_mcfg_model_ret_eq |];
            pstep; apply RP_Step; cbn; auto.
    - destruct dt as [| p dts |]; try apply model_hoare_raise.
      eapply model_hoare_bind; [| intros _; apply model_hoare_ret; intros s Hs; exact Hs].
      revert dts; generalize ([] : list (@dvalue PaV)) as acc.
      induction IHfs as [| f fs' Hf _ IH]; intros acc [| t ts];
        try apply model_hoare_raise.
      + apply model_hoare_ret; intros s Hs; exact Hs.
      + eapply model_hoare_bind; [apply (Hf t) | intros v; apply IH].
    - destruct dt as [| | v sz t]; try apply model_hoare_raise.
      eapply model_hoare_bind; [| intros _; apply model_hoare_ret; intros s Hs; exact Hs].
      generalize ([] : list (@dvalue PaV)) as acc.
      induction IHes as [| e es' He _ IH]; intros acc.
      + apply model_hoare_ret; intros s Hs; exact Hs.
      + eapply model_hoare_bind; [apply (He t) | intros v'; apply IH].
  Qed.

  Lemma model_hoare_denote_exp_lsg_preserve (I : FusedS -> Prop)
    (Hlsg : forall m m' lsg, I (m, lsg) -> I (m', lsg))
    (e : exp dtyp) :
    forall top : option dtyp,
      model_hoare I (denote_exp top e) (fun s' _ => I s').
  Proof using.
    induction e using exp_denote_ind; intros top; cbn [denote_exp];
      try (apply model_hoare_ret; intros s Hs; exact Hs);
      try (apply model_hoare_raise);
      try (destruct top; [apply model_hoare_EOU | apply model_hoare_raise]).
    - (* EXP_Ident *)
      destruct id as [gid | lid]; [apply model_hoare_gread_preserve | apply model_hoare_lread_preserve].
    - (* EXP_Bool *)
      destruct b; apply model_hoare_ret; intros s Hs; exact Hs.
    - (* EXP_Cstring *)
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros _; apply model_hoare_ret; auto].
    - (* EXP_Struct *)
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros _; apply model_hoare_ret; auto].
    - (* EXP_Packed_struct *)
      eapply model_hoare_bind; [apply model_hoare_EOU | intros _].
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros _; apply model_hoare_ret; auto].
    - (* EXP_Array *)
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros _; apply model_hoare_ret; auto].
    - (* EXP_Vector *)
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros _; apply model_hoare_ret; auto].
    - (* OP_IBinop *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [apply IHe2 | intros _; apply model_hoare_EOU].
    - (* OP_ICmp *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [apply IHe2 | intros _; apply model_hoare_EOU].
    - (* OP_FBinop *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [apply IHe2 | intros _; apply model_hoare_EOU].
    - (* OP_Fneg *)
      eapply model_hoare_bind; [apply IHe | intros _; apply model_hoare_EOU].
    - (* OP_FCmp *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [apply IHe2 | intros _; apply model_hoare_EOU].
    - (* OP_Conversion *)
      eapply model_hoare_bind; [apply IHe | intros dv].
      unfold convert; destruct ct as [| pct | ict].
      + destruct (dtyp_eqb tf tt0); [apply model_hoare_ret; auto |].
        destruct (bit_sizeof_dtyp tf =? bit_sizeof_dtyp tt0)%N;
          [apply model_hoare_EOU | apply model_hoare_raise].
      + apply model_hoare_EOU.
      + unfold conv; apply (model_hoare_memory_lsg_preserve I _ Hlsg).
    - (* OP_GetElementPtr *)
      eapply model_hoare_bind; [apply IHe | intros _].
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros _; apply model_hoare_EOU].
    - (* OP_ExtractElement *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [apply IHe2 | intros _; apply model_hoare_EOU].
    - (* OP_InsertElement *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [eapply model_hoare_bind; [apply IHe2 | intros _; apply model_hoare_EOU] | intros _].
      eapply model_hoare_bind; [apply IHe3 | intros _; apply model_hoare_EOU].
    - (* OP_ShuffleVector *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [apply IHe2 | intros _].
      eapply model_hoare_bind; [apply IHe3 | intros _; apply model_hoare_EOU].
    - (* OP_ExtractValue *)
      eapply model_hoare_bind; [apply IHe | intros _; apply model_hoare_EOU].
    - (* OP_InsertValue *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [apply IHe2 | intros _; apply model_hoare_EOU].
    - (* OP_Select *)
      eapply model_hoare_bind; [apply IHe1 | intros _].
      eapply model_hoare_bind; [apply IHe2 | intros _].
      eapply model_hoare_bind; [apply IHe3 | intros _; apply model_hoare_EOU].
    - (* OP_Freeze *)
      eapply model_hoare_bind; [apply IHe | intros dv; apply model_hoare_freeze_preserve].
    - (* EXP_BlockAddress *)
      apply model_hoare_gread_preserve.
    - (* EXP_Splat *)
      eapply model_hoare_bind; [apply model_hoare_EOU | intros [_sz _t]].
      eapply model_hoare_bind; [apply IHe | intros _; apply model_hoare_ret; auto].
    - (* EXP_Metadata (METADATA_Const) *)
      apply IHe.
    - (* EXP_Metadata (other) *)
      destruct md as [| | [t1 e1] | | | |];
        [| | exfalso; exact (H t1 e1 Logic.eq_refl) | | | |];
        apply model_hoare_ret; auto.
  Qed.

  (** Allocating one pointer slot (`alloca DTYPE_Pointer 1%N None`) yields a fresh
      positive address strictly greater than all previously allocated keys in [mem],
      and inserts that address into [mem']. *)
  Lemma model_hoare_alloca_fn_ptr (P : FusedS -> Prop) :
    model_hoare P (alloca (DTYPE_Base DTYPE_Pointer) 1%N None)
      (fun '(m', lsg') dv =>
         exists m0 p,
           P (m0, lsg') /\
           dv = DVALUE_Base (DVALUE_Pointer p) /\
           (ptr_to_int p >= 1)%Z /\
           IM.In (ptr_to_int p) (Memory_stack_memory (state_memory_stack m')) /\
           (forall k,
              IM.In k (Memory_stack_memory (state_memory_stack m0)) ->
              (k < ptr_to_int p)%Z /\
              IM.In k (Memory_stack_memory (state_memory_stack m')))).
  Proof using.
    intros [m0 lsg] U HP.
    unfold alloca; eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity
      | symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    cbn [handle_memoryM]; unfold allocate_dtyp.
    change (dtyp_eqb (DTYPE_Base DTYPE_Pointer) DTYPE_Void) with false.
    set (pbytes := concat_acc (repeatN 1%N (generate_poison_bytes (DTYPE_Base DTYPE_Pointer)))).
    set (al := preferred_alignment (dtyp_alignment (DTYPE_Base DTYPE_Pointer))).
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind_eq, Eqit.bind_bind; reflexivity
      | symmetry; rewrite memM_interp_prov_bind_eq, Eqit.bind_bind; reflexivity |].
    unfold allocate_bytes, fresh_prov; cbn [allocate_bytes_with_pr MemoryModelPrimitivesV].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind memM_interp_prov].
    pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
    right; right; intros pr _.
    left; eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    set (m_pr := {| state_memory_stack := state_memory_stack m0; state_provenance := pr |}).
    unfold Allocate_bytes_with_pr, get_free_block, next_key.
    set (aid := provenance_to_allocation_id pr).
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack m0)) al).
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind_eq, !Eqit.bind_bind; reflexivity
      | symmetry; rewrite memM_interp_prov_bind_eq, !Eqit.bind_bind; reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind_eq, !Eqit.bind_bind; reflexivity
      | symmetry; rewrite memM_interp_prov_bind_eq, !Eqit.bind_bind; reflexivity |].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_memory_stack].
    fold addr.
    unfold int_to_ptr; cbn [PointerV].
    destruct (from_Z addr) as [s | s | s | ip_a] eqn:Efz;
      cbn [EOU_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Vellvm.Semantics.Interfaces.Memory.lift
           memS_mon memS_bind memM_interp_prov].
    - unfold raiseOOM, trigger_cast, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - unfold raise, trigger_cast, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn;
        right; right; split; [exact I | intros [] [] _].
    - set (p := (ip_a, allocation_id_to_prov aid) : @ptr PaV).
      assert (Hp_addr : ptr_to_int p = addr).
      { cbn [ptr_to_int PointerV fst]; apply from_Z_to_Z, Efz. }
      destruct (get_consecutive_ptrs p (N.length pbytes)) as [s | s | s | ptrs] eqn:Ecptrs;
        cbn [Vellvm.Semantics.Interfaces.Memory.lift memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
      + unfold raiseOOM, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
      + unfold raiseUB, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
      + unfold raise, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn;
          right; right; split; [exact I | intros [] [] _].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem,
               app_mem_stack, get, put.
        destruct m0 as [[mem0 fs0 hp0] pr0].
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
             state_memory_stack state_get_memory MemoryModelStateV Memory_stack_memory].
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
        assert (Hmem_eq :
          forall (ks : list (@ptr PaV)) (ms : @Memory_stack PaV),
            Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms).
        { intros ks; induction ks as [| k0 ks' IHks]; intros [mm ss hh]; [reflexivity |].
          cbn [add_all_to_frame fold_left]; rewrite IHks; destruct ss; reflexivity. }
        apply refine_prov_tau2_ret.
        split; [reflexivity | split; [reflexivity |]].
        exists {| state_memory_stack := {| Memory_stack_memory := mem0;
                                           Memory_stack_frame_stack := fs0;
                                           Memory_stack_heap := hp0 |};
                  state_provenance := pr0 |}, p.
        split; [exact HP |].
        split; [reflexivity |].
        split; [rewrite Hp_addr; apply next_key_with_alignment_ge_1 |].
        rewrite Hmem_eq; cbn [Memory_stack_memory].
        assert (Hlen8 : List.length (memory_bytes_to_bytes aid pbytes) = 8%nat) by reflexivity.
        split.
        * apply IM_In_add_all_index_acc; right; rewrite Hlen8; lia.
        * intros k Hk.
          assert (Hk_lt : (k < ptr_to_int p)%Z).
          { rewrite Hp_addr; apply next_key_with_alignment_gt_in, Hk. }
          split; [exact Hk_lt | apply IM_In_add_all_index_acc; left; exact Hk].
  Qed.

  Definition decl_alloc_inv (seen : list (raw_id * Z)) (s : FusedS) : Prop :=
    let '(m, ((sf, fstk), g)) := s in
    sf.(stack_vars) = Maps.empty /\
    sf.(stack_exc) = None /\
    sf.(stack_loc) = None /\
    fstk = [] /\
    (forall x z,
       In (x, z) seen ->
       (z >= 1)%Z /\
       IM.In z (Memory_stack_memory (state_memory_stack m)) /\
       exists p : @ptr PaV,
         ptr_to_int p = z /\
         Maps.lookup x g = Some (DVALUE_Base (DVALUE_Pointer p))) /\
    (forall x v,
       Maps.lookup x g = Some v ->
       In x (List.map fst seen)) /\
    (forall x1 z1 x2 z2,
       In (x1, z1) seen ->
       In (x2, z2) seen ->
       x1 <> x2 ->
       z1 <> z2).

  Definition decl_loop_inv (prev_ds : list (declaration dtyp)) (s : FusedS) : Prop :=
    exists seen : list (raw_id * Z),
      incl (List.map fst seen) (List.map dc_name prev_ds) /\
      (forall d,
         In d prev_ds ->
         lookup_intrinsic_declaration (dc_name d) = None ->
         exists z, In (dc_name d, z) seen) /\
      decl_alloc_inv seen s.

  Lemma model_hoare_allocate_declarations_aux :
    forall (ds prev_ds : list (declaration dtyp)),
      NoDup (List.map dc_name (prev_ds ++ ds)) ->
      model_hoare (decl_loop_inv prev_ds) (allocate_declarations ds)
        (fun s' _ => decl_loop_inv (prev_ds ++ ds) s').
  Proof using.
    induction ds as [| d ds' IH]; intros prev_ds Hnd; unfold allocate_declarations; cbn [loop_monad].
    - rewrite app_nil_r; apply model_hoare_ret; intros s Hs; exact Hs.
    - assert (Hnot_prev : ~ In (dc_name d) (List.map dc_name prev_ds)).
      { rewrite map_app in Hnd; cbn [List.map] in Hnd.
        intros Hin; eapply (inl_nodup_app_disj _ _ Hnd); [exact Hin | left; reflexivity]. }
      assert (Hnd_next : NoDup (List.map dc_name ((prev_ds ++ [d]) ++ ds'))).
      { rewrite <- app_assoc; exact Hnd. }
      replace (prev_ds ++ d :: ds') with ((prev_ds ++ [d]) ++ ds')
        by (rewrite <- app_assoc; reflexivity).
      eapply model_hoare_bind; [| intros []; apply IH, Hnd_next].
      unfold allocate_declaration.
      destruct (lookup_intrinsic_declaration (dc_name d)) as [intr_fn |] eqn:Eintr.
      + apply model_hoare_ret; intros s (seen & Hincl & Hall & Hinv).
        exists seen; split; [| split; [| exact Hinv]].
        * intros x Hx; rewrite map_app; apply in_or_app; left; apply Hincl, Hx.
        * intros d0 Hd0 Hnone; apply in_app_or in Hd0 as [Hd0 | [<- | []]].
          -- apply Hall; assumption.
          -- congruence.
      + eapply model_hoare_bind; [apply model_hoare_alloca_fn_ptr | intros dv].
        apply model_hoare_gwrite.
        intros m' [[sf fstk] g0]
          (m0 & p & (seen & Hincl & Hall & Hinv) & -> & Hp_ge1 & Hp_in & Hprev_lt).
        cbn [decl_alloc_inv] in Hinv.
        destruct Hinv as (Hvars & Hexc & Hloc & -> & Hseen_ok & Hseen_dom & Hseen_disj).
        exists ((dc_name d, ptr_to_int p) :: seen).
        split.
        * intros x [<- | Hx]; rewrite map_app; apply in_or_app;
            [right; left; reflexivity | left; apply Hincl, Hx].
        * split.
          -- intros d0 Hd0 Hnone; apply in_app_or in Hd0 as [Hd0 | [<- | []]].
             ++ destruct (Hall d0 Hd0 Hnone) as [z Hz]; exists z; right; exact Hz.
             ++ exists (ptr_to_int p); left; reflexivity.
          -- cbn [decl_alloc_inv].
             split; [exact Hvars |].
             split; [exact Hexc |].
             split; [exact Hloc |].
             split; [reflexivity |].
             split.
             ++ intros x z [Heq | Hin_s].
                ** injection Heq as <- <-.
                   split; [exact Hp_ge1 |].
                   split; [exact Hp_in |].
                   exists p; split; [reflexivity | apply PassCommon.lookup_add_eq].
                ** destruct (Hseen_ok x z Hin_s) as (Hz_ge1 & Hz_in0 & p0 & Hp0_z & Hlk0).
                   destruct (Hprev_lt z Hz_in0) as (_ & Hz_in').
                   assert (Hne : dc_name d <> x).
                   { intros ->; apply Hnot_prev, Hincl.
                     change (dc_name d) with (fst (dc_name d, z)); apply in_map, Hin_s. }
                   split; [exact Hz_ge1 |].
                   split; [exact Hz_in' |].
                   exists p0; split; [exact Hp0_z |].
                   rewrite PassCommon.lookup_add_neq by exact Hne; exact Hlk0.
             ++ split.
                ** intros x v0 Hlk.
                   cbn [List.map fst].
                   destruct (RawIDOrd.eq_dec (dc_name d) x) as [-> | Hne].
                   --- left; reflexivity.
                   --- rewrite PassCommon.lookup_add_neq in Hlk by exact Hne.
                       right; eapply Hseen_dom, Hlk.
                ** intros x1 z1 x2 z2 [Heq1 | H1] [Heq2 | H2] Hne.
                   --- injection Heq1 as <- <-; injection Heq2 as <- <-; contradiction.
                   --- injection Heq1 as <- <-.
                       destruct (Hseen_ok x2 z2 H2) as (_ & Hz2_in0 & _).
                       destruct (Hprev_lt z2 Hz2_in0) as (Hlt & _); lia.
                   --- injection Heq2 as <- <-.
                       destruct (Hseen_ok x1 z1 H1) as (_ & Hz1_in0 & _).
                       destruct (Hprev_lt z1 Hz1_in0) as (Hlt & _); lia.
                   --- eapply Hseen_disj; eassumption.
  Qed.

  Definition post_decl_inv (all_decls : list (declaration dtyp)) (s : FusedS) : Prop :=
    let decl_names := List.map dc_name all_decls in
    let '(_, ((sf, fstk), g)) := s in
    sf.(stack_vars) = Maps.empty /\
    sf.(stack_exc) = None /\
    sf.(stack_loc) = None /\
    fstk = [] /\
    exists seen : list (raw_id * Z),
      incl (List.map fst seen) decl_names /\
      (forall d,
         In d all_decls ->
         lookup_intrinsic_declaration (dc_name d) = None ->
         exists z, In (dc_name d, z) seen) /\
      (forall x z,
         In (x, z) seen ->
         (z >= 1)%Z /\
         exists p : @ptr PaV,
           ptr_to_int p = z /\
           Maps.lookup x g = Some (DVALUE_Base (DVALUE_Pointer p))) /\
      (forall x v,
         In x decl_names ->
         Maps.lookup x g = Some v ->
         In x (List.map fst seen)) /\
      (forall x1 z1 x2 z2,
         In (x1, z1) seen ->
         In (x2, z2) seen ->
         x1 <> x2 ->
         z1 <> z2).

  Lemma post_decl_inv_lsg (all_decls : list (declaration dtyp))
    (m m' : state) (lsg : (@stack_frame PaV * stack) * global_env) :
    post_decl_inv all_decls (m, lsg) ->
    post_decl_inv all_decls (m', lsg).
  Proof using.
    destruct lsg as [[sf fstk] g]; intros H; exact H.
  Qed.

  Lemma model_hoare_gwrite_post_decl (all_decls : list (declaration dtyp))
    (k : raw_id) (v : @dvalue PaV)
    (Hnin : ~ In k (List.map dc_name all_decls)) :
    model_hoare (post_decl_inv all_decls) (gwrite k v)
      (fun s' _ => post_decl_inv all_decls s').
  Proof using.
    apply model_hoare_gwrite.
    intros m [[sf fstk] g]
      (Hvars & Hexc & Hloc & Hfstk & seen & Hincl & Hall & Hok & Hdom & Hdisj).
    split; [exact Hvars |].
    split; [exact Hexc |].
    split; [exact Hloc |].
    split; [exact Hfstk |].
    exists seen.
    split; [exact Hincl |].
    split; [exact Hall |].
    split; [| split; [| exact Hdisj]].
    - intros x z Hxz.
      destruct (Hok x z Hxz) as (Hz_ge1 & p & Hp_z & Hlk).
      assert (Hne : k <> x).
      { intros ->; apply Hnin, Hincl; change k with (fst (k, z)); apply in_map, Hxz. }
      split; [exact Hz_ge1 |].
      exists p; split; [exact Hp_z |].
      rewrite PassCommon.lookup_add_neq by exact Hne; exact Hlk.
    - intros x v0 Hx_in Hlk.
      assert (Hne : k <> x) by (intros ->; contradiction).
      rewrite PassCommon.lookup_add_neq in Hlk by exact Hne.
      eapply Hdom; eassumption.
  Qed.

  Lemma build_global_environment_inline_post (M : CFG.mcfg dtyp)
    (Hhyg : is_hygienic_module M = true) :
    let all_decls := m_declarations M ++ List.map df_prototype (m_definitions M) in
    model_hoare
      (fun s => s = init_fused_state)
      (build_global_environment M)
      (fun s' _ => post_decl_inv all_decls s').
  Proof using.
    intros all_decls.
    unfold is_hygienic_module in Hhyg.
    apply nodup_raw_ids_spec in Hhyg.
    fold all_decls in Hhyg.
    set (decl_names := List.map dc_name all_decls) in *.
    set (ba_names := List.map (fun '(f, b) => blockaddress_id f b) (mcfg_block_addresses M)) in *.
    set (glob_names := List.map g_ident (m_globals M)) in *.
    pose proof (inl_nodup_app_l decl_names (ba_names ++ glob_names) Hhyg) as Hnd_decl.
    pose proof (inl_nodup_app_disj decl_names (ba_names ++ glob_names) Hhyg) as Hdisj_decl.
    unfold build_global_environment; fold all_decls.
    eapply model_hoare_bind.
    - eapply model_hoare_weaken with
        (P := decl_loop_inv [])
        (Q := fun s' _ => decl_loop_inv ([] ++ all_decls) s').
      + intros s ->.
        exists []; split; [apply incl_refl | split; [intros _ [] |]].
        cbn [decl_alloc_inv init_fused_state stack_vars stack_exc stack_loc].
        split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]].
        split; [intros _ _ [] | split; [intros ? ? Hlk; cbn in Hlk; discriminate Hlk | intros _ _ _ _ []]].
      + intros [m [[sf fstk] g]] _ (seen & Hincl & Hall & Hvars & Hexc & Hloc & Hfstk & Hok & Hdom & Hdisj).
        cbn [app] in *.
        split; [exact Hvars | split; [exact Hexc | split; [exact Hloc | split; [exact Hfstk |]]]].
        exists seen; split; [exact Hincl | split; [exact Hall | split; [| split; [| exact Hdisj]]]].
        * intros x z Hxz; destruct (Hok x z Hxz) as (Hz1 & _ & p & Hpz & Hlk).
          split; [exact Hz1 | exists p; split; assumption].
        * intros x v _ Hlk; eapply Hdom, Hlk.
      + apply model_hoare_allocate_declarations_aux; cbn [app]; exact Hnd_decl.
    - intros _.
      eapply model_hoare_bind.
      + unfold allocate_block_addresses.
        apply model_hoare_loop_monad; intros [f b] Hfb.
        apply nodup_In in Hfb.
        assert (Hnot_decl : ~ In (blockaddress_id f b) decl_names).
        { intros Hin; eapply Hdisj_decl; [exact Hin |].
          apply in_or_app; left; unfold ba_names.
          change (blockaddress_id f b) with ((fun '(f0, b0) => blockaddress_id f0 b0) (f, b)).
          apply in_map, Hfb. }
        unfold allocate_block_address.
        eapply model_hoare_bind;
          [unfold alloca; apply (model_hoare_memory_lsg_preserve _ _ (post_decl_inv_lsg all_decls))
          | intros v; apply model_hoare_gwrite_post_decl, Hnot_decl].
      + intros _.
        eapply model_hoare_bind.
        * unfold allocate_globals.
          apply model_hoare_loop_monad; intros g Hg.
          assert (Hnot_decl : ~ In (g_ident g) decl_names).
          { intros Hin; eapply Hdisj_decl; [exact Hin |].
            apply in_or_app; right; unfold glob_names; apply in_map, Hg. }
          unfold allocate_global; destruct (g_alias g).
          -- apply model_hoare_ret; intros s Hs; exact Hs.
          -- eapply model_hoare_bind;
               [unfold alloca; apply (model_hoare_memory_lsg_preserve _ _ (post_decl_inv_lsg all_decls))
               | intros v; apply model_hoare_gwrite_post_decl, Hnot_decl].
        * intros _.
          unfold initialize_globals.
          apply model_hoare_loop_monad; intros g Hg.
          assert (Hnot_decl : ~ In (g_ident g) decl_names).
          { intros Hin; eapply Hdisj_decl; [exact Hin |].
            apply in_or_app; right; unfold glob_names; apply in_map, Hg. }
          unfold initialize_global; destruct (g_alias g).
          -- destruct (g_exp g) as [ge |]; [| apply model_hoare_raiseUB].
             destruct ge; try apply model_hoare_raiseUB.
             destruct id as [g_src |]; [| apply model_hoare_raiseUB].
             eapply model_hoare_bind;
               [apply model_hoare_gread_preserve
               | intros p; apply model_hoare_gwrite_post_decl, Hnot_decl].
          -- eapply model_hoare_bind; [apply model_hoare_gread_preserve | intros a].
             eapply model_hoare_bind.
             ++ destruct (g_exp g) as [ge |].
                ** apply (model_hoare_denote_exp_lsg_preserve _ (post_decl_inv_lsg all_decls)).
                ** apply model_hoare_ret; intros s Hs; exact Hs.
             ++ intros uv; unfold store.
                apply (model_hoare_memory_lsg_preserve _ _ (post_decl_inv_lsg all_decls)).
  Qed.


  (** * 8. Elastic Inlining Simulation ([gen_inline_sim], [cfg_inline_sim], [mcfg_inline_sim]) *)

  (** ** 8A. Finite [Tau]/Bisimulation Prefix ([itree_tau_star]) and Inlining Contexts *)

  Inductive itree_tau_star {E : Type -> Type} {R : Type}
    : itree E R -> itree E R -> Prop :=
  | ITS_Refl (t : itree E R) :
      itree_tau_star t t
  | ITS_Eq (t1 t2 t3 : itree E R) :
      t1 ≅ t2 ->
      itree_tau_star t2 t3 ->
      itree_tau_star t1 t3
  | ITS_Tau (m t' : itree E R) :
      itree_tau_star m t' ->
      itree_tau_star (Tau m) t'.

  Lemma itree_tau_star_trans {E : Type -> Type} {R : Type}
    (t1 t2 t3 : itree E R) :
    itree_tau_star t1 t2 ->
    itree_tau_star t2 t3 ->
    itree_tau_star t1 t3.
  Proof using.
    intros H12 H23; induction H12 as [t | a b c Hab _ IH | m b _ IH].
    - exact H23.
    - eapply ITS_Eq; [exact Hab | apply IH, H23].
    - apply ITS_Tau, IH, H23.
  Qed.

  Lemma itree_tau_star_bind {E : Type -> Type} {A B : Type}
    (t t' : itree E A) (k : A -> itree E B) :
    itree_tau_star t t' ->
    itree_tau_star (ITree.bind t k) (ITree.bind t' k).
  Proof using.
    intros Ht; induction Ht as [a | a b c Hab _ IH | m b _ IH].
    - apply ITS_Refl.
    - eapply ITS_Eq; [rewrite Hab; reflexivity | exact IH].
    - eapply ITS_Eq; [apply Eqit.bind_tau | apply ITS_Tau, IH].
  Qed.

  Inductive inline_ctx : Type :=
  | IC_Synced (stk : env_stack) (e1 e2 : @local_env PaV)
  | IC_MemPushed (stk : env_stack) (e1 e2 : @local_env PaV)
  | IC_Inlined (stk : env_stack) (caller_e1 e1 e2 : @local_env PaV).

  Definition ic_env1 (ic : inline_ctx) : option (@local_env PaV) :=
    match ic with
    | IC_Synced _ e1 _ => Some e1
    | IC_MemPushed _ _ _ => None
    | IC_Inlined _ _ e1 _ => Some e1
    end.

  Definition ic_env2 (ic : inline_ctx) : option (@local_env PaV) :=
    match ic with
    | IC_Synced _ _ e2 => Some e2
    | IC_MemPushed _ _ _ => None
    | IC_Inlined _ _ _ e2 => Some e2
    end.

  Definition ic_write1 (x : local_id) (v : @dvalue PaV) (ic : inline_ctx) : option inline_ctx :=
    match ic with
    | IC_Synced stk e1 e2 => Some (IC_Synced stk (Maps.add x v e1) e2)
    | IC_MemPushed _ _ _ => None
    | IC_Inlined stk ce1 e1 e2 => Some (IC_Inlined stk ce1 (Maps.add x v e1) e2)
    end.

  Definition ic_write2 (x : local_id) (v : @dvalue PaV) (ic : inline_ctx) : option inline_ctx :=
    match ic with
    | IC_Synced stk e1 e2 => Some (IC_Synced stk e1 (Maps.add x v e2))
    | IC_MemPushed _ _ _ => None
    | IC_Inlined stk ce1 e1 e2 => Some (IC_Inlined stk ce1 e1 (Maps.add x v e2))
    end.

  Definition is_ic_inlined (ic : inline_ctx) : bool :=
    match ic with
    | IC_Inlined _ _ _ _ => true
    | _ => false
    end.

  Definition is_ic_synced (ic : inline_ctx) : bool :=
    match ic with
    | IC_Synced _ _ _ => true
    | _ => false
    end.

  Definition inline_fused_match (g0 : global_env) (ic : inline_ctx) (s1 s2 : FusedS) : Prop :=
    let '(m1, ((sf1, fstk1), g1)) := s1 in
    let '(m2, ((sf2, fstk2), g2)) := s2 in
    g1 = g0 /\
    g2 = g0 /\
    match ic with
    | IC_Synced stk e1 e2 =>
        m1 = m2 /\
        sf_match e1 e2 sf1 sf2 /\
        stk_frames_match stk fstk1 fstk2
    | IC_MemPushed stk e1 e2 =>
        m1 = push_empty_frame m2 /\
        sf_match e1 e2 sf1 sf2 /\
        stk_frames_match stk fstk1 fstk2
    | IC_Inlined stk caller_e1 e1 e2 =>
        m1 = push_empty_frame m2 /\
        sf1.(stack_vars) = e1 /\
        exists caller_sf1 fstk1',
          fstk1 = caller_sf1 :: fstk1' /\
          sf_match caller_e1 e2 caller_sf1 sf2 /\
          stk_frames_match stk fstk1' fstk2
    end.

  Definition inl_is_ub_mcfg {X : Type} (e : @MCFGEtop PaV X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (ThrowOOM _))))))) => true
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (ThrowUB _))))))))) => true
    | _ => false
    end.

  Definition inl_is_ub_cfg {X : Type} (e : @CFGEtop PaV X) : bool :=
    match e with
    | inl1 _ => false
    | inr1 m => inl_is_ub_mcfg m
    end.

  Definition inl_sync_mcfg (ic : inline_ctx) {X : Type} (e : @MCFGEtop PaV X) : bool :=
    match ic with
    | IC_MemPushed _ _ _ => false
    | IC_Synced _ _ _ =>
        match e with
        | inr1 (inr1 (inl1 (GlobalWrite _ _))) => false
        | inr1 (inr1 (inr1 (inl1 (inl1 _)))) => false
        | inr1 (inr1 (inr1 (inl1 (inr1 (StackPush _))))) => false
        | inr1 (inr1 (inr1 (inl1 (inr1 StackPop)))) => false
        | _ => true
        end
    | IC_Inlined _ _ _ _ =>
        match e with
        | inl1 _ => false
        | inr1 (inl1 _) => false
        | inr1 (inr1 (inl1 (GlobalRead _))) => true
        | inr1 (inr1 (inl1 (GlobalWrite _ _))) => false
        | inr1 (inr1 (inr1 (inl1 _))) => false
        | inr1 (inr1 (inr1 (inr1 (inl1 me)))) => is_callee_sync_mem me
        | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 _))))) => true
        | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 _)))))) => true
        | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 _))))))) => false
        | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 _))))))) => true
        end
    end.

  Definition inl_sync_cfg (ic : inline_ctx) {X : Type} (e : @CFGEtop PaV X) : bool :=
    match e with
    | inl1 _ =>
        match ic with
        | IC_Synced _ _ _ => true
        | _ => false
        end
    | inr1 m => inl_sync_mcfg ic m
    end.

  Lemma EqE_CFG_exc_of_event {X1 X2 : Type}
    (e1 : @CFGEtop PaV X1) (e2 : @CFGEtop PaV X2) :
    EqE_CFG X1 X2 e1 e2 ->
    exc_of_event e1 = exc_of_event e2.
  Proof using.
    intros HE; destruct_sum2 e1 e2 HE;
      cbn in *; try contradiction; try reflexivity.
    destruct e1 as [ex1], e2 as [ex2]; subst; reflexivity.
  Qed.

  Lemma inl_is_ub_cfg_no_exc {X : Type} (e : @CFGEtop PaV X) :
    inl_is_ub_cfg e = true ->
    exc_of_event e = None.
  Proof using.
    repeat (destruct e as [e | e]); try discriminate; destruct e; reflexivity.
  Qed.

  Lemma inl_sync_cfg_inlined_no_exc stk ce1 e1 e2 {X : Type} (e : @CFGEtop PaV X) :
    inl_sync_cfg (IC_Inlined stk ce1 e1 e2) e = true ->
    exc_of_event e = None.
  Proof using.
    repeat (destruct e as [e | e]); try discriminate; try reflexivity.
  Qed.

  (** ** 8B. Generic Coinductive Inlining Simulation ([gen_inline_sim]) *)

  Section GenInlineSim.
    Context {E : Type -> Type}
            `{@LocalE PaV -< E}
            `{@StackE PaV -< E}
            `{@GlobalE PaV -< E}
            `{@MemoryE PaV -< E}.
    Variable (is_ub : forall X, E X -> bool).
    Variable (is_sync : inline_ctx -> forall X, E X -> bool).
    Variable (EqE : prerel E E).
    Variable (EqA : postrel E E).
    Variable (ev_post : forall X, E X -> X -> Prop).
    Variable (as_loc : forall X, E X -> option (@LocalE PaV X)).
    Variable (as_stk : forall X, E X -> option (@StackE PaV X)).
    Variable (opt_call1 : forall X, E X -> option (itree E X)).
    Variable (g0 : global_env).
    Variable (allow_frame : bool).

    Definition gis_cont {R1 R2 : Type}
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx) (t1 : itree E R1) (t2 : itree E R2) : Prop :=
      exists m1 m2,
        itree_tau_star t1 m1 /\
        itree_tau_star t2 m2 /\
        r ic m1 m2.

    Lemma gis_cont_mon {R1 R2 : Type}
      (r r' : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (LE : forall ic a1 a2, r ic a1 a2 -> r' ic a1 a2)
      (ic : inline_ctx) (t1 : itree E R1) (t2 : itree E R2) :
      gis_cont r ic t1 t2 -> gis_cont r' ic t1 t2.
    Proof using.
      intros (m1 & m2 & Hs1 & Hs2 & Hr).
      exists m1, m2; split; [exact Hs1 | split; [exact Hs2 | apply LE, Hr]].
    Qed.

    Lemma gis_cont_obs_eq {R1 R2 : Type}
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx) (t1 t1' : itree E R1) (t2 t2' : itree E R2) :
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      gis_cont r ic t1 t2 ->
      gis_cont r ic t1' t2'.
    Proof using.
      intros E1 E2 (m1 & m2 & Hs1 & Hs2 & Hr).
      exists m1, m2.
      split; [eapply ITS_Eq; [symmetry; exact E1 | exact Hs1] |].
      split; [eapply ITS_Eq; [symmetry; exact E2 | exact Hs2] | exact Hr].
    Qed.

    Definition gis_vis_both {R1 R2 : Type}
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx)
      {X1} (e1 : E X1) (k1 : X1 -> itree E R1)
      {X2} (e2 : E X2) (k2 : X2 -> itree E R2) : Prop :=
      (is_sync ic X1 e1 = true /\
       EqE X1 X2 e1 e2 /\
       forall a1 a2,
         EqA X1 X2 e1 a1 e2 a2 ->
         ev_post X1 e1 a1 ->
         gis_cont r ic (k1 a1) (k2 a2)) \/
      match ic with
      | IC_Synced stk env1 env2 =>
          (match as_loc X1 e1, as_loc X2 e2 with
           | Some le1, Some le2 =>
               match le1 in LocalE Y1 return (Y1 -> itree E R1) -> Prop with
               | LocalRead x1 => fun k1' =>
                   match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
                   | LocalRead x2 => fun k2' =>
                       x1 = x2 /\
                       Maps.lookup x1 env1 = Maps.lookup x2 env2 /\
                       forall v,
                         Maps.lookup x1 env1 = Some v ->
                         gis_cont r (IC_Synced stk env1 env2) (k1' v) (k2' v)
                   | _ => fun _ => False
                   end k2
               | LocalWrite x1 v1 => fun k1' =>
                   match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
                   | LocalWrite x2 v2 => fun k2' =>
                       x1 = x2 /\ v1 = v2 /\
                       gis_cont r (IC_Synced stk (Maps.add x1 v1 env1) (Maps.add x2 v2 env2))
                         (k1' tt) (k2' tt)
                   | _ => fun _ => False
                   end k2
               end k1
           | _, _ => False
           end) \/
          (allow_frame = true /\
           match as_stk X1 e1, as_stk X2 e2 with
           | Some se1, Some se2 =>
               match se1 in StackE Y1 return (Y1 -> itree E R1) -> Prop with
               | StackPush bs1 => fun k1' =>
                   match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
                   | StackPush bs2 => fun k2' =>
                       bs1 = bs2 /\
                       gis_cont r (IC_Synced ((env1, env2) :: stk)
                                     (init_local_env bs1) (init_local_env bs2))
                         (k1' tt) (k2' tt)
                   | _ => fun _ => False
                   end k2
               | StackPop => fun k1' =>
                   match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
                   | StackPop => fun k2' =>
                       match stk with
                       | [] => True
                       | (p1, p2) :: rest =>
                           gis_cont r (IC_Synced rest p1 p2) (k1' tt) (k2' tt)
                       end
                   | _ => fun _ => False
                   end k2
               | _ => fun _ => False
               end k1
           | _, _ => False
           end)
      | _ => False
      end.

    Definition gis_step_body {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx)
      (ot1 : itree' E R1) (ot2 : itree' E R2) : Prop :=
      match ot1 with
      | RetF r1 =>
          match ot2 with
          | RetF r2 => RR ic r1 r2
          | _ => False
          end
      | TauF m1 =>
          match ot2 with
          | TauF m2 => gis_cont r ic m1 m2
          | _ => False
          end
      | VisF e1 k1 =>
          is_ub _ e1 = true \/
          match ot2 with
          | VisF e2 k2 => gis_vis_both r ic e1 k1 e2 k2
          | _ => False
          end
      end.

    Inductive gen_inline_sim_ {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      : inline_ctx -> itree E R1 -> itree E R2 -> Prop :=
    | GIS_Step ic t1 t2 :
        gis_step_body RR r ic (observe t1) (observe t2) ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_TauL ic t1 m1 t2 :
        observe t1 = TauF m1 ->
        gen_inline_sim_ RR r ic m1 t2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_TauR ic t1 t2 m2 :
        observe t2 = TauF m2 ->
        gen_inline_sim_ RR r ic t1 m2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_ReadL ic env1 t1 x v k1 t2 :
        ic_env1 ic = Some env1 ->
        t1 ≅ ITree.bind (ITree.trigger (LocalRead x)) k1 ->
        Maps.lookup x env1 = Some v ->
        gen_inline_sim_ RR r ic (k1 v) t2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_ReadR ic env2 t1 t2 x v k2 :
        ic_env2 ic = Some env2 ->
        t2 ≅ ITree.bind (ITree.trigger (LocalRead x)) k2 ->
        Maps.lookup x env2 = Some v ->
        gen_inline_sim_ RR r ic t1 (k2 v) ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_WriteL ic ic' t1 x v k1 t2 :
        ic_write1 x v ic = Some ic' ->
        t1 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) k1 ->
        gen_inline_sim_ RR r ic' (k1 tt) t2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_WriteR ic ic' t1 t2 x v k2 :
        ic_write2 x v ic = Some ic' ->
        t2 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) k2 ->
        gen_inline_sim_ RR r ic' t1 (k2 tt) ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_GReadL ic t1 k v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (GlobalRead k)) k1 ->
        Maps.lookup k g0 = Some v ->
        gen_inline_sim_ RR r ic (k1 v) t2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_ZeroStoreL stk ce1 e1 e2 t1 varg k1 t2 :
        t1 ≅ ITree.bind
               (ITree.trigger
                  (Store (DTYPE_Struct true [])
                     (DVALUE_Base (DVALUE_Pointer varg))
                     (DVALUE_Struct true []))) k1 ->
        gen_inline_sim_ RR r (IC_Inlined stk ce1 e1 e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_Inlined stk ce1 e1 e2) t1 t2
    | GIS_MemPushL stk e1 e2 t1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger MemPush) k1 ->
        gen_inline_sim_ RR r (IC_MemPushed stk e1 e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_Synced stk e1 e2) t1 t2
    | GIS_StackPushL stk ce1 e2 bs t1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger (StackPush bs)) k1 ->
        gen_inline_sim_ RR r (IC_Inlined stk ce1 (init_local_env bs) e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_MemPushed stk ce1 e2) t1 t2
    | GIS_StackPopL stk ce1 e1 e2 t1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger StackPop) k1 ->
        gen_inline_sim_ RR r (IC_MemPushed stk ce1 e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_Inlined stk ce1 e1 e2) t1 t2
    | GIS_MemPopL stk ce1 e2 t1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger MemPop) k1 ->
        gen_inline_sim_ RR r (IC_Synced stk ce1 e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_MemPushed stk ce1 e2) t1 t2
    | GIS_InlCallL stk e1 e2 t1 X (ce : E X) body1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger ce) k1 ->
        opt_call1 X ce = Some body1 ->
        gen_inline_sim_ RR r (IC_Synced stk e1 e2) (ITree.bind body1 k1) t2 ->
        gen_inline_sim_ RR r (IC_Synced stk e1 e2) t1 t2.

    Lemma gen_inline_sim__mon {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop) :
      monotone3 (gen_inline_sim_ RR).
    Proof using.
      intros ic t1 t2 r r' IN LE.
      induction IN as [ic t1 t2 Hstep
                       | ic t1 m1 t2 Ht1 _ IH
                       | ic t1 t2 m2 Ht2 _ IH
                       | ic env1 t1 x v k1 t2 He1 Ht1 Hlk _ IH
                       | ic env2 t1 t2 x v k2 He2 Ht2 Hlk _ IH
                       | ic ic' t1 x v k1 t2 Hw1 Ht1 _ IH
                       | ic ic' t1 t2 x v k2 Hw2 Ht2 _ IH
                       | ic t1 k v k1 t2 Ht1 Hlk _ IH
                       | stk ce1 e1 e2 t1 varg k1 t2 Ht1 _ IH
                       | stk e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                       | stk ce1 e2 bs t1 k1 t2 Hfr Ht1 _ IH
                       | stk ce1 e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                       | stk ce1 e2 t1 k1 t2 Hfr Ht1 _ IH
                       | stk e1 e2 t1 X ce body1 k1 t2 Hfr Ht1 Hopt _ IH].
      - apply GIS_Step; unfold gis_step_body in *.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1].
        + exact Hstep.
        + destruct (observe t2); [exact Hstep | eapply gis_cont_mon; eassumption | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; eapply gis_cont_mon; [exact LE | exact (HA a1 a2 Ha Hp)].
          * right; destruct ic as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [Hfr_s Hstk]].
            -- left.
               destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
               destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
               ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                  intros v Hv; eapply gis_cont_mon; [exact LE | apply Hrd, Hv].
               ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                  eapply gis_cont_mon; [exact LE | exact Hr].
            -- right; split; [exact Hfr_s |].
               destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
               destruct se1, se2; try contradiction.
               ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs | eapply gis_cont_mon; eassumption].
               ++ destruct stk as [[p1 p2] rest |]; [eapply gis_cont_mon; eassumption | exact I].
      - eapply GIS_TauL; [exact Ht1 | exact IH].
      - eapply GIS_TauR; [exact Ht2 | exact IH].
      - eapply GIS_ReadL; [exact He1 | exact Ht1 | exact Hlk | exact IH].
      - eapply GIS_ReadR; [exact He2 | exact Ht2 | exact Hlk | exact IH].
      - eapply GIS_WriteL; [exact Hw1 | exact Ht1 | exact IH].
      - eapply GIS_WriteR; [exact Hw2 | exact Ht2 | exact IH].
      - eapply GIS_GReadL; [exact Ht1 | exact Hlk | exact IH].
      - eapply GIS_ZeroStoreL; [exact Ht1 | exact IH].
      - eapply GIS_MemPushL; [exact Hfr | exact Ht1 | exact IH].
      - eapply GIS_StackPushL; [exact Hfr | exact Ht1 | exact IH].
      - eapply GIS_StackPopL; [exact Hfr | exact Ht1 | exact IH].
      - eapply GIS_MemPopL; [exact Hfr | exact Ht1 | exact IH].
      - eapply GIS_InlCallL; [exact Hfr | exact Ht1 | exact Hopt | exact IH].
    Qed.

    Definition gen_inline_sim {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (t1 : itree E R1) (t2 : itree E R2) : Prop :=
      paco3 (gen_inline_sim_ RR) bot3 ic t1 t2.

    Lemma gen_inline_sim__obs_eq {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop) :
      forall ic t1 t1' t2 t2',
        t1 ≅ t1' ->
        t2 ≅ t2' ->
        gen_inline_sim_ RR r ic t1 t2 ->
        gen_inline_sim_ RR r ic t1' t2'.
    Proof using.
      intros ic t1 t1' t2 t2' E1 E2 Hsim.
      revert t1' t2' E1 E2;
        induction Hsim as [ic t1 t2 Hstep
                           | ic t1 m1 t2 Ht1 _ IH
                           | ic t1 t2 m2 Ht2 _ IH
                           | ic env1 t1 x v k1 t2 He1 Ht1 Hlk _ IH
                           | ic env2 t1 t2 x v k2 He2 Ht2 Hlk _ IH
                           | ic ic' t1 x v k1 t2 Hw1 Ht1 _ IH
                           | ic ic' t1 t2 x v k2 Hw2 Ht2 _ IH
                           | ic t1 k v k1 t2 Ht1 Hlk _ IH
                           | stk ce1 e1 e2 t1 varg k1 t2 Ht1 _ IH
                           | stk e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                           | stk ce1 e2 bs t1 k1 t2 Hfr Ht1 _ IH
                           | stk ce1 e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                           | stk ce1 e2 t1 k1 t2 Hfr Ht1 _ IH
                           | stk e1 e2 t1 X ce body1 k1 t2 Hfr Ht1 Hopt _ IH];
        intros t1' t2' E1 E2.
      - punfold E1; red in E1; punfold E2; red in E2.
        apply GIS_Step; unfold gis_step_body in *.
        destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1]; pclearbot.
        + destruct E2 as [r2 r2' <- | |]; try contradiction; exact Hstep.
        + destruct E2 as [| m2 m2' Hm2 |]; try contradiction; pclearbot.
          eapply gis_cont_obs_eq; [exact Hm1 | exact Hm2 | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct E2 as [| | X2 e2 k2 k2' Hk2]; try contradiction; pclearbot.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; eapply gis_cont_obs_eq;
              [apply Hk1 | apply Hk2 | exact (HA a1 a2 Ha Hp)].
          * right; destruct ic as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [Hfr_s Hstk]].
            -- left.
               destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
               destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
               ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                  intros v Hv; eapply gis_cont_obs_eq; [apply Hk1 | apply Hk2 | apply Hrd, Hv].
               ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                  eapply gis_cont_obs_eq; [apply Hk1 | apply Hk2 | exact Hr].
            -- right; split; [exact Hfr_s |].
               destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
               destruct se1, se2; try contradiction.
               ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs |].
                  eapply gis_cont_obs_eq; [apply Hk1 | apply Hk2 | exact Hr].
               ++ destruct stk as [[p1 p2] rest |];
                    [eapply gis_cont_obs_eq; [apply Hk1 | apply Hk2 | exact Hstk] | exact I].
      - punfold E1; red in E1; rewrite Ht1 in E1; inversion E1 as [| m1_ m1' Hm1 E1a E1b |]; subst; pclearbot.
        eapply GIS_TauL; [symmetry; exact E1b | eapply IH; [exact Hm1 | exact E2]].
      - punfold E2; red in E2; rewrite Ht2 in E2; inversion E2 as [| m2_ m2' Hm2 E2a E2b |]; subst; pclearbot.
        eapply GIS_TauR; [symmetry; exact E2b | eapply IH; [exact E1 | exact Hm2]].
      - eapply GIS_ReadL; [exact He1 | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | exact Hlk | apply IH; [reflexivity | exact E2]].
      - eapply GIS_ReadR; [exact He2 | symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | exact Hlk | apply IH; [exact E1 | reflexivity]].
      - eapply GIS_WriteL; [exact Hw1 | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
      - eapply GIS_WriteR; [exact Hw2 | symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | apply IH; [exact E1 | reflexivity]].
      - eapply GIS_GReadL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | exact Hlk | apply IH; [reflexivity | exact E2]].
      - eapply GIS_ZeroStoreL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
      - eapply GIS_MemPushL; [exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
      - eapply GIS_StackPushL; [exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
      - eapply GIS_StackPopL; [exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
      - eapply GIS_MemPopL; [exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
      - eapply GIS_InlCallL; [exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | exact Hopt | apply IH; [reflexivity | exact E2]].
    Qed.

    Lemma gen_inline_sim_obs_eq {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (t1 t1' : itree E R1) (t2 t2' : itree E R2) :
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      gen_inline_sim RR ic t1 t2 ->
      gen_inline_sim RR ic t1' t2'.
    Proof using.
      intros E1 E2 Hsim; pstep; punfold Hsim.
      eapply gen_inline_sim__obs_eq; eassumption.
    Qed.

    Lemma gen_inline_sim__tau_star_l {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx) (t1 m1 : itree E R1) (t2 : itree E R2) :
      itree_tau_star t1 m1 ->
      gen_inline_sim_ RR r ic m1 t2 ->
      gen_inline_sim_ RR r ic t1 t2.
    Proof using.
      intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH]; intros Hsim.
      - exact Hsim.
      - eapply gen_inline_sim__obs_eq; [symmetry; exact Hab | reflexivity | apply IH, Hsim].
      - eapply GIS_TauL; [reflexivity | apply IH, Hsim].
    Qed.

    Lemma gen_inline_sim__tau_star_r {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx) (t1 : itree E R1) (t2 m2 : itree E R2) :
      itree_tau_star t2 m2 ->
      gen_inline_sim_ RR r ic t1 m2 ->
      gen_inline_sim_ RR r ic t1 t2.
    Proof using.
      intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH]; intros Hsim.
      - exact Hsim.
      - eapply gen_inline_sim__obs_eq; [reflexivity | symmetry; exact Hab | apply IH, Hsim].
      - eapply GIS_TauR; [reflexivity | apply IH, Hsim].
    Qed.

    Lemma gen_inline_sim_tau_star_l {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (t1 m1 : itree E R1) (t2 : itree E R2) :
      itree_tau_star t1 m1 ->
      gen_inline_sim RR ic m1 t2 ->
      gen_inline_sim RR ic t1 t2.
    Proof using.
      intros Hs Hsim; pstep; punfold Hsim.
      eapply gen_inline_sim__tau_star_l; eassumption.
    Qed.

    Lemma gen_inline_sim_tau_star_r {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (t1 : itree E R1) (t2 m2 : itree E R2) :
      itree_tau_star t2 m2 ->
      gen_inline_sim RR ic t1 m2 ->
      gen_inline_sim RR ic t1 t2.
    Proof using.
      intros Hs Hsim; pstep; punfold Hsim.
      eapply gen_inline_sim__tau_star_r; eassumption.
    Qed.

    Lemma gen_inline_sim_ret {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (r1 : R1) (r2 : R2)
      (H : RR ic r1 r2) :
      gen_inline_sim RR ic (Ret r1) (Ret r2).
    Proof using.
      pstep; apply GIS_Step; cbn; exact H.
    Qed.

    Lemma gen_inline_sim_weaken {R1 R2 : Type}
      (RR RR' : inline_ctx -> R1 -> R2 -> Prop)
      (Himp : forall ic r1 r2, RR ic r1 r2 -> RR' ic r1 r2) :
      forall ic t1 t2,
        gen_inline_sim RR ic t1 t2 ->
        gen_inline_sim RR' ic t1 t2.
    Proof using.
      pcofix CIH.
      intros ic t1 t2 Hsim; pstep; punfold Hsim.
      eapply gen_inline_sim__mon with
        (r := fun ic0 a1 a2 => upaco3 (gen_inline_sim_ RR) bot3 ic0 a1 a2);
        [| intros ic0 a1 a2 [Hr | Hb]; [right; apply CIH, Hr | inversion Hb]].
      clear r CIH.
      induction Hsim as [ic t1 t2 Hstep
                         | ic t1 m1 t2 Ht1 _ IH
                         | ic t1 t2 m2 Ht2 _ IH
                         | ic env1 t1 x v k1 t2 He1 Ht1 Hlk _ IH
                         | ic env2 t1 t2 x v k2 He2 Ht2 Hlk _ IH
                         | ic ic' t1 x v k1 t2 Hw1 Ht1 _ IH
                         | ic ic' t1 t2 x v k2 Hw2 Ht2 _ IH
                         | ic t1 k v k1 t2 Ht1 Hlk _ IH
                         | stk ce1 e1 e2 t1 varg k1 t2 Ht1 _ IH
                         | stk e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                         | stk ce1 e2 bs t1 k1 t2 Hfr Ht1 _ IH
                         | stk ce1 e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                         | stk ce1 e2 t1 k1 t2 Hfr Ht1 _ IH
                         | stk e1 e2 t1 X ce body1 k1 t2 Hfr Ht1 Hopt _ IH].
      - apply GIS_Step; unfold gis_step_body in *.
        destruct (observe t1); [destruct (observe t2); [apply Himp, Hstep | exact Hstep | exact Hstep]
                               | exact Hstep | exact Hstep].
      - eapply GIS_TauL; eassumption.
      - eapply GIS_TauR; eassumption.
      - eapply GIS_ReadL; eassumption.
      - eapply GIS_ReadR; eassumption.
      - eapply GIS_WriteL; eassumption.
      - eapply GIS_WriteR; eassumption.
      - eapply GIS_GReadL; eassumption.
      - eapply GIS_ZeroStoreL; eassumption.
      - eapply GIS_MemPushL; eassumption.
      - eapply GIS_StackPushL; eassumption.
      - eapply GIS_StackPopL; eassumption.
      - eapply GIS_MemPopL; eassumption.
      - eapply GIS_InlCallL; eassumption.
    Qed.

    Lemma gen_inline_sim_bind {A1 A2 B1 B2 : Type}
      (RA : inline_ctx -> A1 -> A2 -> Prop)
      (RB : inline_ctx -> B1 -> B2 -> Prop)
      (ic : inline_ctx)
      (t1 : itree E A1) (t2 : itree E A2)
      (k1 : A1 -> itree E B1) (k2 : A2 -> itree E B2)
      (Ht : gen_inline_sim RA ic t1 t2)
      (Hk : forall ic' a1 a2, RA ic' a1 a2 -> gen_inline_sim RB ic' (k1 a1) (k2 a2)) :
      gen_inline_sim RB ic (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof using.
      revert ic t1 t2 Ht; pcofix CIH; intros ic t1 t2 Ht.
      pstep; punfold Ht.
      set (r_bind := fun ic0 (b1 : itree E B1) (b2 : itree E B2) =>
                       upaco3 (gen_inline_sim_ RB) r ic0 b1 b2).
      assert (Hlift_cont :
        forall ic0 u1 u2,
          gis_cont (upaco3 (gen_inline_sim_ RA) bot3) ic0 u1 u2 ->
          gis_cont r_bind ic0 (ITree.bind u1 k1) (ITree.bind u2 k2)).
      { intros ic0 u1 u2 (m1 & m2 & Hs1 & Hs2 & [Hm | Hb]); [| inversion Hb].
        exists (ITree.bind m1 k1), (ITree.bind m2 k2).
        split; [apply itree_tau_star_bind, Hs1 |].
        split; [apply itree_tau_star_bind, Hs2 |].
        right; apply CIH, Hm. }
      induction Ht as [ic t1 t2 Hstep
                       | ic t1 m1 t2 Ht1 _ IH
                       | ic t1 t2 m2 Ht2 _ IH
                       | ic env1 t1 x v f1 t2 He1 Ht1 Hlk _ IH
                       | ic env2 t1 t2 x v f2 He2 Ht2 Hlk _ IH
                       | ic ic' t1 x v f1 t2 Hw1 Ht1 _ IH
                       | ic ic' t1 t2 x v f2 Hw2 Ht2 _ IH
                       | ic t1 k v f1 t2 Ht1 Hlk _ IH
                       | stk ce1 e1 e2 t1 varg f1 t2 Ht1 _ IH
                       | stk e1 e2 t1 f1 t2 Hfr Ht1 _ IH
                       | stk ce1 e2 bs t1 f1 t2 Hfr Ht1 _ IH
                       | stk ce1 e1 e2 t1 f1 t2 Hfr Ht1 _ IH
                       | stk ce1 e2 t1 f1 t2 Hfr Ht1 _ IH
                       | stk e1 e2 t1 X ce body1 f1 t2 Hfr Ht1 Hopt _ IH].
      - unfold gis_step_body in Hstep.
        destruct (observe t1) as [a1 | m1 | X1 e1 f1] eqn:Hot1.
        + destruct (observe t2) as [a2 | m2 | X2 e2 f2] eqn:Hot2; try contradiction.
          assert (Eb1 : ITree.bind t1 k1 ≅ k1 a1).
          { rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity. }
          assert (Eb2 : ITree.bind t2 k2 ≅ k2 a2).
          { rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity. }
          pose proof (Hk ic a1 a2 Hstep) as Hka; punfold Hka.
          eapply gen_inline_sim__obs_eq; [symmetry; exact Eb1 | symmetry; exact Eb2 |].
          eapply gen_inline_sim__mon; [exact Hka |].
          intros ic0 b1 b2 [Hb | Hbot]; [left; exact Hb | inversion Hbot].
        + destruct (observe t2) as [a2 | m2 | X2 e2 f2] eqn:Hot2; try contradiction.
          apply GIS_Step; unfold gis_step_body.
          rewrite !observe_bind, Hot1, Hot2.
          apply Hlift_cont, Hstep.
        + apply GIS_Step; unfold gis_step_body.
          rewrite (observe_bind t1 k1), Hot1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [a2 | m2 | X2 e2 f2] eqn:Hot2; try contradiction.
          rewrite (observe_bind t2 k2), Hot2.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; apply Hlift_cont, (HA a1 a2 Ha Hp).
          * right; destruct ic as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [Hfr_s Hstk]].
            -- left.
               destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
               destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
               ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                  intros v Hv; apply Hlift_cont, Hrd, Hv.
               ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply Hlift_cont, Hr]].
            -- right; split; [exact Hfr_s |].
               destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
               destruct se1, se2; try contradiction.
               ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs | apply Hlift_cont, Hr].
               ++ destruct stk as [[p1 p2] rest |]; [apply Hlift_cont, Hstk | exact I].
      - eapply GIS_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | exact IH].
      - eapply GIS_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | exact IH].
      - eapply GIS_ReadL; [exact He1 | rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_ReadR; [exact He2 | rewrite Ht2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_WriteL; [exact Hw1 | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_WriteR; [exact Hw2 | rewrite Ht2, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_GReadL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_ZeroStoreL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_MemPushL; [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_StackPushL; [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_StackPopL; [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_MemPopL; [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_InlCallL;
          [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hopt |].
        eapply gen_inline_sim__obs_eq;
          [apply Eqit.bind_bind | reflexivity | exact IH].
    Qed.

    Lemma gen_inline_sim_trigger_sync {X1 X2 : Type}
      (e1 : E X1) (e2 : E X2) (ic : inline_ctx)
      (Hsync : is_sync ic X1 e1 = true)
      (HE : EqE X1 X2 e1 e2) :
      gen_inline_sim
        (fun ic' a1 a2 => ic' = ic /\ EqA X1 X2 e1 a1 e2 a2 /\ ev_post X1 e1 a1)
        ic (ITree.trigger e1) (ITree.trigger e2).
    Proof using.
      pstep; apply GIS_Step; unfold gis_step_body, ITree.trigger; cbn [observe].
      right; left; split; [exact Hsync | split; [exact HE |]].
      intros a1 a2 Ha Hp.
      exists (Ret a1), (Ret a2).
      split; [apply ITS_Refl | split; [apply ITS_Refl |]].
      left; apply gen_inline_sim_ret; split; [reflexivity | split; assumption].
    Qed.

  End GenInlineSim.

  #[local] Hint Resolve gen_inline_sim__mon : paco.

  Lemma gen_inline_sim_allow_frame
    {E : Type -> Type}
    `{@LocalE PaV -< E} `{@StackE PaV -< E} `{@GlobalE PaV -< E} `{@MemoryE PaV -< E}
    (is_ub : forall X, E X -> bool)
    (is_sync : inline_ctx -> forall X, E X -> bool)
    (EqE : prerel E E) (EqA : postrel E E)
    (ev_post : forall X, E X -> X -> Prop)
    (as_loc : forall X, E X -> option (@LocalE PaV X))
    (as_stk : forall X, E X -> option (@StackE PaV X))
    (opt_call1 : forall X, E X -> option (itree E X))
    (g0 : global_env) (b1 b2 : bool)
    (Hb : b1 = false \/ b1 = b2)
    {R1 R2 : Type} (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall ic (t1 : itree E R1) (t2 : itree E R2),
      gen_inline_sim is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 b1 RR ic t1 t2 ->
      gen_inline_sim is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 b2 RR ic t1 t2.
  Proof using.
    destruct Hb as [-> | ->]; [| intros ic t1 t2 Hsim; exact Hsim].
    pcofix CIH.
    intros ic t1 t2 Hsim; pstep; punfold Hsim.
    eapply gen_inline_sim__mon with
      (r := fun ic0 a1 a2 =>
              upaco3 (gen_inline_sim_ is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 false RR)
                bot3 ic0 a1 a2);
      [| intros ic0 a1 a2 [Hr | Hbot]; [right; apply CIH, Hr | inversion Hbot]].
    clear r CIH.
    induction Hsim as [ic t1 t2 Hstep
                       | ic t1 m1 t2 Ht1 _ IH
                       | ic t1 t2 m2 Ht2 _ IH
                       | ic env1 t1 x v k1 t2 He1 Ht1 Hlk _ IH
                       | ic env2 t1 t2 x v k2 He2 Ht2 Hlk _ IH
                       | ic ic' t1 x v k1 t2 Hw1 Ht1 _ IH
                       | ic ic' t1 t2 x v k2 Hw2 Ht2 _ IH
                       | ic t1 k v k1 t2 Ht1 Hlk _ IH
                       | stk ce1 e1 e2 t1 varg k1 t2 Ht1 _ IH
                       | stk e1 e2 t1 k1 t2 Hfr
                       | stk ce1 e2 bs t1 k1 t2 Hfr
                       | stk ce1 e1 e2 t1 k1 t2 Hfr
                       | stk ce1 e2 t1 k1 t2 Hfr
                       | stk e1 e2 t1 X ce body1 k1 t2 Hfr];
      try discriminate Hfr.
    - apply GIS_Step; unfold gis_step_body in *.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1]; [exact Hstep | exact Hstep |].
      destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
      destruct (observe t2) as [r2 | m2 | X2 e2 k2]; [exact Hvis | exact Hvis |].
      destruct Hvis as [Hsync | Hls]; [left; exact Hsync | right].
      destruct ic as [stk env1 env2 | |]; try contradiction.
      destruct Hls as [Hloc | [Hfr _]]; [left; exact Hloc | discriminate Hfr].
    - eapply GIS_TauL; eassumption.
    - eapply GIS_TauR; eassumption.
    - eapply GIS_ReadL; eassumption.
    - eapply GIS_ReadR; eassumption.
    - eapply GIS_WriteL; eassumption.
    - eapply GIS_WriteR; eassumption.
    - eapply GIS_GReadL; eassumption.
    - eapply GIS_ZeroStoreL; eassumption.
  Qed.

  (** ** 8C. Concrete [CFGtop] and [MCFGtop] Instances, [denote_ocfg_map] & [run_exc] *)

  Definition callee_opt_call (p_callee : @ptr PaV) (callee_fn : @function_denotation PaV)
    : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X) :=
    fun X e =>
      match e in (_ +' _) Y return option (@CFGtop PaV Y) with
      | inl1 ce =>
          match ce in CallE Y return option (@CFGtop PaV Y) with
          | Call _ cc fv args =>
              match fv with
              | DVALUE_Base (DVALUE_Pointer p) =>
                  if Z.eqb (ptr_to_int p) (ptr_to_int p_callee)
                  then Some (callee_fn cc args)
                  else None
              | _ => None
              end
          end
      | inr1 _ => None
      end.

  Definition no_opt_call {E : Type -> Type} : forall X, E X -> option (itree E X) :=
    fun _ _ => None.

  Definition cfg_inline_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (allow_frame : bool)
    {R1 R2 : Type} (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (u1 : @CFGtop PaV R1) (u2 : @CFGtop PaV R2) : Prop :=
    gen_inline_sim (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
      (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
      opt_call1 g0 allow_frame RR ic u1 u2.

  Definition mcfg_inline_sim
    (g0 : global_env) (allow_frame : bool)
    {R1 R2 : Type} (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2) : Prop :=
    gen_inline_sim (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
      (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
      (@no_opt_call (@MCFGEtop PaV)) g0 allow_frame RR ic u1 u2.

  Lemma denote_ocfg_map_unfold_eq (bks : ocfg dtyp) (va : option (@ptr PaV))
    (bid_from bid_src : block_id) :
    denote_ocfg_map (ocfg_map bks) va (bid_from, bid_src) ≅
    match find_block bks bid_src with
    | None => Ret (inl (bid_from, bid_src))
    | Some bk =>
        ITree.bind (denote_block bk bid_from va)
          (fun bd =>
             match bd with
             | inr dv => Ret (inr dv)
             | inl bid_target =>
                 Tau (denote_ocfg_map (ocfg_map bks) va (bid_src, bid_target))
             end)
    end.
  Proof using.
    unfold denote_ocfg_map; rewrite unfold_iter; cbn [fst snd].
    rewrite ocfg_map_find_block.
    destruct (find_block bks bid_src) as [bk |].
    - rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [bid_target | dv] _ <-; rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma run_exc_ret_eq {A : Type} (u : @CFGtop PaV A) (a : A)
    (Hou : observe u = RetF a) :
    run_exc u ≅ Ret (inr a).
  Proof using.
    unfold run_exc; rewrite unfold_iter, Hou, Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma run_exc_tau_eq {A : Type} (u m : @CFGtop PaV A)
    (Hou : observe u = TauF m) :
    run_exc u ≅ Tau (run_exc m).
  Proof using.
    unfold run_exc; rewrite unfold_iter, Hou, Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma run_exc_vis_some_eq {A X : Type} (u : @CFGtop PaV A)
    (e : @CFGEtop PaV X) (k : X -> @CFGtop PaV A) (ex : @exc PaV)
    (Hou : observe u = VisF e k)
    (Hex : exc_of_event e = Some ex) :
    run_exc u ≅ Ret (inl ex).
  Proof using.
    unfold run_exc; rewrite unfold_iter, Hou, Hex, Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma run_exc_vis_none_eq {A X : Type} (u : @CFGtop PaV A)
    (e : @CFGEtop PaV X) (k : X -> @CFGtop PaV A)
    (Hou : observe u = VisF e k)
    (Hex : exc_of_event e = None) :
    run_exc u ≅ Vis e (fun y => Tau (run_exc (k y))).
  Proof using.
    unfold run_exc; rewrite unfold_iter, Hou, Hex, Eqit.bind_vis.
    apply eqit_Vis; intros y; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma run_exc_proper {A : Type} (u1 u2 : @CFGtop PaV A) :
    u1 ≅ u2 -> run_exc u1 ≅ run_exc u2.
  Proof using.
    revert u1 u2; ginit; gcofix CIH; intros u1 u2 Hu.
    punfold Hu; red in Hu.
    remember (observe u1) as ot1 eqn:Hou1;
    remember (observe u2) as ot2 eqn:Hou2.
    destruct Hu as [r1 r2 <- | m1 m2 REL | X e k1 k2 REL | |];
      symmetry in Hou1, Hou2; pclearbot.
    - rewrite (run_exc_ret_eq _ _ Hou1), (run_exc_ret_eq _ _ Hou2).
      gstep; constructor; reflexivity.
    - rewrite (run_exc_tau_eq _ _ Hou1), (run_exc_tau_eq _ _ Hou2).
      gstep; constructor; gfinal; left; apply CIH, REL.
    - destruct (exc_of_event e) as [ex |] eqn:Eex.
      + rewrite (run_exc_vis_some_eq _ _ _ _ Hou1 Eex), (run_exc_vis_some_eq _ _ _ _ Hou2 Eex).
        gstep; constructor; reflexivity.
      + rewrite (run_exc_vis_none_eq _ _ _ Hou1 Eex), (run_exc_vis_none_eq _ _ _ Hou2 Eex).
        gstep; constructor; intros y; gstep; constructor; gfinal; left; apply CIH, REL.
  Qed.

  Lemma itree_tau_star_run_exc {A : Type} (u u' : @CFGtop PaV A) :
    itree_tau_star u u' ->
    itree_tau_star (run_exc u) (run_exc u').
  Proof using.
    intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH].
    - apply ITS_Refl.
    - eapply ITS_Eq; [apply run_exc_proper, Hab | exact IH].
    - eapply ITS_Eq; [apply (run_exc_tau_eq (Tau m) m Logic.eq_refl) | apply ITS_Tau, IH].
  Qed.

  (** Lift an [allow_frame = false] simulation in [IC_Inlined] through [run_exc]
      on BOTH sides (with an outer bind [K1] on the left for the callee epilogue). *)
  Lemma cfg_inline_sim_bind_run_exc_lr
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    {A1 A2 B1 B2 C1 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RC : inline_ctx -> C1 -> @exc PaV + B2 -> Prop)
    (k1 : A1 -> @CFGtop PaV B1)
    (K1 : @exc PaV + B1 -> @CFGtop PaV C1)
    (k2 : A2 -> @CFGtop PaV B2)
    (Hk : forall ic' x1 x2,
            is_ic_inlined ic' = true ->
            RA ic' x1 x2 ->
            cfg_inline_sim opt_call1 g0 bf RC ic'
              (ITree.bind (run_exc (k1 x1)) K1)
              (run_exc (k2 x2))) :
    forall ic (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2),
      is_ic_inlined ic = true ->
      cfg_inline_sim opt_call1 g0 false RA ic a1 a2 ->
      cfg_inline_sim opt_call1 g0 bf RC ic
        (ITree.bind (run_exc (ITree.bind a1 k1)) K1)
        (run_exc (ITree.bind a2 k2)).
  Proof using.
    pcofix CIH.
    intros ic a1 a2 Hic Hsim; pstep; punfold Hsim.
    set (r_goal :=
      upaco3
        (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
           (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
           opt_call1 g0 bf RC) r).
    revert Hic;
      induction Hsim as [ic a1 a2 Hstep
                         | ic a1 ma1 a2 Ha1 _ IH
                         | ic a1 a2 ma2 Ha2 _ IH
                         | ic env1 a1 x v fa1 a2 He1 Ha1 Hlk _ IH
                         | ic env2 a1 a2 x v fa2 He2 Ha2 Hlk _ IH
                         | ic ic' a1 x v fa1 a2 Hw1 Ha1 _ IH
                         | ic ic' a1 a2 x v fa2 Hw2 Ha2 _ IH
                         | ic a1 k v fa1 a2 Ha1 Hlk _ IH
                         | stk ce1 e1 e2 a1 varg fa1 a2 Ha1 _ IH
                         | stk e1 e2 a1 fa1 a2 Hfr
                         | stk ce1 e2 bs a1 fa1 a2 Hfr
                         | stk ce1 e1 e2 a1 fa1 a2 Hfr
                         | stk ce1 e2 a1 fa1 a2 Hfr
                         | stk e1 e2 a1 X ce body1 fa1 a2 Hfr];
      try discriminate Hfr; intros Hic.
    - unfold gis_step_body in Hstep.
      destruct (observe a1) as [x1 | ma1 | X1 e1 fa1] eqn:Hoa1.
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        assert (Eb1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅ ITree.bind (run_exc (k1 x1)) K1).
        { apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
          apply run_exc_proper; rewrite (itree_eta a1), Hoa1, Eqit.bind_ret_l; reflexivity. }
        assert (Eb2 : run_exc (ITree.bind a2 k2) ≅ run_exc (k2 x2)).
        { apply run_exc_proper; rewrite (itree_eta a2), Hoa2, Eqit.bind_ret_l; reflexivity. }
        pose proof (Hk ic x1 x2 Hic Hstep) as Hkx; punfold Hkx.
        eapply gen_inline_sim__obs_eq; [symmetry; exact Eb1 | symmetry; exact Eb2 |].
        eapply gen_inline_sim__mon; [exact Hkx |].
        intros ic0 u1 u2 [Hu | Hbot]; [left; exact Hu | inversion Hbot].
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        destruct Hstep as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
        assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
        { rewrite observe_bind, Hoa2; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; rewrite (run_exc_tau_eq _ _ Hou1), Eqit.bind_tau; reflexivity
          | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
        apply GIS_Step; cbn [gis_step_body observe].
        exists (ITree.bind (run_exc (ITree.bind m1 k1)) K1),
               (run_exc (ITree.bind m2 k2)).
        split; [apply itree_tau_star_bind, itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
        right; apply (CIH ic m1 m2 Hic Hm).
      + assert (Hou1 : observe (ITree.bind a1 k1) = VisF e1 (fun y => ITree.bind (fa1 y) k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        destruct Hstep as [Hub | Hvis].
        * pose proof (inl_is_ub_cfg_no_exc e1 Hub) as Hex1.
          eapply gen_inline_sim__obs_eq;
            [symmetry; rewrite (run_exc_vis_none_eq _ _ _ Hou1 Hex1), Eqit.bind_vis; reflexivity
            | reflexivity |].
          apply GIS_Step; cbn [gis_step_body observe]; left; exact Hub.
        * destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
          destruct ic as [| | stk ce1 e1_env e2_env]; try discriminate Hic.
          destruct Hvis as [(Hsync & HE & HA) | []].
          pose proof (inl_sync_cfg_inlined_no_exc stk ce1 e1_env e2_env e1 Hsync) as Hex1.
          pose proof (EqE_CFG_exc_of_event e1 e2 HE) as Hex12.
          assert (Hex2 : exc_of_event e2 = None) by congruence.
          assert (Hou2 : observe (ITree.bind a2 k2) = VisF e2 (fun y => ITree.bind (fa2 y) k2)).
          { rewrite observe_bind, Hoa2; reflexivity. }
          eapply gen_inline_sim__obs_eq;
            [symmetry; rewrite (run_exc_vis_none_eq _ _ _ Hou1 Hex1), Eqit.bind_vis; reflexivity
            | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex2) |].
          apply GIS_Step; cbn [gis_step_body observe]; right; left.
          split; [exact Hsync | split; [exact HE |]].
          intros y1 y2 Hy Hp.
          destruct (HA y1 y2 Hy Hp) as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
          exists (ITree.bind (run_exc (ITree.bind m1 k1)) K1),
                 (run_exc (ITree.bind m2 k2)).
          split.
          -- eapply ITS_Eq; [apply Eqit.bind_tau |].
             apply ITS_Tau, itree_tau_star_bind, itree_tau_star_run_exc, itree_tau_star_bind, Hs1.
          -- split.
             ++ apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs2.
             ++ right; apply (CIH _ m1 m2 Logic.eq_refl Hm).
    - assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
      { rewrite observe_bind, Ha1; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [symmetry; rewrite (run_exc_tau_eq _ _ Hou1), Eqit.bind_tau; reflexivity
        | reflexivity |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
      { rewrite observe_bind, Ha2; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [reflexivity | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (LocalRead x)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (LocalRead x))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalRead x))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite Eqit.bind_vis, <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; apply eqit_Tau.
        apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        apply run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ReadL; [exact He1 | exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Eb2 : ITree.bind a2 k2 ≅ ITree.bind (ITree.trigger (LocalRead x)) (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (LocalRead x))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalRead x))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa2 z) k2))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ReadR; [exact He2 | exact Er2 | exact Hlk |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Hic' : is_ic_inlined ic' = true).
      { destruct ic; try discriminate Hic; cbn in Hw1; injection Hw1 as <-; reflexivity. }
      assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (LocalWrite x v))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite x v))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite Eqit.bind_vis, <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; apply eqit_Tau.
        apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        apply run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_WriteL; [exact Hw1 | exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic'].
    - assert (Hic' : is_ic_inlined ic' = true).
      { destruct ic; try discriminate Hic; cbn in Hw2; injection Hw2 as <-; reflexivity. }
      assert (Eb2 : ITree.bind a2 k2 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (LocalWrite x v))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite x v))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa2 z) k2))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_WriteR; [exact Hw2 | exact Er2 |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic'].
    - assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (GlobalRead k)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (GlobalRead k))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (GlobalRead k))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite Eqit.bind_vis, <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; apply eqit_Tau.
        apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        apply run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_GReadL; [exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - set (ze := Store (DTYPE_Struct true []) (DVALUE_Base (DVALUE_Pointer varg)) (DVALUE_Struct true [])).
      assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger ze) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger ze)
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ ze)
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite Eqit.bind_vis, <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; apply eqit_Tau.
        apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        apply run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ZeroStoreL; [exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Logic.eq_refl].
  Qed.

  Definition ic_synced_stk (stk : env_stack) (ic : inline_ctx) : Prop :=
    exists e1 e2, ic = IC_Synced stk e1 e2.

  (** Lift an [allow_frame = false] simulation in [IC_Synced stk] through [run_exc]
      on BOTH sides (handling synchronous [LLVMExc] unwinds as well as normal returns). *)
  Lemma cfg_inline_sim_bind_run_exc_both
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (stk : env_stack)
    {A1 A2 B1 B2 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RB : inline_ctx -> @exc PaV + B1 -> @exc PaV + B2 -> Prop)
    (k1 : A1 -> @CFGtop PaV B1)
    (k2 : A2 -> @CFGtop PaV B2)
    (Hexc : forall e1 e2 ex,
              RB (IC_Synced stk e1 e2) (inl ex) (inl ex))
    (Hk : forall ic' x1 x2,
            ic_synced_stk stk ic' ->
            RA ic' x1 x2 ->
            cfg_inline_sim opt_call1 g0 bf RB ic'
              (run_exc (k1 x1))
              (run_exc (k2 x2))) :
    forall ic (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2),
      ic_synced_stk stk ic ->
      cfg_inline_sim opt_call1 g0 false RA ic a1 a2 ->
      cfg_inline_sim opt_call1 g0 bf RB ic
        (run_exc (ITree.bind a1 k1))
        (run_exc (ITree.bind a2 k2)).
  Proof using.
    pcofix CIH.
    intros ic a1 a2 Hic Hsim; pstep; punfold Hsim.
    assert (Hlift_sync_cont :
      forall ic0 u1 u2,
        ic_synced_stk stk ic0 ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false RA) bot3)
          ic0 u1 u2 ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 bf RB) r)
          ic0
          (Tau (run_exc (ITree.bind u1 k1)))
          (Tau (run_exc (ITree.bind u2 k2)))).
    { intros ic0 u1 u2 Hic0 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (run_exc (ITree.bind m1 k1)), (run_exc (ITree.bind m2 k2)).
      split; [apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
      split; [apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
      right; apply (CIH ic0 m1 m2 Hic0 Hm). }
    revert Hic;
      induction Hsim as [ic a1 a2 Hstep
                         | ic a1 ma1 a2 Ha1 _ IH
                         | ic a1 a2 ma2 Ha2 _ IH
                         | ic env1 a1 x v fa1 a2 He1 Ha1 Hlk _ IH
                         | ic env2 a1 a2 x v fa2 He2 Ha2 Hlk _ IH
                         | ic ic' a1 x v fa1 a2 Hw1 Ha1 _ IH
                         | ic ic' a1 a2 x v fa2 Hw2 Ha2 _ IH
                         | ic a1 k v fa1 a2 Ha1 Hlk _ IH
                         | stk0 ce1 e1 e2 a1 varg fa1 a2 Ha1 _ IH
                         | stk0 e1 e2 a1 fa1 a2 Hfr
                         | stk0 ce1 e2 bs a1 fa1 a2 Hfr
                         | stk0 ce1 e1 e2 a1 fa1 a2 Hfr
                         | stk0 ce1 e2 a1 fa1 a2 Hfr
                         | stk0 e1 e2 a1 X ce body1 fa1 a2 Hfr];
      try discriminate Hfr; intros Hic.
    - unfold gis_step_body in Hstep.
      destruct (observe a1) as [x1 | ma1 | X1 e1 fa1] eqn:Hoa1.
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        assert (Eb1 : run_exc (ITree.bind a1 k1) ≅ run_exc (k1 x1)).
        { apply run_exc_proper; rewrite (itree_eta a1), Hoa1, Eqit.bind_ret_l; reflexivity. }
        assert (Eb2 : run_exc (ITree.bind a2 k2) ≅ run_exc (k2 x2)).
        { apply run_exc_proper; rewrite (itree_eta a2), Hoa2, Eqit.bind_ret_l; reflexivity. }
        pose proof (Hk ic x1 x2 Hic Hstep) as Hkx; punfold Hkx.
        eapply gen_inline_sim__obs_eq; [symmetry; exact Eb1 | symmetry; exact Eb2 |].
        eapply gen_inline_sim__mon; [exact Hkx |].
        intros ic0 u1 u2 [Hu | Hbot]; [left; exact Hu | inversion Hbot].
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        destruct Hstep as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
        assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
        { rewrite observe_bind, Hoa2; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; apply (run_exc_tau_eq _ _ Hou1)
          | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
        apply GIS_Step; cbn [gis_step_body observe].
        exists (run_exc (ITree.bind m1 k1)), (run_exc (ITree.bind m2 k2)).
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
        right; apply (CIH ic m1 m2 Hic Hm).
      + assert (Hou1 : observe (ITree.bind a1 k1) = VisF e1 (fun y => ITree.bind (fa1 y) k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        destruct Hstep as [Hub | Hvis].
        * pose proof (inl_is_ub_cfg_no_exc e1 Hub) as Hex1.
          eapply gen_inline_sim__obs_eq;
            [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1) | reflexivity |].
          apply GIS_Step; cbn [gis_step_body observe]; left; exact Hub.
        * destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
          assert (Hou2 : observe (ITree.bind a2 k2) = VisF e2 (fun y => ITree.bind (fa2 y) k2)).
          { rewrite observe_bind, Hoa2; reflexivity. }
          destruct Hic as (env1 & env2 & ->).
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | [Hfr_s _]]]; [| | discriminate Hfr_s].
          -- pose proof (EqE_CFG_exc_of_event e1 e2 HE) as Hex12.
             destruct (exc_of_event e1) as [ex |] eqn:Hex1.
             ++ symmetry in Hex12.
                eapply gen_inline_sim__obs_eq;
                  [symmetry; apply (run_exc_vis_some_eq _ _ _ _ Hou1 Hex1)
                  | symmetry; apply (run_exc_vis_some_eq _ _ _ _ Hou2 Hex12) |].
                apply GIS_Step; cbn [gis_step_body observe]; apply Hexc.
             ++ symmetry in Hex12.
                eapply gen_inline_sim__obs_eq;
                  [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1)
                  | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex12) |].
                apply GIS_Step; cbn [gis_step_body observe]; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros y1 y2 Hy Hp.
                apply (Hlift_sync_cont _ _ _ (ex_intro _ env1 (ex_intro _ env2 Logic.eq_refl)) (HA y1 y2 Hy Hp)).
          -- destruct (as_local_cfg e1) as [le1 |] eqn:Ele1,
                      (as_local_cfg e2) as [le2 |] eqn:Ele2; try contradiction.
             assert (Hex1 : exc_of_event e1 = None).
             { repeat (destruct e1 as [e1 | e1]); try discriminate Ele1; reflexivity. }
             assert (Hex2 : exc_of_event e2 = None).
             { repeat (destruct e2 as [e2 | e2]); try discriminate Ele2; reflexivity. }
             eapply gen_inline_sim__obs_eq;
               [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1)
               | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex2) |].
             apply GIS_Step; cbn [gis_step_body observe]; right; right; left.
             rewrite Ele1, Ele2.
             destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
             ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                intros v Hv.
                apply (Hlift_sync_cont _ _ _ (ex_intro _ env1 (ex_intro _ env2 Logic.eq_refl)) (Hrd v Hv)).
             ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                apply (Hlift_sync_cont _ _ _
                         (ex_intro _ (Maps.add x1 v1 env1) (ex_intro _ (Maps.add x2 v2 env2) Logic.eq_refl)) Hr).
    - assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
      { rewrite observe_bind, Ha1; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [symmetry; apply (run_exc_tau_eq _ _ Hou1) | reflexivity |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
      { rewrite observe_bind, Ha2; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [reflexivity | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (LocalRead x)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (LocalRead x))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalRead x))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ReadL; [exact He1 | exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Eb2 : ITree.bind a2 k2 ≅ ITree.bind (ITree.trigger (LocalRead x)) (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (LocalRead x))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalRead x))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa2 z) k2))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ReadR; [exact He2 | exact Er2 | exact Hlk |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Hic' : ic_synced_stk stk ic').
      { destruct Hic as (e1_0 & e2_0 & ->); cbn in Hw1; injection Hw1 as <-.
        exists (Maps.add x v e1_0), e2_0; reflexivity. }
      assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (LocalWrite x v))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite x v))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_WriteL; [exact Hw1 | exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic'].
    - assert (Hic' : ic_synced_stk stk ic').
      { destruct Hic as (e1_0 & e2_0 & ->); cbn in Hw2; injection Hw2 as <-.
        exists e1_0, (Maps.add x v e2_0); reflexivity. }
      assert (Eb2 : ITree.bind a2 k2 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (LocalWrite x v))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite x v))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa2 z) k2))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_WriteR; [exact Hw2 | exact Er2 |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic'].
    - assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (GlobalRead k)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (GlobalRead k))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (GlobalRead k))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_GReadL; [exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - destruct Hic as (? & ? & Hbad); discriminate Hbad.
  Qed.

  (** ** 8D. Lifting Across [mrec], [interp_intrinsics], and [interp_state] ([to_model]) *)

  Definition is_ic_active (ic : inline_ctx) : bool :=
    match ic with
    | IC_MemPushed _ _ _ => false
    | _ => true
    end.

  Lemma gis_cont_to_sim
    {E : Type -> Type}
    `{@LocalE PaV -< E} `{@StackE PaV -< E} `{@GlobalE PaV -< E} `{@MemoryE PaV -< E}
    (is_ub : forall X, E X -> bool)
    (is_sync : inline_ctx -> forall X, E X -> bool)
    (EqE : prerel E E) (EqA : postrel E E)
    (ev_post : forall X, E X -> X -> Prop)
    (as_loc : forall X, E X -> option (@LocalE PaV X))
    (as_stk : forall X, E X -> option (@StackE PaV X))
    (opt_call1 : forall X, E X -> option (itree E X))
    (g0 : global_env) (bf : bool)
    {R1 R2 : Type} (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (u1 : itree E R1) (u2 : itree E R2) :
    gis_cont
      (upaco3
         (gen_inline_sim_ is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 bf RR)
         bot3)
      ic u1 u2 ->
    gen_inline_sim is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 bf RR ic u1 u2.
  Proof using.
    intros (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
    eapply gen_inline_sim_tau_star_l; [exact Hs1 |].
    eapply gen_inline_sim_tau_star_r; [exact Hs2 | exact Hm].
  Qed.

  Lemma cfg_inline_sim_run_exc_both
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (stk : env_stack)
    {A1 A2 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RB : inline_ctx -> @exc PaV + A1 -> @exc PaV + A2 -> Prop)
    (Hexc : forall e1 e2 ex,
              RB (IC_Synced stk e1 e2) (inl ex) (inl ex))
    (Hret : forall ic' x1 x2,
              ic_synced_stk stk ic' ->
              RA ic' x1 x2 ->
              RB ic' (inr x1) (inr x2))
    (ic : inline_ctx) (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2)
    (Hic : ic_synced_stk stk ic)
    (Hsim : cfg_inline_sim opt_call1 g0 false RA ic a1 a2) :
    cfg_inline_sim opt_call1 g0 bf RB ic (run_exc a1) (run_exc a2).
  Proof using.
    eapply gen_inline_sim_obs_eq;
      [apply run_exc_proper, Eqit.bind_ret_r
      | apply run_exc_proper, Eqit.bind_ret_r |].
    eapply (cfg_inline_sim_bind_run_exc_both opt_call1 g0 bf stk RA RB
              (fun x => Ret x) (fun x => Ret x) Hexc);
      [| exact Hic | exact Hsim].
    intros ic' x1 x2 Hic' Hra.
    eapply gen_inline_sim_obs_eq;
      [symmetry; apply (run_exc_ret_eq (Ret x1) x1 Logic.eq_refl)
      | symmetry; apply (run_exc_ret_eq (Ret x2) x2 Logic.eq_refl) |].
    apply gen_inline_sim_ret, (Hret ic' x1 x2 Hic' Hra).
  Qed.

  Lemma mcfg_inline_sim_raise {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    mcfg_inline_sim g0 bf RR ic (raise msg1) (raise msg2).
  Proof using.
    unfold raise, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
    right; left.
    split; [destruct ic; try discriminate Hact; reflexivity |].
    split; [exact I | intros [] [] _ _].
  Qed.

  Lemma mcfg_inline_sim_raiseUB {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 : string) (t2 : @MCFGtop PaV R2) :
    mcfg_inline_sim g0 bf RR ic (raiseUB msg1) t2.
  Proof using.
    unfold raiseUB, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
    left; reflexivity.
  Qed.

  Lemma mcfg_inline_sim_raiseOOM {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 : string) (t2 : @MCFGtop PaV R2) :
    mcfg_inline_sim g0 bf RR ic (raiseOOM msg1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
    left; reflexivity.
  Qed.

  Lemma mcfg_inline_sim_EOU {A : Type}
    (g0 : global_env) (bf : bool)
    (ic : inline_ctx) (m : EOU A)
    (Hact : is_ic_active ic = true) :
    mcfg_inline_sim g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply mcfg_inline_sim_raiseOOM.
    - apply mcfg_inline_sim_raiseUB.
    - apply mcfg_inline_sim_raise, Hact.
    - apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma cfg_inline_sim_raise
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf RR ic (raise msg1) (raise msg2).
  Proof using.
    unfold raise, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
    right; left.
    split; [destruct ic; try discriminate Hact; reflexivity |].
    split; [exact I | intros [] [] _ _].
  Qed.

  Lemma cfg_inline_sim_raiseUB
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 : string) (t2 : @CFGtop PaV R2) :
    cfg_inline_sim opt_call1 g0 bf RR ic (raiseUB msg1) t2.
  Proof using.
    unfold raiseUB, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
    left; reflexivity.
  Qed.

  Lemma cfg_inline_sim_raiseOOM
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 : string) (t2 : @CFGtop PaV R2) :
    cfg_inline_sim opt_call1 g0 bf RR ic (raiseOOM msg1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
    left; reflexivity.
  Qed.

  Lemma cfg_inline_sim_EOU
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {A : Type}
    (g0 : global_env) (bf : bool)
    (ic : inline_ctx) (m : EOU A)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply cfg_inline_sim_raiseOOM.
    - apply cfg_inline_sim_raiseUB.
    - apply cfg_inline_sim_raise, Hact.
    - apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma mcfg_inline_sim_trigger_refl {X : Type}
    (g0 : global_env) (bf : bool) (ic : inline_ctx) (e : @MCFGEtop PaV X)
    (Hsync : inl_sync_mcfg ic e = true) :
    mcfg_inline_sim g0 bf (fun ic' a1 a2 => ic' = ic /\ a1 = a2)
      ic (ITree.trigger e) (ITree.trigger e).
  Proof using.
    eapply gen_inline_sim_weaken;
      [| apply gen_inline_sim_trigger_sync; [exact Hsync | apply EqE_MCFG_refl]].
    intros ic' a1 a2 (-> & Ha & _); apply EqA_MCFG_eq in Ha; split; [reflexivity | exact Ha].
  Qed.

  Lemma cfg_inline_sim_trigger_refl
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {X : Type}
    (g0 : global_env) (bf : bool) (ic : inline_ctx) (e : @CFGEtop PaV X)
    (Hsync : inl_sync_cfg ic e = true) :
    cfg_inline_sim opt_call1 g0 bf (fun ic' a1 a2 => ic' = ic /\ a1 = a2)
      ic (ITree.trigger e) (ITree.trigger e).
  Proof using.
    eapply gen_inline_sim_weaken;
      [| apply gen_inline_sim_trigger_sync; [exact Hsync | apply EqE_CFG_refl]].
    intros ic' a1 a2 (-> & Ha & _); apply EqA_CFG_eq in Ha; split; [reflexivity | exact Ha].
  Qed.

  Lemma inl_withCall_proper {R : Type} (u1 u2 : @MCFGtop PaV R) :
    u1 ≅ u2 ->
    @withCall PaV R u1 ≅ @withCall PaV R u2.
  Proof using.
    unfold withCall; intros H; rewrite H; reflexivity.
  Qed.

  Lemma itree_tau_star_withCall {R : Type} (u u' : @MCFGtop PaV R) :
    itree_tau_star u u' ->
    itree_tau_star (@withCall PaV R u) (@withCall PaV R u').
  Proof using.
    intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH].
    - apply ITS_Refl.
    - eapply ITS_Eq; [apply inl_withCall_proper, Hab | exact IH].
    - eapply ITS_Eq; [unfold withCall; apply translate_tau | apply ITS_Tau, IH].
  Qed.

  Lemma inl_withCall_bind_trigger {X R : Type}
    (e : @MCFGEtop PaV X) (k : X -> @MCFGtop PaV R) :
    @withCall PaV R (ITree.bind (ITree.trigger e) k) ≅
    ITree.bind (ITree.trigger (subevent _ e)) (fun x => @withCall PaV R (k x)).
  Proof using.
    rewrite inl_withCall_bind.
    apply eq_itree_clo_bind with (UU := Logic.eq); [| intros x _ <-; reflexivity].
    unfold withCall; apply translate_trigger.
  Qed.

  Lemma mcfg_to_cfg_withCall_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall ic (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
      mcfg_inline_sim g0 false RR ic u1 u2 ->
      cfg_inline_sim opt_call1 g0 false RR ic (withCall u1) (withCall u2).
  Proof using.
    pcofix CIH.
    intros ic u1 u2 Hsim; pstep; punfold Hsim.
    assert (Hlift_cont :
      forall ic0 w1 w2,
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
                (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
                (@no_opt_call (@MCFGEtop PaV)) g0 false RR) bot3)
          ic0 w1 w2 ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false RR) r)
          ic0 (withCall w1) (withCall w2)).
    { intros ic0 w1 w2 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (withCall m1), (withCall m2).
      split; [apply itree_tau_star_withCall, Hs1 |].
      split; [apply itree_tau_star_withCall, Hs2 |].
      right; apply CIH, Hm. }
    induction Hsim as [ic u1 u2 Hstep
                       | ic u1 m1 u2 Hu1 _ IH
                       | ic u1 u2 m2 Hu2 _ IH
                       | ic env1 u1 x v k1 u2 He1 Hu1 Hlk _ IH
                       | ic env2 u1 u2 x v k2 He2 Hu2 Hlk _ IH
                       | ic ic' u1 x v k1 u2 Hw1 Hu1 _ IH
                       | ic ic' u1 u2 x v k2 Hw2 Hu2 _ IH
                       | ic u1 k v k1 u2 Hu1 Hlk _ IH
                       | stk ce1 e1 e2 u1 varg k1 u2 Hu1 _ IH
                       | stk e1 e2 u1 k1 u2 Hfr
                       | stk ce1 e2 bs u1 k1 u2 Hfr
                       | stk ce1 e1 e2 u1 k1 u2 Hfr
                       | stk ce1 e2 u1 k1 u2 Hfr
                       | stk e1 e2 u1 X ce body1 k1 u2 Hfr];
      try discriminate Hfr.
    - apply GIS_Step; unfold gis_step_body in *.
      unfold withCall; rewrite !observe_translate.
      destruct (observe u1) as [r1 | m1 | X1 e1 k1].
      + destruct (observe u2); exact Hstep.
      + destruct (observe u2); try contradiction; apply Hlift_cont, Hstep.
      + cbn [observe subevent resum ReSum_inr inr1].
        destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe u2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        cbn [observe subevent resum ReSum_inr inr1].
        destruct Hvis as [(Hsync & HE & HA) | Hls].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; apply Hlift_cont, (HA a1 a2 Ha Hp).
        * right; destruct ic as [stk env1 env2 | |]; try contradiction.
          destruct Hls as [Hloc | [Hfr_s _]]; [| discriminate Hfr_s].
          left; cbn [as_local_cfg].
          destruct (as_local_mcfg e1) as [le1 |], (as_local_mcfg e2) as [le2 |]; try contradiction.
          destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
          -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
             intros v Hv; apply Hlift_cont, Hrd, Hv.
          -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply Hlift_cont, Hr]].
    - eapply GIS_TauL; [unfold withCall; rewrite observe_translate, Hu1; reflexivity | exact IH].
    - eapply GIS_TauR; [unfold withCall; rewrite observe_translate, Hu2; reflexivity | exact IH].
    - eapply GIS_ReadL;
        [exact He1
        | rewrite (inl_withCall_proper _ _ Hu1); apply inl_withCall_bind_trigger
        | exact Hlk | exact IH].
    - eapply GIS_ReadR;
        [exact He2
        | rewrite (inl_withCall_proper _ _ Hu2); apply inl_withCall_bind_trigger
        | exact Hlk | exact IH].
    - eapply GIS_WriteL;
        [exact Hw1
        | rewrite (inl_withCall_proper _ _ Hu1); apply inl_withCall_bind_trigger
        | exact IH].
    - eapply GIS_WriteR;
        [exact Hw2
        | rewrite (inl_withCall_proper _ _ Hu2); apply inl_withCall_bind_trigger
        | exact IH].
    - eapply GIS_GReadL;
        [rewrite (inl_withCall_proper _ _ Hu1); apply inl_withCall_bind_trigger
        | exact Hlk | exact IH].
    - eapply GIS_ZeroStoreL;
        [rewrite (inl_withCall_proper _ _ Hu1); apply inl_withCall_bind_trigger
        | exact IH].
  Qed.

  Lemma inl_interp_mrec_proper (ctx : @CallE PaV ~> @CFGtop PaV)
    {R : Type} (u1 u2 : @CFGtop PaV R) :
    u1 ≅ u2 ->
    interp_mrec ctx u1 ≅ interp_mrec ctx u2.
  Proof using.
    revert u1 u2; ginit; gcofix CIH; intros u1 u2 Hu.
    rewrite (unfold_interp_mrec ctx u1), (unfold_interp_mrec ctx u2).
    punfold Hu; red in Hu.
    remember (observe u1) as ot1 eqn:Hou1;
    remember (observe u2) as ot2 eqn:Hou2.
    destruct Hu as [r1 r2 <- | m1 m2 REL | X e k1 k2 REL | |];
      symmetry in Hou1, Hou2; pclearbot; cbn [_interp_mrec].
    - gstep; constructor; reflexivity.
    - gstep; constructor; gfinal; left; apply CIH, REL.
    - destruct e as [ce | me].
      + gstep; constructor; gfinal; left; apply CIH.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros x _ <-; apply REL.
      + gstep; constructor; intros x; gstep; constructor; gfinal; left; apply CIH, REL.
  Qed.

  Lemma itree_tau_star_interp_mrec (ctx : @CallE PaV ~> @CFGtop PaV)
    {R : Type} (u u' : @CFGtop PaV R) :
    itree_tau_star u u' ->
    itree_tau_star (interp_mrec ctx u) (interp_mrec ctx u').
  Proof using.
    intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH].
    - apply ITS_Refl.
    - eapply ITS_Eq; [apply inl_interp_mrec_proper, Hab | exact IH].
    - eapply ITS_Eq; [rewrite unfold_interp_mrec; reflexivity | apply ITS_Tau, IH].
  Qed.

  Lemma interp_mrec_bind_subevent (ctx : @CallE PaV ~> @CFGtop PaV)
    {X R : Type} (me : @MCFGEtop PaV X) (k : X -> @CFGtop PaV R) :
    interp_mrec ctx (ITree.bind (ITree.trigger (inr1 me)) k) ≅
    ITree.bind (ITree.trigger me) (fun y => Tau (interp_mrec ctx (k y))).
  Proof using.
    rewrite bind_trigger, unfold_interp_mrec; cbn [observe _interp_mrec].
    rewrite <- bind_trigger; reflexivity.
  Qed.

  Lemma cfg_to_mcfg_inline_sim_mrec
    (p_callee : @ptr PaV)
    (callee_fn : @function_denotation PaV)
    (ctx1 ctx2 : IntMap (@function_denotation PaV))
    (g0 : global_env)
    (Hp_nn : (ptr_to_int p_callee >= 1)%Z)
    (Hlk_callee : lookup (ptr_to_int p_callee) ctx1 = Some callee_fn)
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk e1 e2 cc args,
                     cfg_inline_sim (callee_opt_call p_callee callee_fn) g0 true
                       (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                       (IC_Synced stk e1 e2) (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx)
      (u1 : @CFGtop PaV R1)
      (u2 : @CFGtop PaV R2),
      cfg_inline_sim (callee_opt_call p_callee callee_fn) g0 true RR ic u1 u2 ->
      mcfg_inline_sim g0 true RR ic
        (interp_mrec (inl_mrec_ctx ctx1) u1)
        (interp_mrec (inl_mrec_ctx ctx2) u2).
  Proof using.
    intros R1 R2 RR.
    set (opt_c := callee_opt_call p_callee callee_fn).
    assert (Hcall :
      forall stk env1 env2 X (c1 c2 : @CallE PaV X),
        EqE_Call X X c1 c2 ->
        cfg_inline_sim opt_c g0 true
          (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
          (IC_Synced stk env1 env2)
          (inl_mrec_ctx ctx1 X c1) (inl_mrec_ctx ctx2 X c2)).
    { intros stk env1 env2 X [dt1 cc1 fv1 fas1] [dt2 cc2 fv2 fas2] (<- & <- & <- & <-).
      unfold inl_mrec_ctx.
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
      assert (Hext :
        cfg_inline_sim opt_c g0 true
          (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
          (IC_Synced stk env1 env2)
          (Functor.fmap inr (external_call dt1 fv1 fas1))
          (Functor.fmap inr (external_call dt1 fv1 fas1))).
      { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
        eapply gen_inline_sim_bind.
        - apply cfg_inline_sim_trigger_refl; reflexivity.
        - intros ? rv1 rv2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
      unfold lookup_defn.
      destruct fv1 as [[p | | | | | | |] | |]; try exact Hext.
      pose proof (Hctx (ptr_to_int p)) as Hlk.
      destruct (lookup (ptr_to_int p) ctx1) as [f1 |],
               (lookup (ptr_to_int p) ctx2) as [f2 |];
        inversion Hlk as [? ? Hf12 |]; subst.
      - apply Hf12.
      - exact Hext. }
    pcofix CIH.
    intros ic u1 u2 Hsim; pstep.
    set (r_mrec :=
      fun ic0 (a1 : @MCFGtop PaV R1) (a2 : @MCFGtop PaV R2) =>
        exists v1 v2,
          a1 = interp_mrec (inl_mrec_ctx ctx1) v1 /\
          a2 = interp_mrec (inl_mrec_ctx ctx2) v2 /\
          cfg_inline_sim opt_c g0 true RR ic0 v1 v2).
    eapply gen_inline_sim__mon with (r := r_mrec);
      [| intros ic0 a1 a2 (v1 & v2 & -> & -> & Hv); right; apply CIH, Hv].
    assert (Hlift_tau_cont :
      forall ic0 w1 w2,
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_c g0 true RR) bot3)
          ic0 w1 w2 ->
        gis_cont r_mrec ic0
          (Tau (interp_mrec (inl_mrec_ctx ctx1) w1))
          (Tau (interp_mrec (inl_mrec_ctx ctx2) w2))).
    { intros ic0 w1 w2 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (interp_mrec (inl_mrec_ctx ctx1) m1),
             (interp_mrec (inl_mrec_ctx ctx2) m2).
      split; [apply ITS_Tau, itree_tau_star_interp_mrec, Hs1 |].
      split; [apply ITS_Tau, itree_tau_star_interp_mrec, Hs2 |].
      exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hm]]. }
    punfold Hsim; clear r CIH.
    induction Hsim as [ic u1 u2 Hstep
                       | ic u1 mu1 u2 Hu1 _ IH
                       | ic u1 u2 mu2 Hu2 _ IH
                       | ic env1 u1 x v k1 u2 He1 Hu1 Hlk _ IH
                       | ic env2 u1 u2 x v k2 He2 Hu2 Hlk _ IH
                       | ic ic' u1 x v k1 u2 Hw1 Hu1 _ IH
                       | ic ic' u1 u2 x v k2 Hw2 Hu2 _ IH
                       | ic u1 k v k1 u2 Hu1 Hlk _ IH
                       | stk ce1 e1 e2 u1 varg k1 u2 Hu1 _ IH
                       | stk e1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e2 bs u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk e1 e2 u1 X ce body1 k1 u2 Hfr Hu1 Hopt _ IH].
    - eapply gen_inline_sim__obs_eq;
        [symmetry; apply unfold_interp_mrec
        | symmetry; apply unfold_interp_mrec |].
      unfold gis_step_body in Hstep.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply GIS_Step; cbn; exact Hstep.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hstep as (m1' & m2' & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
        apply GIS_Step; cbn [gis_step_body observe _interp_mrec].
        exists (interp_mrec (inl_mrec_ctx ctx1) m1'),
               (interp_mrec (inl_mrec_ctx ctx2) m2').
        split; [apply itree_tau_star_interp_mrec, Hs1 |].
        split; [apply itree_tau_star_interp_mrec, Hs2 |].
        exists m1', m2'; split; [reflexivity | split; [reflexivity | exact Hm]].
      + destruct Hstep as [Hub | Hvis].
        * destruct ev1 as [ce1 | me1]; [discriminate Hub |].
          apply GIS_Step; cbn; left; exact Hub.
        * destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          -- destruct ev1 as [ce1 | me1], ev2 as [ce2 | me2]; cbn in HE; try contradiction.
             ++ destruct ic as [stk env1 env2 | |]; try discriminate Hsync.
                apply GIS_Step; cbn [gis_step_body observe _interp_mrec].
                exists (interp_mrec (inl_mrec_ctx ctx1) (ITree.bind (inl_mrec_ctx ctx1 _ ce1) k1)),
                       (interp_mrec (inl_mrec_ctx ctx2) (ITree.bind (inl_mrec_ctx ctx2 _ ce2) k2)).
                split; [apply ITS_Refl | split; [apply ITS_Refl |]].
                exists (ITree.bind (inl_mrec_ctx ctx1 _ ce1) k1),
                       (ITree.bind (inl_mrec_ctx ctx2 _ ce2) k2).
                split; [reflexivity | split; [reflexivity |]].
                eapply gen_inline_sim_bind; [apply Hcall, HE |].
                intros ? rv1 rv2 [-> <-].
                assert (Heqa : EqA_CFG X1 X2 (inl1 ce1) rv1 (inl1 ce2) rv1).
                { destruct ce1, ce2; cbn; reflexivity. }
                apply gis_cont_to_sim, (HA rv1 rv1 Heqa I).
             ++ apply GIS_Step; cbn [gis_step_body observe _interp_mrec]; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros a1 a2 Ha Hp; apply Hlift_tau_cont, (HA a1 a2 Ha Hp).
          -- destruct ic as [stk env1 env2 | |]; try contradiction.
             destruct Hls as [Hloc | [_ Hstk]].
             ++ destruct ev1 as [| me1], ev2 as [| me2]; cbn [as_local_cfg] in Hloc; try contradiction.
                apply GIS_Step; cbn [gis_step_body observe _interp_mrec]; right; right; left.
                destruct (as_local_mcfg me1) as [le1 |], (as_local_mcfg me2) as [le2 |]; try contradiction.
                destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
                ** destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                   intros v Hv; apply Hlift_tau_cont, Hrd, Hv.
                ** destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply Hlift_tau_cont, Hr]].
             ++ destruct ev1 as [| me1], ev2 as [| me2]; cbn [as_stack_cfg] in Hstk; try contradiction.
                apply GIS_Step; cbn [gis_step_body observe _interp_mrec]; right; right; right.
                split; [reflexivity |].
                destruct (as_stack_mcfg me1) as [se1 |], (as_stack_mcfg me2) as [se2 |]; try contradiction.
                destruct se1, se2; try contradiction.
                ** destruct Hstk as [Hbs Hr]; split; [exact Hbs | apply Hlift_tau_cont, Hr].
                ** destruct stk as [[p1 p2] rest |]; [apply Hlift_tau_cont, Hstk | exact I].
    - eapply gen_inline_sim__obs_eq;
        [symmetry; rewrite unfold_interp_mrec, Hu1; reflexivity | reflexivity |].
      eapply GIS_TauL; [reflexivity | exact IH].
    - eapply gen_inline_sim__obs_eq;
        [reflexivity | symmetry; rewrite unfold_interp_mrec, Hu2; reflexivity |].
      eapply GIS_TauR; [reflexivity | exact IH].
    - eapply GIS_ReadL;
        [exact He1
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | exact Hlk
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_ReadR;
        [exact He2
        | rewrite (inl_interp_mrec_proper _ _ _ Hu2); apply interp_mrec_bind_subevent
        | exact Hlk
        | eapply GIS_TauR; [reflexivity | exact IH]].
    - eapply GIS_WriteL;
        [exact Hw1
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_WriteR;
        [exact Hw2
        | rewrite (inl_interp_mrec_proper _ _ _ Hu2); apply interp_mrec_bind_subevent
        | eapply GIS_TauR; [reflexivity | exact IH]].
    - eapply GIS_GReadL;
        [rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | exact Hlk
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_ZeroStoreL;
        [rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_MemPushL;
        [exact Hfr
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_StackPushL;
        [exact Hfr
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_StackPopL;
        [exact Hfr
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_MemPopL;
        [exact Hfr
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - destruct ce as [ce0 | me0]; [| discriminate Hopt].
      destruct ce0 as [dt cc fv args]; cbn [opt_c callee_opt_call] in Hopt.
      destruct fv as [[p | | | | | | |] | |]; try discriminate Hopt.
      destruct (Z.eqb_spec (ptr_to_int p) (ptr_to_int p_callee)) as [Hp_eq | _];
        [| discriminate Hopt].
      injection Hopt as <-.
      assert (Hp_gt0 : (ptr_to_int p > 0)%Z) by lia.
      assert (Emrec_step :
        interp_mrec (inl_mrec_ctx ctx1) u1 ≅
        Tau (interp_mrec (inl_mrec_ctx ctx1) (ITree.bind (callee_fn cc args) k1))).
      { rewrite (inl_interp_mrec_proper _ _ _ Hu1), bind_trigger, unfold_interp_mrec.
        cbn [observe _interp_mrec].
        apply eqit_Tau, inl_interp_mrec_proper.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        unfold inl_mrec_ctx; rewrite (check_callee_nonnull_ptr p Hp_gt0).
        cbn [EOU_to_itree lookup_defn ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        rewrite Eqit.bind_ret_l, Hp_eq, Hlk_callee; reflexivity. }
      eapply gen_inline_sim__obs_eq; [symmetry; exact Emrec_step | reflexivity |].
      eapply GIS_TauL; [reflexivity | exact IH].
  Qed.

  (** *** Lifting [mcfg_inline_sim] Across [interp_intrinsics] *)

  Definition inl_sem_fn_sync
    (g0 : global_env)
    (sem : @semantic_function PaV (@MCFGEtop PaV) _ _ _ _) : Prop :=
    forall args va stk env1 env2,
      mcfg_inline_sim g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
        (IC_Synced stk env1 env2) (sem args va) (sem args va).

  Lemma inl_pure_to_semantic_sync (g0 : global_env) pf :
    inl_sem_fn_sync g0 (pure_to_semantic pf).
  Proof using.
    intros args va stk env1 env2; unfold pure_to_semantic.
    apply mcfg_inline_sim_EOU; reflexivity.
  Qed.

  Lemma inl_pure_base_to_semantic_sync (g0 : global_env) pbf :
    inl_sem_fn_sync g0 (pure_base_to_semantic pbf).
  Proof using.
    unfold pure_base_to_semantic; apply inl_pure_to_semantic_sync.
  Qed.

  Lemma inl_Forall_map_pure_to_semantic {A : Type} (g0 : global_env)
    (f : A -> declaration dtyp * _) (l : list A)
    (Hf : forall x, inl_sem_fn_sync g0 (snd (f x))) :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) (List.map f l).
  Proof using.
    induction l as [| x xs IH]; constructor; [apply Hf | exact IH].
  Qed.

  Lemma inl_defined_intrinsics_sync (g0 : global_env) :
    Forall (fun p => inl_sem_fn_sync g0 (snd p))
      (@defined_intrinsics PaV (@MCFGEtop PaV) _ _ _ _).
  Proof using.
    unfold defined_intrinsics, extra_fp_intrinsics, extra_int_intrinsics.
    repeat apply Forall_app;
      try (repeat constructor; cbn [snd]; apply inl_pure_base_to_semantic_sync);
      try (apply inl_Forall_map_pure_to_semantic; intros; cbn [snd];
           first [apply inl_pure_to_semantic_sync | apply inl_pure_base_to_semantic_sync]).
    repeat constructor; cbn [snd]; try apply inl_pure_base_to_semantic_sync.
    - (* llvm_va_start *)
      intros args va stk env1 env2; unfold llvm_va_start.
      destruct args as [| a [| ? ?]], va as [vp |];
        try (apply mcfg_inline_sim_raise; reflexivity).
      destruct a as [[p | | | | | | |] | |];
        try (eapply gen_inline_sim_bind;
             [unfold store; apply mcfg_inline_sim_trigger_refl; reflexivity
             | intros ? [] _ [-> _]; apply gen_inline_sim_ret; split; reflexivity]).
      apply mcfg_inline_sim_raiseUB.
    - (* llvm_va_end *)
      intros args va stk env1 env2; unfold llvm_va_end.
      apply gen_inline_sim_ret; split; reflexivity.
    - (* llvm_va_copy *)
      intros args va stk env1 env2; unfold llvm_va_copy.
      destruct args as [| dst [| src [| ? ?]]];
        try (apply mcfg_inline_sim_raise; reflexivity).
      eapply gen_inline_sim_bind.
      + unfold load; apply mcfg_inline_sim_trigger_refl; reflexivity.
      + intros ? vargs _ [-> <-].
        eapply gen_inline_sim_bind.
        * unfold store; apply mcfg_inline_sim_trigger_refl; reflexivity.
        * intros ? [] _ [-> _]; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma mcfg_inline_sim_handle_intrinsics {X : Type}
    (g0 : global_env) (ie : @IntrinsicE PaV X) stk env1 env2 :
    mcfg_inline_sim g0 true
      (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
      (IC_Synced stk env1 env2)
      (handle_intrinsics ie) (handle_intrinsics ie).
  Proof using.
    destruct ie as [dt fname args va]; cbn [handle_intrinsics].
    pose proof (inl_defined_intrinsics_sync g0) as Hdefs.
    unfold defs_assoc.
    induction Hdefs as [| [decl sem] rest Hsem _ IH]; cbn [List.map].
    - cbn; apply mcfg_inline_sim_trigger_refl; reflexivity.
    - cbn [snd] in Hsem.
      set (nm := match dc_name decl with Name s => s | _ => ""%string end).
      cbn [assoc].
      destruct (Eqv.eqv_dec_p fname nm) as [_ | _].
      + apply Hsem.
      + exact IH.
  Qed.

  Lemma interp_intrinsics_bind_non_intr {X R : Type}
    (me : @MCFGEtop PaV X) (k : X -> @MCFGtop PaV R)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_intrinsics (ITree.bind (ITree.trigger me) k) ≅
    ITree.bind (ITree.trigger me) (fun x => Tau (interp_intrinsics (k x))).
  Proof using.
    unfold interp_intrinsics.
    rewrite bind_trigger, unfold_interp; cbn [_interp observe]; rewrite Hni.
    reflexivity.
  Qed.

  Lemma mcfg_inline_sim_interp_intrinsics (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall ic (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
      mcfg_inline_sim g0 true RR ic u1 u2 ->
      mcfg_inline_sim g0 true RR ic (interp_intrinsics u1) (interp_intrinsics u2).
  Proof using.
    set (intr_rel :=
      fun ic0 (x1 : R1 + @MCFGtop PaV R1) (x2 : R2 + @MCFGtop PaV R2) =>
        match x1, x2 with
        | inl r1, inl r2 => RR ic0 r1 r2
        | inr v1, inr v2 => mcfg_inline_sim g0 true RR ic0 v1 v2
        | _, _ => False
        end).
    assert (Hstep_decomp :
      forall ic (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
        gis_step_body (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
          (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) true
          RR
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
                (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
                (@no_opt_call (@MCFGEtop PaV)) g0 true RR) bot3)
          ic (observe u1) (observe u2) ->
        mcfg_inline_sim g0 true intr_rel ic (decomp_intr u1) (decomp_intr u2)).
    { intros ic u1 u2 Hstep.
      unfold gis_step_body, decomp_intr in *.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply gen_inline_sim_ret; exact Hstep.
      - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply gen_inline_sim_ret; apply gis_cont_to_sim, Hstep.
      - destruct Hstep as [Hub | Hvis].
        + assert (Hni1 : interp_intrinsics_h ev1 = ITree.trigger ev1).
          { repeat (destruct ev1 as [ev1 | ev1]); try discriminate Hub; reflexivity. }
          rewrite Hni1; unfold ITree.trigger.
          pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
          left; exact Hub.
        + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * destruct ev1 as [ec1 | [ie1 | rest1]], ev2 as [ec2 | [ie2 | rest2]];
              cbn in HE; try contradiction.
            -- cbn [interp_intrinsics_h]; unfold ITree.trigger.
               pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
               right; left; split; [exact Hsync | split; [exact HE |]].
               intros a1 a2 Ha Hp.
               exists (Ret (inr (k1 a1))), (Ret (inr (k2 a2))).
               split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
               split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
               left; apply gen_inline_sim_ret; apply gis_cont_to_sim, (HA a1 a2 Ha Hp).
            -- destruct ic as [stk env1 env2 | |]; try discriminate Hsync.
               assert (Hie_eq : ie1 = ie2).
               { destruct ie1, ie2; destruct HE as (<- & <- & <- & <-); reflexivity. }
               subst ie2; cbn [interp_intrinsics_h case_ id_ Id_IFun].
               eapply gen_inline_sim_bind;
                 [apply mcfg_inline_sim_handle_intrinsics |].
               intros ? a1 a2 [-> <-]; apply gen_inline_sim_ret; cbn [intr_rel].
               assert (Heqa : EqA_MCFG X1 X2 (inr1 (inl1 ie1)) a1 (inr1 (inl1 ie1)) a1).
               { destruct ie1; cbn; reflexivity. }
               apply gis_cont_to_sim, (HA a1 a1 Heqa I).
            -- cbn [interp_intrinsics_h]; unfold ITree.trigger.
               pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
               right; left; split; [exact Hsync | split; [exact HE |]].
               intros a1 a2 Ha Hp.
               exists (Ret (inr (k1 a1))), (Ret (inr (k2 a2))).
               split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
               split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
               left; apply gen_inline_sim_ret; apply gis_cont_to_sim, (HA a1 a2 Ha Hp).
          * destruct ic as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [_ Hstk]].
            -- destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                        (as_local_mcfg ev2) as [le2 |] eqn:Ele2; try contradiction.
               assert (Hni1 : interp_intrinsics_h ev1 = ITree.trigger ev1).
               { repeat (destruct ev1 as [ev1 | ev1]); try discriminate Ele1; reflexivity. }
               assert (Hni2 : interp_intrinsics_h ev2 = ITree.trigger ev2).
               { repeat (destruct ev2 as [ev2 | ev2]); try discriminate Ele2; reflexivity. }
               rewrite Hni1, Hni2; unfold ITree.trigger.
               pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
               right; right; left; rewrite Ele1, Ele2.
               destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
               ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                  intros v Hv.
                  exists (Ret (inr (k1 v))), (Ret (inr (k2 v))).
                  split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                  split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                  left; apply gen_inline_sim_ret; apply gis_cont_to_sim, Hrd, Hv.
               ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                  exists (Ret (inr (k1 tt))), (Ret (inr (k2 tt))).
                  split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                  split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                  left; apply gen_inline_sim_ret; apply gis_cont_to_sim, Hr.
            -- destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                        (as_stack_mcfg ev2) as [se2 |] eqn:Ese2; try contradiction.
               assert (Hni1 : interp_intrinsics_h ev1 = ITree.trigger ev1).
               { repeat (destruct ev1 as [ev1 | ev1]); try discriminate Ese1; reflexivity. }
               assert (Hni2 : interp_intrinsics_h ev2 = ITree.trigger ev2).
               { repeat (destruct ev2 as [ev2 | ev2]); try discriminate Ese2; reflexivity. }
               rewrite Hni1, Hni2; unfold ITree.trigger.
               pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
               right; right; right; split; [reflexivity |]; rewrite Ese1, Ese2.
               destruct se1, se2; try contradiction.
               ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs |].
                  exists (Ret (inr (k1 tt))), (Ret (inr (k2 tt))).
                  split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                  split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                  left; apply gen_inline_sim_ret; apply gis_cont_to_sim, Hr.
               ++ destruct stk as [[p1 p2] rest |]; [| exact I].
                  exists (Ret (inr (k1 tt))), (Ret (inr (k2 tt))).
                  split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                  split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                  left; apply gen_inline_sim_ret; apply gis_cont_to_sim, Hstk. }
    set (r_both :=
      fun ic0 (a1 : @MCFGtop PaV R1) (a2 : @MCFGtop PaV R2) =>
        (exists v1 v2,
           a1 = interp_intrinsics v1 /\
           a2 = interp_intrinsics v2 /\
           mcfg_inline_sim g0 true RR ic0 v1 v2) \/
        (exists w1 w2,
           a1 = ITree.bind w1 intr_cont /\
           a2 = ITree.bind w2 intr_cont /\
           mcfg_inline_sim g0 true intr_rel ic0 w1 w2)).
    assert (Hbranch_b :
      forall ic0 w1 w2,
        mcfg_inline_sim g0 true intr_rel ic0 w1 w2 ->
        gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
          (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
          (@no_opt_call (@MCFGEtop PaV)) g0 true RR r_both
          ic0 (ITree.bind w1 intr_cont) (ITree.bind w2 intr_cont)).
    { intros ic0 w1 w2 Hw; punfold Hw.
      assert (Hlift_b :
        forall ic1 q1 q2,
          gis_cont
            (upaco3
               (gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
                  (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
                  (@no_opt_call (@MCFGEtop PaV)) g0 true intr_rel) bot3)
            ic1 q1 q2 ->
          gis_cont r_both ic1 (ITree.bind q1 intr_cont) (ITree.bind q2 intr_cont)).
      { intros ic1 q1 q2 Hc.
        exists (ITree.bind q1 intr_cont), (ITree.bind q2 intr_cont).
        split; [apply ITS_Refl | split; [apply ITS_Refl |]].
        right; exists q1, q2; split; [reflexivity | split; [reflexivity | apply gis_cont_to_sim, Hc]]. }
      induction Hw as [ic0 w1 w2 Hstep
                       | ic0 w1 mw1 w2 Hw1 _ IH
                       | ic0 w1 w2 mw2 Hw2 _ IH
                       | ic0 env1 w1 x v fw1 w2 He1 Hw1 Hlk _ IH
                       | ic0 env2 w1 w2 x v fw2 He2 Hw2 Hlk _ IH
                       | ic0 ic' w1 x v fw1 w2 Hw_ic Hw1 _ IH
                       | ic0 ic' w1 w2 x v fw2 Hw_ic Hw2 _ IH
                       | ic0 w1 k v fw1 w2 Hw1 Hlk _ IH
                       | stk ce1 e1 e2 w1 varg fw1 w2 Hw1 _ IH
                       | stk e1 e2 w1 fw1 w2 Hfr Hw1 _ IH
                       | stk ce1 e2 bs w1 fw1 w2 Hfr Hw1 _ IH
                       | stk ce1 e1 e2 w1 fw1 w2 Hfr Hw1 _ IH
                       | stk ce1 e2 w1 fw1 w2 Hfr Hw1 _ IH
                       | stk e1 e2 w1 X ce body1 fw1 w2 Hfr Hw1 Hopt];
        [| | | | | | | | | | | | | discriminate Hopt].
      - unfold gis_step_body in Hstep.
        destruct (observe w1) as [x1 | mw1 | X1 ev1 fw1] eqn:How1.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 fw2] eqn:How2; try contradiction.
          destruct x1 as [r1 | v1], x2 as [r2 | v2]; cbn in Hstep; try contradiction.
          * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, How1, How2; cbn; exact Hstep.
          * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, How1, How2; cbn.
            exists (interp_intrinsics v1), (interp_intrinsics v2).
            split; [apply ITS_Refl | split; [apply ITS_Refl |]].
            left; exists v1, v2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 fw2] eqn:How2; try contradiction.
          apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, How1, How2.
          apply Hlift_b, Hstep.
        + apply GIS_Step; unfold gis_step_body; rewrite (observe_bind w1 intr_cont), How1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe w2) as [x2 | mw2 | X2 ev2 fw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 intr_cont), How2.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; apply Hlift_b, (HA a1 a2 Ha Hp).
          * right; destruct ic0 as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [_ Hstk]].
            -- left; destruct (as_local_mcfg ev1) as [le1 |], (as_local_mcfg ev2) as [le2 |]; try contradiction.
               destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
               ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                  intros v Hv; apply Hlift_b, Hrd, Hv.
               ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply Hlift_b, Hr]].
            -- right; split; [reflexivity |];
               destruct (as_stack_mcfg ev1) as [se1 |], (as_stack_mcfg ev2) as [se2 |]; try contradiction.
               destruct se1, se2; try contradiction.
               ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs | apply Hlift_b, Hr].
               ++ destruct stk as [[p1 p2] rest |]; [apply Hlift_b, Hstk | exact I].
      - eapply GIS_TauL; [rewrite (observe_bind w1 intr_cont), Hw1; reflexivity | exact IH].
      - eapply GIS_TauR; [rewrite (observe_bind w2 intr_cont), Hw2; reflexivity | exact IH].
      - eapply GIS_ReadL; [exact He1 | rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_ReadR; [exact He2 | rewrite Hw2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_WriteL; [exact Hw_ic | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_WriteR; [exact Hw_ic | rewrite Hw2, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_GReadL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_ZeroStoreL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_MemPushL; [exact Hfr | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_StackPushL; [exact Hfr | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_StackPopL; [exact Hfr | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_MemPopL; [exact Hfr | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH]. }
    assert (Hbranch_a :
      forall ic0 v1 v2,
        mcfg_inline_sim g0 true RR ic0 v1 v2 ->
        gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
          (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
          (@no_opt_call (@MCFGEtop PaV)) g0 true RR r_both
          ic0 (interp_intrinsics v1) (interp_intrinsics v2)).
    { intros ic0 v1 v2 Hv; punfold Hv.
      induction Hv as [ic0 v1 v2 Hstep
                       | ic0 v1 mv1 v2 Hv1 _ IH
                       | ic0 v1 v2 mv2 Hv2 _ IH
                       | ic0 env1 v1 x v kv1 v2 He1 Hv1 Hlk _ IH
                       | ic0 env2 v1 v2 x v kv2 He2 Hv2 Hlk _ IH
                       | ic0 ic' v1 x v kv1 v2 Hw_ic Hv1 _ IH
                       | ic0 ic' v1 v2 x v kv2 Hw_ic Hv2 _ IH
                       | ic0 v1 k v kv1 v2 Hv1 Hlk _ IH
                       | stk ce1 e1 e2 v1 varg kv1 v2 Hv1 _ IH
                       | stk e1 e2 v1 kv1 v2 Hfr Hv1 _ IH
                       | stk ce1 e2 bs v1 kv1 v2 Hfr Hv1 _ IH
                       | stk ce1 e1 e2 v1 kv1 v2 Hfr Hv1 _ IH
                       | stk ce1 e2 v1 kv1 v2 Hfr Hv1 _ IH
                       | stk e1 e2 v1 X ce body1 kv1 v2 Hfr Hv1 Hopt];
        [| | | | | | | | | | | | | discriminate Hopt].
      - eapply gen_inline_sim__obs_eq;
          [apply decomp_intr_spec | apply decomp_intr_spec |].
        apply Hbranch_b, Hstep_decomp, Hstep.
      - eapply gen_inline_sim__obs_eq;
          [symmetry; unfold interp_intrinsics; rewrite unfold_interp, Hv1; reflexivity
          | reflexivity |].
        eapply GIS_TauL; [reflexivity | exact IH].
      - eapply gen_inline_sim__obs_eq;
          [reflexivity
          | symmetry; unfold interp_intrinsics; rewrite unfold_interp, Hv2; reflexivity |].
        eapply GIS_TauR; [reflexivity | exact IH].
      - eapply GIS_ReadL;
          [exact He1
          | unfold interp_intrinsics at 1; rewrite Hv1; fold (interp_intrinsics (ITree.bind (ITree.trigger (LocalRead x)) kv1));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | exact Hlk
          | eapply GIS_TauL; [reflexivity | exact IH]].
      - eapply GIS_ReadR;
          [exact He2
          | unfold interp_intrinsics at 1; rewrite Hv2; fold (interp_intrinsics (ITree.bind (ITree.trigger (LocalRead x)) kv2));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | exact Hlk
          | eapply GIS_TauR; [reflexivity | exact IH]].
      - eapply GIS_WriteL;
          [exact Hw_ic
          | unfold interp_intrinsics at 1; rewrite Hv1; fold (interp_intrinsics (ITree.bind (ITree.trigger (LocalWrite x v)) kv1));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | eapply GIS_TauL; [reflexivity | exact IH]].
      - eapply GIS_WriteR;
          [exact Hw_ic
          | unfold interp_intrinsics at 1; rewrite Hv2; fold (interp_intrinsics (ITree.bind (ITree.trigger (LocalWrite x v)) kv2));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | eapply GIS_TauR; [reflexivity | exact IH]].
      - eapply GIS_GReadL;
          [unfold interp_intrinsics at 1; rewrite Hv1; fold (interp_intrinsics (ITree.bind (ITree.trigger (GlobalRead k)) kv1));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | exact Hlk
          | eapply GIS_TauL; [reflexivity | exact IH]].
      - eapply GIS_ZeroStoreL;
          [unfold interp_intrinsics at 1; rewrite Hv1;
            fold (interp_intrinsics
                    (ITree.bind
                       (ITree.trigger
                          (Store (DTYPE_Struct true [])
                             (DVALUE_Base (DVALUE_Pointer varg))
                             (DVALUE_Struct true []))) kv1));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | eapply GIS_TauL; [reflexivity | exact IH]].
      - eapply GIS_MemPushL;
          [exact Hfr
          | unfold interp_intrinsics at 1; rewrite Hv1; fold (interp_intrinsics (ITree.bind (ITree.trigger MemPush) kv1));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | eapply GIS_TauL; [reflexivity | exact IH]].
      - eapply GIS_StackPushL;
          [exact Hfr
          | unfold interp_intrinsics at 1; rewrite Hv1; fold (interp_intrinsics (ITree.bind (ITree.trigger (StackPush bs)) kv1));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | eapply GIS_TauL; [reflexivity | exact IH]].
      - eapply GIS_StackPopL;
          [exact Hfr
          | unfold interp_intrinsics at 1; rewrite Hv1; fold (interp_intrinsics (ITree.bind (ITree.trigger StackPop) kv1));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | eapply GIS_TauL; [reflexivity | exact IH]].
      - eapply GIS_MemPopL;
          [exact Hfr
          | unfold interp_intrinsics at 1; rewrite Hv1; fold (interp_intrinsics (ITree.bind (ITree.trigger MemPop) kv1));
            apply interp_intrinsics_bind_non_intr; reflexivity
          | eapply GIS_TauL; [reflexivity | exact IH]]. }
    assert (Hmain :
      forall ic0 t1 t2,
        r_both ic0 t1 t2 ->
        mcfg_inline_sim g0 true RR ic0 t1 t2).
    { pcofix CIH.
      intros ic0 t1 t2 Hrb; pstep.
      eapply gen_inline_sim__mon with (r := r_both);
        [| intros ic1 a1 a2 Hr; right; apply CIH, Hr].
      destruct Hrb as [(v1 & v2 & -> & -> & Hv) | (w1 & w2 & -> & -> & Hw)].
      - apply Hbranch_a, Hv.
      - apply Hbranch_b, Hw. }
    intros ic u1 u2 Hsim.
    apply Hmain; left; exists u1, u2; split; [reflexivity | split; [reflexivity | exact Hsim]].
  Qed.

  (** *** Soundness of [mcfg_inline_sim] over [interp_state interp_vellvm_prov_h] *)

  Lemma interp_vellvm_prov_h_inline_sync {X1 X2 : Type}
    (g0 : global_env) (ic : inline_ctx)
    (e1 : @MCFGEtop PaV X1) (e2 : @MCFGEtop PaV X2)
    (Hsync : inl_sync_mcfg ic e1 = true)
    (HE : EqE_MCFG X1 X2 e1 e2)
    (s1 s2 : FusedS)
    (Hmatch : inline_fused_match g0 ic s1 s2)
    (U : list N) :
    refine_prov
      (fun _ '(s1', a1) '(s2', a2) =>
         inline_fused_match g0 ic s1' s2' /\
         EqA_MCFG X1 X2 e1 a1 e2 a2 /\
         inl_mcfg_event_post e1 a1)
      U (interp_vellvm_prov_h e1 s1) (interp_vellvm_prov_h e2 s2).
  Proof using.
    destruct s1 as [m1 [[sf1 fstk1] g1]], s2 as [m2 [[sf2 fstk2] g2]].
    destruct ic as [stk env1 env2 | stk env1 env2 | stk ce1 env1 env2];
      [| discriminate Hsync |].
    - (* IC_Synced *)
      destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
      destruct_sum2 e1 e2 HE; try discriminate Hsync.
      + (* ExternalCallE *)
        destruct e1, e2; cbn in HE; try contradiction;
          repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
          unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov;
          (eapply refine_prov_bind;
           [apply refine_prov_refl with (RR := fun _ a1 a2 => a1 = a2); intros; reflexivity
           | intros U' a1 a2 _ <-; pstep; apply RP_Step; cbn;
             repeat split; try exact Hsf; try exact Hsfm; reflexivity]).
      + (* IntrinsicE *)
        destruct e1, e2; destruct HE as (<- & <- & <- & <-).
        unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_intrinsic_prov, on_mem_prov.
        eapply refine_prov_bind;
          [apply refine_prov_refl with (RR := fun _ p1 p2 => p1 = p2); intros; reflexivity |].
        intros U' [m' r] _ _ <-; pstep; apply RP_Step; cbn.
        repeat split; try exact Hsf; try exact Hsfm; reflexivity.
      + (* GlobalE: only GlobalRead *)
        destruct e1 as [k1 v1 | k1], e2 as [k2 v2 | k2];
          cbn in HE; try contradiction; try discriminate Hsync.
        subst k2; unfold interp_vellvm_prov_h; cbn [case_].
        destruct (Maps.lookup k1 g0) as [gv |] eqn:Egv.
        * eapply refine_prov_obs_eq;
            [symmetry; apply (fused_global_prov_read_some k1 gv (m2, ((sf1, fstk1), g0)) Egv)
            | symmetry; apply (fused_global_prov_read_some k1 gv (m2, ((sf2, fstk2), g0)) Egv) |].
          pstep; apply RP_Step; cbn; repeat split; try exact Hsf; try exact Hsfm; reflexivity.
        * destruct (fused_global_prov_read_none k1 (m2, ((sf1, fstk1), g0)) Egv) as (u1 & kf1 & Ef1).
          destruct (fused_global_prov_read_none k1 (m2, ((sf2, fstk2), g0)) Egv) as (u2 & kf2 & Ef2).
          eapply refine_prov_obs_eq; [symmetry; exact Ef1 | symmetry; exact Ef2 |].
          pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + (* StackE: StackRaise / StackGetExc *)
        destruct e1, e2; cbn in HE; try contradiction; try discriminate Hsync.
        * subst; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_stack_prov, on_ls_prov, handle_stack.
          eapply refine_prov_obs_eq;
            [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
          destruct Hsf as (Hv1 & Hv2 & Hexc & Hloc).
          pstep; apply RP_Step; cbn;
            repeat split; try exact Hv1; try exact Hv2; try exact Hloc; try exact Hsfm; reflexivity.
        * unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_stack_prov, on_ls_prov, handle_stack.
          destruct Hsf as (Hv1 & Hv2 & Hexc & Hloc).
          rewrite <- Hexc.
          eapply refine_prov_obs_eq;
            [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
          pstep; apply RP_Step; cbn;
            repeat split; try exact Hv1; try exact Hv2; try exact Hloc; try exact Hsfm; reflexivity.
      + (* MemoryE *)
        assert (Hme_eq : e1 = e2) by
          (destruct e1, e2; cbn in HE; try contradiction;
           repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst; reflexivity).
        subst e2.
        unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_memory_prov, on_mem_prov, handle_memory.
        eapply refine_prov_bind.
        * apply (memM_interp_prov_post _ (handle_memoryM e1) (handle_memoryM_inl_post e1)).
        * intros U' [m1' r1] [m2' r2] _ (-> & <- & Hpost).
          pstep; apply RP_Step; cbn [rp_step_body observe inline_fused_match inl_mcfg_event_post].
          split; [repeat split; try exact Hsf; try exact Hsfm; reflexivity |].
          split; [destruct e1; cbn; reflexivity | exact Hpost].
      + (* DrawE *)
        destruct e1 as [dt1], e2 as [dt2]; subst dt2.
        unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_draw_prov, handle_draw.
        destruct (default_dvalue_of_dtyp dt1) as [s | s | s | dv]; cbn [EOU_to_itree].
        * unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
        * unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
        * unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn.
          right; right; split; [exact I | intros [] [] _].
        * eapply refine_prov_obs_eq;
            [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
          pstep; apply RP_Step; cbn;
            repeat split; try exact Hsf; try exact Hsfm; reflexivity.
      + (* OOME *)
        destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
      + (* LLVMExcE *)
        destruct e1, e2; subst; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; right; right; split; [reflexivity | intros [] [] _].
      + (* UBE *)
        destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
      + (* DebugE *)
        destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
        right; right; split; [exact I | intros [] [] _].
        left; eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        pstep; apply RP_Step; cbn.
        repeat split; try exact Hsf; try exact Hsfm; reflexivity.
      + (* FailureE *)
        destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; right; right; split; [exact I | intros [] [] _].
    - (* IC_Inlined *)
      destruct Hmatch as (-> & -> & -> & Hvars1 & csf1 & fstk1' & -> & Hcsf & Hsfm).
      destruct_sum2 e1 e2 HE; try discriminate Hsync.
      + (* GlobalE: GlobalRead *)
        destruct e1 as [k1 v1 | k1], e2 as [k2 v2 | k2];
          cbn in HE; try contradiction; try discriminate Hsync.
        subst k2; unfold interp_vellvm_prov_h; cbn [case_].
        destruct (Maps.lookup k1 g0) as [gv |] eqn:Egv.
        * eapply refine_prov_obs_eq;
            [symmetry; apply (fused_global_prov_read_some k1 gv (push_empty_frame m2, ((sf1, csf1 :: fstk1'), g0)) Egv)
            | symmetry; apply (fused_global_prov_read_some k1 gv (m2, ((sf2, fstk2), g0)) Egv) |].
          pstep; apply RP_Step; cbn.
          split; [split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hvars1 | exists csf1, fstk1'; auto]]]] |].
          split; [reflexivity | exact I].
        * destruct (fused_global_prov_read_none k1 (push_empty_frame m2, ((sf1, csf1 :: fstk1'), g0)) Egv) as (u1 & kf1 & Ef1).
          destruct (fused_global_prov_read_none k1 (m2, ((sf2, fstk2), g0)) Egv) as (u2 & kf2 & Ef2).
          eapply refine_prov_obs_eq; [symmetry; exact Ef1 | symmetry; exact Ef2 |].
          pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + (* MemoryE: is_callee_sync_mem e1 = true *)
        assert (Hme_eq : e1 = e2) by
          (destruct e1, e2; cbn in HE; try contradiction;
           repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst; reflexivity).
        subst e2.
        unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_memory_prov, on_mem_prov, handle_memory.
        eapply refine_prov_bind.
        * apply (handle_memoryM_empty_frame e1 Hsync m2 U).
        * intros U' [m1' r1] [m2' r2] _ (-> & <- & Hpost).
          pstep; apply RP_Step; cbn [rp_step_body observe inline_fused_match inl_mcfg_event_post].
          split; [split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hvars1 | exists csf1, fstk1'; auto]]]] |].
          split; [destruct e1; cbn; reflexivity | exact Hpost].
      + (* DrawE *)
        destruct e1 as [dt1], e2 as [dt2]; subst dt2.
        unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_draw_prov, handle_draw.
        destruct (default_dvalue_of_dtyp dt1) as [s | s | s | dv]; cbn [EOU_to_itree].
        * unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
        * unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
        * unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn.
          right; right; split; [exact I | intros [] [] _].
        * eapply refine_prov_obs_eq;
            [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
          pstep; apply RP_Step; cbn.
          split; [split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hvars1 | exists csf1, fstk1'; auto]]]] |].
          split; [reflexivity | exact I].
      + (* OOME *)
        destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
      + (* UBE *)
        destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
      + (* DebugE *)
        destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
        right; right; split; [exact I | intros [] [] _].
        left; eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        pstep; apply RP_Step; cbn.
        split; [split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hvars1 | exists csf1, fstk1'; auto]]]] |].
        split; [reflexivity | exact I].
      + (* FailureE *)
        destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_]; unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Definition model_inline_step_rel (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    : list N -> model_step_state R1 -> model_step_state R2 -> Prop :=
    fun _ x1 x2 =>
      match x1, x2 with
      | inl (s1, r1), inl (s2, r2) =>
          exists ic, inline_fused_match g0 ic s1 s2 /\ RR ic r1 r2
      | inr (s1, u1), inr (s2, u2) =>
          exists ic, inline_fused_match g0 ic s1 s2 /\ mcfg_inline_sim g0 true RR ic u1 u2
      | _, _ => False
      end.

  Lemma mcfg_inline_sim_to_model (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall U ic (s1 s2 : FusedS)
      (u1 : @MCFGtop PaV R1)
      (u2 : @MCFGtop PaV R2),
      inline_fused_match g0 ic s1 s2 ->
      mcfg_inline_sim g0 true RR ic u1 u2 ->
      refine_prov
        (fun _ '(s1', r1) '(s2', r2) =>
           exists ic', inline_fused_match g0 ic' s1' s2' /\ RR ic' r1 r2)
        U
        (interp_state interp_vellvm_prov_h u1 s1)
        (interp_state interp_vellvm_prov_h u2 s2).
  Proof using.
    set (RR_out :=
      fun (_ : list N) '(s1', r1) '(s2', r2) =>
        exists ic', inline_fused_match g0 ic' s1' s2' /\ RR ic' r1 r2).
    assert (Hstep_decomp :
      forall U ic (s1 s2 : FusedS)
        (u1 : @MCFGtop PaV R1)
        (u2 : @MCFGtop PaV R2),
        inline_fused_match g0 ic s1 s2 ->
        gis_step_body (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
          (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) true
          RR
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
                (@inl_mcfg_event_post) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
                (@no_opt_call (@MCFGEtop PaV)) g0 true RR) bot3)
          ic (observe u1) (observe u2) ->
        refine_prov (model_inline_step_rel g0 RR) U (decomp_model u1 s1) (decomp_model u2 s2)).
    { intros U ic s1 s2 u1 u2 Hmatch Hstep.
      unfold gis_step_body, decomp_model in *.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        pstep; apply RP_Step; cbn; exists ic; split; assumption.
      - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        pstep; apply RP_Step; cbn; exists ic; split; [exact Hmatch | apply gis_cont_to_sim, Hstep].
      - destruct Hstep as [Hub | Hvis].
        + repeat (destruct ev1 as [ev1 | ev1]); try discriminate Hub; destruct ev1 as [msg].
          * pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
          * pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
        + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * eapply refine_prov_bind;
              [eapply interp_vellvm_prov_h_inline_sync; eassumption |].
            intros U' [s1' a1] [s2' a2] _ (Hm' & Ha & Hp).
            pstep; apply RP_Step; cbn; exists ic;
              split; [exact Hm' | apply gis_cont_to_sim, (HA a1 a2 Ha Hp)].
          * destruct ic as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [_ Hstk]].
            -- destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                        (as_local_mcfg ev2) as [le2 |] eqn:Ele2; try contradiction.
               destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction;
                 repeat (destruct ev1 as [ev1 | ev1]); try discriminate Ele1;
                 repeat (destruct ev2 as [ev2 | ev2]); try discriminate Ele2;
                 inversion Ele1; subst; inversion Ele2; subst;
                 unfold interp_vellvm_prov_h; cbn [case_];
                 destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
               ++ destruct Hloc as (<- & Hlk_eq & Hrd).
                  pose proof Hmatch as (Hg1 & Hg2 & Hmm & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
                  destruct (Maps.lookup x1 env1) as [v |] eqn:Elkv.
                  ** assert (Elkv2 : Maps.lookup x1 env2 = Some v) by congruence.
                     eapply refine_prov_obs_eq.
                     --- symmetry; rewrite (fused_local_prov_read_some x1 v (mm1, ((sf1, fstk1), gg1))
                                              (ltac:(rewrite Hvars1; exact Elkv))), Eqit.bind_ret_l; reflexivity.
                     --- symmetry; rewrite (fused_local_prov_read_some x1 v (mm2, ((sf2, fstk2), gg2))
                                              (ltac:(rewrite Hvars2; exact Elkv2))), Eqit.bind_ret_l; reflexivity.
                     --- pstep; apply RP_Step; cbn; exists (IC_Synced stk env1 env2);
                           split; [exact Hmatch | apply gis_cont_to_sim, (Hrd v Elkv)].
                  ** assert (Elkv2 : Maps.lookup x1 env2 = None) by congruence.
                     destruct (fused_local_prov_read_none x1 (mm1, ((sf1, fstk1), gg1))
                                 (ltac:(rewrite Hvars1; exact Elkv))) as (msg1 & kf1 & Ef1).
                     destruct (fused_local_prov_read_none x1 (mm2, ((sf2, fstk2), gg2))
                                 (ltac:(rewrite Hvars2; exact Elkv2))) as (msg2 & kf2 & Ef2).
                     eapply refine_prov_obs_eq;
                       [symmetry; rewrite Ef1, Eqit.bind_vis; reflexivity
                       | symmetry; rewrite Ef2, Eqit.bind_vis; reflexivity |].
                     pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
               ++ destruct Hloc as (<- & <- & Hr).
                  destruct Hmatch as (-> & -> & -> & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
                  eapply refine_prov_obs_eq;
                    [symmetry; rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity
                    | symmetry; rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity |].
                  pstep; apply RP_Step; cbn.
                  exists (IC_Synced stk (Maps.add x1 v1 env1) (Maps.add x1 v1 env2)).
                  split; [| apply gis_cont_to_sim, Hr].
                  rewrite Hvars1, Hvars2;
                    repeat split; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
            -- destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                        (as_stack_mcfg ev2) as [se2 |] eqn:Ese2; try contradiction.
               destruct se1, se2; try contradiction;
                 repeat (destruct ev1 as [ev1 | ev1]); try discriminate Ese1;
                 repeat (destruct ev2 as [ev2 | ev2]); try discriminate Ese2;
                 inversion Ese1; subst; inversion Ese2; subst;
                 unfold interp_vellvm_prov_h; cbn [case_];
                 destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]];
                 destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
               ++ destruct Hstk as [<- Hr].
                  unfold fused_stack_prov, on_ls_prov, handle_stack; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
                  eapply refine_prov_obs_eq;
                    [symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity
                    | symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity |].
                  pstep; apply RP_Step; cbn.
                  exists (IC_Synced ((env1, env2) :: stk) (init_local_env l) (init_local_env l)).
                  split; [| apply gis_cont_to_sim, Hr].
                  repeat split; try reflexivity.
                  apply SFM_cons; [exact Hsf | exact Hsfm].
               ++ destruct stk as [[p1 p2] rest |].
                  ** inversion Hsfm as [| ? ? sf1' sf2' ? fstk1' fstk2' Hsf' Hsfm']; subst.
                     unfold fused_stack_prov, on_ls_prov, handle_stack; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
                     eapply refine_prov_obs_eq;
                       [symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity
                       | symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity |].
                     pstep; apply RP_Step; cbn.
                     exists (IC_Synced rest p1 p2); split; [| apply gis_cont_to_sim, Hstk].
                     repeat split; try exact Hsf'; try exact Hsfm'; reflexivity.
                  ** inversion Hsfm; subst.
                     unfold fused_stack_prov, on_ls_prov, handle_stack, raise, trigger_cast, ITree.trigger, lift_bot_prov;
                       cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
                     pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn.
                     right; right; split; [exact I | intros [] [] _]. }
    set (r_both :=
      fun U0 (a1 : itree ProvBotE (FusedS * R1)) (a2 : itree ProvBotE (FusedS * R2)) =>
        (exists ic s1 s2 v1 v2,
           interp_state interp_vellvm_prov_h v1 s1 ≅ a1 /\
           interp_state interp_vellvm_prov_h v2 s2 ≅ a2 /\
           inline_fused_match g0 ic s1 s2 /\
           mcfg_inline_sim g0 true RR ic v1 v2) \/
        (exists w1 w2,
           ITree.bind w1 (model_cont R1) ≅ a1 /\
           ITree.bind w2 (model_cont R2) ≅ a2 /\
           refine_prov (model_inline_step_rel g0 RR) U0 w1 w2)).
    assert (Hr_eq :
      forall U0 a1 a1' a2 a2',
        a1 ≅ a1' -> a2 ≅ a2' -> r_both U0 a1 a2 -> r_both U0 a1' a2').
    { intros U0 a1 a1' a2 a2' Ea1 Ea2
        [(ic & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - left; exists ic, s1, s2, v1, v2.
        split; [etransitivity; eassumption | split; [etransitivity; eassumption | split; assumption]].
      - right; exists w1, w2.
        split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hw]]. }
    assert (Hbranch_b :
      forall U0 w1 w2 t1 t2,
        ITree.bind w1 (model_cont R1) ≅ t1 ->
        ITree.bind w2 (model_cont R2) ≅ t2 ->
        refine_prov (model_inline_step_rel g0 RR) U0 w1 w2 ->
        refine_prov_ RR_out r_both U0 t1 t2).
    { intros U0 w1 w2 t1 t2 Et1 Et2 Hw.
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hw; clear t1 t2 Et1 Et2.
      induction Hw as [U0 w1 w2 Hstep | U0 w1 mw1 w2 Hw1 _ IH | U0 w1 w2 mw2 Hw2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          destruct x1 as [[s1 r1] | [s1 v1]], x2 as [[s2 r2] | [s2 v2]]; cbn in Hstep; try contradiction.
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, How1, How2; cbn; exact Hstep.
          * destruct Hstep as (ic & Hm & Hv).
            apply RP_Step; unfold rp_step_body; rewrite !observe_bind, How1, How2; cbn.
            left; exists ic, s1, s2, v1, v2;
              split; [reflexivity | split; [reflexivity | split; assumption]].
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction; pclearbot.
          apply RP_Step; unfold rp_step_body; rewrite !observe_bind, How1, How2.
          right; exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + apply RP_Step; unfold rp_step_body; rewrite (observe_bind w1 (model_cont R1)), How1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct ev1 as [p1 | b1]; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            right; exists (kw1 p), w2; split; [reflexivity | split; [reflexivity | exact Hleft]].
          * right; right.
            destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
            rewrite (observe_bind w2 (model_cont R2)), How2.
            destruct ev1 as [p1 | b1], ev2 as [p2 | b2]; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               right; exists (kw1 p), (kw2 p); split; [reflexivity | split; [reflexivity | exact Hboth]].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               right; exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
      - eapply RP_TauL; [rewrite (observe_bind w1 (model_cont R1)), Hw1; reflexivity | exact IH].
      - eapply RP_TauR; [rewrite (observe_bind w2 (model_cont R2)), Hw2; reflexivity | exact IH]. }
    assert (Hbranch_a :
      forall U0 ic s1 s2 u1 u2 t1 t2,
        interp_state interp_vellvm_prov_h u1 s1 ≅ t1 ->
        interp_state interp_vellvm_prov_h u2 s2 ≅ t2 ->
        inline_fused_match g0 ic s1 s2 ->
        mcfg_inline_sim g0 true RR ic u1 u2 ->
        refine_prov_ RR_out r_both U0 t1 t2).
    { intros U0 ic s1 s2 u1 u2 t1 t2 Et1 Et2 Hmatch Hu.
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hu; clear t1 t2 Et1 Et2.
      revert s1 s2 Hmatch;
        induction Hu as [ic u1 u2 Hstep
                         | ic u1 mu1 u2 Hu1 _ IH
                         | ic u1 u2 mu2 Hu2 _ IH
                         | ic env1 u1 x v k1 u2 He1 Hu1 Hlk _ IH
                         | ic env2 u1 u2 x v k2 He2 Hu2 Hlk _ IH
                         | ic ic' u1 x v k1 u2 Hw1 Hu1 _ IH
                         | ic ic' u1 u2 x v k2 Hw2 Hu2 _ IH
                         | ic u1 k v k1 u2 Hu1 Hlk _ IH
                         | stk ce1 e1 e2 u1 varg k1 u2 Hu1 _ IH
                         | stk e1 e2 u1 k1 u2 Hfr Hu1 _ IH
                         | stk ce1 e2 bs u1 k1 u2 Hfr Hu1 _ IH
                         | stk ce1 e1 e2 u1 k1 u2 Hfr Hu1 _ IH
                         | stk ce1 e2 u1 k1 u2 Hfr Hu1 _ IH
                         | stk e1 e2 u1 X ce body1 k1 u2 Hfr Hu1 Hopt];
        [| | | | | | | | | | | | | discriminate Hopt];
        intros s1 s2 Hmatch.
      - eapply Hbranch_b;
          [apply decomp_model_spec | apply decomp_model_spec | eapply Hstep_decomp; eassumption].
      - eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h mu1 s1))
          (t2 := interp_state interp_vellvm_prov_h u2 s2);
          [exact Hr_eq
          | symmetry; rewrite (unfold_interp_state interp_vellvm_prov_h u1 s1), Hu1; reflexivity
          | reflexivity |].
        eapply RP_TauL; [reflexivity | apply IH, Hmatch].
      - eapply refine_prov__obs_eq with
          (t1 := interp_state interp_vellvm_prov_h u1 s1)
          (t2 := Tau (interp_state interp_vellvm_prov_h mu2 s2));
          [exact Hr_eq
          | reflexivity
          | symmetry; rewrite (unfold_interp_state interp_vellvm_prov_h u2 s2), Hu2; reflexivity |].
        eapply RP_TauR; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        assert (Hvars1 : sf1.(stack_vars) = env1).
        { destruct ic as [stk e1_0 e2_0 | | stk ce1 e1_0 e2_0]; try discriminate He1;
            cbn in He1; injection He1 as <-;
            [destruct Hmatch as (_ & _ & _ & [Hv1 _] & _); exact Hv1
            | destruct Hmatch as (_ & _ & _ & Hv1 & _); exact Hv1]. }
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 v) (mm1, ((sf1, fstk1), gg1))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          rewrite (fused_local_prov_read_some x v (mm1, ((sf1, fstk1), gg1))
                     (ltac:(rewrite Hvars1; exact Hlk))), Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        assert (Hvars2 : sf2.(stack_vars) = env2).
        { destruct ic as [stk e1_0 e2_0 | | stk ce1 e1_0 e2_0]; try discriminate He2;
            cbn in He2; injection He2 as <-;
            [destruct Hmatch as (_ & _ & _ & (_ & Hv2 & _) & _); exact Hv2
            | destruct Hmatch as (_ & _ & _ & _ & csf1 & fstk1' & _ & (_ & Hv2 & _) & _); exact Hv2]. }
        eapply refine_prov__obs_eq with
          (t1 := interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)))
          (t2 := Tau (interp_state interp_vellvm_prov_h (k2 v) (mm2, ((sf2, fstk2), gg2)))).
        + exact Hr_eq.
        + reflexivity.
        + symmetry; rewrite Hu2, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          rewrite (fused_local_prov_read_some x v (mm2, ((sf2, fstk2), gg2))
                     (ltac:(rewrite Hvars2; exact Hlk))), Eqit.bind_ret_l; reflexivity.
        + eapply RP_TauR; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                        (mm1, ((upd_local_sf sf1 (Maps.add x v sf1.(stack_vars)), fstk1), gg1))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH].
          destruct ic as [stk e1_0 e2_0 | | stk ce1 e1_0 e2_0]; try discriminate Hw1;
            cbn in Hw1; injection Hw1 as <-.
          * destruct Hmatch as (-> & -> & -> & (Hv1 & Hv2 & Hexc & Hloc) & Hsfm).
            rewrite Hv1; repeat split; try exact Hv2; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
          * destruct Hmatch as (-> & -> & -> & Hv1 & csf1 & fstk1' & -> & Hcsf & Hsfm).
            rewrite Hv1; split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | exists csf1, fstk1'; auto]]]].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        eapply refine_prov__obs_eq with
          (t1 := interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)))
          (t2 := Tau (interp_state interp_vellvm_prov_h (k2 tt)
                        (mm2, ((upd_local_sf sf2 (Maps.add x v sf2.(stack_vars)), fstk2), gg2)))).
        + exact Hr_eq.
        + reflexivity.
        + symmetry; rewrite Hu2, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity.
        + eapply RP_TauR; [reflexivity | apply IH].
          destruct ic as [stk e1_0 e2_0 | | stk ce1 e1_0 e2_0]; try discriminate Hw2;
            cbn in Hw2; injection Hw2 as <-.
          * destruct Hmatch as (-> & -> & -> & (Hv1 & Hv2 & Hexc & Hloc) & Hsfm).
            rewrite Hv2; repeat split; try exact Hv1; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
          * destruct Hmatch as (-> & -> & -> & Hv1 & csf1 & fstk1' & -> & (Hcv1 & Hv2 & Hexc & Hloc) & Hsfm).
            rewrite Hv2; split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hv1 |]]]].
            exists csf1, fstk1'; split; [reflexivity | split; [| exact Hsfm]].
            repeat split; try exact Hcv1; try exact Hexc; try exact Hloc; reflexivity.
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        assert (Hg1 : gg1 = g0).
        { destruct Hmatch as (Hg1 & _); exact Hg1. }
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 v) (mm1, ((sf1, fstk1), gg1))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          rewrite (fused_global_prov_read_some k v (mm1, ((sf1, fstk1), gg1))
                     (ltac:(cbn [snd]; rewrite Hg1; exact Hlk))), Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt) (mm1, ((sf1, fstk1), gg1))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          unfold fused_memory_prov, on_mem_prov, handle_memory.
          rewrite (store_zero_struct_noop varg mm1), !Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                        (push_empty_frame mm2, ((sf1, fstk1), g0))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), g0))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          unfold fused_memory_prov, on_mem_prov, handle_memory.
          rewrite (mempush_empty_frame mm2), !Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH].
          cbn [inline_fused_match]; repeat split; try exact Hsf; try exact Hsfm; reflexivity.
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
        set (new_sf1 := {| stack_vars := init_local_env bs;
                           stack_exc  := None;
                           stack_loc  := Some (printer_object.(printer_get_loc) tt) |}).
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                        (push_empty_frame mm2, ((new_sf1, sf1 :: fstk1), g0))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), g0))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          unfold fused_stack_prov, on_ls_prov, handle_stack;
            cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
          rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH].
          cbn [inline_fused_match stack_vars new_sf1].
          split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]].
          exists sf1, fstk1; split; [reflexivity | split; assumption].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        destruct Hmatch as (-> & -> & -> & _ & csf1 & fstk1' & -> & Hcsf & Hsfm).
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                        (push_empty_frame mm2, ((csf1, fstk1'), g0))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), g0))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          unfold fused_stack_prov, on_ls_prov, handle_stack;
            cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
          rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH].
          cbn [inline_fused_match]; repeat split; try exact Hcsf; try exact Hsfm; reflexivity.
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                        (mm2, ((sf1, fstk1), g0))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), g0))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl inr1 inl1].
          unfold fused_memory_prov, on_mem_prov, handle_memory.
          rewrite (mempop_empty_frame mm2), !Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH].
          cbn [inline_fused_match]; repeat split; try exact Hsf; try exact Hsfm; reflexivity. }
    assert (Hmain :
      forall U0 t1 t2,
        r_both U0 t1 t2 ->
        refine_prov RR_out U0 t1 t2).
    { pcofix CIH.
      intros U0 t1 t2 Hrb; pstep.
      eapply refine_prov__mon with (r := r_both);
        [| intros U1 a1 a2 Hr; right; apply CIH, Hr].
      destruct Hrb as [(ic & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - eapply Hbranch_a; eassumption.
      - eapply Hbranch_b; eassumption. }
    intros U ic s1 s2 u1 u2 Hmatch Hsim.
    apply Hmain; left; exists ic, s1, s2, u1, u2;
      split; [reflexivity | split; [reflexivity | split; assumption]].
  Qed.


  (** * 9. Expression, Attribute, Callee Block, and Parameter-Copy Simulations *)

  (** ** 9A. Local-Environment Invariants, [ren_exp_id], and Monad Helpers *)

  Definition env_agree_outside (fresh_set : list raw_id) (e1 e2 : @local_env PaV) : Prop :=
    forall x, ~ In x fresh_set -> Maps.lookup x e1 = Maps.lookup x e2.

  Lemma env_agree_outside_refl (fresh_set : list raw_id) (e : @local_env PaV) :
    env_agree_outside fresh_set e e.
  Proof.
    intros x _; reflexivity.
  Qed.

  Lemma env_agree_outside_add_both (fresh_set : list raw_id)
    (x : local_id) (v : @dvalue PaV) (e1 e2 : @local_env PaV) :
    env_agree_outside fresh_set e1 e2 ->
    env_agree_outside fresh_set (Maps.add x v e1) (Maps.add x v e2).
  Proof.
    intros Hagree y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - rewrite !PassCommon.lookup_add_eq; reflexivity.
    - rewrite !PassCommon.lookup_add_neq by exact Hne; apply Hagree, Hy.
  Qed.

  Lemma env_agree_outside_add_fresh_r (fresh_set : list raw_id)
    (x : local_id) (v : @dvalue PaV) (e1 e2 : @local_env PaV)
    (Hx : In x fresh_set) :
    env_agree_outside fresh_set e1 e2 ->
    env_agree_outside fresh_set e1 (Maps.add x v e2).
  Proof.
    intros Hagree y Hy.
    assert (Hne : x <> y) by (intros ->; contradiction).
    rewrite PassCommon.lookup_add_neq by exact Hne; apply Hagree, Hy.
  Qed.

  Definition callee_defs_bound (ren_l : raw_id -> raw_id) (defs : list raw_id)
    (e1 e2 : @local_env PaV) : Prop :=
    forall x,
      In x defs ->
      exists v, Maps.lookup x e1 = Some v /\ Maps.lookup (ren_l x) e2 = Some v.

  Lemma callee_defs_bound_incl (ren_l : raw_id -> raw_id) (d1 d2 : list raw_id)
    (e1 e2 : @local_env PaV) :
    incl d1 d2 ->
    callee_defs_bound ren_l d2 e1 e2 ->
    callee_defs_bound ren_l d1 e1 e2.
  Proof.
    intros Hincl Hbound x Hx; apply Hbound, Hincl, Hx.
  Qed.

  Lemma callee_defs_bound_add (ren_l : raw_id -> raw_id) (dom defs : list raw_id)
    (x : local_id) (v : @dvalue PaV) (e1 e2 : @local_env PaV)
    (Hinj : forall x1 x2, In x1 dom -> In x2 dom -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hdefs_dom : incl defs dom)
    (Hx_dom : In x dom) :
    callee_defs_bound ren_l defs e1 e2 ->
    callee_defs_bound ren_l (defs ++ [x]) (Maps.add x v e1) (Maps.add (ren_l x) v e2).
  Proof.
    intros Hbound y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - exists v; rewrite !PassCommon.lookup_add_eq; split; reflexivity.
    - apply in_app_or in Hy as [Hy | [Heq | []]]; [| congruence].
      assert (Hy_dom : In y dom) by (apply Hdefs_dom, Hy).
      assert (Hren_ne : ren_l x <> ren_l y).
      { intros Heq; apply Hne, (Hinj x y Hx_dom Hy_dom Heq). }
      rewrite PassCommon.lookup_add_neq by exact Hne.
      rewrite PassCommon.lookup_add_neq by exact Hren_ne.
      apply Hbound, Hy.
  Qed.

  Lemma callee_defs_bound_add_other_r (ren_l : raw_id -> raw_id) (defs : list raw_id)
    (z : local_id) (v : @dvalue PaV) (e1 e2 : @local_env PaV)
    (Hother : forall x, In x defs -> ren_l x <> z) :
    callee_defs_bound ren_l defs e1 e2 ->
    callee_defs_bound ren_l defs e1 (Maps.add z v e2).
  Proof.
    intros Hbound x Hx.
    destruct (Hbound x Hx) as (vx & Hlk1 & Hlk2).
    assert (Hne : z <> ren_l x) by (intros ->; exact (Hother x Hx Logic.eq_refl)).
    exists vx; split; [exact Hlk1 | rewrite PassCommon.lookup_add_neq by exact Hne; exact Hlk2].
  Qed.

  Lemma ren_exp_id {T : Set} (e : exp T) :
    ren_exp (fun x : raw_id => x) e = e.
  Proof.
    assert (Hlist :
      forall (elts : list (T * exp T)),
        (forall p, In p elts -> ren_exp (fun x => x) (snd p) = snd p) ->
        (fix go (l : list (T * exp T)) : list (T * exp T) :=
           match l with
           | [] => []
           | (t, ex) :: rest => (t, ren_exp (fun x => x) ex) :: go rest
           end) elts = elts).
    { induction elts as [| [t ex] rest IHl]; intros Hall; [reflexivity |].
      cbn [snd]; rewrite (Hall (t, ex) (or_introl Logic.eq_refl)), IHl; [reflexivity |].
      intros p Hp; apply Hall; right; exact Hp. }
    assert (Hmdlist :
      forall (ms : list (metadata T)),
        (forall m, In m ms -> ren_metadata (fun x => x) m = m) ->
        (fix go_md (l : list (metadata T)) : list (metadata T) :=
           match l with
           | [] => []
           | m :: rest => ren_metadata (fun x => x) m :: go_md rest
           end) ms = ms).
    { induction ms as [| m rest IHm]; intros Hall; [reflexivity |].
      rewrite (Hall m (or_introl Logic.eq_refl)), IHm; [reflexivity |].
      intros m0 Hm0; apply Hall; right; exact Hm0. }
    apply (AstLib.exp_ind_full T
             (fun v => ren_exp (fun x => x) v = v)
             (fun m => ren_metadata (fun x => x) m = m));
      intros;
      repeat match goal with p : T * exp T |- _ => destruct p as [? ?] end;
      try match goal with i : ident |- _ => destruct i end;
      cbn [ren_exp ren_metadata ren_ident snd] in *;
      try reflexivity;
      try congruence;
      try (f_equal; apply Hlist; assumption);
      try (f_equal; apply Hmdlist; assumption).
    - (* OP_GetElementPtr *)
      rewrite H, (Hlist idxs H0); reflexivity.
  Qed.

  Lemma loop_monad_itree_app {E : Type -> Type} {A : Type}
    (f : A -> itree E unit) (xs ys : list A) :
    loop_monad f (xs ++ ys) ≅
    ITree.bind (loop_monad f xs) (fun _ => loop_monad f ys).
  Proof.
    induction xs as [| x xs' IH]; cbn [app loop_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - symmetry; apply Eqit.bind_ret_l.
    - rewrite Eqit.bind_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [] _ _; exact IH.
  Qed.

  (** ** 9B. Primitive [lread], [lwrite], [stack_push], [stack_pop], and [raiseLLVM] Lemmas *)

  Lemma mcfg_inline_sim_lread_both
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (e1 e2 : @local_env PaV) (x1 x2 : local_id) (v : @dvalue PaV)
    (He1 : ic_env1 ic = Some e1)
    (He2 : ic_env2 ic = Some e2)
    (Hlk1 : Maps.lookup x1 e1 = Some v)
    (Hlk2 : Maps.lookup x2 e2 = Some v) :
    mcfg_inline_sim g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = v /\ r2 = v)
      ic (lread x1) (lread x2).
  Proof.
    pstep.
    eapply GIS_ReadL with (env1 := e1) (x := x1) (v := v) (k1 := fun z => Ret z);
      [exact He1 | unfold lread; symmetry; apply Eqit.bind_ret_r | exact Hlk1 |].
    eapply GIS_ReadR with (env2 := e2) (x := x2) (v := v) (k2 := fun z => Ret z);
      [exact He2 | unfold lread; symmetry; apply Eqit.bind_ret_r | exact Hlk2 |].
    apply GIS_Step; cbn; auto.
  Qed.

  Lemma mcfg_inline_sim_lread_synced
    (g0 : global_env) (bf : bool)
    stk (e1 e2 : @local_env PaV) (x : local_id)
    (Hlk : Maps.lookup x e1 = Maps.lookup x e2) :
    mcfg_inline_sim g0 bf
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
      (IC_Synced stk e1 e2) (lread x) (lread x).
  Proof.
    unfold lread, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body;
      cbn [observe gis_vis_both as_local_mcfg subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    right; right; left.
    split; [reflexivity | split; [exact Hlk |]].
    intros v _; exists (Ret v), (Ret v).
    split; [apply ITS_Refl | split; [apply ITS_Refl |]].
    left; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma cfg_inline_sim_lwrite_lr
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    (ic ic1 ic2 : inline_ctx) (x1 x2 : local_id) (v : @dvalue PaV)
    (Hw1 : ic_write1 x1 v ic = Some ic1)
    (Hw2 : ic_write2 x2 v ic1 = Some ic2) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic2 /\ r1 = tt /\ r2 = tt)
      ic (lwrite x1 v) (lwrite x2 v).
  Proof.
    pstep.
    eapply GIS_WriteL with (ic' := ic1) (x := x1) (v := v) (k1 := fun z => Ret z);
      [exact Hw1 | unfold lwrite; symmetry; apply Eqit.bind_ret_r |].
    eapply GIS_WriteR with (ic' := ic2) (x := x2) (v := v) (k2 := fun z => Ret z);
      [exact Hw2 | unfold lwrite; symmetry; apply Eqit.bind_ret_r |].
    apply GIS_Step; cbn; auto.
  Qed.

  Lemma cfg_inline_sim_lwrite_r
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    (ic ic' : inline_ctx) (x2 : local_id) (v : @dvalue PaV)
    (Hw2 : ic_write2 x2 v ic = Some ic') :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic0 r1 r2 => ic0 = ic' /\ r1 = tt /\ r2 = tt)
      ic (Ret tt) (lwrite x2 v).
  Proof.
    pstep.
    eapply GIS_WriteR with (ic' := ic') (x := x2) (v := v) (k2 := fun z => Ret z);
      [exact Hw2 | unfold lwrite; symmetry; apply Eqit.bind_ret_r |].
    apply GIS_Step; cbn; auto.
  Qed.

  Lemma cfg_inline_sim_stack_push_sync
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    stk (e1 e2 : @local_env PaV) (bs : list (local_id * @dvalue PaV)) :
    cfg_inline_sim opt_call1 g0 true
      (fun ic' r1 r2 =>
         ic' = IC_Synced ((e1, e2) :: stk) (init_local_env bs) (init_local_env bs) /\
         r1 = tt /\ r2 = tt)
      (IC_Synced stk e1 e2) (stack_push bs) (stack_push bs).
  Proof.
    unfold stack_push, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body;
      cbn [observe gis_vis_both as_stack_cfg as_stack_mcfg subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    right; right; right; split; [reflexivity | split; [reflexivity |]].
    exists (Ret tt), (Ret tt).
    split; [apply ITS_Refl | split; [apply ITS_Refl |]].
    left; apply gen_inline_sim_ret; auto.
  Qed.

  Lemma cfg_inline_sim_stack_pop_sync
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    stk (p1 p2 e1 e2 : @local_env PaV) :
    cfg_inline_sim opt_call1 g0 true
      (fun ic' r1 r2 => ic' = IC_Synced stk p1 p2 /\ r1 = tt /\ r2 = tt)
      (IC_Synced ((p1, p2) :: stk) e1 e2) stack_pop stack_pop.
  Proof.
    unfold stack_pop, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body;
      cbn [observe gis_vis_both as_stack_cfg as_stack_mcfg subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    right; right; right; split; [reflexivity |].
    exists (Ret tt), (Ret tt).
    split; [apply ITS_Refl | split; [apply ITS_Refl |]].
    left; apply gen_inline_sim_ret; auto.
  Qed.

  Lemma cfg_inline_sim_raiseLLVM
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    stk (e1 e2 : @local_env PaV) (ex : @exc PaV) :
    cfg_inline_sim opt_call1 g0 bf RR (IC_Synced stk e1 e2) (raiseLLVM ex) (raiseLLVM ex).
  Proof.
    unfold raiseLLVM, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
    right; left; split; [reflexivity | split; [reflexivity | intros [] [] _ _]].
  Qed.

  (** ** 9C. Expression Denotation Simulation ([denote_exp], [denote_exp']) *)

  Lemma mcfg_inline_sim_freeze
    (g0 : global_env) (bf : bool) (ic : inline_ctx) (dv : @dvalue PaV)
    (Hact : is_ic_active ic = true) :
    forall dt : dtyp,
      mcfg_inline_sim g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
        ic (freeze dt dv) (freeze dt dv).
  Proof.
    induction dv as [db | pk fs IHfs | vc es IHes] using dvalue_ind_nested; intros dt;
      unfold freeze.
    - destruct db as [| | | | | | | sz bv];
        try (cbn [freeze_base Functor.fmap Functor_itree ITree.map ExtLib.Structures.Monad.ret Monad_itree];
             eapply gen_inline_sim_obs_eq;
             [symmetry; apply Eqit.bind_ret_l
             | symmetry; apply Eqit.bind_ret_l
             | apply gen_inline_sim_ret; split; reflexivity]).
      + cbn [freeze_base]; unfold draw; apply mcfg_inline_sim_trigger_refl.
        destruct ic; try discriminate Hact; reflexivity.
      + destruct bv as [bi | p ix | bits];
          try (cbn [freeze_base Functor.fmap Functor_itree ITree.map ExtLib.Structures.Monad.ret Monad_itree];
               eapply gen_inline_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l
               | symmetry; apply Eqit.bind_ret_l
               | apply gen_inline_sim_ret; split; reflexivity]).
        cbn [freeze_base]; destruct (existsb is_poison_bit bits).
        * eapply gen_inline_sim_bind.
          -- unfold draw; apply mcfg_inline_sim_trigger_refl.
             destruct ic; try discriminate Hact; reflexivity.
          -- intros ? x1 x2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
        * cbn [Functor.fmap Functor_itree ITree.map ExtLib.Structures.Monad.ret Monad_itree].
          eapply gen_inline_sim_obs_eq;
            [symmetry; apply Eqit.bind_ret_l
            | symmetry; apply Eqit.bind_ret_l
            | apply gen_inline_sim_ret; split; reflexivity].
    - destruct dt as [| p dts |]; try (apply mcfg_inline_sim_raise, Hact).
      eapply gen_inline_sim_bind;
        [| intros ? v1 v2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
      revert dts; generalize ([] : list (@dvalue PaV)) as acc.
      induction IHfs as [| f fs' Hf _ IH]; intros acc [| t ts];
        try (apply mcfg_inline_sim_raise, Hact).
      + apply gen_inline_sim_ret; split; reflexivity.
      + eapply gen_inline_sim_bind; [apply (Hf t) | intros ? v1 v2 [-> <-]; apply IH].
    - destruct dt as [| | v sz t]; try (apply mcfg_inline_sim_raise, Hact).
      eapply gen_inline_sim_bind;
        [| intros ? v1 v2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
      generalize ([] : list (@dvalue PaV)) as acc.
      induction IHes as [| e es' He _ IH]; intros acc.
      + apply gen_inline_sim_ret; split; reflexivity.
      + eapply gen_inline_sim_bind; [apply (He t) | intros ? v1 v2 [-> <-]; apply IH].
  Qed.

  Lemma mcfg_inline_sim_map_texps
    (g0 : global_env) (ic : inline_ctx) (ren_l : raw_id -> raw_id)
    (es : list (dtyp * exp dtyp))
    (IHes : Forall
              (fun te =>
                 (forall x,
                    In x (full_exp_uses (snd te)) ->
                    mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
                      ic (lread x) (lread (ren_l x))) ->
                 forall top,
                   mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
                     ic (denote_exp top (snd te)) (denote_exp top (ren_exp ren_l (snd te))))
              es)
    (Hvar : forall x,
              In x ((fix go (l : list (dtyp * exp dtyp)) : list raw_id :=
                       match l with
                       | [] => []
                       | (_, ex) :: rest => full_exp_uses ex ++ go rest
                       end) es) ->
              mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
                ic (lread x) (lread (ren_l x))) :
    mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2) ic
      (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) es)
      (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex)
         ((fix go (l : list (dtyp * exp dtyp)) : list (dtyp * exp dtyp) :=
             match l with
             | [] => []
             | (t, ex) :: rest => (t, ren_exp ren_l ex) :: go rest
             end) es)).
  Proof.
    induction IHes as [| [t ex] rest Hex _ IH]; cbn [map_monad snd] in *.
    - apply gen_inline_sim_ret; split; reflexivity.
    - eapply gen_inline_sim_bind.
      + apply Hex; intros x Hx; apply Hvar, in_or_app; left; exact Hx.
      + intros ? v1 v2 [-> <-].
        eapply gen_inline_sim_bind.
        * apply IH; intros x Hx; apply Hvar, in_or_app; right; exact Hx.
        * intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma denote_exp_gen_sim
    (g0 : global_env) (ic : inline_ctx) (ren_l : raw_id -> raw_id)
    (Hact : is_ic_active ic = true)
    (e : exp dtyp)
    (Hvar : forall x,
              In x (full_exp_uses e) ->
              mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
                ic (lread x) (lread (ren_l x))) :
    forall top : option dtyp,
      mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
        ic (denote_exp top e) (denote_exp top (ren_exp ren_l e)).
  Proof.
    revert Hvar; induction e using exp_denote_ind; intros Hvar top;
      cbn [ren_exp ren_metadata denote_exp full_exp_uses full_metadata_uses] in *;
      try (apply gen_inline_sim_ret; split; reflexivity);
      try (apply mcfg_inline_sim_raise, Hact);
      try (destruct top; [apply mcfg_inline_sim_EOU, Hact | apply mcfg_inline_sim_raise, Hact]).
    - (* EXP_Ident *)
      destruct id as [gid | lid]; cbn [ren_ident denote_exp lookup_id].
      + unfold gread; apply mcfg_inline_sim_trigger_refl.
        destruct ic; try discriminate Hact; reflexivity.
      + apply Hvar; left; reflexivity.
    - (* EXP_Bool *)
      destruct b; apply gen_inline_sim_ret; split; reflexivity.
    - (* EXP_Cstring *)
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* EXP_Struct *)
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* EXP_Packed_struct *)
      eapply gen_inline_sim_bind; [apply mcfg_inline_sim_EOU, Hact | intros ? [] _ [-> _]].
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* EXP_Array *)
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* EXP_Vector *)
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* OP_IBinop *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_ICmp *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_FBinop *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_Fneg *)
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? v1 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_FCmp *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_Conversion *)
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? dv _ [-> <-]].
      unfold convert; destruct ct as [| pct | ict].
      + destruct (dtyp_eqb tf tt0); [apply gen_inline_sim_ret; split; reflexivity |].
        destruct (bit_sizeof_dtyp tf =? bit_sizeof_dtyp tt0)%N;
          [apply mcfg_inline_sim_EOU, Hact | apply mcfg_inline_sim_raise, Hact].
      + apply mcfg_inline_sim_EOU, Hact.
      + unfold conv; apply mcfg_inline_sim_trigger_refl.
        destruct ic; try discriminate Hact; reflexivity.
    - (* OP_GetElementPtr *)
      eapply gen_inline_sim_bind;
        [apply IHe; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? vp _ [-> <-]].
      eapply gen_inline_sim_bind.
      + apply (mcfg_inline_sim_map_texps g0 ic ren_l idxs H).
        intros x Hx; apply Hvar, in_or_app; right; exact Hx.
      + intros ? vs _ [-> <-]; apply mcfg_inline_sim_EOU, Hact.
    - (* OP_ExtractElement *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_InsertElement *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind.
      + eapply gen_inline_sim_bind;
          [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; left; exact Hx
          | intros ? v2 _ [-> <-]; apply mcfg_inline_sim_EOU, Hact].
      + intros ? b2 _ [-> <-].
        eapply gen_inline_sim_bind;
          [apply IHe3; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; right; exact Hx
          | intros ? v3 _ [-> <-]; apply mcfg_inline_sim_EOU, Hact].
    - (* OP_ShuffleVector *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; left; exact Hx
        | intros ? v2 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe3; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; right; exact Hx
        | intros ? v3 _ [-> <-]; apply mcfg_inline_sim_EOU, Hact].
    - (* OP_ExtractValue *)
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? v1 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_InsertValue *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_Select *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; left; exact Hx
        | intros ? v2 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe3; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; right; exact Hx
        | intros ? v3 _ [-> <-]; apply mcfg_inline_sim_EOU, Hact].
    - (* OP_Freeze *)
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? dv _ [-> <-]].
      apply mcfg_inline_sim_freeze, Hact.
    - (* EXP_BlockAddress *)
      unfold gread; apply mcfg_inline_sim_trigger_refl.
      destruct ic; try discriminate Hact; reflexivity.
    - (* EXP_Splat *)
      eapply gen_inline_sim_bind; [apply mcfg_inline_sim_EOU, Hact | intros ? [sz t] _ [-> <-]].
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? v _ [-> <-]].
      apply gen_inline_sim_ret; split; reflexivity.
    - (* EXP_Metadata (METADATA_Const) *)
      apply IHe, Hvar.
    - (* EXP_Metadata (other) *)
      destruct md as [| | [t1 e1] | | | |];
        [| | exfalso; exact (H t1 e1 Logic.eq_refl) | | | |];
        cbn [ren_metadata denote_exp];
        apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma denote_exp'_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (ren_l : raw_id -> raw_id) (d_avail : list raw_id)
    stk (ce1 e1 e2 : @local_env PaV)
    (top : option dtyp) (e : exp dtyp)
    (Huses : incl (full_exp_uses e) d_avail)
    (Hbound : callee_defs_bound ren_l d_avail e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 => ic' = IC_Inlined stk ce1 e1 e2 /\ r1 = r2)
      (IC_Inlined stk ce1 e1 e2)
      (denote_exp' top e)
      (denote_exp' top (ren_exp ren_l e)).
  Proof.
    unfold denote_exp'; apply mcfg_to_cfg_withCall_sim.
    apply denote_exp_gen_sim; [reflexivity |].
    intros x Hx.
    destruct (Hbound x (Huses x Hx)) as (v & Hlk1 & Hlk2).
    eapply gen_inline_sim_weaken;
      [| apply (mcfg_inline_sim_lread_both g0 false (IC_Inlined stk ce1 e1 e2)
                  e1 e2 x (ren_l x) v Logic.eq_refl Logic.eq_refl Hlk1 Hlk2)].
    intros ? ? ? (-> & -> & ->); split; reflexivity.
  Qed.

  Lemma denote_exp'_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (top : option dtyp) (e : exp dtyp)
    (Huses : forall x, In x (full_exp_uses e) -> ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
      (IC_Synced stk e1 e2)
      (denote_exp' top e)
      (denote_exp' top e).
  Proof.
    unfold denote_exp'; apply mcfg_to_cfg_withCall_sim.
    rewrite <- (ren_exp_id e) at 2.
    apply (denote_exp_gen_sim g0 (IC_Synced stk e1 e2) (fun x => x)); [reflexivity |].
    intros x Hx; apply mcfg_inline_sim_lread_synced, Hagree, Huses, Hx.
  Qed.

  (** ** 9D. Attribute, Dereferenceability, and [select_switch] Lemmas *)

  Lemma cfg_inline_sim_assert_deref
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (or_null : bool) (n : N) (v : @dvalue PaV) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = tt /\ r2 = tt)
      ic
      (assert_dereferenceable or_null n v msg1)
      (assert_dereferenceable or_null n v msg2).
  Proof.
    unfold assert_dereferenceable.
    destruct v as [db | |]; [| apply cfg_inline_sim_raise, Hact | apply cfg_inline_sim_raise, Hact].
    destruct db as [p | | | | | | |];
      try (apply cfg_inline_sim_raise, Hact).
    - destruct ((or_null && (ptr_to_int p =? ptr_to_int (@null PaV))%Z) || (n =? 0)%N)%bool.
      + apply gen_inline_sim_ret; auto.
      + eapply gen_inline_sim_bind.
        * unfold load; apply cfg_inline_sim_trigger_refl.
          destruct ic; try discriminate Hact; reflexivity.
        * intros ? _ _ [-> _]; apply gen_inline_sim_ret; auto.
    - apply cfg_inline_sim_raiseUB.
  Qed.

  Lemma cfg_inline_sim_assert_load_deref
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (md : list (metadata dtyp)) (v : @dvalue PaV) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = tt /\ r2 = tt)
      ic
      (assert_load_dereferenceable md v msg1)
      (assert_load_dereferenceable md v msg2).
  Proof.
    unfold assert_load_dereferenceable.
    destruct (load_metadata_dereferenceable md) as [[or_null n] |].
    - apply cfg_inline_sim_assert_deref, Hact.
    - apply gen_inline_sim_ret; auto.
  Qed.

  Lemma cfg_inline_sim_apply_attrs
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (attrs : list param_attr) (msg1 msg2 : string) (v : @dvalue PaV)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic
      (apply_attrs attrs msg1 v)
      (apply_attrs attrs msg2 v).
  Proof.
    unfold apply_attrs, apply_value_attrs.
    set (vp := value_attrs_poison attrs v).
    destruct (existsb attr_is_noundef attrs && negb (dvalue_well_defined vp))%bool.
    - cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
      unfold raiseUB, trigger_cast, ITree.trigger.
      pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe]; left; reflexivity.
    - cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      eapply gen_inline_sim_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[or_null n] |], vp as [db | |];
        try (eapply gen_inline_sim_obs_eq;
             [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |];
             apply gen_inline_sim_ret; split; reflexivity).
      destruct db;
        try (eapply gen_inline_sim_obs_eq;
             [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |];
             apply gen_inline_sim_ret; split; reflexivity).
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_assert_deref, Hact
        | intros ? _ _ (-> & _ & _); apply gen_inline_sim_ret; split; reflexivity].
  Qed.

  Lemma cfg_inline_sim_apply_args_attrs
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (attrss : list (list param_attr)) (msg1 msg2 : string) (args : list (@dvalue PaV))
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic
      (apply_args_attrs attrss msg1 args)
      (apply_args_attrs attrss msg2 args).
  Proof.
    revert attrss; induction args as [| v vs IH]; intros attrss; cbn [apply_args_attrs].
    - apply gen_inline_sim_ret; split; reflexivity.
    - destruct attrss as [| a rest].
      + eapply gen_inline_sim_bind; [apply cfg_inline_sim_apply_attrs, Hact | intros ? v1 _ [-> <-]].
        eapply gen_inline_sim_bind; [apply IH | intros ? vs1 _ [-> <-]].
        apply gen_inline_sim_ret; split; reflexivity.
      + eapply gen_inline_sim_bind; [apply cfg_inline_sim_apply_attrs, Hact | intros ? v1 _ [-> <-]].
        eapply gen_inline_sim_bind; [apply IH | intros ? vs1 _ [-> <-]].
        apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma cfg_inline_sim_check_call_return
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax)))
    (loc1 loc2 : string) (args : list (@dvalue PaV)) (res : @exc PaV + @dvalue PaV)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic
      (check_call_return fattrs ret_attrs ranges loc1 args res)
      (check_call_return fattrs ret_attrs ranges loc2 args res).
  Proof.
    unfold check_call_return, check_call_result.
    destruct res as [ex | v].
    - destruct (existsb fn_attr_is_nounwind fattrs).
      + cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
        unfold raiseUB, trigger_cast, ITree.trigger.
        pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe]; left; reflexivity.
      + cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply gen_inline_sim_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        apply gen_inline_sim_ret; split; reflexivity.
    - destruct (existsb fn_attr_is_noreturn fattrs).
      + cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
        unfold raiseUB, trigger_cast, ITree.trigger.
        pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe]; left; reflexivity.
      + destruct (existsb fn_attr_is_nocreateundeforpoison fattrs
                  && forallb dvalue_well_defined args
                  && negb (dvalue_well_defined v))%bool.
        * cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
          unfold raiseUB, trigger_cast, ITree.trigger.
          pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe]; left; reflexivity.
        * cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
          eapply gen_inline_sim_obs_eq;
            [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
          eapply gen_inline_sim_bind;
            [apply cfg_inline_sim_apply_attrs, Hact
            | intros ? v1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
  Qed.

  Lemma select_switch_ren_b (ren_b : block_id -> block_id)
    (val : @dvalue PaV) (def_b : block_id) :
    forall (sws : list (@dvalue PaV * block_id)),
      (exists msg,
         select_switch val def_b sws = raise_error msg /\
         select_switch val (ren_b def_b)
           (List.map (fun '(v, b) => (v, ren_b b)) sws) = raise_error msg) \/
      (exists b,
         In b (def_b :: List.map snd sws) /\
         select_switch val def_b sws = raise_ret b /\
         select_switch val (ren_b def_b)
           (List.map (fun '(v, b) => (v, ren_b b)) sws) = raise_ret (ren_b b)).
  Proof.
    induction sws as [| [v id] rest IH]; cbn [List.map select_switch snd].
    - right; exists def_b; split; [left; reflexivity | split; reflexivity].
    - destruct val as [db1 | |];
        [| left; eexists; split; reflexivity | left; eexists; split; reflexivity].
      destruct db1; try (left; eexists; split; reflexivity).
      destruct v as [db2 | |];
        [| left; eexists; split; reflexivity | left; eexists; split; reflexivity].
      destruct db2; try (left; eexists; split; reflexivity).
      destruct (Pos.eq_dec sz sz0) as [<- | _]; [cbn | left; eexists; split; reflexivity].
      destruct (VellvmIntegers.cmp Ceq x x0).
      + right; exists id; split; [right; left; reflexivity | split; reflexivity].
      + destruct IH as [(msg & E1 & E2) | (b & Hb & E1 & E2)].
        * left; exists msg; split; assumption.
        * right; exists b; split.
          -- destruct Hb as [<- | Hb]; [left; reflexivity | right; right; exact Hb].
          -- split; assumption.
  Qed.

  Lemma switch_elab_ren_b (ren_b : block_id -> block_id)
    (val : @dvalue PaV) (def_b : block_id)
    (dests : list (tint_literal * block_id)) :
    let elab (db : block_id) (ds : list (tint_literal * block_id)) : EOU block_id :=
      ExtLib.Structures.Monad.bind
        (map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           ds)
        (fun switches => select_switch val db switches)
    in
    (exists eou_err,
       (forall b0, eou_err <> raise_ret b0) /\
       elab def_b dests = eou_err /\
       elab (ren_b def_b) (List.map (fun '(lit, b) => (lit, ren_b b)) dests) = eou_err) \/
    (exists b,
       In b (def_b :: List.map snd dests) /\
       elab def_b dests = raise_ret b /\
       elab (ren_b def_b) (List.map (fun '(lit, b) => (lit, ren_b b)) dests) = raise_ret (ren_b b)).
  Proof.
    intros elab.
    assert (Hmap :
      (exists err_sw,
         (forall l0, err_sw <> raise_ret l0) /\
         map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           dests = err_sw /\
         map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           (List.map (fun '(lit, b) => (lit, ren_b b)) dests) = err_sw) \/
      (exists sws,
         List.map snd sws = List.map snd dests /\
         map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           dests = raise_ret sws /\
         map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           (List.map (fun '(lit, b) => (lit, ren_b b)) dests) =
         raise_ret (List.map (fun '(v, b) => (v, ren_b b)) sws))).
    { induction dests as [| [[sz x] id] rest IH]; cbn [List.map map_monad snd].
      - right; exists []; split; [reflexivity | split; reflexivity].
      - destruct (coerce_integer_to_int (Some sz) (denote_int_syntax x)) as [m | m | m | s];
          cbn [EOU_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret].
        + left; exists (raise_oom m); split; [intros ?; discriminate | split; reflexivity].
        + left; exists (raise_ub m); split; [intros ?; discriminate | split; reflexivity].
        + left; exists (raise_error m); split; [intros ?; discriminate | split; reflexivity].
        + destruct IH as [(err_sw & Hnr & E1 & E2) | (sws & Hsnd & E1 & E2)].
          * rewrite E1, E2.
            destruct err_sw as [m | m | m | l0]; [| | | exfalso; exact (Hnr l0 Logic.eq_refl)];
              cbn; left; eexists; split; [intros ?; discriminate | split; reflexivity].
          * rewrite E1, E2; cbn [EOU_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret List.map].
            right; exists ((DVALUE_Base s, id) :: sws).
            cbn [List.map snd]; rewrite Hsnd; split; [reflexivity | split; reflexivity]. }
    unfold elab.
    destruct Hmap as [(err_sw & Hnr & E1 & E2) | (sws & Hsnd & E1 & E2)].
    - rewrite E1, E2.
      destruct err_sw as [m | m | m | l0]; [| | | exfalso; exact (Hnr l0 Logic.eq_refl)];
        cbn; left; eexists; split; [intros ?; discriminate | split; reflexivity].
    - rewrite E1, E2; cbn [EOU_monad ExtLib.Structures.Monad.bind].
      destruct (select_switch_ren_b ren_b val def_b sws)
        as [(msg & Es1 & Es2) | (b & Hb & Es1 & Es2)].
      + left; exists (raise_error msg); split; [intros ?; discriminate | split; assumption].
      + right; exists b; rewrite <- Hsnd; split; [exact Hb | split; assumption].
  Qed.

  Lemma map_id_pairs {A B : Type} (xs : list (A * B)) :
    List.map (fun '(a, b) => (a, b)) xs = xs.
  Proof.
    induction xs as [| [a b] rest IH]; [reflexivity | cbn; rewrite IH; reflexivity].
  Qed.

  (** ** 9E. Callee Leaf-Instruction, Code, Phi, Block, and Parameter-Copy Simulations *)

  Lemma denote_instr_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l_origs all_fresh d_cur : list raw_id)
    (ren_l : raw_id -> raw_id)
    stk (ce1 e1 e2 : @local_env PaV)
    (va1 va2 : option (@ptr PaV))
    (iid : instr_id) (ins : instr dtyp) (md : list (metadata dtyp))
    (Hleaf : is_leaf_instr_entry (iid, ins, md) = true)
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh)
    (Hd_dom : incl d_cur l_origs)
    (Hiid_dom : incl (instr_id_defs iid) l_origs)
    (Huses : incl (full_instr_uses ins ++ flat_map full_metadata_uses md) d_cur)
    (Hbound : callee_defs_bound ren_l d_cur e1 e2)
    (Hagree : env_agree_outside all_fresh ce1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Inlined stk ce1 e1' e2' /\
           callee_defs_bound ren_l (d_cur ++ instr_id_defs iid) e1' e2' /\
           env_agree_outside all_fresh ce1 e2')
      (IC_Inlined stk ce1 e1 e2)
      (denote_instr (iid, ins, md) va1)
      (denote_instr (ren_code_entry ren_l (iid, ins, md)) va2).
  Proof.
    unfold is_leaf_instr_entry in Hleaf.
    apply andb_prop in Hleaf as [_ Hleaf].
    destruct iid as [x | vn],
             ins as [s_cmt | op | ? ? ? ? | dt anns | dt [du ptr] anns | [dt val] [du ptr] anns
                     | ? ? | ? | ? | s_f1 s_f2 | ? ? ?];
      try discriminate Hleaf.
    - (* IId x, INSTR_Op op *)
      assert (Hx_dom : In x l_origs) by (apply Hiid_dom; left; reflexivity).
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_cur stk ce1 e1 e2 None op);
          [intros z Hz; apply Huses, in_or_app; left; exact Hz | exact Hbound].
      + intros ? uv _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                   (IC_Inlined stk ce1 e1 e2)
                   (IC_Inlined stk ce1 (Maps.add x uv e1) e2)
                   (IC_Inlined stk ce1 (Maps.add x uv e1) (Maps.add (ren_l x) uv e2))
                   x (ren_l x) uv Logic.eq_refl Logic.eq_refl).
        * intros ? [] [] (-> & _ & _).
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | split].
          -- apply (callee_defs_bound_add ren_l l_origs d_cur x uv e1 e2 Hinj_l Hd_dom Hx_dom Hbound).
          -- apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hx_dom | exact Hagree].
    - (* IId x, INSTR_Alloca dt anns (0-byte varargs alloca) *)
      unfold is_zero_vararg_alloca in Hleaf; apply andb_prop in Hleaf as [Hdt Hanns].
      apply dtyp_eqb_spec in Hdt; apply is_empty_list_spec in Hanns; subst dt anns.
      assert (Hx_dom : In x l_origs) by (apply Hiid_dom; left; reflexivity).
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr explicit_alignment find_option].
      eapply gen_inline_sim_bind.
      + eapply gen_inline_sim_bind.
        * unfold alloca; apply cfg_inline_sim_trigger_refl.
          cbn [inl_sync_cfg inl_sync_mcfg is_callee_sync_mem subevent resum
               ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
          rewrite dtyp_eqb_refl; reflexivity.
        * intros ? v _ [-> <-].
          apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                   (IC_Inlined stk ce1 e1 e2)
                   (IC_Inlined stk ce1 (Maps.add x v e1) e2)
                   (IC_Inlined stk ce1 (Maps.add x v e1) (Maps.add (ren_l x) v e2))
                   x (ren_l x) v Logic.eq_refl Logic.eq_refl).
      + intros ? [] [] (-> & _ & _).
        apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
        eexists _, _; split; [reflexivity | split].
        * apply (callee_defs_bound_add ren_l l_origs d_cur x _ e1 e2 Hinj_l Hd_dom Hx_dom Hbound).
        * apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hx_dom | exact Hagree].
    - (* IId x, INSTR_Load dt (du, ptr) anns *)
      assert (Hx_dom : In x l_origs) by (apply Hiid_dom; left; reflexivity).
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_cur stk ce1 e1 e2 (Some du) ptr);
          [intros z Hz; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd];
           apply in_or_app; left; exact Hz
          | exact Hbound].
      + intros ? a _ [-> <-].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
        eapply gen_inline_sim_bind;
          [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? v _ [-> <-]].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? v' _ [-> <-]].
        eapply gen_inline_sim_bind;
          [apply cfg_inline_sim_assert_load_deref; reflexivity | intros ? [] _ (-> & _ & _)].
        eapply gen_inline_sim_weaken;
          [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                      (IC_Inlined stk ce1 e1 e2)
                      (IC_Inlined stk ce1 (Maps.add x v' e1) e2)
                      (IC_Inlined stk ce1 (Maps.add x v' e1) (Maps.add (ren_l x) v' e2))
                      x (ren_l x) v' Logic.eq_refl Logic.eq_refl)].
        intros ? [] [] (-> & _ & _).
        split; [reflexivity | split; [reflexivity |]].
        eexists _, _; split; [reflexivity | split].
        * apply (callee_defs_bound_add ren_l l_origs d_cur x v' e1 e2 Hinj_l Hd_dom Hx_dom Hbound).
        * apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hx_dom | exact Hagree].
    - (* IVoid vn, INSTR_Comment *)
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr instr_id_defs].
      rewrite app_nil_r; apply gen_inline_sim_ret.
      split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* IVoid vn, INSTR_Store (dt, val) (du, ptr) anns *)
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr instr_id_defs].
      rewrite app_nil_r.
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_cur stk ce1 e1 e2 (Some dt) val);
          [intros z Hz; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd];
           apply in_or_app; left; exact Hz
          | exact Hbound].
      + intros ? v _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_cur stk ce1 e1 e2 (Some du) ptr);
            [intros z Hz; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd];
             apply in_or_app; right; apply in_or_app; left; exact Hz
            | exact Hbound].
        * intros ? a _ [-> <-].
          eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
          eapply gen_inline_sim_bind.
          -- destruct a as [db | |];
               try (unfold store; apply cfg_inline_sim_trigger_refl; reflexivity).
             destruct db;
               try (unfold store; apply cfg_inline_sim_trigger_refl; reflexivity).
             apply cfg_inline_sim_raiseUB.
          -- intros ? [] _ [-> _]; apply gen_inline_sim_ret.
             split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* IVoid vn, INSTR_Fence *)
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr instr_id_defs].
      rewrite app_nil_r; apply gen_inline_sim_ret.
      split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
  Qed.

  Lemma denote_code_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l_origs all_fresh : list raw_id)
    (ren_l : raw_id -> raw_id)
    (va1 va2 : option (@ptr PaV))
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh) :
    forall (cd : code dtyp) (d_cur d_out : list raw_id)
           stk (ce1 e1 e2 : @local_env PaV),
      forallb is_leaf_instr_entry cd = true ->
      check_code_defs d_cur cd = Some d_out ->
      incl d_cur l_origs ->
      incl (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd) l_origs ->
      callee_defs_bound ren_l d_cur e1 e2 ->
      env_agree_outside all_fresh ce1 e2 ->
      cfg_inline_sim opt_call1 g0 false
        (fun ic' r1 r2 =>
           r1 = tt /\ r2 = tt /\
           exists e1' e2',
             ic' = IC_Inlined stk ce1 e1' e2' /\
             callee_defs_bound ren_l d_out e1' e2' /\
             env_agree_outside all_fresh ce1 e2')
        (IC_Inlined stk ce1 e1 e2)
        (denote_code cd va1)
        (denote_code (List.map (ren_code_entry ren_l) cd) va2).
  Proof.
    induction cd as [| [[iid ins] md] rest IH];
      intros d_cur d_out stk ce1 e1 e2 Hleaf Hchk Hd_dom Hcd_dom Hbound Hagree.
    - cbn [check_code_defs] in Hchk; injection Hchk as <-.
      cbn [List.map denote_code loop_monad].
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - cbn [forallb] in Hleaf; apply andb_prop in Hleaf as [Hi Hrest_leaf].
      apply check_code_defs_inv in Hchk as [Huses Hchk_rest].
      cbn [flat_map] in Hcd_dom.
      assert (Hiid_dom : incl (instr_id_defs iid) l_origs).
      { intros z Hz; apply Hcd_dom, in_or_app; left; exact Hz. }
      assert (Hrest_dom : incl (flat_map (fun '(iid0, _, _) => instr_id_defs iid0) rest) l_origs).
      { intros z Hz; apply Hcd_dom, in_or_app; right; exact Hz. }
      cbn [List.map denote_code loop_monad].
      eapply gen_inline_sim_bind.
      + eapply denote_instr_callee_sim; eassumption.
      + intros ? [] [] (_ & _ & e1' & e2' & -> & Hbound' & Hagree').
        apply (IH (d_cur ++ instr_id_defs iid) d_out stk ce1 e1' e2' Hrest_leaf Hchk_rest);
          try assumption.
        apply incl_app; assumption.
  Qed.

  Lemma denote_phis_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l_origs b_origs all_fresh d_in : list raw_id)
    (ren_l ren_b : raw_id -> raw_id)
    stk (ce1 e1 e2 : @local_env PaV)
    (b_from1 b_from2 : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh)
    (Hinj_b : forall b1 b2, In b1 b_origs -> In b2 b_origs -> ren_b b1 = ren_b b2 -> b1 = b2)
    (Hd_dom : incl d_in l_origs)
    (Hp_defs_dom : incl (List.map (fun '(x, _, _) => x) phis) l_origs)
    (Hp_lbls_dom : incl (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) phis) b_origs)
    (Hbound : callee_defs_bound ren_l d_in e1 e2)
    (Hagree : env_agree_outside all_fresh ce1 e2)
    (Hentry_or_pred :
       phis = [] \/
       (b_from2 = ren_b b_from1 /\
        In b_from1 b_origs /\
        Forall
          (fun '(_, Phi _ _ pargs, md) =>
             exists op,
               assoc b_from1 pargs = Some op /\
               incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_in)
          phis)) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Inlined stk ce1 e1' e2' /\
           callee_defs_bound ren_l (d_in ++ List.map (fun '(x, _, _) => x) phis) e1' e2' /\
           env_agree_outside all_fresh ce1 e2')
      (IC_Inlined stk ce1 e1 e2)
      (denote_phis b_from1 phis)
      (denote_phis b_from2 (List.map (ren_phi_entry ren_l ren_b) phis)).
  Proof.
    destruct Hentry_or_pred as [-> | (Hb_eq & Hfrom_dom & Hall_p)].
    - cbn [List.map denote_phis map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite app_nil_r.
      eapply gen_inline_sim_obs_eq;
        [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
        | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - subst b_from2; unfold denote_phis.
      assert (Heval :
        forall ps,
          incl (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) ps) b_origs ->
          Forall
            (fun '(_, Phi _ _ pargs, md) =>
               exists op,
                 assoc b_from1 pargs = Some op /\
                 incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_in)
            ps ->
          cfg_inline_sim opt_call1 g0 false
            (fun ic' dvs1 dvs2 =>
               ic' = IC_Inlined stk ce1 e1 e2 /\
               List.map fst dvs1 = List.map (fun '(x, _, _) => x) ps /\
               dvs2 = List.map (fun '(x, dv) => (ren_l x, dv)) dvs1)
            (IC_Inlined stk ce1 e1 e2)
            (map_monad (denote_phi b_from1) ps)
            (map_monad (denote_phi (ren_b b_from1)) (List.map (ren_phi_entry ren_l ren_b) ps))).
      { intros ps Hlbls Hps.
        induction Hps as [| [[x [fm dt pargs]] md] rest (op & Eop & Hop_uses) _ IH];
          cbn [List.map map_monad].
        - apply gen_inline_sim_ret; auto.
        - cbn [flat_map] in Hlbls.
          assert (Hpargs_dom : incl (List.map fst pargs) b_origs).
          { intros b Hb; apply Hlbls, in_or_app; left; exact Hb. }
          assert (Hrest_lbls : incl (flat_map (fun '(_, Phi _ _ pargs0, _) => List.map fst pargs0) rest) b_origs).
          { intros b Hb; apply Hlbls, in_or_app; right; exact Hb. }
          eapply gen_inline_sim_bind with
            (RA := fun ic' p1 p2 =>
                     ic' = IC_Inlined stk ce1 e1 e2 /\
                     exists uv, p1 = (x, uv) /\ p2 = (ren_l x, uv)).
          + cbn [ren_phi_entry denote_phi].
            rewrite (assoc_ren_phi ren_b (ren_exp ren_l) b_origs b_from1 pargs Hinj_b Hfrom_dom Hpargs_dom).
            rewrite Eop; cbn [option_map].
            eapply gen_inline_sim_bind.
            * apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_in stk ce1 e1 e2 (Some dt) op);
                [intros z Hz; apply Hop_uses, in_or_app; left; exact Hz | exact Hbound].
            * intros ? uv _ [-> <-]; apply gen_inline_sim_ret.
              split; [reflexivity | exists uv; split; reflexivity].
          + intros ? [id1 uv1] [id2 uv2] (-> & uv & E1 & E2).
            injection E1 as <- <-; injection E2 as -> _.
            eapply gen_inline_sim_bind; [apply (IH Hrest_lbls) |].
            intros ? dvs1 dvs2 (-> & Hfst & ->).
            apply gen_inline_sim_ret; cbn [List.map fst]; rewrite Hfst; auto. }
      assert (Hwrites :
        forall (dvs : list (local_id * @dvalue PaV)) (d_cur : list raw_id) (ea1 ea2 : @local_env PaV),
          incl d_cur l_origs ->
          incl (List.map fst dvs) l_origs ->
          callee_defs_bound ren_l d_cur ea1 ea2 ->
          env_agree_outside all_fresh ce1 ea2 ->
          cfg_inline_sim opt_call1 g0 false
            (fun ic' _ _ =>
               exists ea1' ea2',
                 ic' = IC_Inlined stk ce1 ea1' ea2' /\
                 callee_defs_bound ren_l (d_cur ++ List.map fst dvs) ea1' ea2' /\
                 env_agree_outside all_fresh ce1 ea2')
            (IC_Inlined stk ce1 ea1 ea2)
            (map_monad (fun '(id, dv) => lwrite id dv) dvs)
            (map_monad (fun '(id, dv) => lwrite id dv)
               (List.map (fun '(x, dv) => (ren_l x, dv)) dvs))).
      { induction dvs as [| [x dv] rest IHw];
          intros d_cur ea1 ea2 Hd_cur Hdvs_dom Hb_cur Hag_cur;
          cbn [List.map map_monad fst].
        - rewrite app_nil_r; apply gen_inline_sim_ret; exists ea1, ea2; auto.
        - assert (Hx_dom : In x l_origs) by (apply Hdvs_dom; left; reflexivity).
          assert (Hrest_dom : incl (List.map fst rest) l_origs).
          { intros z Hz; apply Hdvs_dom; right; exact Hz. }
          eapply gen_inline_sim_bind.
          + apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                     (IC_Inlined stk ce1 ea1 ea2)
                     (IC_Inlined stk ce1 (Maps.add x dv ea1) ea2)
                     (IC_Inlined stk ce1 (Maps.add x dv ea1) (Maps.add (ren_l x) dv ea2))
                     x (ren_l x) dv Logic.eq_refl Logic.eq_refl).
          + intros ? [] [] (-> & _ & _).
            eapply gen_inline_sim_bind.
            * apply (IHw (d_cur ++ [x]) (Maps.add x dv ea1) (Maps.add (ren_l x) dv ea2)).
              -- apply incl_app; [exact Hd_cur | intros z [<- | []]; exact Hx_dom].
              -- exact Hrest_dom.
              -- apply (callee_defs_bound_add ren_l l_origs d_cur x dv ea1 ea2 Hinj_l Hd_cur Hx_dom Hb_cur).
              -- apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hx_dom | exact Hag_cur].
            * intros ? _ _ (ea1' & ea2' & -> & Hb' & Hag').
              rewrite <- app_assoc in Hb'.
              apply gen_inline_sim_ret; exists ea1', ea2'; auto. }
      eapply gen_inline_sim_bind; [apply (Heval phis Hp_lbls_dom Hall_p) |].
      intros ? dvs1 dvs2 (-> & Hfst & ->).
      eapply gen_inline_sim_bind.
      + apply (Hwrites dvs1 d_in e1 e2 Hd_dom); [rewrite Hfst; exact Hp_defs_dom | exact Hbound | exact Hagree].
      + intros ? _ _ (e1' & e2' & -> & Hb' & Hag').
        rewrite Hfst in Hb'.
        apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1', e2'; auto]].
  Qed.

  Lemma denote_exp'_mk_copy_exp (ty_i1 dt : dtyp) (ex : exp dtyp) :
    @denote_exp' PaV None (mk_copy_exp ty_i1 dt ex) ≅
    @denote_exp' PaV (Some dt) ex.
  Proof.
    unfold denote_exp'; apply inl_withCall_proper, denote_mk_copy_exp.
  Qed.

  Lemma check_code_defs_dom {T : Set} (dom : list raw_id) :
    forall (cd : list (instr_id * instr T * list (metadata T))) (cur d_out : list raw_id),
      check_code_defs cur cd = Some d_out ->
      incl cur dom ->
      incl (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd) dom ->
      incl d_out dom.
  Proof.
    induction cd as [| [[iid ins] md] rest IH]; intros cur d_out Hchk Hcur Hcd.
    - cbn [check_code_defs] in Hchk; injection Hchk as <-; exact Hcur.
    - apply check_code_defs_inv in Hchk as [_ Hrest].
      cbn [flat_map] in Hcd.
      apply (IH (cur ++ instr_id_defs iid) d_out Hrest).
      + apply incl_app; [exact Hcur | intros x Hx; apply Hcd, in_or_app; left; exact Hx].
      + intros x Hx; apply Hcd, in_or_app; right; exact Hx.
  Qed.

  Lemma denote_block_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (opt_ret_dt : option dtyp)
    (l_origs b_origs all_fresh d_in : list raw_id)
    (in_map : list (block_id * list raw_id))
    (callee_bks : ocfg dtyp)
    (ren_l ren_b : raw_id -> raw_id)
    (post_bid : block_id)
    (va1 va2 : option (@ptr PaV))
    stk (ce1 e1 e2 : @local_env PaV)
    (b_from1 b_from2 : block_id)
    (bk : block dtyp) (rtmp : raw_id)
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh)
    (Hinj_b : forall b1 b2, In b1 b_origs -> In b2 b_origs -> ren_b b1 = ren_b b2 -> b1 = b2)
    (Hrtmp_fresh : In rtmp all_fresh)
    (Hleaf : is_leaf_block opt_ret_dt bk = true)
    (Hvblk : verify_block_defs callee_bks in_map bk = true)
    (Hdin_dom : incl d_in l_origs)
    (Hd0_in : incl (lookup_def_set in_map (blk_id bk)) d_in)
    (Hdefs_dom : incl (full_block_defs bk) l_origs)
    (Hlbls_dom : incl (block_all_label_ids bk) b_origs)
    (Hbound : callee_defs_bound ren_l d_in e1 e2)
    (Hagree : env_agree_outside all_fresh ce1 e2)
    (Hentry_or_pred :
       blk_phis bk = [] \/
       (b_from2 = ren_b b_from1 /\
        In b_from1 b_origs /\
        Forall
          (fun '(_, Phi _ _ pargs, md) =>
             exists op,
               assoc b_from1 pargs = Some op /\
               incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_in)
          (blk_phis bk))) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' bd1 bd2 =>
         (exists succ_bid d_out e1' e2',
            bd1 = inl succ_bid /\
            bd2 = inl (ren_b succ_bid) /\
            In succ_bid (term_succ_bids (snd (fst (blk_term bk)))) /\
            check_succ_edge callee_bks in_map (blk_id bk) d_out succ_bid = true /\
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
                (exists rpair, snd (fst (blk_term bk)) = TERM_Ret rpair) /\
                Maps.lookup rtmp e2' = Some dv
            end))
      (IC_Inlined stk ce1 e1 e2)
      (denote_block bk b_from1 va1)
      (denote_block (transform_callee_block ren_l ren_b post_bid (bk, rtmp)) b_from2 va2).
  Proof.
    unfold is_leaf_block in Hleaf.
    apply andb_prop in Hleaf as [Hleaf1 Hterm_leaf].
    apply andb_prop in Hleaf1 as [_ Hcode_leaf].
    apply verify_block_defs_inv in Hvblk as (d_out & Hchk_cd & Htm_uses & Hsuccs).
    assert (Hd0_dom : incl (lookup_def_set in_map (blk_id bk)) l_origs).
    { intros z Hz; apply Hdin_dom, Hd0_in, Hz. }
    assert (Hp_defs_dom : incl (List.map (fun '(x, _, _) => x) (blk_phis bk)) l_origs).
    { intros z Hz; apply Hdefs_dom; unfold full_block_defs; apply in_or_app; left; exact Hz. }
    assert (Hcd_defs_dom : incl (flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk)) l_origs).
    { intros z Hz; apply Hdefs_dom; unfold full_block_defs;
        apply in_or_app; right; apply in_or_app; left; exact Hz. }
    assert (Hp_lbls_dom : incl (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) (blk_phis bk)) b_origs).
    { intros b Hb; apply Hlbls_dom; unfold block_all_label_ids;
        right; apply in_or_app; left; exact Hb. }
    unfold denote_block, transform_callee_block.
    destruct (blk_term bk) as [[tiid tm] tmd] eqn:Ebt.
    cbn [fst snd] in *.
    assert (Hphis_eq :
      blk_phis
        (let '(new_code, new_term) :=
           match tm with
           | TERM_Ret (dt, op) =>
               (List.map (ren_code_entry ren_l) (blk_code bk) ++
                [(IId rtmp, INSTR_Op (mk_copy_exp (DTYPE_I 1) dt (ren_exp ren_l op)), [])],
                (IVoid 0%Z, TERM_Br_1 post_bid, []))
           | TERM_Ret_void =>
               (List.map (ren_code_entry ren_l) (blk_code bk),
                (IVoid 0%Z, TERM_Br_1 post_bid, []))
           | TERM_Br (dt, op) b1 b2 =>
               (List.map (ren_code_entry ren_l) (blk_code bk),
                (tiid, TERM_Br (dt, ren_exp ren_l op) (ren_b b1) (ren_b b2), tmd))
           | TERM_Br_1 b =>
               (List.map (ren_code_entry ren_l) (blk_code bk),
                (tiid, TERM_Br_1 (ren_b b), tmd))
           | TERM_Switch (dt, op) def_b brs =>
               (List.map (ren_code_entry ren_l) (blk_code bk),
                (tiid,
                 TERM_Switch (dt, ren_exp ren_l op) (ren_b def_b)
                   (List.map (fun '(lit, b) => (lit, ren_b b)) brs), tmd))
           | _ =>
               (List.map (ren_code_entry ren_l) (blk_code bk), (tiid, tm, tmd))
           end
         in
         {| blk_id       := ren_b (blk_id bk);
            blk_phis     := List.map (ren_phi_entry ren_l ren_b) (blk_phis bk);
            blk_code     := new_code;
            blk_term     := new_term;
            blk_comments := blk_comments bk |}) =
      List.map (ren_phi_entry ren_l ren_b) (blk_phis bk)).
    { destruct tm as [[? ?] | | [? ?] ? ? | ? | [? ?] ? ? | ? ? ? | ? | ? ? ? ? ? ? | ]; reflexivity. }
    rewrite Hphis_eq; clear Hphis_eq.
    eapply gen_inline_sim_bind.
    - apply (denote_phis_callee_sim opt_call1 g0 l_origs b_origs all_fresh d_in
               ren_l ren_b stk ce1 e1 e2 b_from1 b_from2 (blk_phis bk));
        assumption.
    - intros ? [] [] (_ & _ & e1_p & e2_p & -> & Hbound_p & Hagree_p).
      assert (Hbound_p0 :
        callee_defs_bound ren_l
          (lookup_def_set in_map (blk_id bk) ++ List.map (fun '(x, _, _) => x) (blk_phis bk))
          e1_p e2_p).
      { eapply callee_defs_bound_incl; [| exact Hbound_p].
        intros z Hz; apply in_app_or in Hz as [Hz | Hz]; apply in_or_app;
          [left; apply Hd0_in, Hz | right; exact Hz]. }
      assert (Hd_phi_dom :
        incl (lookup_def_set in_map (blk_id bk) ++ List.map (fun '(x, _, _) => x) (blk_phis bk)) l_origs).
      { apply incl_app; assumption. }
      assert (Hd_out_dom : incl d_out l_origs).
      { exact (check_code_defs_dom l_origs (blk_code bk) _ d_out Hchk_cd Hd_phi_dom Hcd_defs_dom). }
      unfold is_leaf_term_entry in Hterm_leaf.
      apply andb_prop in Hterm_leaf as [_ Htm_ok].
      destruct tm as [[dt op] | | [dt op] b1 b2 | b | [dt op] def_b brs | ? ? ? | ? | ? ? ? ? ? ? | ];
        try discriminate Htm_ok;
        cbn [blk_code blk_term].
      + (* TERM_Ret (dt, op) *)
        eapply gen_inline_sim_obs_eq.
        * reflexivity.
        * symmetry; unfold denote_code at 1.
          rewrite loop_monad_itree_app, Eqit.bind_bind; reflexivity.
        * eapply gen_inline_sim_bind.
          -- apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                      Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                      Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
          -- intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hbound_c & Hagree_c).
             cbn [loop_monad denote_instr denote_terminator ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
             eapply gen_inline_sim_obs_eq.
             ++ reflexivity.
             ++ symmetry.
                rewrite !Eqit.bind_bind.
                eapply eq_itree_clo_bind with (UU := Logic.eq);
                  [apply denote_exp'_mk_copy_exp | intros uv _ <-].
                rewrite !Eqit.bind_bind, !Eqit.bind_ret_l; reflexivity.
             ++ eapply gen_inline_sim_bind.
                ** apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_out stk ce1 e1_c e2_c (Some dt) op);
                     [intros z Hz; apply Htm_uses, in_or_app; left; exact Hz | exact Hbound_c].
                ** intros ? dv _ [-> <-].
                   eapply gen_inline_sim_obs_eq;
                     [apply Eqit.bind_ret_l | reflexivity |].
                   eapply gen_inline_sim_bind.
                   --- apply (cfg_inline_sim_lwrite_r opt_call1 g0 false
                                (IC_Inlined stk ce1 e1_c e2_c)
                                (IC_Inlined stk ce1 e1_c (Maps.add rtmp dv e2_c))
                                rtmp dv Logic.eq_refl).
                   --- intros ? [] [] (-> & _ & _).
                       apply gen_inline_sim_ret; right.
                       exists dv, e1_c, (Maps.add rtmp dv e2_c).
                       split; [reflexivity | split; [reflexivity | split; [reflexivity | split]]].
                       +++ apply env_agree_outside_add_fresh_r; [exact Hrtmp_fresh | exact Hagree_c].
                       +++ destruct opt_ret_dt as [rdt |]; [| exact I].
                           split; [exists (dt, op); reflexivity | apply PassCommon.lookup_add_eq].
      + (* TERM_Ret_void *)
        destruct opt_ret_dt as [rdt |]; [discriminate Htm_ok |].
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & _ & Hagree_c).
          cbn [denote_terminator].
          apply gen_inline_sim_ret; right.
          exists (DVALUE_Base DVALUE_None), e1_c, e2_c; auto 7.
      + (* TERM_Br (dt, op) b1 b2 *)
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hbound_c & Hagree_c).
          cbn [denote_terminator].
          eapply gen_inline_sim_bind.
          -- apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_out stk ce1 e1_c e2_c (Some dt) op);
               [intros z Hz; apply Htm_uses, in_or_app; left; exact Hz | exact Hbound_c].
          -- intros ? v _ [-> <-].
             destruct v as [db | |]; try (apply cfg_inline_sim_raise; reflexivity).
             destruct db; try (apply cfg_inline_sim_raise; reflexivity).
             ++ destruct sz as [? | ? |]; try (apply cfg_inline_sim_raise; reflexivity).
                destruct (equ x one).
                ** apply gen_inline_sim_ret; left.
                   assert (Hb1 : In b1 (term_succ_bids (TERM_Br (dt, op) b1 b2))) by (left; reflexivity).
                   exists b1, d_out, e1_c, e2_c; auto 10.
                ** apply gen_inline_sim_ret; left.
                   assert (Hb2 : In b2 (term_succ_bids (TERM_Br (dt, op) b1 b2))) by (right; left; reflexivity).
                   exists b2, d_out, e1_c, e2_c; auto 10.
             ++ apply cfg_inline_sim_raiseUB.
      + (* TERM_Br_1 b *)
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hbound_c & Hagree_c).
          cbn [denote_terminator].
          apply gen_inline_sim_ret; left.
          assert (Hb : In b (term_succ_bids (TERM_Br_1 b))) by (left; reflexivity).
          exists b, d_out, e1_c, e2_c; auto 10.
      + (* TERM_Switch (dt, op) def_b brs *)
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hbound_c & Hagree_c).
          cbn [denote_terminator].
          eapply gen_inline_sim_bind.
          -- apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_out stk ce1 e1_c e2_c (Some dt) op);
               [intros z Hz; apply Htm_uses, in_or_app; left; exact Hz | exact Hbound_c].
          -- intros ? sel _ [-> <-].
             destruct (dvalue_is_poison sel).
             ++ apply cfg_inline_sim_raiseUB.
             ++ destruct (switch_elab_ren_b ren_b sel def_b brs)
                  as [(eou_err & Hnr & E1 & E2) | (b & Hb & E1 & E2)].
                ** rewrite E1, E2.
                   destruct eou_err as [m | m | m | b0];
                     [| | | exfalso; exact (Hnr b0 Logic.eq_refl)];
                     cbn [EOU_to_itree].
                   --- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
                         [apply cfg_inline_sim_raiseOOM | intros ? ? ? []].
                   --- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
                         [apply cfg_inline_sim_raiseUB | intros ? ? ? []].
                   --- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
                         [apply cfg_inline_sim_raise; reflexivity | intros ? ? ? []].
                ** rewrite E1, E2; cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
                   eapply gen_inline_sim_obs_eq;
                     [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
                   apply gen_inline_sim_ret; left.
                   exists b, d_out, e1_c, e2_c; auto 10.
      + (* TERM_Unreachable *)
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & _ & _).
          cbn [denote_terminator]; apply cfg_inline_sim_raiseUB.
  Qed.

  Lemma denote_call_args_param_copies_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l_origs all_fresh : list raw_id)
    (ren_l : raw_id -> raw_id)
    (msg : string)
    (caller_va : option (@ptr PaV))
    stk (e1 : @local_env PaV)
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh) :
    forall (params : list local_id)
           (call_args : list (texp dtyp * list param_attr))
           (e2 : @local_env PaV),
      List.length call_args = List.length params ->
      NoDup params ->
      incl params l_origs ->
      (forall te pattrs, In (te, pattrs) call_args -> pattrs = []) ->
      (forall te pattrs x,
         In (te, pattrs) call_args ->
         In x (full_texp_uses te) ->
         ~ In x all_fresh) ->
      env_agree_outside all_fresh e1 e2 ->
      cfg_inline_sim opt_call1 g0 false
        (fun ic' vs r2 =>
           r2 = tt /\
           List.length vs = List.length params /\
           exists e2',
             ic' = IC_Synced stk e1 e2' /\
             env_agree_outside all_fresh e1 e2' /\
             (forall z, ~ In z (List.map ren_l params) -> Maps.lookup z e2' = Maps.lookup z e2) /\
             (forall p v, In (p, v) (combine params vs) -> Maps.lookup (ren_l p) e2' = Some v))
        (IC_Synced stk e1 e2)
        (denote_call_args call_args msg)
        (denote_code (build_param_copies ren_l params call_args) caller_va).
  Proof.
    induction params as [| p ps IH];
      intros [| [[arg_dt arg_e] pattrs] rest] e2 Hlen Hnd Hdom Hpattrs Huses Hagree;
      try discriminate Hlen.
    - cbn [denote_call_args build_param_copies denote_code map_monad loop_monad].
      apply gen_inline_sim_ret.
      split; [reflexivity | split; [reflexivity |]].
      exists e2; split; [reflexivity | split; [exact Hagree | split; [reflexivity | intros _ _ []]]].
    - cbn [List.length] in Hlen; injection Hlen as Hlen.
      inversion Hnd as [| ? ? Hnin_p Hnd_ps]; subst.
      assert (Hp_dom : In p l_origs) by (apply Hdom; left; reflexivity).
      assert (Hps_dom : incl ps l_origs) by (intros q Hq; apply Hdom; right; exact Hq).
      assert (Hp_pattrs : pattrs = []) by (eapply Hpattrs; left; reflexivity).
      subst pattrs.
      cbn [denote_call_args build_param_copies denote_code map_monad loop_monad denote_instr
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      eapply gen_inline_sim_obs_eq.
      + symmetry.
        rewrite Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros v _ <-].
        rewrite apply_attrs_nil_eq, Eqit.bind_ret_l; reflexivity.
      + symmetry.
        rewrite !Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq);
          [apply denote_exp'_mk_copy_exp | intros uv _ <-].
        rewrite !Eqit.bind_bind; reflexivity.
      + eapply gen_inline_sim_bind.
        * apply (denote_exp'_caller_sim opt_call1 g0 all_fresh stk e1 e2 (Some arg_dt) arg_e);
            [intros x Hx; eapply Huses; [left; reflexivity | exact Hx]
            | exact Hagree].
        * intros ? v _ [-> <-].
          eapply gen_inline_sim_obs_eq;
            [apply Eqit.bind_ret_l
            | symmetry; eapply eq_itree_clo_bind with (UU := Logic.eq);
              [reflexivity | intros [] _ _; apply Eqit.bind_ret_l] |].
          eapply gen_inline_sim_bind.
          -- apply (cfg_inline_sim_lwrite_r opt_call1 g0 false
                      (IC_Synced stk e1 e2)
                      (IC_Synced stk e1 (Maps.add (ren_l p) v e2))
                      (ren_l p) v Logic.eq_refl).
          -- intros ? [] [] (-> & _ & _).
             assert (Hagree1 : env_agree_outside all_fresh e1 (Maps.add (ren_l p) v e2)).
             { apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hp_dom | exact Hagree]. }
             eapply gen_inline_sim_obs_eq;
               [reflexivity
               | apply Eqit.bind_ret_r |].
             eapply gen_inline_sim_bind.
             ++ apply (IH rest (Maps.add (ren_l p) v e2) Hlen Hnd_ps Hps_dom).
                ** intros te0 pa0 Hin; eapply Hpattrs; right; exact Hin.
                ** intros te0 pa0 x Hin Hx; eapply Huses; [right; exact Hin | exact Hx].
                ** exact Hagree1.
             ++ intros ? vs [] (_ & Hlen_vs & e2' & -> & Hagree' & Hpres & Hlk_ps).
                apply gen_inline_sim_ret.
                cbn [List.length List.map combine].
                split; [reflexivity | split; [f_equal; exact Hlen_vs |]].
                exists e2'; split; [reflexivity | split; [exact Hagree' | split]].
                ** intros z Hz.
                   assert (Hne_p : ren_l p <> z) by (intros Heq; apply Hz; left; exact Heq).
                   assert (Hnin_ps : ~ In z (List.map ren_l ps)) by (intros Hin; apply Hz; right; exact Hin).
                   rewrite (Hpres z Hnin_ps), PassCommon.lookup_add_neq by exact Hne_p; reflexivity.
                ** intros q w [Heq | Hin].
                   --- injection Heq as <- <-.
                       assert (Hnin_ren_ps : ~ In (ren_l p) (List.map ren_l ps)).
                       { intros Hin; apply in_map_iff in Hin as [q [Heq Hq]].
                         apply Hnin_p; replace p with q; [exact Hq |].
                         apply Hinj_l; [apply Hps_dom, Hq | exact Hp_dom | exact Heq]. }
                       rewrite (Hpres (ren_l p) Hnin_ren_ps); apply PassCommon.lookup_add_eq.
                   --- apply Hlk_ps, Hin.
  Qed.

(** * 10. Caller CFG Simulation, Function/Module Lifting & Top-Level Refinement *)

  (** ** 10A. Caller Instruction, Code, Remapped-Phi, Terminator & Sync-Iter Simulations *)

  Lemma find_option_ann_num_elements_uses
    (anns : list (annotation dtyp)) (t : dtyp) (num_exp : exp dtyp) :
    find_option ann_num_elements anns = Some (t, num_exp) ->
    forall x, In x (full_exp_uses num_exp) -> In x (flat_map full_ann_uses anns).
  Proof.
    induction anns as [| a rest IH]; cbn [find_option flat_map]; [discriminate |].
    destruct a; cbn [ann_num_elements];
      try (intros H x Hx; apply in_or_app; right; eapply IH; eassumption).
    intros H; injection H as ->.
    intros x Hx; apply in_or_app; left; exact Hx.
  Qed.

  Lemma assoc_some_in {B : Type} (k : block_id) (xs : list (block_id * B)) (v : B) :
    assoc k xs = Some v -> In (k, v) xs.
  Proof.
    induction xs as [| [b ex] rest IH]; [cbn; discriminate |].
    destruct (RawIDOrd.eq_dec k b) as [-> | Hne].
    - rewrite assoc_hd; intros H; injection H as <-; left; reflexivity.
    - rewrite assoc_tl by exact Hne; intros H; right; apply IH, H.
  Qed.

  Lemma denote_call_args_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (args : list (texp dtyp * list param_attr)) (msg1 msg2 : string)
    (Huses : forall x,
               In x (flat_map (fun '(te, _) => full_texp_uses te) args) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
      (IC_Synced stk e1 e2)
      (denote_call_args args msg1)
      (denote_call_args args msg2).
  Proof.
    unfold denote_call_args.
    induction args as [| [[t op] attrs] rest IH]; cbn [map_monad flat_map] in *.
    - apply gen_inline_sim_ret; split; reflexivity.
    - eapply gen_inline_sim_bind.
      + eapply gen_inline_sim_bind.
        * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) op);
            [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
        * intros ? v _ [-> <-]; apply cfg_inline_sim_apply_attrs; reflexivity.
      + intros ? v1 _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply IH; intros x Hx; apply Huses, in_or_app; right; exact Hx.
        * intros ? vs1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma cfg_inline_sim_assume_deref
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (or_null : bool) (loc1 loc2 : string) (vs : list (@dvalue PaV))
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = tt /\ r2 = tt)
      ic
      (assume_dereferenceable or_null loc1 vs)
      (assume_dereferenceable or_null loc2 vs).
  Proof.
    unfold assume_dereferenceable, assume_violated, assume_malformed.
    destruct vs as [| p [| sz [| ? ?]]]; try (apply cfg_inline_sim_raise, Hact).
    destruct (dvalue_ptr_address p) as [a |], (bundle_uint sz) as [n |];
      try apply cfg_inline_sim_raiseUB.
    destruct (n =? 0)%Z; [apply gen_inline_sim_ret; auto | apply cfg_inline_sim_assert_deref, Hact].
  Qed.

  Lemma cfg_inline_sim_bundle_check
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (f : exp dtyp) (tag : string) (loc1 loc2 : string) (vs : list (@dvalue PaV))
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = tt /\ r2 = tt)
      ic
      (match bundle_check f tag with Some check => check loc1 vs | None => Ret tt end)
      (match bundle_check f tag with Some check => check loc2 vs | None => Ret tt end).
  Proof.
    unfold bundle_check, assume_bundle_checks.
    destruct (is_llvm_assume f); [| apply gen_inline_sim_ret; auto].
    cbn [find].
    destruct (String.eqb "nonnull" tag); [cbn [option_map snd] |
    destruct (String.eqb "noundef" tag); [cbn [option_map snd] |
    destruct (String.eqb "align" tag); [cbn [option_map snd] |
    destruct (String.eqb "dereferenceable" tag); [cbn [option_map snd] |
    destruct (String.eqb "dereferenceable_or_null" tag); cbn [option_map snd]]]]].
    - unfold assume_nonnull, assume_violated, assume_malformed.
      destruct vs as [| p [| ? ?]]; try (apply cfg_inline_sim_raise, Hact).
      destruct (dvalue_ptr_address p) as [a |]; [| apply cfg_inline_sim_raiseUB].
      destruct (a =? 0)%Z; [apply cfg_inline_sim_raiseUB | apply gen_inline_sim_ret; auto].
    - unfold assume_noundef, assume_violated, assume_malformed.
      destruct vs as [| v [| ? ?]]; try (apply cfg_inline_sim_raise, Hact).
      destruct (dvalue_well_defined v);
        [apply gen_inline_sim_ret; auto | apply cfg_inline_sim_raiseUB].
    - unfold assume_align, assume_violated, assume_malformed.
      destruct vs as [| p [| al off]]; try (apply cfg_inline_sim_raise, Hact).
      destruct (dvalue_ptr_address p) as [a |],
               (bundle_uint al) as [n |],
               (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end) as [o |];
        try apply cfg_inline_sim_raiseUB.
      destruct (if is_power_of_two n then ((a - o) mod n =? 0)%Z else (a =? 0)%Z);
        [apply gen_inline_sim_ret; auto | apply cfg_inline_sim_raiseUB].
    - apply cfg_inline_sim_assume_deref, Hact.
    - apply cfg_inline_sim_assume_deref, Hact.
    - apply gen_inline_sim_ret; auto.
  Qed.

  Lemma denote_operand_bundles_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (loc1 loc2 : string) (f : exp dtyp) (obs : list (@operand_bundle dtyp))
    (Huses : forall x, In x (flat_map full_ob_uses obs) -> ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = tt /\ r2 = tt)
      (IC_Synced stk e1 e2)
      (denote_operand_bundles loc1 f obs)
      (denote_operand_bundles loc2 f obs).
  Proof.
    unfold denote_operand_bundles.
    assert (Hops :
      forall ops,
        (forall x, In x (flat_map full_operand_uses ops) -> ~ In x fresh_set) ->
        cfg_inline_sim opt_call1 g0 false
          (fun ic' vs1 vs2 => ic' = IC_Synced stk e1 e2 /\ vs1 = vs2)
          (IC_Synced stk e1 e2)
          (map_monad (fun o => match o with SSA_value (t, e) => denote_exp' (Some t) e
                                          | Metadata_string _ => ret (DVALUE_Base DVALUE_None) end) ops)
          (map_monad (fun o => match o with SSA_value (t, e) => denote_exp' (Some t) e
                                          | Metadata_string _ => ret (DVALUE_Base DVALUE_None) end) ops)).
    { induction ops as [| o rest IH]; intros Hop_u; cbn [map_monad flat_map] in *.
      - apply gen_inline_sim_ret; split; reflexivity.
      - eapply gen_inline_sim_bind.
        + destruct o as [[t ex] | m].
          * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) ex);
              [intros x Hx; apply Hop_u, in_or_app; left; exact Hx | exact Hagree].
          * apply gen_inline_sim_ret; split; reflexivity.
        + intros ? v1 _ [-> <-].
          eapply gen_inline_sim_bind.
          * apply IH; intros x Hx; apply Hop_u, in_or_app; right; exact Hx.
          * intros ? vs1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
    assert (Hobs :
      forall bs,
        (forall x, In x (flat_map full_ob_uses bs) -> ~ In x fresh_set) ->
        cfg_inline_sim opt_call1 g0 false
          (fun ic' u1 u2 => ic' = IC_Synced stk e1 e2 /\ u1 = u2)
          (IC_Synced stk e1 e2)
          (map_monad
             (fun ob =>
                vs <- map_monad
                        (fun o => match o with SSA_value (t, e) => denote_exp' (Some t) e
                                             | Metadata_string _ => ret (DVALUE_Base DVALUE_None) end)
                        (ob_ops ob) ;;
                match bundle_check f (ob_tag ob) with Some check => check loc1 vs | None => ret tt end) bs)
          (map_monad
             (fun ob =>
                vs <- map_monad
                        (fun o => match o with SSA_value (t, e) => denote_exp' (Some t) e
                                             | Metadata_string _ => ret (DVALUE_Base DVALUE_None) end)
                        (ob_ops ob) ;;
                match bundle_check f (ob_tag ob) with Some check => check loc2 vs | None => ret tt end) bs)).
    { induction bs as [| ob rest IH]; intros Hbs_u; cbn [map_monad flat_map] in *.
      - apply gen_inline_sim_ret; split; reflexivity.
      - eapply gen_inline_sim_bind.
        + eapply gen_inline_sim_bind.
          * apply Hops; intros x Hx; apply Hbs_u, in_or_app; left; exact Hx.
          * intros ? vs1 _ [-> <-].
            eapply gen_inline_sim_weaken;
              [| apply (cfg_inline_sim_bundle_check opt_call1 g0 false (IC_Synced stk e1 e2)
                          f (ob_tag ob) loc1 loc2 vs1 Logic.eq_refl)].
            intros ? ? ? (-> & -> & ->); split; reflexivity.
        + intros ? u1 _ [-> <-].
          eapply gen_inline_sim_bind.
          * apply IH; intros x Hx; apply Hbs_u, in_or_app; right; exact Hx.
          * intros ? us1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
    eapply gen_inline_sim_bind; [apply (Hobs obs Huses) |].
    intros ? _ _ [-> _]; apply gen_inline_sim_ret; auto.
  Qed.

  Lemma denote_cmpxchg_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (id : raw_id) (cpx : cmpxchg dtyp)
    (Huses : forall x,
               In x (full_texp_uses (c_ptr cpx) ++ full_texp_uses (c_cmp cpx) ++ full_texp_uses (c_new cpx)) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_cmpxchg id cpx)
      (denote_cmpxchg id cpx).
  Proof.
    unfold denote_cmpxchg.
    destruct (c_ptr cpx) as [ptr_ty ptr_val],
             (c_cmp cpx) as [cmp_ty cmp_val],
             (c_new cpx) as [new_ty new_val].
    destruct (dtyp_eq_dec cmp_ty new_ty); [| apply cfg_inline_sim_raise; reflexivity].
    eapply gen_inline_sim_bind.
    - apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some ptr_ty) ptr_val);
        [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
    - intros ? ptr_v _ [-> <-].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some cmp_ty) cmp_val);
          [intros x Hx; apply Huses, in_or_app; right; apply in_or_app; left; exact Hx | exact Hagree].
      + intros ? cmp_v _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some cmp_ty) new_val);
            [intros x Hx; apply Huses, in_or_app; right; apply in_or_app; right; exact Hx | exact Hagree].
        * intros ? new_v _ [-> <-].
          eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
          eapply gen_inline_sim_bind;
            [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? loaded_v _ [-> <-]].
          eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? dv _ [-> <-]].
          destruct dv as [db | |]; try (apply cfg_inline_sim_raise; reflexivity).
          destruct db; try (apply cfg_inline_sim_raise; reflexivity).
          -- destruct sz as [? | ? |]; try (apply cfg_inline_sim_raise; reflexivity).
             destruct (equ x one).
             ++ eapply gen_inline_sim_bind;
                  [unfold store; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
                set (ret_v := DVALUE_Struct false [loaded_v; DVALUE_Base (DVALUE_I 1 one)]).
                eapply gen_inline_sim_weaken;
                  [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                              (IC_Synced stk e1 e2)
                              (IC_Synced stk (Maps.add id ret_v e1) e2)
                              (IC_Synced stk (Maps.add id ret_v e1) (Maps.add id ret_v e2))
                              id id ret_v Logic.eq_refl Logic.eq_refl)].
                intros ? [] [] (-> & _ & _).
                split; [reflexivity | split; [reflexivity |]].
                eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
             ++ set (ret_v := DVALUE_Struct false [loaded_v; DVALUE_Base (DVALUE_I 1 zero)]).
                eapply gen_inline_sim_weaken;
                  [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                              (IC_Synced stk e1 e2)
                              (IC_Synced stk (Maps.add id ret_v e1) e2)
                              (IC_Synced stk (Maps.add id ret_v e1) (Maps.add id ret_v e2))
                              id id ret_v Logic.eq_refl Logic.eq_refl)].
                intros ? [] [] (-> & _ & _).
                split; [reflexivity | split; [reflexivity |]].
                eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
          -- apply cfg_inline_sim_raiseUB.
  Qed.

  Lemma denote_atomicrmw_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (id : raw_id) (armw : atomicrmw dtyp)
    (Huses : forall x,
               In x (full_texp_uses (a_ptr armw) ++ full_texp_uses (a_val armw)) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_atomicrmw id armw)
      (denote_atomicrmw id armw).
  Proof.
    unfold denote_atomicrmw.
    destruct (a_ptr armw) as [ptr_ty ptr_val],
             (a_val armw) as [a_ty a_v_exp].
    eapply gen_inline_sim_bind.
    - apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some ptr_ty) ptr_val);
        [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
    - intros ? ptr_v _ [-> <-].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some a_ty) a_v_exp);
          [intros x Hx; apply Huses, in_or_app; right; exact Hx | exact Hagree].
      + intros ? a_v _ [-> <-].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
        eapply gen_inline_sim_bind;
          [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? loaded_v _ [-> <-]].
        eapply gen_inline_sim_bind with
          (RA := fun ic' sv1 sv2 => ic' = IC_Synced stk e1 e2 /\ sv1 = sv2).
        * unfold denote_atomic_rmw_operation.
          destruct (a_operation armw);
            try (apply cfg_inline_sim_EOU; reflexivity);
            try (apply cfg_inline_sim_raise; reflexivity).
          -- apply gen_inline_sim_ret; split; reflexivity.
          -- destruct a_v as [db | |]; try (apply cfg_inline_sim_raise; reflexivity).
             destruct db; try (apply cfg_inline_sim_raise; reflexivity).
             apply cfg_inline_sim_EOU; reflexivity.
        * intros ? stored_v _ [-> <-].
          eapply gen_inline_sim_bind;
            [unfold store; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
          eapply gen_inline_sim_bind.
          -- apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                      (IC_Synced stk e1 e2)
                      (IC_Synced stk (Maps.add id loaded_v e1) e2)
                      (IC_Synced stk (Maps.add id loaded_v e1) (Maps.add id loaded_v e2))
                      id id loaded_v Logic.eq_refl Logic.eq_refl).
          -- intros ? [] [] (-> & _ & _).
             apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
             eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
  Qed.

  Lemma denote_instr_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (va : option (@ptr PaV))
    (iid : instr_id) (ins : instr dtyp) (md : list (metadata dtyp))
    (Huses : forall x,
               In x (full_instr_uses ins ++ flat_map full_metadata_uses md) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_instr (iid, ins, md) va)
      (denote_instr (iid, ins, md) va).
  Proof.
    destruct ins as [s_cmt | op | [dt f] args anns obs | dt annotations
                     | dt [du ptr] anns | [dt val] [du ptr] anns
                     | cpx | armw | [t ptr_exp] argty | s_f1 s_f2 | lp_t lp_b lp_cs].
    - (* INSTR_Comment *)
      destruct iid as [id | vn]; cbn [denote_instr].
      + apply cfg_inline_sim_raise; reflexivity.
      + apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* INSTR_Op *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 None op);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? uv _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                   (IC_Synced stk e1 e2)
                   (IC_Synced stk (Maps.add id uv e1) e2)
                   (IC_Synced stk (Maps.add id uv e1) (Maps.add id uv e2))
                   id id uv Logic.eq_refl Logic.eq_refl).
        * intros ? [] [] (-> & _ & _).
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
    - (* INSTR_Call *)
      cbn [denote_instr].
      eapply gen_inline_sim_bind.
      + apply (denote_call_args_caller_sim opt_call1 g0 fresh_set stk e1 e2 args);
          [| exact Hagree].
        intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses].
        apply in_or_app; right; apply in_or_app; left; exact Hx.
      + intros ? vs _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_operand_bundles_caller_sim opt_call1 g0 fresh_set stk e1 e2 _ _ f obs);
            [| exact Hagree].
          intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses].
          apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hx.
        * intros ? [] _ (-> & _ & _).
          eapply gen_inline_sim_bind with
            (RA := fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2).
          -- destruct (intrinsic_exp f) as [s |].
             ++ unfold intrinsic, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity.
             ++ eapply gen_inline_sim_bind.
                ** apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 None f);
                     [| exact Hagree].
                   intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd].
                   apply in_or_app; left; exact Hx.
                ** intros ? fv _ [-> <-].
                   unfold call, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity.
          -- intros ? res _ [-> <-].
             eapply gen_inline_sim_bind;
               [apply cfg_inline_sim_check_call_return; reflexivity | intros ? res' _ [-> <-]].
             destruct res' as [ex | dv].
             ++ eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
                  [apply cfg_inline_sim_raiseLLVM; reflexivity | intros ? ? ? []].
             ++ eapply gen_inline_sim_obs_eq;
                  [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
                destruct iid as [id | vn].
                ** eapply gen_inline_sim_weaken;
                     [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                                 (IC_Synced stk e1 e2)
                                 (IC_Synced stk (Maps.add id dv e1) e2)
                                 (IC_Synced stk (Maps.add id dv e1) (Maps.add id dv e2))
                                 id id dv Logic.eq_refl Logic.eq_refl)].
                   intros ? [] [] (-> & _ & _).
                   split; [reflexivity | split; [reflexivity |]].
                   eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
                ** apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* INSTR_Alloca *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      destruct (find_option ann_num_elements annotations) as [[t num_exp] |] eqn:Eann.
      + eapply gen_inline_sim_bind.
        * eapply gen_inline_sim_bind.
          -- apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) num_exp);
               [| exact Hagree].
             intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses].
             eapply find_option_ann_num_elements_uses; eassumption.
          -- intros ? n _ [-> <-].
             destruct (dvalue_is_poison n).
             ++ apply cfg_inline_sim_raiseUB.
             ++ eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? n' _ [-> <-]].
                eapply gen_inline_sim_bind;
                  [unfold alloca; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? v _ [-> <-]].
                apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                         (IC_Synced stk e1 e2)
                         (IC_Synced stk (Maps.add id v e1) e2)
                         (IC_Synced stk (Maps.add id v e1) (Maps.add id v e2))
                         id id v Logic.eq_refl Logic.eq_refl).
        * intros ? [] [] (-> & _ & _).
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
      + eapply gen_inline_sim_bind.
        * eapply gen_inline_sim_bind;
            [unfold alloca; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? v _ [-> <-]].
          apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                   (IC_Synced stk e1 e2)
                   (IC_Synced stk (Maps.add id v e1) e2)
                   (IC_Synced stk (Maps.add id v e1) (Maps.add id v e2))
                   id id v Logic.eq_refl Logic.eq_refl).
        * intros ? [] [] (-> & _ & _).
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
    - (* INSTR_Load *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some du) ptr);
          [| exact Hagree].
        intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd].
        apply in_or_app; left; exact Hx.
      + intros ? a _ [-> <-].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
        eapply gen_inline_sim_bind;
          [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? v _ [-> <-]].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? v' _ [-> <-]].
        eapply gen_inline_sim_bind;
          [apply cfg_inline_sim_assert_load_deref; reflexivity | intros ? [] _ (-> & _ & _)].
        eapply gen_inline_sim_weaken;
          [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                      (IC_Synced stk e1 e2)
                      (IC_Synced stk (Maps.add id v' e1) e2)
                      (IC_Synced stk (Maps.add id v' e1) (Maps.add id v' e2))
                      id id v' Logic.eq_refl Logic.eq_refl)].
        intros ? [] [] (-> & _ & _).
        split; [reflexivity | split; [reflexivity |]].
        eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
    - (* INSTR_Store *)
      destruct iid as [id | vn]; cbn [denote_instr]; [apply cfg_inline_sim_raise; reflexivity |].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) val);
          [| exact Hagree].
        intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd].
        apply in_or_app; left; exact Hx.
      + intros ? v _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some du) ptr);
            [| exact Hagree].
          intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd].
          apply in_or_app; right; apply in_or_app; left; exact Hx.
        * intros ? a _ [-> <-].
          eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
          eapply gen_inline_sim_bind.
          -- destruct a as [db | |];
               try (unfold store; apply cfg_inline_sim_trigger_refl; reflexivity).
             destruct db;
               try (unfold store; apply cfg_inline_sim_trigger_refl; reflexivity).
             apply cfg_inline_sim_raiseUB.
          -- intros ? [] _ [-> _]; apply gen_inline_sim_ret.
             split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* INSTR_AtomicCmpXchg *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      apply denote_cmpxchg_caller_sim; [| exact Hagree].
      intros x Hx; apply Huses, in_or_app; left; exact Hx.
    - (* INSTR_AtomicRMW *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      apply denote_atomicrmw_caller_sim; [| exact Hagree].
      intros x Hx; apply Huses, in_or_app; left; exact Hx.
    - (* INSTR_VAArg *)
      cbn [denote_instr].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2
                 (Some (DTYPE_Base DTYPE_Pointer)) ptr_exp);
          [| exact Hagree].
        intros x Hx; apply Huses, in_or_app; left; exact Hx.
      + intros ? ptr_to_args _ [-> <-].
        eapply gen_inline_sim_bind;
          [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? args_p _ [-> <-]].
        eapply gen_inline_sim_bind;
          [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? retv _ [-> <-]].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? ix _ [-> <-]].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? args' _ [-> <-]].
        eapply gen_inline_sim_bind;
          [unfold store; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
        destruct iid as [id | vn].
        * eapply gen_inline_sim_weaken;
            [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                        (IC_Synced stk e1 e2)
                        (IC_Synced stk (Maps.add id retv e1) e2)
                        (IC_Synced stk (Maps.add id retv e1) (Maps.add id retv e2))
                        id id retv Logic.eq_refl Logic.eq_refl)].
          intros ? [] [] (-> & _ & _).
          split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
        * apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* INSTR_Fence *)
      cbn [denote_instr].
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* INSTR_LandingPad *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      eapply gen_inline_sim_bind;
        [unfold stack_get_exc, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity
        | intros ? oe _ [-> <-]].
      destruct oe as [ex |]; [| apply cfg_inline_sim_raise; reflexivity].
      eapply gen_inline_sim_weaken;
        [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                    (IC_Synced stk e1 e2)
                    (IC_Synced stk (Maps.add id ex e1) e2)
                    (IC_Synced stk (Maps.add id ex e1) (Maps.add id ex e2))
                    id id ex Logic.eq_refl Logic.eq_refl)].
      intros ? [] [] (-> & _ & _).
      split; [reflexivity | split; [reflexivity |]].
      eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
  Qed.

  Lemma denote_code_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (va : option (@ptr PaV)) :
    forall (cd : code dtyp) (e1 e2 : @local_env PaV),
      (forall x,
         In x (flat_map (fun '(_, i, mds) => full_instr_uses i ++ flat_map full_metadata_uses mds) cd) ->
         ~ In x fresh_set) ->
      env_agree_outside fresh_set e1 e2 ->
      cfg_inline_sim opt_call1 g0 false
        (fun ic' r1 r2 =>
           r1 = tt /\ r2 = tt /\
           exists e1' e2',
             ic' = IC_Synced stk e1' e2' /\
             env_agree_outside fresh_set e1' e2')
        (IC_Synced stk e1 e2)
        (denote_code cd va)
        (denote_code cd va).
  Proof.
    induction cd as [| [[iid ins] md] rest IH]; intros e1 e2 Huses Hagree;
      cbn [denote_code loop_monad flat_map] in *.
    - apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - eapply gen_inline_sim_bind.
      + apply (denote_instr_caller_sim opt_call1 g0 fresh_set stk e1 e2 va iid ins md);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? [] [] (_ & _ & e1' & e2' & -> & Hagree').
        apply IH; [intros x Hx; apply Huses, in_or_app; right; exact Hx | exact Hagree'].
  Qed.

  Lemma denote_phis_sync_writes_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk :
    forall (dvs : list (local_id * @dvalue PaV)) (e1 e2 : @local_env PaV),
      env_agree_outside fresh_set e1 e2 ->
      cfg_inline_sim opt_call1 g0 false
        (fun ic' _ _ =>
           exists e1' e2',
             ic' = IC_Synced stk e1' e2' /\
             env_agree_outside fresh_set e1' e2')
        (IC_Synced stk e1 e2)
        (map_monad (fun '(id, dv) => lwrite id dv) dvs)
        (map_monad (fun '(id, dv) => lwrite id dv) dvs).
  Proof.
    induction dvs as [| [id dv] rest IH]; intros e1 e2 Hagree; cbn [map_monad].
    - apply gen_inline_sim_ret; exists e1, e2; auto.
    - eapply gen_inline_sim_bind.
      + apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                 (IC_Synced stk e1 e2)
                 (IC_Synced stk (Maps.add id dv e1) e2)
                 (IC_Synced stk (Maps.add id dv e1) (Maps.add id dv e2))
                 id id dv Logic.eq_refl Logic.eq_refl).
      + intros ? [] [] (-> & _ & _).
        eapply gen_inline_sim_bind.
        * apply IH, env_agree_outside_add_both, Hagree.
        * intros ? _ _ (e1' & e2' & -> & Hag'); apply gen_inline_sim_ret; exists e1', e2'; auto.
  Qed.

  Lemma denote_phis_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    (call_bid post_bid b_from1 b_from2 : block_id)
    stk (e1 e2 : @local_env PaV)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (Huses : forall x,
               In x (flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) phis) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2)
    (Hentry_or_remap :
       phis = [] \/
       (call_bid <> post_bid /\
        b_from1 <> post_bid /\
        b_from2 = remap_pred_id call_bid post_bid b_from1 /\
        ~ In post_bid (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) phis))) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_phis b_from1 phis)
      (denote_phis b_from2 (remap_phis_pred call_bid post_bid phis)).
  Proof.
    destruct Hentry_or_remap as [-> | (Hne_cp & Hne_fp & -> & Hnin_pb)].
    - cbn [remap_phis_pred List.map denote_phis map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      eapply gen_inline_sim_obs_eq;
        [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
        | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - unfold denote_phis.
      assert (Heval :
        forall ps,
          (forall x,
             In x (flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) ps) ->
             ~ In x fresh_set) ->
          ~ In post_bid (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) ps) ->
          cfg_inline_sim opt_call1 g0 false
            (fun ic' dvs1 dvs2 => ic' = IC_Synced stk e1 e2 /\ dvs1 = dvs2)
            (IC_Synced stk e1 e2)
            (map_monad (denote_phi b_from1) ps)
            (map_monad (denote_phi (remap_pred_id call_bid post_bid b_from1))
               (remap_phis_pred call_bid post_bid ps))).
      { induction ps as [| [[x [fm dt pargs]] md] rest IH]; intros Hu Hpb;
          cbn [remap_phis_pred List.map map_monad flat_map] in *.
        - apply gen_inline_sim_ret; split; reflexivity.
        - assert (Hpargs_pb : ~ In post_bid (List.map fst pargs)).
          { intros Hin; apply Hpb, in_or_app; left; exact Hin. }
          eapply gen_inline_sim_bind.
          + cbn [denote_phi].
            rewrite (assoc_remap_pred_id call_bid post_bid b_from1 pargs Hne_cp Hne_fp Hpargs_pb).
            destruct (assoc b_from1 pargs) as [op |] eqn:Eop;
              [| apply cfg_inline_sim_raise; reflexivity].
            pose proof (assoc_some_in _ _ _ Eop) as Hop_in.
            eapply gen_inline_sim_bind.
            * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) op);
                [| exact Hagree].
              intros z Hz; apply Hu, in_or_app; left; apply in_or_app; left; cbn [full_phi_uses].
              apply in_flat_map; exists (b_from1, op); split; assumption.
            * intros ? uv _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
          + intros ? p1 _ [-> <-].
            eapply gen_inline_sim_bind.
            * apply IH;
                [intros z Hz; apply Hu, in_or_app; right; exact Hz
                | intros Hin; apply Hpb, in_or_app; right; exact Hin].
            * intros ? dvs1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
      eapply gen_inline_sim_bind; [apply (Heval phis Huses Hnin_pb) |].
      intros ? dvs _ [-> <-].
      eapply gen_inline_sim_bind;
        [apply (denote_phis_sync_writes_sim opt_call1 g0 fresh_set stk dvs e1 e2 Hagree) |].
      intros ? _ _ (e1' & e2' & -> & Hag').
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1', e2'; auto]].
  Qed.

  Lemma denote_phis_sync_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    (b_from : block_id)
    stk (e1 e2 : @local_env PaV)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (Huses : forall x,
               In x (flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) phis) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_phis b_from phis)
      (denote_phis b_from phis).
  Proof.
    unfold denote_phis.
    assert (Heval :
      forall ps,
        (forall x,
           In x (flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) ps) ->
           ~ In x fresh_set) ->
        cfg_inline_sim opt_call1 g0 false
          (fun ic' dvs1 dvs2 => ic' = IC_Synced stk e1 e2 /\ dvs1 = dvs2)
          (IC_Synced stk e1 e2)
          (map_monad (denote_phi b_from) ps)
          (map_monad (denote_phi b_from) ps)).
    { induction ps as [| [[x [fm dt pargs]] md] rest IH]; intros Hu;
        cbn [map_monad flat_map] in *.
      - apply gen_inline_sim_ret; split; reflexivity.
      - eapply gen_inline_sim_bind.
        + cbn [denote_phi].
          destruct (assoc b_from pargs) as [op |] eqn:Eop;
            [| apply cfg_inline_sim_raise; reflexivity].
          pose proof (assoc_some_in _ _ _ Eop) as Hop_in.
          eapply gen_inline_sim_bind.
          * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) op);
              [| exact Hagree].
            intros z Hz; apply Hu, in_or_app; left; apply in_or_app; left; cbn [full_phi_uses].
            apply in_flat_map; exists (b_from, op); split; assumption.
          * intros ? uv _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
        + intros ? p1 _ [-> <-].
          eapply gen_inline_sim_bind.
          * apply IH; intros z Hz; apply Hu, in_or_app; right; exact Hz.
          * intros ? dvs1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
    eapply gen_inline_sim_bind; [apply (Heval phis Huses) |].
    intros ? dvs _ [-> <-].
    eapply gen_inline_sim_bind;
      [apply (denote_phis_sync_writes_sim opt_call1 g0 fresh_set stk dvs e1 e2 Hagree) |].
    intros ? _ _ (e1' & e2' & -> & Hag').
    apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1', e2'; auto]].
  Qed.

  Lemma denote_terminator_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (tiid : instr_id) (tm : terminator dtyp) (tmd : list (metadata dtyp))
    (Huses : forall x,
               In x (full_term_uses tm ++ flat_map full_metadata_uses tmd) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' bd1 bd2 =>
         bd1 = bd2 /\
         (forall succ_bid, bd1 = inl succ_bid -> In succ_bid (term_succ_bids tm)) /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_terminator (tiid, tm, tmd))
      (denote_terminator (tiid, tm, tmd)).
  Proof.
    destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt ex] def_b dests
                    | [t addr] brs fn | [t expr]
                    | [dt fnptrval] args to_lbl unwind_lbl anns obs | ];
      cbn [denote_terminator].
    - (* TERM_Ret *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) op);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? dv _ [-> <-]; apply gen_inline_sim_ret.
        split; [reflexivity | split; [intros ?; discriminate | exists e1, e2; auto]].
    - (* TERM_Ret_void *)
      apply gen_inline_sim_ret.
      split; [reflexivity | split; [intros ?; discriminate | exists e1, e2; auto]].
    - (* TERM_Br *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) op);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? v _ [-> <-].
        destruct v as [db | |]; try (apply cfg_inline_sim_raise; reflexivity).
        destruct db; try (apply cfg_inline_sim_raise; reflexivity).
        * destruct sz as [? | ? |]; try (apply cfg_inline_sim_raise; reflexivity).
          destruct (equ x one).
          -- apply gen_inline_sim_ret.
             split; [reflexivity | split; [intros ? H; injection H as <-; left; reflexivity | exists e1, e2; auto]].
          -- apply gen_inline_sim_ret.
             split; [reflexivity | split; [intros ? H; injection H as <-; right; left; reflexivity | exists e1, e2; auto]].
        * apply cfg_inline_sim_raiseUB.
    - (* TERM_Br_1 *)
      apply gen_inline_sim_ret.
      split; [reflexivity | split; [intros ? H; injection H as <-; left; reflexivity | exists e1, e2; auto]].
    - (* TERM_Switch *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) ex);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? sel _ [-> <-].
        destruct (dvalue_is_poison sel); [apply cfg_inline_sim_raiseUB |].
        destruct (switch_elab_ren_b (fun b => b) sel def_b dests)
          as [(eou_err & Hnr & E1 & _) | (b & Hb & E1 & _)].
        * rewrite E1.
          destruct eou_err as [m | m | m | b0];
            [| | | exfalso; exact (Hnr b0 Logic.eq_refl)];
            cbn [EOU_to_itree].
          -- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
               [apply cfg_inline_sim_raiseOOM | intros ? ? ? []].
          -- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
               [apply cfg_inline_sim_raiseUB | intros ? ? ? []].
          -- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
               [apply cfg_inline_sim_raise; reflexivity | intros ? ? ? []].
        * rewrite E1; cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
          eapply gen_inline_sim_obs_eq;
            [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
          apply gen_inline_sim_ret.
          split; [reflexivity | split; [intros ? H; injection H as <-; exact Hb | exists e1, e2; auto]].
    - (* TERM_IndirectBr *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) addr);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? a _ [-> <-].
        destruct (dvalue_is_poison a); [apply cfg_inline_sim_raiseUB |].
        destruct fn as [f |]; [| apply cfg_inline_sim_raise; reflexivity].
        assert (Haddrs :
          forall bs,
            cfg_inline_sim opt_call1 g0 false
              (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
              (IC_Synced stk e1 e2)
              (map_monad (fun b => ba <- gread (blockaddress_id f b) ;; ret (dvalue_ptr_address ba)) bs)
              (map_monad (fun b => ba <- gread (blockaddress_id f b) ;; ret (dvalue_ptr_address ba)) bs)).
        { induction bs as [| b0 rest IH]; cbn [map_monad].
          - apply gen_inline_sim_ret; split; reflexivity.
          - eapply gen_inline_sim_bind.
            + eapply gen_inline_sim_bind.
              * unfold gread, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity.
              * intros ? ba _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
            + intros ? oa _ [-> <-].
              eapply gen_inline_sim_bind; [exact IH | intros ? oas _ [-> <-]].
              apply gen_inline_sim_ret; split; reflexivity. }
        eapply gen_inline_sim_bind; [apply (Haddrs brs) | intros ? addrs _ [-> <-]].
        destruct (dvalue_ptr_address a) as [z |]; [| apply cfg_inline_sim_raise; reflexivity].
        destruct (indirectbr_target z (combine brs addrs)) as [b |] eqn:Eib;
          [| apply cfg_inline_sim_raiseUB].
        pose proof (indirectbr_target_In z brs addrs b Eib) as Hb_in.
        apply gen_inline_sim_ret.
        split; [reflexivity | split; [intros ? H; injection H as <-; exact Hb_in | exists e1, e2; auto]].
    - (* TERM_Resume *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) expr);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? exn _ [-> <-]; apply cfg_inline_sim_raiseLLVM; reflexivity.
    - (* TERM_Invoke *)
      eapply gen_inline_sim_bind.
      + apply (denote_call_args_caller_sim opt_call1 g0 fresh_set stk e1 e2 args);
          [| exact Hagree].
        intros x Hx; apply Huses, in_or_app; left; cbn [full_term_uses].
        apply in_or_app; right; apply in_or_app; left; exact Hx.
      + intros ? uvs _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_operand_bundles_caller_sim opt_call1 g0 fresh_set stk e1 e2 _ _ fnptrval obs);
            [| exact Hagree].
          intros x Hx; apply Huses, in_or_app; left; cbn [full_term_uses].
          apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hx.
        * intros ? [] _ (-> & _ & _).
          eapply gen_inline_sim_bind.
          -- apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 None fnptrval);
               [| exact Hagree].
             intros x Hx; apply Huses, in_or_app; left; cbn [full_term_uses full_texp_uses snd].
             apply in_or_app; left; exact Hx.
          -- intros ? fv _ [-> <-].
             eapply gen_inline_sim_bind;
               [unfold call, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity
               | intros ? rv _ [-> <-]].
             eapply gen_inline_sim_bind;
               [apply cfg_inline_sim_check_call_return; reflexivity
               | intros ? rv' _ [-> <-]].
             destruct rv' as [exn | ret_v].
             ++ eapply gen_inline_sim_bind;
                  [unfold stack_raise, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity
                  | intros ? [] _ [-> _]].
                apply gen_inline_sim_ret.
                split; [reflexivity | split;
                  [intros ? H; injection H as <-; right; left; reflexivity | exists e1, e2; auto]].
             ++ destruct tiid as [id | vn].
                ** eapply gen_inline_sim_bind.
                   --- apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                                (IC_Synced stk e1 e2)
                                (IC_Synced stk (Maps.add id ret_v e1) e2)
                                (IC_Synced stk (Maps.add id ret_v e1) (Maps.add id ret_v e2))
                                id id ret_v Logic.eq_refl Logic.eq_refl).
                   --- intros ? [] [] (-> & _ & _); apply gen_inline_sim_ret.
                       split; [reflexivity | split;
                         [intros ? H; injection H as <-; left; reflexivity
                         | eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree]]].
                ** eapply gen_inline_sim_obs_eq;
                     [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
                   apply gen_inline_sim_ret.
                   split; [reflexivity | split;
                     [intros ? H; injection H as <-; left; reflexivity | exists e1, e2; auto]].
    - (* TERM_Unreachable *)
      apply cfg_inline_sim_raiseUB.
  Qed.

  Lemma cfg_inline_sim_iter_sync
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    (fresh_set : list raw_id)
    stk
    {I1 I2 R1 R2 : Type}
    (RI : I1 -> I2 -> Prop)
    (RR : R1 -> R2 -> Prop)
    (step1 : I1 -> @CFGtop PaV (I1 + R1))
    (step2 : I2 -> @CFGtop PaV (I2 + R2))
    (Hstep :
       forall i1 i2 (e1 e2 : @local_env PaV),
         RI i1 i2 ->
         env_agree_outside fresh_set e1 e2 ->
         cfg_inline_sim opt_call1 g0 false
           (fun ic' lr1 lr2 =>
              exists e1' e2',
                ic' = IC_Synced stk e1' e2' /\
                env_agree_outside fresh_set e1' e2' /\
                match lr1, lr2 with
                | inl next1, inl next2 => RI next1 next2
                | inr r1, inr r2 => RR r1 r2
                | _, _ => False
                end)
           (IC_Synced stk e1 e2)
           (step1 i1) (step2 i2)) :
    forall i1 i2 (e1 e2 : @local_env PaV),
      RI i1 i2 ->
      env_agree_outside fresh_set e1 e2 ->
      cfg_inline_sim opt_call1 g0 bf
        (fun ic' r1 r2 =>
           exists e1' e2',
             ic' = IC_Synced stk e1' e2' /\
             env_agree_outside fresh_set e1' e2' /\
             RR r1 r2)
        (IC_Synced stk e1 e2)
        (ITree.iter step1 i1)
        (ITree.iter step2 i2).
  Proof.
    set (step_rel :=
      fun ic' (lr1 : I1 + R1) (lr2 : I2 + R2) =>
        exists e1' e2',
          ic' = IC_Synced stk e1' e2' /\
          env_agree_outside fresh_set e1' e2' /\
          match lr1, lr2 with
          | inl next1, inl next2 => RI next1 next2
          | inr r1, inr r2 => RR r1 r2
          | _, _ => False
          end).
    set (out_rel :=
      fun ic' (r1 : R1) (r2 : R2) =>
        exists e1' e2',
          ic' = IC_Synced stk e1' e2' /\
          env_agree_outside fresh_set e1' e2' /\
          RR r1 r2).
    set (iter_k1 :=
      fun lr : I1 + R1 =>
        match lr with
        | inl j => Tau (ITree.iter step1 j)
        | inr v => Ret v
        end).
    set (iter_k2 :=
      fun lr : I2 + R2 =>
        match lr with
        | inl j => Tau (ITree.iter step2 j)
        | inr v => Ret v
        end).
    set (r_iter :=
      fun ic0 (a1 : @CFGtop PaV R1) (a2 : @CFGtop PaV R2) =>
        is_ic_synced ic0 = true /\
        exists u1 u2,
          a1 = ITree.bind u1 iter_k1 /\
          a2 = ITree.bind u2 iter_k2 /\
          cfg_inline_sim opt_call1 g0 false step_rel ic0 u1 u2).
    assert (Hlift_cont :
      forall ic0 w1 w2,
        is_ic_synced ic0 = true ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false step_rel) bot3)
          ic0 w1 w2 ->
        gis_cont r_iter ic0 (ITree.bind w1 iter_k1) (ITree.bind w2 iter_k2)).
    { intros ic0 w1 w2 Hic0 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (ITree.bind m1 iter_k1), (ITree.bind m2 iter_k2).
      split; [apply itree_tau_star_bind, Hs1 |].
      split; [apply itree_tau_star_bind, Hs2 |].
      split; [exact Hic0 | exists m1, m2; auto]. }
    assert (Hone :
      forall ic0 u1 u2,
        is_ic_synced ic0 = true ->
        cfg_inline_sim opt_call1 g0 false step_rel ic0 u1 u2 ->
        gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
          (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
          opt_call1 g0 bf out_rel r_iter
          ic0 (ITree.bind u1 iter_k1) (ITree.bind u2 iter_k2)).
    { intros ic0 u1 u2 Hic0 Hu; punfold Hu.
      revert Hic0;
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
        try discriminate Hfr; intros Hic0.
      - unfold gis_step_body in Hst.
        destruct (observe u1) as [lr1 | m1 | X1 ev1 k1] eqn:Hou1.
        + destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hst as (e1' & e2' & -> & Hag' & Hlr).
          destruct lr1 as [next1 | r1], lr2 as [next2 | r2]; try contradiction.
          * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2; cbn [observe iter_k1 iter_k2].
            exists (ITree.bind (step1 next1) iter_k1), (ITree.bind (step2 next2) iter_k2).
            split; [eapply ITS_Eq; [apply unfold_iter | apply ITS_Refl] |].
            split; [eapply ITS_Eq; [apply unfold_iter | apply ITS_Refl] |].
            split; [reflexivity | exists (step1 next1), (step2 next2); split; [reflexivity | split; [reflexivity |]]].
            apply (Hstep next1 next2 e1' e2' Hlr Hag').
          * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2; cbn [observe iter_k1 iter_k2].
            exists e1', e2'; auto.
        + destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2.
          apply (Hlift_cont ic0 m1 m2 Hic0 Hst).
        + apply GIS_Step; unfold gis_step_body; rewrite (observe_bind u1 iter_k1), Hou1.
          destruct Hst as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          rewrite (observe_bind u2 iter_k2), Hou2.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; apply (Hlift_cont ic0 _ _ Hic0 (HA a1 a2 Ha Hp)).
          * right; destruct ic0 as [stk0 env1 env2 | |]; try discriminate Hic0.
            destruct Hls as [Hloc | [Hfr_s _]]; [| discriminate Hfr_s].
            left; destruct (as_local_cfg ev1) as [le1 |], (as_local_cfg ev2) as [le2 |]; try contradiction.
            destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; apply (Hlift_cont _ _ _ Logic.eq_refl (Hrd v Hv)).
            -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
               apply (Hlift_cont _ _ _ Logic.eq_refl Hr).
      - eapply GIS_TauL; [rewrite (observe_bind u1 iter_k1), Hu1; reflexivity | apply IH, Hic0].
      - eapply GIS_TauR; [rewrite (observe_bind u2 iter_k2), Hu2; reflexivity | apply IH, Hic0].
      - eapply GIS_ReadL; [exact He1 | rewrite Hu1, Eqit.bind_bind; reflexivity | exact Hlk | apply IH, Hic0].
      - eapply GIS_ReadR; [exact He2 | rewrite Hu2, Eqit.bind_bind; reflexivity | exact Hlk | apply IH, Hic0].
      - assert (Hic' : is_ic_synced ic' = true).
        { destruct ic0; try discriminate Hic0; cbn in Hw1; injection Hw1 as <-; reflexivity. }
        eapply GIS_WriteL; [exact Hw1 | rewrite Hu1, Eqit.bind_bind; reflexivity | apply IH, Hic'].
      - assert (Hic' : is_ic_synced ic' = true).
        { destruct ic0; try discriminate Hic0; cbn in Hw2; injection Hw2 as <-; reflexivity. }
        eapply GIS_WriteR; [exact Hw2 | rewrite Hu2, Eqit.bind_bind; reflexivity | apply IH, Hic'].
      - eapply GIS_GReadL; [rewrite Hu1, Eqit.bind_bind; reflexivity | exact Hlk | apply IH, Hic0].
      - discriminate Hic0. }
    assert (Hmain :
      forall ic0 t1 t2,
        r_iter ic0 t1 t2 ->
        cfg_inline_sim opt_call1 g0 bf out_rel ic0 t1 t2).
    { pcofix CIH.
      intros ic0 t1 t2 (Hic0 & u1 & u2 & -> & -> & Hu); pstep.
      eapply gen_inline_sim__mon with (r := r_iter);
        [apply Hone; assumption | intros ic1 a1 a2 Hr; right; apply CIH, Hr]. }
    intros i1 i2 e1 e2 Hi Hagree.
    eapply gen_inline_sim_obs_eq;
      [symmetry; apply unfold_iter | symmetry; apply unfold_iter |].
    apply Hmain; split; [reflexivity |].
    exists (step1 i1), (step2 i2); split; [reflexivity | split; [reflexivity | apply Hstep; assumption]].
  Qed.


  (** ** 10B. Single-Step [run_exc] Lifting, Unchanged Function & Caller Inlining Loop *)

  Lemma denote_exp'_global_eq (top : option dtyp) (gid : function_id) :
    @denote_exp' PaV top (EXP_Ident (ID_Global gid)) ≅
    ITree.trigger (GlobalRead gid).
  Proof using.
    unfold denote_exp'; cbn [denote_exp lookup_id]; unfold gread.
    change (@ITree.trigger (@GlobalE PaV) (@MCFGEtop PaV) _ (GlobalRead gid))
      with (@ITree.trigger (@MCFGEtop PaV) (@MCFGEtop PaV) _ (subevent _ (GlobalRead gid))).
    rewrite <- (Eqit.bind_ret_r (ITree.trigger (subevent _ (GlobalRead gid)))).
    rewrite (inl_withCall_bind_trigger (subevent _ (GlobalRead gid)) (fun x => Ret x)).
    change (@ITree.trigger (@MCFGEtop PaV) (@CFGEtop PaV) _ (subevent _ (GlobalRead gid)))
      with (@ITree.trigger (@GlobalE PaV) (@CFGEtop PaV) _ (GlobalRead gid)).
    rewrite <- (Eqit.bind_ret_r (ITree.trigger (GlobalRead gid))) at 2.
    apply eq_itree_clo_bind with (UU := Logic.eq);
      [reflexivity | intros x _ <-; apply inl_withCall_ret].
  Qed.

  Lemma denote_exp'_local_eq (top : option dtyp) (lid : local_id) :
    @denote_exp' PaV top (EXP_Ident (ID_Local lid)) ≅
    ITree.trigger (LocalRead lid).
  Proof using.
    unfold denote_exp'; cbn [denote_exp lookup_id]; unfold lread.
    change (@ITree.trigger (@LocalE PaV) (@MCFGEtop PaV) _ (LocalRead lid))
      with (@ITree.trigger (@MCFGEtop PaV) (@MCFGEtop PaV) _ (subevent _ (LocalRead lid))).
    rewrite <- (Eqit.bind_ret_r (ITree.trigger (subevent _ (LocalRead lid)))).
    rewrite (inl_withCall_bind_trigger (subevent _ (LocalRead lid)) (fun x => Ret x)).
    change (@ITree.trigger (@MCFGEtop PaV) (@CFGEtop PaV) _ (subevent _ (LocalRead lid)))
      with (@ITree.trigger (@LocalE PaV) (@CFGEtop PaV) _ (LocalRead lid)).
    rewrite <- (Eqit.bind_ret_r (ITree.trigger (LocalRead lid))) at 2.
    apply eq_itree_clo_bind with (UU := Logic.eq);
      [reflexivity | intros x _ <-; apply inl_withCall_ret].
  Qed.

  Definition finish_cfg (r : (block_id * block_id) + @dvalue PaV) : @CFGtop PaV (@dvalue PaV) :=
    match r with
    | inl bid => raise ("Can't find block in denote_cfg " ++ show (snd bid))%string
    | inr uv  => Ret uv
    end.

  Definition step_bd_cont (bks : ocfg dtyp) (va : option (@ptr PaV)) (src_bid : block_id)
    (bd : block_id + @dvalue PaV) : @CFGtop PaV (@dvalue PaV) :=
    match bd with
    | inr dv => Ret dv
    | inl bid_target =>
        Tau (ITree.bind (denote_ocfg_map (ocfg_map bks) va (src_bid, bid_target)) finish_cfg)
    end.

  Lemma ocfg_bind_finish_none_eq (bks : ocfg dtyp) (va : option (@ptr PaV))
    (b_from bid : block_id)
    (Hfb : find_block bks bid = None) :
    ITree.bind (denote_ocfg_map (ocfg_map bks) va (b_from, bid)) finish_cfg ≅
    raise ("Can't find block in denote_cfg " ++ show bid)%string.
  Proof using.
    rewrite denote_ocfg_map_unfold_eq, Hfb, Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma ocfg_bind_finish_some_eq (bks : ocfg dtyp) (va : option (@ptr PaV))
    (b_from bid : block_id) (bk : block dtyp)
    (Hfb : find_block bks bid = Some bk) :
    ITree.bind (denote_ocfg_map (ocfg_map bks) va (b_from, bid)) finish_cfg ≅
    ITree.bind (denote_block bk b_from va) (step_bd_cont bks va bid).
  Proof using.
    rewrite denote_ocfg_map_unfold_eq, Hfb, Eqit.bind_bind.
    apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [bid_target | dv] _ <-; cbn [step_bd_cont].
    - apply Eqit.bind_tau.
    - apply Eqit.bind_ret_l.
  Qed.

  Lemma denote_cfg_other_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (c : CFG.cfg dtyp) (va : option (@ptr PaV))
    stk (e1 e2 : @local_env PaV)
    (Hagree : env_agree_outside [] e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside [] e1' e2' /\
           r1 = r2)
      (IC_Synced stk e1 e2)
      (denote_cfg_map (ocfg_map (blks c)) c va)
      (denote_cfg_map (ocfg_map (blks c)) c va).
  Proof using.
    unfold denote_cfg_map.
    eapply gen_inline_sim_bind.
    - unfold denote_ocfg_map.
      apply (cfg_inline_sim_iter_sync opt_call1 g0 false [] stk Logic.eq Logic.eq);
        [| reflexivity | exact Hagree].
      intros [bid_from bid_src] ? ea1 ea2 <- Hag_i.
      destruct (RM.find bid_src (ocfg_map (blks c))) as [bk |].
      + unfold denote_block.
        eapply gen_inline_sim_bind.
        * apply (denote_phis_sync_sim opt_call1 g0 [] bid_from stk ea1 ea2 (blk_phis bk)
                   (fun _ _ H => H) Hag_i).
        * intros ? [] [] (_ & _ & e1_p & e2_p & -> & Hag_p).
          eapply gen_inline_sim_bind.
          -- apply (denote_code_caller_sim opt_call1 g0 [] stk va (blk_code bk) e1_p e2_p
                      (fun _ _ H => H) Hag_p).
          -- intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hag_c).
             destruct (blk_term bk) as [[tiid tm] tmd].
             eapply gen_inline_sim_bind.
             ++ apply (denote_terminator_caller_sim opt_call1 g0 [] stk e1_c e2_c tiid tm tmd
                         (fun _ _ H => H) Hag_c).
             ++ intros ? bd1 bd2 (<- & _ & e1_t & e2_t & -> & Hag_t).
                destruct bd1 as [bid_target | dv];
                  apply gen_inline_sim_ret; exists e1_t, e2_t; auto.
      + apply gen_inline_sim_ret; exists ea1, ea2; auto.
    - intros ? r1 r2 (e1' & e2' & -> & Hag' & <-).
      destruct r1 as [bid | uv].
      + apply cfg_inline_sim_raise; reflexivity.
      + apply gen_inline_sim_ret; exists e1', e2'; auto.
  Qed.

  Lemma denote_function_from_run_exc_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (Hproto : df_prototype df1 = df_prototype df2)
    (Hargs : df_args df1 = df_args df2)
    (Hrun :
       forall stk0 (e0 : @local_env PaV) (varg : @ptr PaV),
         cfg_inline_sim opt_call1 g0 true
           (fun ic' rv1 rv2 =>
              exists e1' e2',
                ic' = IC_Synced stk0 e1' e2' /\
                rv1 = rv2)
           (IC_Synced stk0 e0 e0)
           (run_exc (denote_cfg_map (ocfg_map (blks (df_instrs df1))) (df_instrs df1) (Some varg)))
           (run_exc (denote_cfg_map (ocfg_map (blks (df_instrs df2))) (df_instrs df2) (Some varg)))) :
    forall stk e1 e2 cc args,
      cfg_inline_sim opt_call1 g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
        (IC_Synced stk e1 e2)
        (denote_function df1 cc args)
        (denote_function df2 cc args).
  Proof using.
    intros stk e1 e2 cc args.
    unfold denote_function; rewrite <- Hproto.
    destruct (dc_param_attrs (df_prototype df1)) as [ret_attrs args_attrs].
    eapply gen_inline_sim_bind;
      [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
    eapply gen_inline_sim_bind;
      [apply cfg_inline_sim_apply_args_attrs; reflexivity | intros ? args' _ [-> <-]].
    eapply gen_inline_sim_bind.
    - unfold push_call_frame; rewrite <- Hargs.
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_EOU; reflexivity | intros ? [bs vs] _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_EOU; reflexivity | intros ? dts _ [-> <-]].
      eapply gen_inline_sim_bind;
        [unfold mem_push; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_stack_push_sync | intros ? [] [] (-> & _ & _)].
      eapply gen_inline_sim_bind;
        [unfold alloca; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? va1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [unfold store; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
      destruct va1 as [[varg | | | | | | |] | |];
        try (apply cfg_inline_sim_raise; reflexivity).
      apply gen_inline_sim_ret.
      split; [reflexivity | exists bs; split; reflexivity].
    - intros ? varg1 varg2 (-> & bs & -> & <-).
      eapply gen_inline_sim_bind.
      + apply (Hrun ((e1, e2) :: stk) (init_local_env bs) varg1).
      + intros ? rv1 rv2 (e1' & e2' & -> & <-).
        eapply gen_inline_sim_bind.
        * unfold pop_call_frame.
          eapply gen_inline_sim_bind;
            [apply cfg_inline_sim_stack_pop_sync | intros ? [] [] (-> & _ & _)].
          unfold mem_pop; apply cfg_inline_sim_trigger_refl; reflexivity.
        * intros ? [] _ [-> _].
          apply cfg_inline_sim_check_call_return; reflexivity.
  Qed.

  Lemma denote_function_other_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (df : definition dtyp (CFG.cfg dtyp)) :
    forall stk e1 e2 cc args,
      cfg_inline_sim opt_call1 g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
        (IC_Synced stk e1 e2)
        (denote_function df cc args)
        (denote_function df cc args).
  Proof using.
    apply (denote_function_from_run_exc_sim opt_call1 g0 df df Logic.eq_refl Logic.eq_refl).
    intros stk0 e0 varg.
    eapply (cfg_inline_sim_run_exc_both opt_call1 g0 true stk0);
      [| | exists e0, e0; reflexivity
       | apply denote_cfg_other_sim, env_agree_outside_refl].
    - intros e1' e2' ex; exists e1', e2'; auto.
    - intros ic' x1 x2 _ (e1' & e2' & -> & _ & <-); exists e1', e2'; auto.
  Qed.

  Lemma run_exc_bind_step_sync
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (stk : env_stack)
    {A1 A2 B1 B2 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RB : inline_ctx -> @exc PaV + B1 -> @exc PaV + B2 -> Prop)
    (r_co : inline_ctx -> @CFGtop PaV (@exc PaV + B1) -> @CFGtop PaV (@exc PaV + B2) -> Prop)
    (k1 : A1 -> @CFGtop PaV B1)
    (k2 : A2 -> @CFGtop PaV B2)
    (Hexc : forall e1 e2 ex, RB (IC_Synced stk e1 e2) (inl ex) (inl ex))
    (Hr_wrap :
       forall ic' m1 m2,
         ic_synced_stk stk ic' ->
         cfg_inline_sim opt_call1 g0 false RA ic' m1 m2 ->
         r_co ic' (run_exc (ITree.bind m1 k1)) (run_exc (ITree.bind m2 k2)))
    (Hret :
       forall ic' x1 x2,
         ic_synced_stk stk ic' ->
         RA ic' x1 x2 ->
         gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
           (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
           opt_call1 g0 bf RB r_co ic'
           (run_exc (k1 x1)) (run_exc (k2 x2))) :
    forall ic (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2),
      ic_synced_stk stk ic ->
      cfg_inline_sim opt_call1 g0 false RA ic a1 a2 ->
      gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
        (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
        opt_call1 g0 bf RB r_co ic
        (run_exc (ITree.bind a1 k1))
        (run_exc (ITree.bind a2 k2)).
  Proof using.
    intros ic a1 a2 Hic Hsim; punfold Hsim.
    assert (Hlift_sync_cont :
      forall ic0 u1 u2,
        ic_synced_stk stk ic0 ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false RA) bot3)
          ic0 u1 u2 ->
        gis_cont r_co ic0
          (Tau (run_exc (ITree.bind u1 k1)))
          (Tau (run_exc (ITree.bind u2 k2)))).
    { intros ic0 u1 u2 Hic0 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (run_exc (ITree.bind m1 k1)), (run_exc (ITree.bind m2 k2)).
      split; [apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
      split; [apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
      apply (Hr_wrap ic0 m1 m2 Hic0 Hm). }
    revert Hic;
      induction Hsim as [ic a1 a2 Hstep
                         | ic a1 ma1 a2 Ha1 _ IH
                         | ic a1 a2 ma2 Ha2 _ IH
                         | ic env1 a1 x v fa1 a2 He1 Ha1 Hlk _ IH
                         | ic env2 a1 a2 x v fa2 He2 Ha2 Hlk _ IH
                         | ic ic' a1 x v fa1 a2 Hw1 Ha1 _ IH
                         | ic ic' a1 a2 x v fa2 Hw2 Ha2 _ IH
                         | ic a1 k v fa1 a2 Ha1 Hlk _ IH
                         | stk0 ce1 e1 e2 a1 varg fa1 a2 Ha1 _ IH
                         | stk0 e1 e2 a1 fa1 a2 Hfr
                         | stk0 ce1 e2 bs a1 fa1 a2 Hfr
                         | stk0 ce1 e1 e2 a1 fa1 a2 Hfr
                         | stk0 ce1 e2 a1 fa1 a2 Hfr
                         | stk0 e1 e2 a1 X ce body1 fa1 a2 Hfr];
      try discriminate Hfr; intros Hic.
    - unfold gis_step_body in Hstep.
      destruct (observe a1) as [x1 | ma1 | X1 e1 fa1] eqn:Hoa1.
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        assert (Eb1 : run_exc (ITree.bind a1 k1) ≅ run_exc (k1 x1)).
        { apply run_exc_proper; rewrite (itree_eta a1), Hoa1, Eqit.bind_ret_l; reflexivity. }
        assert (Eb2 : run_exc (ITree.bind a2 k2) ≅ run_exc (k2 x2)).
        { apply run_exc_proper; rewrite (itree_eta a2), Hoa2, Eqit.bind_ret_l; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; exact Eb1 | symmetry; exact Eb2 | apply (Hret ic x1 x2 Hic Hstep)].
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        destruct Hstep as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
        assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
        { rewrite observe_bind, Hoa2; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; apply (run_exc_tau_eq _ _ Hou1)
          | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
        apply GIS_Step; cbn [gis_step_body observe].
        exists (run_exc (ITree.bind m1 k1)), (run_exc (ITree.bind m2 k2)).
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
        apply (Hr_wrap ic m1 m2 Hic Hm).
      + assert (Hou1 : observe (ITree.bind a1 k1) = VisF e1 (fun y => ITree.bind (fa1 y) k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        destruct Hstep as [Hub | Hvis].
        * pose proof (inl_is_ub_cfg_no_exc e1 Hub) as Hex1.
          eapply gen_inline_sim__obs_eq;
            [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1) | reflexivity |].
          apply GIS_Step; cbn [gis_step_body observe]; left; exact Hub.
        * destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
          assert (Hou2 : observe (ITree.bind a2 k2) = VisF e2 (fun y => ITree.bind (fa2 y) k2)).
          { rewrite observe_bind, Hoa2; reflexivity. }
          destruct Hic as (env1' & env2' & ->).
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | [Hfr_s _]]]; [| | discriminate Hfr_s].
          -- pose proof (EqE_CFG_exc_of_event e1 e2 HE) as Hex12.
             destruct (exc_of_event e1) as [ex |] eqn:Hex1.
             ++ symmetry in Hex12.
                eapply gen_inline_sim__obs_eq;
                  [symmetry; apply (run_exc_vis_some_eq _ _ _ _ Hou1 Hex1)
                  | symmetry; apply (run_exc_vis_some_eq _ _ _ _ Hou2 Hex12) |].
                apply GIS_Step; cbn [gis_step_body observe]; apply Hexc.
             ++ symmetry in Hex12.
                eapply gen_inline_sim__obs_eq;
                  [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1)
                  | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex12) |].
                apply GIS_Step; cbn [gis_step_body observe]; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros y1 y2 Hy Hp.
                apply (Hlift_sync_cont _ _ _ (ex_intro _ env1' (ex_intro _ env2' Logic.eq_refl))
                         (HA y1 y2 Hy Hp)).
          -- destruct (as_local_cfg e1) as [le1 |] eqn:Ele1,
                      (as_local_cfg e2) as [le2 |] eqn:Ele2; try contradiction.
             assert (Hex1 : exc_of_event e1 = None).
             { repeat (destruct e1 as [e1 | e1]); try discriminate Ele1; reflexivity. }
             assert (Hex2 : exc_of_event e2 = None).
             { repeat (destruct e2 as [e2 | e2]); try discriminate Ele2; reflexivity. }
             eapply gen_inline_sim__obs_eq;
               [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1)
               | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex2) |].
             apply GIS_Step; cbn [gis_step_body observe]; right; right; left.
             rewrite Ele1, Ele2.
             destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
             ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                intros v Hv.
                apply (Hlift_sync_cont _ _ _ (ex_intro _ env1' (ex_intro _ env2' Logic.eq_refl))
                         (Hrd v Hv)).
             ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                apply (Hlift_sync_cont _ _ _
                         (ex_intro _ (Maps.add x1 v1 env1') (ex_intro _ (Maps.add x2 v2 env2') Logic.eq_refl))
                         Hr).
    - assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
      { rewrite observe_bind, Ha1; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [symmetry; apply (run_exc_tau_eq _ _ Hou1) | reflexivity |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
      { rewrite observe_bind, Ha2; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [reflexivity | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (LocalRead x)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (LocalRead x))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalRead x))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ReadL; [exact He1 | exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Eb2 : ITree.bind a2 k2 ≅ ITree.bind (ITree.trigger (LocalRead x)) (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (LocalRead x))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalRead x))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa2 z) k2))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ReadR; [exact He2 | exact Er2 | exact Hlk |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Hic' : ic_synced_stk stk ic').
      { destruct Hic as (env1' & env2' & ->); cbn in Hw1; injection Hw1 as <-.
        eexists _, _; reflexivity. }
      assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (LocalWrite x v))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite x v))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_WriteL; [exact Hw1 | exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic'].
    - assert (Hic' : ic_synced_stk stk ic').
      { destruct Hic as (env1' & env2' & ->); cbn in Hw2; injection Hw2 as <-.
        eexists _, _; reflexivity. }
      assert (Eb2 : ITree.bind a2 k2 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (LocalWrite x v))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite x v))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa2 z) k2))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_WriteR; [exact Hw2 | exact Er2 |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic'].
    - assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (GlobalRead k)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (GlobalRead k))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (GlobalRead k))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_GReadL; [exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - destruct Hic as (? & ? & Hdisc); discriminate Hdisc.
  Qed.

  Lemma cfg_entry_has_no_phis_inv {T : Set} (c : CFG.cfg T) :
    cfg_entry_has_no_phis c = true ->
    exists b0, find_block (blks c) (init c) = Some b0 /\ blk_phis b0 = [].
  Proof using.
    unfold cfg_entry_has_no_phis.
    destruct (find_block (blks c) (init c)) as [b0 |]; [| discriminate].
    intros H; apply is_empty_list_spec in H; exists b0; auto.
  Qed.

  Lemma gen_inline_sim__run_exc_raise
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> @exc PaV + R1 -> @exc PaV + R2 -> Prop)
    (r_co : inline_ctx -> @CFGtop PaV (@exc PaV + R1) -> @CFGtop PaV (@exc PaV + R2) -> Prop)
    (ic : inline_ctx) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
      (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
      opt_call1 g0 bf RR r_co ic (run_exc (raise msg1)) (run_exc (raise msg2)).
  Proof using.
    unfold raise, trigger_cast, ITree.trigger.
    eapply gen_inline_sim__obs_eq;
      [symmetry; apply (run_exc_vis_none_eq _ (subevent _ (Failure msg1)) _
                          (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl)
      | symmetry; apply (run_exc_vis_none_eq _ (subevent _ (Failure msg2)) _
                          (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl) |].
    apply GIS_Step; cbn [gis_step_body observe]; right; left.
    split; [destruct ic; try discriminate Hact; reflexivity |].
    split; [exact I | intros [] [] _ _].
  Qed.

  Lemma run_exc_bind_step_inlined
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    {A1 A2 B1 B2 C1 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RC : inline_ctx -> C1 -> @exc PaV + B2 -> Prop)
    (r_co : inline_ctx -> @CFGtop PaV C1 -> @CFGtop PaV (@exc PaV + B2) -> Prop)
    (k1 : A1 -> @CFGtop PaV B1)
    (K1 : @exc PaV + B1 -> @CFGtop PaV C1)
    (k2 : A2 -> @CFGtop PaV B2)
    (Hr_wrap :
       forall ic' m1 m2,
         is_ic_inlined ic' = true ->
         cfg_inline_sim opt_call1 g0 false RA ic' m1 m2 ->
         r_co ic' (ITree.bind (run_exc (ITree.bind m1 k1)) K1) (run_exc (ITree.bind m2 k2)))
    (Hret :
       forall ic' x1 x2,
         is_ic_inlined ic' = true ->
         RA ic' x1 x2 ->
         gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
           (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
           opt_call1 g0 bf RC r_co ic'
           (ITree.bind (run_exc (k1 x1)) K1)
           (run_exc (k2 x2))) :
    forall ic (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2),
      is_ic_inlined ic = true ->
      cfg_inline_sim opt_call1 g0 false RA ic a1 a2 ->
      gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
        (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
        opt_call1 g0 bf RC r_co ic
        (ITree.bind (run_exc (ITree.bind a1 k1)) K1)
        (run_exc (ITree.bind a2 k2)).
  Proof using.
    intros ic a1 a2 Hic Hsim; punfold Hsim.
    revert Hic;
      induction Hsim as [ic a1 a2 Hstep
                         | ic a1 ma1 a2 Ha1 _ IH
                         | ic a1 a2 ma2 Ha2 _ IH
                         | ic env1 a1 x v fa1 a2 He1 Ha1 Hlk _ IH
                         | ic env2 a1 a2 x v fa2 He2 Ha2 Hlk _ IH
                         | ic ic' a1 x v fa1 a2 Hw1 Ha1 _ IH
                         | ic ic' a1 a2 x v fa2 Hw2 Ha2 _ IH
                         | ic a1 k v fa1 a2 Ha1 Hlk _ IH
                         | stk ce1 e1 e2 a1 varg fa1 a2 Ha1 _ IH
                         | stk e1 e2 a1 fa1 a2 Hfr
                         | stk ce1 e2 bs a1 fa1 a2 Hfr
                         | stk ce1 e1 e2 a1 fa1 a2 Hfr
                         | stk ce1 e2 a1 fa1 a2 Hfr
                         | stk e1 e2 a1 X ce body1 fa1 a2 Hfr];
      try discriminate Hfr; intros Hic.
    - unfold gis_step_body in Hstep.
      destruct (observe a1) as [x1 | ma1 | X1 e1 fa1] eqn:Hoa1.
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        assert (Eb1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅ ITree.bind (run_exc (k1 x1)) K1).
        { apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
          apply run_exc_proper; rewrite (itree_eta a1), Hoa1, Eqit.bind_ret_l; reflexivity. }
        assert (Eb2 : run_exc (ITree.bind a2 k2) ≅ run_exc (k2 x2)).
        { apply run_exc_proper; rewrite (itree_eta a2), Hoa2, Eqit.bind_ret_l; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; exact Eb1 | symmetry; exact Eb2 | apply (Hret ic x1 x2 Hic Hstep)].
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        destruct Hstep as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
        assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
        { rewrite observe_bind, Hoa2; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; rewrite (run_exc_tau_eq _ _ Hou1), Eqit.bind_tau; reflexivity
          | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
        apply GIS_Step; cbn [gis_step_body observe].
        exists (ITree.bind (run_exc (ITree.bind m1 k1)) K1),
               (run_exc (ITree.bind m2 k2)).
        split; [apply itree_tau_star_bind, itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
        apply (Hr_wrap ic m1 m2 Hic Hm).
      + assert (Hou1 : observe (ITree.bind a1 k1) = VisF e1 (fun y => ITree.bind (fa1 y) k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        destruct Hstep as [Hub | Hvis].
        * pose proof (inl_is_ub_cfg_no_exc e1 Hub) as Hex1.
          eapply gen_inline_sim__obs_eq;
            [symmetry; rewrite (run_exc_vis_none_eq _ _ _ Hou1 Hex1), Eqit.bind_vis; reflexivity
            | reflexivity |].
          apply GIS_Step; cbn [gis_step_body observe]; left; exact Hub.
        * destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
          destruct ic as [| | stk ce1 e1_env e2_env]; try discriminate Hic.
          destruct Hvis as [(Hsync & HE & HA) | []].
          pose proof (inl_sync_cfg_inlined_no_exc stk ce1 e1_env e2_env e1 Hsync) as Hex1.
          pose proof (EqE_CFG_exc_of_event e1 e2 HE) as Hex12.
          assert (Hex2 : exc_of_event e2 = None) by congruence.
          assert (Hou2 : observe (ITree.bind a2 k2) = VisF e2 (fun y => ITree.bind (fa2 y) k2)).
          { rewrite observe_bind, Hoa2; reflexivity. }
          eapply gen_inline_sim__obs_eq;
            [symmetry; rewrite (run_exc_vis_none_eq _ _ _ Hou1 Hex1), Eqit.bind_vis; reflexivity
            | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex2) |].
          apply GIS_Step; cbn [gis_step_body observe]; right; left.
          split; [exact Hsync | split; [exact HE |]].
          intros y1 y2 Hy Hp.
          destruct (HA y1 y2 Hy Hp) as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
          exists (ITree.bind (run_exc (ITree.bind m1 k1)) K1),
                 (run_exc (ITree.bind m2 k2)).
          split.
          -- eapply ITS_Eq; [apply Eqit.bind_tau |].
             apply ITS_Tau, itree_tau_star_bind, itree_tau_star_run_exc, itree_tau_star_bind, Hs1.
          -- split.
             ++ apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs2.
             ++ apply (Hr_wrap _ m1 m2 Logic.eq_refl Hm).
    - assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
      { rewrite observe_bind, Ha1; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [symmetry; rewrite (run_exc_tau_eq _ _ Hou1), Eqit.bind_tau; reflexivity
        | reflexivity |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
      { rewrite observe_bind, Ha2; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [reflexivity | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (LocalRead x)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (LocalRead x))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalRead x))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite Eqit.bind_vis, <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; apply eqit_Tau.
        apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        apply run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ReadL; [exact He1 | exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Eb2 : ITree.bind a2 k2 ≅ ITree.bind (ITree.trigger (LocalRead x)) (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (LocalRead x))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalRead x))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa2 z) k2))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ReadR; [exact He2 | exact Er2 | exact Hlk |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Hic' : is_ic_inlined ic' = true).
      { destruct ic; try discriminate Hic; cbn in Hw1; injection Hw1 as <-; reflexivity. }
      assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (LocalWrite x v))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite x v))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite Eqit.bind_vis, <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; apply eqit_Tau.
        apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        apply run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_WriteL; [exact Hw1 | exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic'].
    - assert (Hic' : is_ic_inlined ic' = true).
      { destruct ic; try discriminate Hic; cbn in Hw2; injection Hw2 as <-; reflexivity. }
      assert (Eb2 : ITree.bind a2 k2 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (LocalWrite x v))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite x v))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa2 z) k2))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_WriteR; [exact Hw2 | exact Er2 |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic'].
    - assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (GlobalRead k)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (GlobalRead k))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ (GlobalRead k))
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite Eqit.bind_vis, <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; apply eqit_Tau.
        apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        apply run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_GReadL; [exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - set (ze := Store (DTYPE_Struct true []) (DVALUE_Base (DVALUE_Pointer varg)) (DVALUE_Struct true [])).
      assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger ze) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger ze)
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite (run_exc_vis_none_eq _ (subevent _ ze)
                   (fun y => ITree.bind (Ret y) (fun z => ITree.bind (fa1 z) k1))
                   (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
        rewrite Eqit.bind_vis, <- bind_trigger.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; apply eqit_Tau.
        apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        apply run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
      eapply GIS_ZeroStoreL; [exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Logic.eq_refl].
  Qed.

  (** *** 7-State Coinductive Invariant for Single-Call-Site Inlining *)

  Section CallerInlineLoop.
    Variable g0 : global_env.
    Variable p_callee : @ptr PaV.
    Variable caller_df callee_df : definition dtyp (CFG.cfg dtyp).
    Variable pre_blks post_blks : ocfg dtyp.
    Variable b_call : block dtyp.
    Variable pre_cd post_cd : code dtyp.
    Variable call_iid : instr_id.
    Variable call_md : list (metadata dtyp).
    Variable ret_dt : dtyp.
    Variable call_args : list (texp dtyp * list param_attr).
    Variable call_anns : list (annotation dtyp).
    Variable caller_va : option (@ptr PaV).
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

    Let tree_callee1 (b_from bid : block_id) (varg : @ptr PaV) : @CFGtop PaV (@dvalue PaV) :=
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
        (vs : list (@dvalue PaV)) (varg : @ptr PaV) :
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
        (vs : list (@dvalue PaV)) (varg : @ptr PaV) :
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
    | RC_CalleeStep (ce1 : @local_env PaV) (vs : list (@dvalue PaV)) (varg : @ptr PaV)
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
      unfold is_inlinable_caller in Hc1; fold caller_cfg in Hc1.
      apply andb_prop in Hc1 as [Hc1 _].
      apply andb_prop in Hc1 as [Hcaller_nd Hcaller_entry].
      apply nodup_raw_ids_spec in Hcaller_nd.

      pose proof Hcallee_ok as Hce.
      unfold is_inlinable_callee in Hce; fold callee_gid callee_cfg in Hce.
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
        split; [intros ->; exact (Hnaf Hpb_af) | intros Hbf; exact (Hnaf (Hbf_af b Hbf))]. }
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
          gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
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
              [symmetry; apply (run_exc_tau_eq _ _ Logic.eq_refl)
              | symmetry; apply (run_exc_tau_eq _ _ Logic.eq_refl) |].
            apply GIS_Step; cbn [gis_step_body observe].
            exists (run_exc (tree_at1 src1 succ_bid)),
                   (run_exc (tree_at2 src2 succ_bid)).
            split; [apply ITS_Refl | split; [apply ITS_Refl |]].
            destruct (Hsucc succ_bid Logic.eq_refl) as [Hs_post Hs_bf].
            apply RC_CallerAt; [exact Hag' | exact Hs_post | exact Hs_bf | right; split; assumption].
          + eapply gen_inline_sim__obs_eq;
              [symmetry; apply (run_exc_ret_eq _ _ Logic.eq_refl)
              | symmetry; apply (run_exc_ret_eq _ _ Logic.eq_refl) |].
            apply GIS_Step; cbn [gis_step_body observe]; exists e1', e2'; auto. }

      (* 2. [RC_CalleeStep]: step inlined callee block body to [RC_CalleeAt] or [RC_PostAt] *)
      assert (Hcallee_step :
        forall ce1 vs varg b_cur bk_cur rtmp_cur ic0 u1 u2,
          is_ic_inlined ic0 = true ->
          List.length vs = List.length (df_args callee_df) ->
          b_cur = blk_id bk_cur ->
          In (bk_cur, rtmp_cur) bk_rtmps ->
          cfg_inline_sim opt_c g0 false (callee_bd_rel bk_cur rtmp_cur ce1) ic0 u1 u2 ->
          gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
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
              [symmetry; rewrite (run_exc_tau_eq _ _ Logic.eq_refl), Eqit.bind_tau; reflexivity
              | symmetry; apply (run_exc_tau_eq _ _ Logic.eq_refl) |].
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
              ITree.bind (ITree.trigger StackPop)
                (fun _ =>
                   ITree.bind (ITree.trigger MemPop)
                     (fun _ => Tau (run_exc (call_after_ret_k1 vs (inr dv)))))).
            { rewrite (run_exc_ret_eq (Ret dv) dv Logic.eq_refl), Eqit.bind_ret_l.
              unfold callee_epilogue_k1, pop_call_frame, stack_pop, mem_pop.
              rewrite Eqit.bind_bind.
              apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
              rewrite Eqit.bind_bind.
              apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
              rewrite Hproto_rattrs.
              rewrite (check_call_return_safe_inr_eq _ _ _ _ Hproto_fattrs), Eqit.bind_ret_l.
              reflexivity. }
            eapply GIS_StackPopL; [reflexivity | exact El_pop |].
            eapply GIS_MemPopL; [reflexivity | reflexivity |].
            eapply gen_inline_sim__obs_eq;
              [reflexivity | symmetry; apply (run_exc_tau_eq _ _ Logic.eq_refl) |].
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
          gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller (IC_Inlined stk ce1 e1_c e2_c)
            (ITree.bind (run_exc (tree_callee1 b_from1 b_cur varg)) (callee_epilogue_k1 vs))
            (run_exc (tree_at2 b_from2 (ren_b b_cur)))).
      { intros b_from1 b_from2 b_cur d_in ce1 e1_c e2_c vs varg
          Hvs_len Hdin_dom Hd0_in Hbound Hagree (bk_cur & Hfb_cur & Hentry_or_pred).
        pose proof (find_block_has_id _ _ Hfb_cur) as Hbcur_id; symmetry in Hbcur_id.
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
          gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
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
        eapply GIS_ZeroStoreL; [reflexivity |].
        assert (Er_va :
          run_exc (ITree.bind (lwrite va_tmp_id dv_va)
                     (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg))))) ≅
          ITree.bind (ITree.trigger (LocalWrite va_tmp_id dv_va))
            (fun _ => Tau (run_exc (Tau (tree_at2 call_bid (ren_b (init callee_cfg))))))).
        { unfold lwrite.
          rewrite (run_exc_vis_none_eq _ (subevent _ (LocalWrite va_tmp_id dv_va))
                     (fun y => ITree.bind (Ret y) (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg)))))
                     (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
          rewrite <- bind_trigger.
          apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
          apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
        eapply GIS_WriteR with (ic' := IC_Inlined stk ce1 e1_c0 (Maps.add va_tmp_id dv_va e2_args));
          [reflexivity | exact Er_va |].
        eapply GIS_TauR; [reflexivity |].
        eapply gen_inline_sim__obs_eq;
          [reflexivity | symmetry; apply (run_exc_tau_eq _ _ Logic.eq_refl) |].
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
          gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
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
            ITree.bind (ITree.trigger (GlobalRead callee_gid))
              (fun fv =>
                 Tau (run_exc (ITree.bind (call ret_dt (anns_cconv call_anns) fv vs)
                                 (call_after_ret_k1 vs))))).
          { assert (Eb : call_after_args_k1 vs ≅
                         ITree.bind (ITree.trigger (GlobalRead callee_gid))
                           (fun fv => ITree.bind (call ret_dt (anns_cconv call_anns) fv vs)
                                        (call_after_ret_k1 vs))).
            { unfold call_after_args_k1; rewrite Eqit.bind_bind.
              apply eq_itree_clo_bind with (UU := Logic.eq);
                [apply denote_exp'_global_eq | intros fv _ <-; reflexivity]. }
            rewrite (run_exc_proper _ _ Eb).
            rewrite (run_exc_vis_none_eq _ (subevent _ (GlobalRead callee_gid))
                       (fun fv => ITree.bind (Ret fv)
                                    (fun z => ITree.bind (call ret_dt (anns_cconv call_anns) z vs)
                                                (call_after_ret_k1 vs)))
                       (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
            rewrite <- bind_trigger.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros fv _ <-].
            apply eqit_Tau, run_exc_proper; rewrite Eqit.bind_ret_l; reflexivity. }
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
          { unfold call, ce_call.
            rewrite (run_exc_vis_none_eq _
                       (subevent _ (Call ret_dt (anns_cconv call_anns)
                                      (DVALUE_Base (DVALUE_Pointer p_callee)) vs))
                       (fun rv => ITree.bind (Ret rv) (call_after_ret_k1 vs))
                       (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
            rewrite <- bind_trigger.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros rv _ <-].
            unfold callee_outer_k1; apply eqit_Tau, run_exc_proper, Eqit.bind_ret_l. }
          assert (Hopt_eq : opt_c _ ce_call = Some (denote_function callee_df (anns_cconv call_anns) vs)).
          { unfold opt_c, callee_opt_call, ce_call;
              cbn [subevent resum ReSum_inl ReSum_id id_ Id_IFun inl1].
            rewrite Z.eqb_refl; reflexivity. }
          eapply GIS_InlCallL; [reflexivity | exact El_call | exact Hopt_eq |].
          set (bs_c := combine (df_args callee_df) vs).
          assert (El_dfn :
            ITree.bind (denote_function callee_df (anns_cconv call_anns) vs) (callee_outer_k1 vs) ≅
            ITree.bind (ITree.trigger MemPush)
              (fun _ =>
                 ITree.bind (ITree.trigger (StackPush bs_c))
                   (fun _ =>
                      ITree.bind (ITree.trigger (Alloca (DTYPE_Struct true []) 1%N None))
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
          { unfold denote_function, push_call_frame, mem_push, stack_push, alloca.
            fold callee_gid callee_cfg.
            pose proof Hproto_rattrs as Hpr; pose proof Hproto_pattrs as Hpp.
            destruct (dc_param_attrs (df_prototype callee_df)) as [ret_attrs args_attrs] eqn:Edcpa.
            cbn [fst] in Hpr; subst ret_attrs; cbn [snd] in Hpp.
            rewrite (check_cconv_eq_true _ _ _ Hcc_eq).
            cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
            rewrite Eqit.bind_ret_l, Eqit.bind_bind.
            rewrite (apply_args_attrs_all_nil_eq _ _ _ Hpp), Eqit.bind_ret_l.
            rewrite (combine_lists_varargs_exact (df_args callee_df) vs (eq_sym Hvs_len)).
            cbn [EOU_to_itree map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_itree]; fold bs_c.
            rewrite !Eqit.bind_ret_l, !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros varargs _ <-].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros varg _ <-].
            unfold callee_epilogue_k1; rewrite Edcpa; cbn [fst].
            unfold denote_cfg_map, tree_callee1, finish_cfg; reflexivity. }
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
          { unfold pre_after_args_k2, alloca, ev_va.
            rewrite Eqit.bind_bind.
            rewrite (run_exc_vis_none_eq _ (subevent _ (Alloca (DTYPE_Struct true []) 1%N None))
                       (fun v => ITree.bind (Ret v)
                                   (fun z => ITree.bind (lwrite va_tmp_id z)
                                               (fun _ => Tau (tree_at2 call_bid (ren_b (init callee_cfg))))))
                       (ltac:(rewrite observe_bind; reflexivity)) Logic.eq_refl).
            apply eqit_Vis; intros v; apply eqit_Tau, run_exc_proper, Eqit.bind_ret_l. }
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
            apply Eqit.bind_ret_l.
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
          gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            opt_c g0 true out_rel r_caller (IC_Synced stk ce1 e2')
            (run_exc (call_after_ret_k1 vs (inr dv)))
            (run_exc (tree_at2 (ren_b b_ret) post_bid))).
      { intros b_ret rtmp_ret bk_ret dv ce1 e2' vs Hb_ret Hbk_rtmp Hagree Hret_info.
        pose proof (find_block_new_post_bid caller_df callee_df pre_blks post_blks
                      b_call pre_cd post_cd call_iid ret_dt call_args
                      Hcaller_nd Hcaller_split Hcallee_nd) as Hfb_post.
        fold caller_df' caller_cfg' used_ids l_origs b_origs n_loc n_blk n_ret
             all_fresh post_bid b_fresh ret_tmps ren_b bk_rtmps in Hfb_post.
        set (post_phis :=
          match call_iid with
          | IId res_id => [(res_id, Phi [] ret_dt (collect_ret_phi_incoming ren_b bk_rtmps), [])]
          | IVoid _ => []
          end) in *.
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
          rewrite !Eqit.bind_ret_l, Eqit.bind_bind; reflexivity. }
        assert (Er_post :
          tree_at2 (ren_b b_ret) post_bid ≅
          ITree.bind
            (ITree.bind (denote_phis (ren_b b_ret) post_phis)
               (fun _ => ITree.bind (denote_code post_cd caller_va)
                           (fun _ => denote_terminator (blk_term b_call))))
            (step_bd_cont (blks caller_cfg') caller_va post_bid)).
        { unfold tree_at2; apply ocfg_bind_finish_some_eq, Hfb_post. }
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
          destruct call_iid as [res_id | vn].
          + cbn [opt_ret_dt] in Hret_info.
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
              ITree.bind (ITree.trigger (LocalRead rtmp_ret))
                (fun uv => lwrite res_id uv)).
            { cbn [denote_phis map_monad denote_phi]; rewrite Hassoc_ret.
              rewrite !Eqit.bind_bind.
              apply eq_itree_clo_bind with (UU := Logic.eq);
                [apply denote_exp'_local_eq | intros uv _ <-].
              rewrite !Eqit.bind_ret_l; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
              rewrite !Eqit.bind_bind.
              apply eq_itree_clo_bind with (UU := Logic.eq);
                [reflexivity | intros [] _ _; rewrite !Eqit.bind_ret_l; reflexivity]. }
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
                symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
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
            destruct (blk_term b_call) as [[tiid tm] tmd] eqn:Ebt_call.
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
          gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
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
          fold call_bid caller_df' caller_cfg' used_ids l_origs b_origs n_loc n_blk n_ret
               all_fresh post_bid va_tmp_id l_fresh b_fresh ren_l ren_b in Hfb2.
          assert (Hphis_cond :
            blk_phis b_call = [] \/
            (call_bid <> post_bid /\
             b_from1 <> post_bid /\
             b_from2 = remap_pred_id call_bid post_bid b_from1 /\
             ~ In post_bid (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) (blk_phis b_call)))).
          { destruct Hpred as [(Hinit_eq & _ & _) | (Hbf1 & Hbf2_eq)].
            - left; destruct (cfg_entry_has_no_phis_inv _ Hcaller_entry) as (b0 & Hfb0 & Hb0_phis).
              rewrite <- Hinit_eq, Hfb1 in Hfb0; injection Hfb0 as <-; exact Hb0_phis.
            - right; split; [exact Hcall_ne_post | split; [exact Hbf1 | split; [exact Hbf2_eq |]]].
              intros Hin; eapply (proj1 (Hcaller_lbl_safe b_call post_bid Hbcall_in _)); [reflexivity |].
              unfold block_all_label_ids; right; apply in_or_app; left; exact Hin. }
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
            unfold denote_block; rewrite Hcd_split.
            unfold denote_code at 1; rewrite loop_monad_itree_app.
            cbn [loop_monad]; fold (denote_code pre_cd caller_va) (denote_code post_cd caller_va).
            cbn [denote_instr]; fold call_loc.
            rewrite denote_operand_bundles_nil_eq, (intrinsic_exp_global_none _ Hintr_none).
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros vs _ <-].
            rewrite Eqit.bind_ret_l; unfold call_after_args_k1, call_after_ret_k1, write_call_res, post_call_u1.
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros fv _ <-].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros rv _ <-].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros res _ <-].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros retv _ <-].
            rewrite !Eqit.bind_bind; reflexivity. }
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
            unfold denote_block; cbn [blk_phis blk_code blk_term].
            unfold denote_code at 1; rewrite !loop_monad_itree_app.
            fold (denote_code pre_cd caller_va)
                 (denote_code (build_param_copies ren_l (df_args callee_df) call_args) caller_va).
            cbn [loop_monad denote_instr explicit_alignment find_option denote_terminator
                 step_bd_cont ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
            unfold pre_after_args_k2, tree_at2.
            rewrite !Eqit.bind_bind.
            apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros v _ <-].
            rewrite !Eqit.bind_bind.
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
              eapply gen_inline_sim_weaken;
                [| apply (denote_call_args_param_copies_sim opt_c g0 l_origs all_fresh ren_l
                            (call_loc ++ ": Call argument violates noundef.")%string
                            caller_va stk ce1 Hinj_l Hfresh_l
                            (df_args callee_df) call_args e2_c
                            Harg_len Hcallee_args_nd
                            (fun p Hp => callee_local_ids_arg callee_df p Hp)
                            Hpattrs_nil _ Hag_c)].
              -- intros ? vs [] (_ & Hvs_len & e2_args & -> & Hag_args & _ & Hparams).
                 split; [reflexivity | split; [exact Hvs_len | exists ce1, e2_args; auto]].
              -- intros te pattrs x Hin_arg Hx_use.
                 apply (Hcaller_use_safe b_call x Hbcall_in).
                 unfold full_block_uses; apply in_or_app; right; apply in_or_app; left.
                 rewrite Hcd_split, flat_map_app; apply in_or_app; right; cbn [flat_map].
                 apply in_or_app; left; apply in_or_app; left; cbn [full_instr_uses].
                 apply in_or_app; right; apply in_or_app; left.
                 apply in_flat_map; exists (te, pattrs); split; assumption.
        - (* Non-call caller block [bid_cur <> call_bid] *)
          pose proof (find_block_new_caller_other caller_df callee_df pre_blks post_blks
                        b_call pre_cd post_cd call_iid ret_dt call_args bid_cur
                        Hcaller_nd Hcaller_split Hcallee_nd
                        Hne_call Hcur_post Hcur_bf) as Hfb_other.
          fold call_bid caller_df' caller_cfg' used_ids l_origs b_origs n_loc n_blk n_ret
               all_fresh post_bid b_fresh in Hfb_other.
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
                rewrite <- Hinit_eq, Efb1 in Hfb0; injection Hfb0 as <-; exact Hb0_phis.
              - right; split; [exact Hcall_ne_post | split; [exact Hbf1 | split; [exact Hbf2_eq |]]].
                intros Hin; eapply (proj1 (Hcaller_lbl_safe bk post_bid Hbk_in _)); [reflexivity |].
                unfold block_all_label_ids; right; apply in_or_app; left; exact Hin. }
            assert (Hremap_cur : bid_cur = remap_pred_id call_bid post_bid bid_cur).
            { unfold remap_pred_id.
              destruct (raw_id_eqb bid_cur call_bid) eqn:Eeq;
                [apply raw_id_eqb_spec in Eeq; contradiction | reflexivity]. }
            eapply gen_inline_sim__obs_eq;
              [symmetry; apply run_exc_proper; unfold tree_at1; apply (ocfg_bind_finish_some_eq _ _ _ _ _ Efb1)
              | symmetry; apply run_exc_proper; unfold tree_at2; apply (ocfg_bind_finish_some_eq _ _ _ _ _ Hfb_other) |].
            eapply (Hsync_step bid_cur bid_cur (IC_Synced stk ea1 ea2));
              [exact Hcur_post | exact Hremap_cur | exists ea1, ea2; reflexivity |].
            unfold denote_block, remap_block_phis; cbn [blk_phis blk_code blk_term].
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
    (p_callee : @ptr PaV)
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
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
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
        gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
          (@inl_cfg_event_post) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
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
            destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; apply Hlift_cont, Hrd, Hv.
            -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
               apply Hlift_cont, Hr.
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
    stk e1 e2 (strptr : @ptr PaV) (index : Z) :
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
      destruct d_byte as [[| sz b | | | | | |] | |]; try apply Herr.
      destruct sz as [p | p |]; try apply Herr;
        destruct p as [p | p |]; try apply Herr;
        destruct p as [p | p |]; try apply Herr;
        destruct p as [p | p |]; try apply Herr.
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
    destruct args as [| ch [| ? ?]];
      try (apply cfg_inline_sim_raise; reflexivity).
    cbn [Functor.fmap Functor_itree ITree.map].
    eapply gen_inline_sim_bind with
      (RA := fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2);
      [| intros ? dv _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    destruct ch as [[| sz x32 | | | | | |] | |];
      try apply cfg_inline_sim_raiseUB.
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
    destruct args as [| u_strptr [| ? ?]];
      try (apply cfg_inline_sim_raise; reflexivity).
    cbn [Functor.fmap Functor_itree ITree.map].
    eapply gen_inline_sim_bind with
      (RA := fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2);
      [| intros ? dv _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    destruct u_strptr as [[strptr | | | | | | |] | |];
      try apply cfg_inline_sim_raiseUB.
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
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      repeat constructor;
      intros stk e1 e2 cc args;
      first [apply puts_denotation_inline_sim | apply putchar_denotation_inline_sim].
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
    - cbn [IntMaps.IP.of_list fold_right fst snd]; unfold lookup.
      apply IntMaps.IP.F.add_eq_o; reflexivity.
    - assert (Hne : k <> k0) by (intros ->; apply Hnin; left; reflexivity).
      assert (Hnin' : ~ In k0 (List.map fst rest)) by (intros H; apply Hnin; right; exact H).
      cbn [IntMaps.IP.of_list fold_right fst snd]; unfold lookup.
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
    - cbn [IntMaps.IP.of_list fold_right fst snd]; unfold lookup.
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
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    destruct (Maps.lookup k (snd (snd s0))) as [v |] eqn:Elk.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite (fused_global_prov_read_some k v s0 Elk), Eqit.bind_ret_l; reflexivity
        | symmetry; rewrite (fused_global_prov_read_some k v s0 Elk), Eqit.bind_ret_l; reflexivity |].
      apply refine_prov_tau2_ret; repeat split; [reflexivity | exact Elk].
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
         (exists p : @ptr PaV,
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
             (exists p : @ptr PaV,
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
    destruct fv1 as [[p | | | | | | |] | |]; try apply Herr.
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
                exists p : @ptr PaV,
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
    - eapply gen_inline_sim_bind.
      + unfold address_one_library_function.
        eapply gen_inline_sim_bind.
        * unfold gread, trigger_cast; apply mcfg_inline_sim_trigger_refl; reflexivity.
        * intros ? fv _ [-> <-].
          destruct fv as [[p | | | | | | |] | |];
            try (apply mcfg_inline_sim_raise; reflexivity).
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
    { rewrite Edefs, Edefs'.
      apply Forall2_app.
      - induction pre_defs as [| d ds IH]; constructor;
          [split; [reflexivity | apply denote_function_other_sim] | exact IH].
      - constructor.
        + split; [reflexivity |].
          exact (denote_function_caller_sim
                   g0 p_callee caller_df callee_df pre_blks post_blks b_call pre_cd post_cd
                   call_iid call_md ret_dt call_args call_anns
                   Hg_callee Hcaller_ok Hcaller_split Hcd_split Harg_len Hpattrs_nil
                   Hcc_eq Hcall_rattrs Hcall_fattrs Hcall_range Hcallee_ok).
        + induction post_defs as [| d ds IH]; constructor;
            [split; [reflexivity | apply denote_function_other_sim] | exact IH]. }
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq
      | symmetry; apply interp_mcfg_model_bind_eq |].
    eapply refine_prov_bind;
      [apply (interp_map_address_functions_inline opt_c g0 (m_bg, ((sf_bg, []), g0))
                (m_definitions M) defs' Hdefs_pair (m_bg, ((sf_bg, []), g0)) U1 Logic.eq_refl) |].
    intros U2 [s_d1 defns1] [s_d2 defns2] _ (-> & -> & Hdefns1_src & Hdefns_rel).
    rewrite Ec_split in Hdefns1_src.
    apply inl_Forall2_app_inv_l in Hdefns1_src
      as (defns1_pre & defns1_rest & -> & Hsrc_pre & Hsrc_rest).
    inversion Hsrc_rest as [| ? [k_c fn_c] ? defns1_post Hc_hd Hsrc_post]; subst.
    destruct Hc_hd as (p_c & -> & Hlk_pc & ->).
    rewrite Hg_callee in Hlk_pc; injection Hlk_pc as <-.
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
        rewrite map_map; apply in_map, Hd_in_defs. }
      pose proof (Hdom_seen _ _ Hd_in_decl_names Hlk_d) as Hd_in_seen_fst.
      apply in_map_iff in Hd_in_seen_fst as ([x_d z_d] & Hxz_eq & Hxz_in).
      cbn [fst] in Hxz_eq; subst x_d.
      destruct (Hok_seen _ _ Hxz_in) as (_ & p_d0 & Hp_d0_z & Hlk_d0).
      rewrite Hlk_d in Hlk_d0; injection Hlk_d0 as <-.
      assert (Hne_nm : dc_name (df_prototype d) <> dc_name (df_prototype callee_df)).
      { intros Heq_nm; apply Hcpre_nin.
        rewrite <- Heq_nm; apply (in_map (fun d0 => dc_name (df_prototype d0))), Hd_in_cpre. }
      apply (Hdisj_seen _ _ _ _ Hxz_in Hz_callee_seen Hne_nm).
      lia. }
    unfold interp_mcfg_model.
    eapply refine_prov_antitone with (U := U2);
      [intros _ _ [s1 r1] [s2 r2] _ (_ & _ & <-); reflexivity | apply incl_refl |].
    eapply (mcfg_inline_sim_to_model g0 (fun _ r1 r2 => r1 = r2)
              U2 (IC_Synced [] Maps.empty Maps.empty)).
    { split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
      split; [repeat split; try exact Hsf_vars; reflexivity | constructor]. }
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
      + lia.
      + rewrite <- app_assoc; cbn [app]; apply of_list_lookup_split, Hnin_pre.
      + exact Hctx.
      + unfold inl_mrec_ctx.
        eapply gen_inline_sim_bind;
          [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
        assert (Hext :
          cfg_inline_sim opt_c g0 true
            (fun ic' r1 r2 => ic' = IC_Synced [] Maps.empty Maps.empty /\ r1 = r2)
            (IC_Synced [] Maps.empty Maps.empty)
            (Functor.fmap inr (external_call ret_typ addr args))
            (Functor.fmap inr (external_call ret_typ addr args))).
        { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
          eapply gen_inline_sim_bind.
          - apply cfg_inline_sim_trigger_refl; reflexivity.
          - intros ? rv1 rv2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
        unfold lookup_defn.
        destruct addr as [[p | | | | | | |] | |]; try exact Hext.
        pose proof (Hctx (ptr_to_int p)) as Hlk.
        destruct (lookup (ptr_to_int p)
                    (IntMaps.IP.of_list ((defns1_pre ++ (ptr_to_int p_callee, denote_function callee_df) :: defns1_post) ++ libs1)))
                 as [f1 |],
                 (lookup (ptr_to_int p) (IntMaps.IP.of_list (defns2 ++ libs2)))
                 as [f2 |];
          inversion Hlk as [? ? Hf12 |]; subst.
        * apply Hf12.
        * exact Hext.
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
