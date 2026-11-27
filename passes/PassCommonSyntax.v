(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Shared Syntactic Utilities & Use-Site Collectors ([CertPasses.PassCommonSyntax])

    Purpose:
      Provides extraction-clean equality deciders, collision-free fresh [Name]
      generation, poison-preserving copy expressions, and complete SSA
      use-site and syntax-guard collectors (closing upstream [Scope.v] gaps).

    Trust Contract & Fail-Closed Boundary:
      Purely syntactic AST utilities and boolean guards consumed by extracted
      passes; [mcfg_no_inttoptr] and [cfg_no_block_addresses] fail closed.

    Assumptions:
      Depends on Rocq [Stdlib], [ITree], [ExtLib], and [Vellvm] AST/semantics;
      zero custom axioms or [Admitted].

    Section Outline:
      1. Extraction-clean equality deciders and list membership.
      2. Fresh [Name] generation.
      3. Canonical poison-preserving copy expression ([mk_copy_exp]).
      4. [SyntaxCollectors]: complete use/def, block-address, and [inttoptr] checks. *)

From Stdlib Require Import
  ZArith
  Strings.String
  Strings.Ascii
  List
  Bool
  Morphisms
  RelationClasses
  Lia.
Import ListNotations.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit.

From ExtLib Require Import
  Structures.Monads.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  ScopeTheory
  Semantics.Interfaces.Params.
Export LLVMAst.
Import Logic.

Arguments exp_block_addresses {T} _.
Arguments texps_block_addresses {T} _.
Arguments instr_block_addresses {T} _.
Arguments term_block_addresses {T} _.
Arguments block_block_addresses {T} _.

Set Default Goal Selector "!".
Unset Implicit Arguments.

(** * 1. Extraction-Clean Equality Deciders & List Membership *)

Definition raw_id_eqb (x y : raw_id) : bool :=
  if RawIDOrd.eq_dec x y then true else false.

Lemma raw_id_eqb_spec (x y : raw_id) :
  raw_id_eqb x y = true <-> x = y.
Proof.
  unfold raw_id_eqb.
  destruct (RawIDOrd.eq_dec x y) as [Heq | Hneq]; split; intros H;
    try exact Heq; try reflexivity; try discriminate; contradiction.
Qed.

Lemma raw_id_eqb_refl (x : raw_id) :
  raw_id_eqb x x = true.
Proof.
  apply raw_id_eqb_spec; reflexivity.
Qed.

Lemma raw_id_eqb_neq (x y : raw_id) :
  raw_id_eqb x y = false <-> x <> y.
Proof.
  unfold raw_id_eqb.
  destruct (RawIDOrd.eq_dec x y) as [Heq | Hneq]; split; intros H;
    try exact Hneq; try discriminate; try contradiction; reflexivity.
Qed.

Lemma raw_id_eqb_sym (x y : raw_id) :
  raw_id_eqb x y = raw_id_eqb y x.
Proof.
  destruct (raw_id_eqb x y) eqn:E.
  - apply raw_id_eqb_spec in E; subst; symmetry; apply raw_id_eqb_refl.
  - apply raw_id_eqb_neq in E; symmetry; apply raw_id_eqb_neq; congruence.
Qed.

Definition ident_eqb (x y : ident) : bool :=
  match x, y with
  | ID_Global gx, ID_Global gy => raw_id_eqb gx gy
  | ID_Local lx, ID_Local ly => raw_id_eqb lx ly
  | _, _ => false
  end.

Lemma ident_eqb_spec (x y : ident) :
  ident_eqb x y = true <-> x = y.
Proof.
  destruct x as [gx | lx], y as [gy | ly]; cbn [ident_eqb];
    try (split; intros H; discriminate).
  - rewrite raw_id_eqb_spec; split;
      [intros ->; reflexivity | intros H; inversion H; reflexivity].
  - rewrite raw_id_eqb_spec; split;
      [intros ->; reflexivity | intros H; inversion H; reflexivity].
Qed.

Definition in_raw_ids (x : raw_id) (xs : list raw_id) : bool :=
  existsb (raw_id_eqb x) xs.

Lemma in_raw_ids_spec (x : raw_id) (xs : list raw_id) :
  in_raw_ids x xs = true <-> In x xs.
Proof.
  unfold in_raw_ids; rewrite existsb_exists.
  split.
  - intros [y [Hin Heq]]; apply raw_id_eqb_spec in Heq; subst; exact Hin.
  - intros Hin; exists x; split; [exact Hin | apply raw_id_eqb_refl].
Qed.

Lemma in_raw_ids_false (x : raw_id) (xs : list raw_id) :
  in_raw_ids x xs = false <-> ~ In x xs.
Proof.
  destruct (in_raw_ids x xs) eqn:E.
  - apply in_raw_ids_spec in E; split; [discriminate | intros H; contradiction].
  - split; [| intros _; reflexivity].
    intros _ Hin; apply in_raw_ids_spec in Hin; congruence.
Qed.

(** * 2. Fresh [Name] Generation (Preserving Valid LLVM Textual Surface Syntax) *)

Fixpoint repeat_underscore (n : nat) : string :=
  match n with
  | O => EmptyString
  | S n' => String "_"%char (repeat_underscore n')
  end.

Lemma repeat_underscore_length (n : nat) :
  String.length (repeat_underscore n) = n.
Proof.
  induction n as [| n' IH]; [reflexivity | cbn; lia].
Qed.

Lemma string_app_length (s1 s2 : string) :
  String.length (s1 ++ s2)%string = (String.length s1 + String.length s2)%nat.
Proof.
  induction s1 as [| c s1' IH];
    [reflexivity | change (String c s1' ++ s2)%string with (String c (s1' ++ s2)%string); cbn [String.length]; lia].
Qed.

Definition raw_id_name_len (id : raw_id) : nat :=
  match id with
  | Name s => String.length s
  | _ => O
  end.

Definition max_name_len (ids : list raw_id) : nat :=
  fold_right (fun x acc => Nat.max (raw_id_name_len x) acc) O ids.

Lemma max_name_len_ge (x : raw_id) (ids : list raw_id) :
  In x ids -> (raw_id_name_len x <= max_name_len ids)%nat.
Proof.
  induction ids as [| y ys IH]; intros Hin; [contradiction |].
  cbn [max_name_len fold_right]; fold (max_name_len ys).
  destruct Hin as [<- | Hin];
    [apply Nat.le_max_l | eapply Nat.le_trans; [exact (IH Hin) | apply Nat.le_max_r]].
Qed.

Definition fresh_name (prefix : string) (avoid : list raw_id) : raw_id :=
  Name (prefix ++ repeat_underscore (S (max_name_len avoid)))%string.

Lemma fresh_name_not_in (prefix : string) (avoid : list raw_id) :
  ~ In (fresh_name prefix avoid) avoid.
Proof.
  intros Hin.
  apply max_name_len_ge in Hin.
  unfold fresh_name, raw_id_name_len in Hin.
  rewrite string_app_length, repeat_underscore_length in Hin.
  lia.
Qed.

Fixpoint fresh_names (prefix : string) (n : nat) (avoid : list raw_id) : list raw_id :=
  match n with
  | O => []
  | S n' =>
      let x := fresh_name prefix avoid in
      x :: fresh_names prefix n' (x :: avoid)
  end.

Lemma fresh_names_length (prefix : string) (n : nat) (avoid : list raw_id) :
  List.length (fresh_names prefix n avoid) = n.
Proof.
  revert avoid; induction n as [| n' IH]; intros avoid;
    [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma fresh_names_disjoint (prefix : string) (n : nat) (avoid : list raw_id) :
  forall x, In x (fresh_names prefix n avoid) -> ~ In x avoid.
Proof.
  revert avoid; induction n as [| n' IH]; intros avoid x Hin; [contradiction |].
  cbn [fresh_names] in Hin.
  destruct Hin as [<- | Hin].
  - apply fresh_name_not_in.
  - intros Havoid.
    eapply IH; [exact Hin | right; exact Havoid].
Qed.

Lemma fresh_names_nodup (prefix : string) (n : nat) (avoid : list raw_id) :
  NoDup (fresh_names prefix n avoid).
Proof.
  revert avoid; induction n as [| n' IH]; intros avoid; [constructor |].
  cbn [fresh_names]; constructor.
  - intros Hin; eapply fresh_names_disjoint; [exact Hin | left; reflexivity].
  - apply IH.
Qed.

(** * 3. Canonical Poison-Preserving Copy Expression *)

Definition mk_copy_exp {T : Set} (ty_i1 : T) (t : T) (e : exp T) : exp T :=
  OP_Select [] (ty_i1, EXP_Bool true) (t, e) (t, EXP_Poison).

Lemma denote_mk_copy_exp {Pa : Params} (top : option dtyp) (ty_i1 t : dtyp) (e : exp dtyp) :
  denote_exp top (mk_copy_exp ty_i1 t e) ≅ denote_exp (Some t) e.
Proof.
  cbn [denote_exp mk_copy_exp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
  rewrite Eqit.bind_ret_l.
  rewrite <- (Eqit.bind_ret_r (denote_exp (Some t) e)) at 2.
  eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros v _ <-.
  rewrite Eqit.bind_ret_l.
  cbn [eval_select eval_select_base_dvalue].
  replace (@Integers.unsigned 1 VellvmIntegers.one =? 1)%Z with true by reflexivity.
  cbn [EOU_to_itree EOU_monad ExtLib.Structures.Monad.ret Monad_itree].
  reflexivity.
Qed.

(** * 4. Complete Use-Site & Syntax Guards (Closing Upstream [Scope.v] Gaps) *)

Section SyntaxCollectors.
  Context {T : Set}.

  Fixpoint full_exp_uses (e : exp T) : list raw_id :=
    let full_texp_list :=
      fix go (l : list (T * exp T)) : list raw_id :=
        match l with
        | [] => []
        | (_, ex) :: rest => full_exp_uses ex ++ go rest
        end
    in
    match e with
    | EXP_Ident (ID_Local x) => [x]
    | EXP_Ident (ID_Global _) => []
    | EXP_Integer _ | EXP_Float _ | EXP_Bool _ | EXP_Null
    | EXP_Zero_initializer | EXP_Undef | EXP_Poison
    | EXP_Asm _ _ _ _ _ _ | EXP_BlockAddress _ _ => []
    | EXP_Cstring elts | EXP_Struct elts | EXP_Packed_struct elts
    | EXP_Array elts | EXP_Vector elts => full_texp_list elts
    | OP_IBinop _ _ e1 e2 | OP_ICmp _ _ _ e1 e2
    | OP_FBinop _ _ _ e1 e2 | OP_FCmp _ _ _ e1 e2 =>
        full_exp_uses e1 ++ full_exp_uses e2
    | OP_Fneg _ (_, e1) | OP_Conversion _ _ e1 _
    | OP_ExtractValue (_, e1) _ | OP_Freeze (_, e1)
    | EXP_Splat (_, e1) => full_exp_uses e1
    | OP_GetElementPtr _ _ (_, ep) idxs =>
        full_exp_uses ep ++ full_texp_list idxs
    | OP_ExtractElement (_, e1) (_, e2)
    | OP_InsertValue (_, e1) (_, e2) _ =>
        full_exp_uses e1 ++ full_exp_uses e2
    | OP_InsertElement (_, e1) (_, e2) (_, e3)
    | OP_ShuffleVector (_, e1) (_, e2) (_, e3)
    | OP_Select _ (_, e1) (_, e2) (_, e3) =>
        full_exp_uses e1 ++ full_exp_uses e2 ++ full_exp_uses e3
    | EXP_Metadata md => full_metadata_uses md
    end
  with full_metadata_uses (md : metadata T) : list raw_id :=
    let full_md_list :=
      fix go_md (l : list (metadata T)) : list raw_id :=
        match l with
        | [] => []
        | m :: rest => full_metadata_uses m ++ go_md rest
        end
    in
    match md with
    | METADATA_Null | METADATA_Id _ | METADATA_Debug _ _ | METADATA_File_info _ => []
    | METADATA_Const (_, ex) => full_exp_uses ex
    | METADATA_Node mds => full_md_list mds
    | METADATA_Pair m1 m2 => full_metadata_uses m1 ++ full_metadata_uses m2
    end.

  Definition full_texp_uses (te : texp T) : list raw_id :=
    full_exp_uses (snd te).

  Definition full_ann_uses (a : annotation T) : list raw_id :=
    match a with
    | ANN_metadata mds => flat_map full_metadata_uses mds
    | ANN_prefix te | ANN_prologue te | ANN_personality te | ANN_num_elements te =>
        full_texp_uses te
    | _ => []
    end.

  Definition full_operand_uses (op : @operand T) : list raw_id :=
    match op with
    | SSA_value te => full_texp_uses te
    | Metadata_string md => full_metadata_uses md
    end.

  Definition full_ob_uses (ob : @operand_bundle T) : list raw_id :=
    flat_map full_operand_uses (ob_ops ob).

  Definition full_lp_clause_uses (c : @landingpad_clause T) : list raw_id :=
    match c with
    | CATCH te | FILTER te => full_texp_uses te
    end.

  Definition full_instr_uses (i : instr T) : list raw_id :=
    match i with
    | INSTR_Comment _ | INSTR_Fence _ _ => []
    | INSTR_Op e => full_exp_uses e
    | INSTR_Call fn args anns obs =>
        full_texp_uses fn
        ++ flat_map (fun '(te, _) => full_texp_uses te) args
        ++ flat_map full_ann_uses anns
        ++ flat_map full_ob_uses obs
    | INSTR_Alloca _ anns => flat_map full_ann_uses anns
    | INSTR_Load _ ptr anns => full_texp_uses ptr ++ flat_map full_ann_uses anns
    | INSTR_Store val ptr anns =>
        full_texp_uses val ++ full_texp_uses ptr ++ flat_map full_ann_uses anns
    | INSTR_AtomicCmpXchg c =>
        full_texp_uses (c_ptr c) ++ full_texp_uses (c_cmp c) ++ full_texp_uses (c_new c)
    | INSTR_AtomicRMW a =>
        full_texp_uses (a_ptr a) ++ full_texp_uses (a_val a)
    | INSTR_VAArg va _ => full_texp_uses va
    | INSTR_LandingPad _ _ cs => flat_map full_lp_clause_uses cs
    end.

  Definition full_phi_uses (p : phi T) : list raw_id :=
    match p with
    | Phi _ _ args => flat_map (fun '(_, ex) => full_exp_uses ex) args
    end.

  Definition full_term_uses (tm : terminator T) : list raw_id :=
    match tm with
    | TERM_Ret te | TERM_Br te _ _ | TERM_Switch te _ _
    | TERM_IndirectBr te _ _ | TERM_Resume te => full_texp_uses te
    | TERM_Ret_void | TERM_Br_1 _ | TERM_Unreachable => []
    | TERM_Invoke fn args _ _ anns obs =>
        full_texp_uses fn
        ++ flat_map (fun '(te, _) => full_texp_uses te) args
        ++ flat_map full_ann_uses anns
        ++ flat_map full_ob_uses obs
    end.

  Definition instr_id_defs (iid : instr_id) : list raw_id :=
    match iid with
    | IId x => [x]
    | IVoid _ => []
    end.

  Definition full_block_uses (bk : block T) : list raw_id :=
    flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) (blk_phis bk)
    ++ flat_map (fun '(_, i, mds) => full_instr_uses i ++ flat_map full_metadata_uses mds) (blk_code bk)
    ++ (let '(_, tm, mds) := blk_term bk in full_term_uses tm ++ flat_map full_metadata_uses mds).

  Definition full_block_defs (bk : block T) : list raw_id :=
    List.map (fun '(x, _, _) => x) (blk_phis bk)
    ++ flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk)
    ++ (let '(iid, _, _) := blk_term bk in instr_id_defs iid).

  Definition cfg_all_ids (c : CFG.cfg T) : list raw_id :=
    init c :: args c
    ++ List.map blk_id (blks c)
    ++ flat_map full_block_defs (blks c)
    ++ flat_map full_block_uses (blks c).

  Definition cfg_no_block_addresses (c : CFG.cfg T) : bool :=
    match flat_map block_block_addresses (blks c) with
    | [] => true
    | _ => false
    end.

  Lemma cfg_no_block_addresses_nil (c : CFG.cfg T) :
    cfg_no_block_addresses c = true <-> flat_map block_block_addresses (blks c) = [].
  Proof.
    unfold cfg_no_block_addresses.
    destruct (flat_map block_block_addresses (blks c)); split; intros H;
      try reflexivity; discriminate.
  Qed.

  Fixpoint exp_has_inttoptr (e : exp T) : bool :=
    let texp_list_has :=
      fix go (l : list (T * exp T)) : bool :=
        match l with
        | [] => false
        | (_, ex) :: rest => exp_has_inttoptr ex || go rest
        end
    in
    match e with
    | OP_Conversion (CONV_Impure Inttoptr) _ _ _ => true
    | OP_Conversion _ _ e1 _ | OP_Fneg _ (_, e1)
    | OP_ExtractValue (_, e1) _ | OP_Freeze (_, e1) | EXP_Splat (_, e1) =>
        exp_has_inttoptr e1
    | OP_IBinop _ _ e1 e2 | OP_ICmp _ _ _ e1 e2
    | OP_FBinop _ _ _ e1 e2 | OP_FCmp _ _ _ e1 e2
    | OP_ExtractElement (_, e1) (_, e2) | OP_InsertValue (_, e1) (_, e2) _ =>
        exp_has_inttoptr e1 || exp_has_inttoptr e2
    | OP_InsertElement (_, e1) (_, e2) (_, e3)
    | OP_ShuffleVector (_, e1) (_, e2) (_, e3)
    | OP_Select _ (_, e1) (_, e2) (_, e3) =>
        exp_has_inttoptr e1 || exp_has_inttoptr e2 || exp_has_inttoptr e3
    | OP_GetElementPtr _ _ (_, ep) idxs =>
        exp_has_inttoptr ep || texp_list_has idxs
    | EXP_Cstring elts | EXP_Struct elts | EXP_Packed_struct elts
    | EXP_Array elts | EXP_Vector elts => texp_list_has elts
    | EXP_Metadata md => metadata_has_inttoptr md
    | _ => false
    end
  with metadata_has_inttoptr (md : metadata T) : bool :=
    let md_list_has :=
      fix go_md (l : list (metadata T)) : bool :=
        match l with
        | [] => false
        | m :: rest => metadata_has_inttoptr m || go_md rest
        end
    in
    match md with
    | METADATA_Const (_, ex) => exp_has_inttoptr ex
    | METADATA_Node mds => md_list_has mds
    | METADATA_Pair m1 m2 => metadata_has_inttoptr m1 || metadata_has_inttoptr m2
    | _ => false
    end.

  Definition ann_has_inttoptr (a : annotation T) : bool :=
    match a with
    | ANN_metadata mds => existsb metadata_has_inttoptr mds
    | ANN_prefix (_, ex) | ANN_prologue (_, ex)
    | ANN_personality (_, ex) | ANN_num_elements (_, ex) => exp_has_inttoptr ex
    | _ => false
    end.

  Definition ob_has_inttoptr (ob : @operand_bundle T) : bool :=
    existsb (fun op =>
               match op with
               | SSA_value (_, ex) => exp_has_inttoptr ex
               | Metadata_string md => metadata_has_inttoptr md
               end) (ob_ops ob).

  Definition instr_has_inttoptr (i : instr T) : bool :=
    match i with
    | INSTR_Comment _ | INSTR_Fence _ _ => false
    | INSTR_Op e => exp_has_inttoptr e
    | INSTR_Call (_, fn) args anns obs =>
        exp_has_inttoptr fn
        || existsb (fun '((_, ex), _) => exp_has_inttoptr ex) args
        || existsb ann_has_inttoptr anns
        || existsb ob_has_inttoptr obs
    | INSTR_Alloca _ anns => existsb ann_has_inttoptr anns
    | INSTR_Load _ (_, ep) anns => exp_has_inttoptr ep || existsb ann_has_inttoptr anns
    | INSTR_Store (_, ev) (_, ep) anns =>
        exp_has_inttoptr ev || exp_has_inttoptr ep || existsb ann_has_inttoptr anns
    | INSTR_AtomicCmpXchg c =>
        exp_has_inttoptr (snd (c_ptr c))
        || exp_has_inttoptr (snd (c_cmp c))
        || exp_has_inttoptr (snd (c_new c))
    | INSTR_AtomicRMW a =>
        exp_has_inttoptr (snd (a_ptr a)) || exp_has_inttoptr (snd (a_val a))
    | INSTR_VAArg (_, ex) _ => exp_has_inttoptr ex
    | INSTR_LandingPad _ _ cs =>
        existsb (fun cl => match cl with CATCH (_, ex) | FILTER (_, ex) => exp_has_inttoptr ex end) cs
    end.

  Definition term_has_inttoptr (tm : terminator T) : bool :=
    match tm with
    | TERM_Ret (_, ex) | TERM_Br (_, ex) _ _ | TERM_Switch (_, ex) _ _
    | TERM_IndirectBr (_, ex) _ _ | TERM_Resume (_, ex) => exp_has_inttoptr ex
    | TERM_Ret_void | TERM_Br_1 _ | TERM_Unreachable => false
    | TERM_Invoke (_, fn) args _ _ anns obs =>
        exp_has_inttoptr fn
        || existsb (fun '((_, ex), _) => exp_has_inttoptr ex) args
        || existsb ann_has_inttoptr anns
        || existsb ob_has_inttoptr obs
    end.

  Definition block_has_inttoptr (bk : block T) : bool :=
    existsb (fun '(_, Phi _ _ args, mds) =>
               existsb (fun '(_, ex) => exp_has_inttoptr ex) args
               || existsb metadata_has_inttoptr mds) (blk_phis bk)
    || existsb (fun '(_, i, mds) =>
                  instr_has_inttoptr i || existsb metadata_has_inttoptr mds) (blk_code bk)
    || (let '(_, tm, mds) := blk_term bk in
        term_has_inttoptr tm || existsb metadata_has_inttoptr mds).

  Definition mcfg_no_inttoptr (M : CFG.mcfg T) : bool :=
    negb (existsb (fun g => match g_exp g with Some ex => exp_has_inttoptr ex | None => false end)
            (m_globals M)
          || existsb (fun d => existsb block_has_inttoptr (blks (df_instrs d)))
               (m_definitions M)).

  Definition map_defn_cfg (f : CFG.cfg T -> CFG.cfg T)
    (df : definition T (CFG.cfg T)) : definition T (CFG.cfg T) :=
    {| df_prototype := df_prototype df;
       df_args      := df_args df;
       df_instrs    := f (df_instrs df) |}.

  Definition map_mcfg_cfg (f : CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T) : CFG.mcfg T :=
    {| m_name         := m_name M;
       m_target       := m_target M;
       m_datalayout   := m_datalayout M;
       m_type_defs    := m_type_defs M;
       m_globals      := m_globals M;
       m_declarations := m_declarations M;
       m_definitions  := List.map (map_defn_cfg f) (m_definitions M) |}.

  Lemma map_mcfg_cfg_prototypes (f : CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T) :
    List.map df_prototype (m_definitions (map_mcfg_cfg f M)) =
    List.map df_prototype (m_definitions M).
  Proof.
    cbn [map_mcfg_cfg m_definitions]; rewrite map_map; reflexivity.
  Qed.

  Lemma map_mcfg_cfg_block_addresses (f : CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T)
    (Hba : forall c, flat_map block_block_addresses (blks (f c)) =
                     flat_map block_block_addresses (blks c)) :
    mcfg_block_addresses (map_mcfg_cfg f M) = mcfg_block_addresses M.
  Proof.
    unfold mcfg_block_addresses; cbn [map_mcfg_cfg m_globals m_definitions].
    f_equal.
    induction (m_definitions M) as [| d ds IH]; [reflexivity |].
    cbn [List.map flat_map map_defn_cfg df_instrs].
    rewrite Hba, IH; reflexivity.
  Qed.

End SyntaxCollectors.

