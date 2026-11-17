(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Shared Pass Infrastructure & Whole-Program Refinement Framework

    Provides extraction-clean syntactic utilities, fresh [Name] generation,
    complete SSA use-site collection (remediating upstream [Scope.v] gaps),
    vanilla-CIC event relations (zero [JMeq], zero [Equations]), provenance
    choice elasticity ([ProvE] / [refine_prov]), a [PreOrder] whole-program
    refinement relation ([prog_refines]), and modular pass lifters
    ([lift_cfg_pass] and [lift_cfg_local_pass]). *)

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
  Basics.HeterogeneousRelations.

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
  Utils.rutt_cutoff
  Theory.Equational
  Theory.MemoryBytesFacts
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.IPtrInfinite
  Semantics.Implementations.IPtrFinite
  Semantics.Implementations.Provenance
  Semantics.Implementations.Pointer
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.
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
  - rewrite raw_id_eqb_spec; split; [intros ->; reflexivity | intros H; inversion H; reflexivity].
  - rewrite raw_id_eqb_spec; split; [intros ->; reflexivity | intros H; inversion H; reflexivity].
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
  revert avoid; induction n as [| n' IH]; intros avoid; [reflexivity | cbn; rewrite IH; reflexivity].
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

(** * 5. Vanilla-CIC Event & Answer Relations (Zero [JMeq], Zero [Equations]) *)

Definition sum_prerel_c {E1 E2 D1 D2 : Type -> Type}
  (PR1 : prerel E1 D1) (PR2 : prerel E2 D2) : prerel (E1 +' E2) (D1 +' D2) :=
  fun A B e1 e2 =>
    match e1, e2 with
    | inl1 x1, inl1 x2 => PR1 A B x1 x2
    | inr1 y1, inr1 y2 => PR2 A B y1 y2
    | _, _ => False
    end.

Definition sum_postrel_c {E1 E2 D1 D2 : Type -> Type}
  (PO1 : postrel E1 D1) (PO2 : postrel E2 D2) : postrel (E1 +' E2) (D1 +' D2) :=
  fun A B e1 a1 e2 a2 =>
    match e1 return A -> (D1 +' D2) B -> B -> Prop with
    | inl1 x1 => fun a1' e2' a2' =>
        match e2' return B -> Prop with
        | inl1 x2 => fun a2'' => PO1 _ _ x1 a1' x2 a2''
        | inr1 _ => fun _ => False
        end a2'
    | inr1 y1 => fun a1' e2' a2' =>
        match e2' return B -> Prop with
        | inl1 _ => fun _ => False
        | inr1 y2 => fun a2'' => PO2 _ _ y1 a1' y2 a2''
        end a2'
    end a1 e2 a2.

Variant cutNone {E : Type -> Type} : forall [A : Type], E A -> Prop := .

Variant cutUB_rel {E : Type -> Type} `{UBE -< E} : forall [A : Type], E A -> Prop :=
  | CutUB_rel u : cutUB_rel (subevent _ (ThrowUB u)).

Ltac destruct_sum1 e :=
  repeat (let Te := type of e in
          let Te' := eval hnf in Te in
          match Te' with
          | (_ +' _) _ => destruct e as [e | e]
          end).

Ltac destruct_sum2 e1 e2 HE :=
  repeat (let Te := type of e1 in
          let Te' := eval hnf in Te in
          match Te' with
          | (_ +' _) _ =>
              match type of HE with
              | sum_prerel_c _ _ _ _ _ _ => idtac
              | sum_postrel_c _ _ _ _ _ _ _ _ => idtac
              | _ => try red in HE
              end;
              destruct e1 as [e1 | e1], e2 as [e2 | e2];
              cbn [sum_prerel_c sum_postrel_c] in HE;
              try contradiction
          end).

Ltac destruct_sum3 e1 e2 e3 H12 H23 :=
  repeat (let Te := type of e1 in
          let Te' := eval hnf in Te in
          match Te' with
          | (_ +' _) _ =>
              match type of H12 with
              | sum_prerel_c _ _ _ _ _ _ => idtac
              | sum_postrel_c _ _ _ _ _ _ _ _ => idtac
              | _ => try red in H12
              end;
              match type of H23 with
              | sum_prerel_c _ _ _ _ _ _ => idtac
              | sum_postrel_c _ _ _ _ _ _ _ _ => idtac
              | _ => try red in H23
              end;
              destruct e1 as [e1 | e1], e2 as [e2 | e2], e3 as [e3 | e3];
              cbn [sum_prerel_c sum_postrel_c] in H12, H23;
              try contradiction
          end).

Section EventRelations.
  Context {Pa : Params}.

  Definition EqE_Call : prerel CallE CallE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | Call t1 cc1 f1 args1, Call t2 cc2 f2 args2 =>
          t1 = t2 /\ cc1 = cc2 /\ f1 = f2 /\ args1 = args2
      end.

  Definition EqA_Call : postrel CallE CallE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in CallE A' return A' -> CallE _ -> _ -> Prop with
      | Call _ _ _ _ => fun r1 e2' r2 =>
          match e2' in CallE B' return B' -> Prop with
          | Call _ _ _ _ => fun r2' => r1 = r2'
          end r2
      end a1 e2 a2.

  Definition EqE_ExternalCall : prerel ExternalCallE ExternalCallE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | ExternalCall t1 f1 args1, ExternalCall t2 f2 args2 =>
          t1 = t2 /\ f1 = f2 /\ args1 = args2
      | IO_stdout s1, IO_stdout s2 => s1 = s2
      | IO_stderr s1, IO_stderr s2 => s1 = s2
      | _, _ => False
      end.

  Definition EqA_ExternalCall : postrel ExternalCallE ExternalCallE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in ExternalCallE A' return A' -> ExternalCallE _ -> _ -> Prop with
      | ExternalCall _ _ _ => fun r1 e2' r2 =>
          match e2' in ExternalCallE B' return B' -> Prop with
          | ExternalCall _ _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | IO_stdout _ => fun r1 e2' r2 =>
          match e2' in ExternalCallE B' return B' -> Prop with
          | IO_stdout _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | IO_stderr _ => fun r1 e2' r2 =>
          match e2' in ExternalCallE B' return B' -> Prop with
          | IO_stderr _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Intrinsic : prerel IntrinsicE IntrinsicE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | Intrinsic t1 f1 args1 va1, Intrinsic t2 f2 args2 va2 =>
          t1 = t2 /\ f1 = f2 /\ args1 = args2 /\ va1 = va2
      end.

  Definition EqA_Intrinsic : postrel IntrinsicE IntrinsicE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in IntrinsicE A' return A' -> IntrinsicE _ -> _ -> Prop with
      | Intrinsic _ _ _ _ => fun r1 e2' r2 =>
          match e2' in IntrinsicE B' return B' -> Prop with
          | Intrinsic _ _ _ _ => fun r2' => r1 = r2'
          end r2
      end a1 e2 a2.

  Definition EqE_Global : prerel GlobalE GlobalE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | GlobalWrite x1 v1, GlobalWrite x2 v2 => x1 = x2 /\ v1 = v2
      | GlobalRead x1, GlobalRead x2 => x1 = x2
      | _, _ => False
      end.

  Definition EqA_Global : postrel GlobalE GlobalE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in GlobalE A' return A' -> GlobalE _ -> _ -> Prop with
      | GlobalWrite _ _ => fun r1 e2' r2 =>
          match e2' in GlobalE B' return B' -> Prop with
          | GlobalWrite _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | GlobalRead _ => fun r1 e2' r2 =>
          match e2' in GlobalE B' return B' -> Prop with
          | GlobalRead _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Local : prerel LocalE LocalE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | LocalWrite x1 v1, LocalWrite x2 v2 => x1 = x2 /\ v1 = v2
      | LocalRead x1, LocalRead x2 => x1 = x2
      | _, _ => False
      end.

  Definition EqA_Local : postrel LocalE LocalE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in LocalE A' return A' -> LocalE _ -> _ -> Prop with
      | LocalWrite _ _ => fun r1 e2' r2 =>
          match e2' in LocalE B' return B' -> Prop with
          | LocalWrite _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | LocalRead _ => fun r1 e2' r2 =>
          match e2' in LocalE B' return B' -> Prop with
          | LocalRead _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Stack : prerel StackE StackE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | StackPush args1, StackPush args2 => args1 = args2
      | StackPop, StackPop => True
      | StackRaise exc1, StackRaise exc2 => exc1 = exc2
      | StackGetExc, StackGetExc => True
      | _, _ => False
      end.

  Definition EqA_Stack : postrel StackE StackE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in StackE A' return A' -> StackE _ -> _ -> Prop with
      | StackPush _ => fun r1 e2' r2 =>
          match e2' in StackE B' return B' -> Prop with
          | StackPush _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | StackPop => fun r1 e2' r2 =>
          match e2' in StackE B' return B' -> Prop with
          | StackPop => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | StackRaise _ => fun r1 e2' r2 =>
          match e2' in StackE B' return B' -> Prop with
          | StackRaise _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | StackGetExc => fun r1 e2' r2 =>
          match e2' in StackE B' return B' -> Prop with
          | StackGetExc => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Memory : prerel MemoryE MemoryE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | MemPush, MemPush => True
      | MemPop, MemPop => True
      | Alloca t1 n1 al1, Alloca t2 n2 al2 => t1 = t2 /\ n1 = n2 /\ al1 = al2
      | Load t1 a1, Load t2 a2 => t1 = t2 /\ a1 = a2
      | Store t1 a1 v1, Store t2 a2 v2 => t1 = t2 /\ a1 = a2 /\ v1 = v2
      | Conv cv1 tf1 v1 tt1, Conv cv2 tf2 v2 tt2 =>
          cv1 = cv2 /\ tf1 = tf2 /\ v1 = v2 /\ tt1 = tt2
      | _, _ => False
      end.

  Definition EqA_Memory : postrel MemoryE MemoryE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in MemoryE A' return A' -> MemoryE _ -> _ -> Prop with
      | MemPush => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | MemPush => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | MemPop => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | MemPop => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | Alloca _ _ _ => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | Alloca _ _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | Load _ _ => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | Load _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | Store _ _ _ => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | Store _ _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | Conv _ _ _ _ => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | Conv _ _ _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Draw : prerel DrawE DrawE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | Draw t1, Draw t2 => t1 = t2
      end.

  Definition EqA_Draw : postrel DrawE DrawE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in DrawE A' return A' -> DrawE _ -> _ -> Prop with
      | Draw _ => fun r1 e2' r2 =>
          match e2' in DrawE B' return B' -> Prop with
          | Draw _ => fun r2' => r1 = r2'
          end r2
      end a1 e2 a2.

  Definition EqE_OOM : prerel OOME OOME :=
    fun _ _ e1 e2 => match e1, e2 with ThrowOOM _, ThrowOOM _ => True end.

  Definition EqA_OOM : postrel OOME OOME :=
    fun _ _ e1 a1 _ _ => match e1 in OOME A' return A' -> Prop with ThrowOOM _ => fun v : void => match v with end end a1.

  Definition EqE_Exc : prerel LLVMExcE LLVMExcE :=
    fun _ _ e1 e2 => match e1, e2 with LLVMExc x1, LLVMExc x2 => x1 = x2 end.

  Definition EqA_Exc : postrel LLVMExcE LLVMExcE :=
    fun _ _ e1 a1 _ _ => match e1 in LLVMExcE A' return A' -> Prop with LLVMExc _ => fun v : void => match v with end end a1.

  Definition EqE_UB : prerel UBE UBE :=
    fun _ _ e1 e2 => match e1, e2 with ThrowUB _, ThrowUB _ => True end.

  Definition EqA_UB : postrel UBE UBE :=
    fun _ _ e1 a1 _ _ => match e1 in UBE A' return A' -> Prop with ThrowUB _ => fun v : void => match v with end end a1.

  Definition EqE_Debug : prerel DebugE DebugE :=
    fun _ _ e1 e2 => match e1, e2 with Debug _, Debug _ => True end.

  Definition EqA_Debug : postrel DebugE DebugE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in DebugE A' return A' -> DebugE _ -> _ -> Prop with
      | Debug _ => fun r1 e2' r2 =>
          match e2' in DebugE B' return B' -> Prop with
          | Debug _ => fun r2' => r1 = r2'
          end r2
      end a1 e2 a2.

  Definition EqE_Failure : prerel FailureE FailureE :=
    fun _ _ e1 e2 => match e1, e2 with Throw _, Throw _ => True end.

  Definition EqA_Failure : postrel FailureE FailureE :=
    fun _ _ e1 a1 _ _ => match e1 in FailureE A' return A' -> Prop with Throw _ => fun v : void => match v with end end a1.

  Definition EqE_MCFG : prerel MCFGEtop MCFGEtop :=
    sum_prerel_c EqE_ExternalCall
      (sum_prerel_c EqE_Intrinsic
         (sum_prerel_c EqE_Global
            (sum_prerel_c (sum_prerel_c EqE_Local EqE_Stack)
               (sum_prerel_c EqE_Memory
                  (sum_prerel_c EqE_Draw
                     (sum_prerel_c EqE_OOM
                        (sum_prerel_c EqE_Exc
                           (sum_prerel_c EqE_UB
                              (sum_prerel_c EqE_Debug EqE_Failure))))))))).

  Definition EqA_MCFG : postrel MCFGEtop MCFGEtop :=
    sum_postrel_c EqA_ExternalCall
      (sum_postrel_c EqA_Intrinsic
         (sum_postrel_c EqA_Global
            (sum_postrel_c (sum_postrel_c EqA_Local EqA_Stack)
               (sum_postrel_c EqA_Memory
                  (sum_postrel_c EqA_Draw
                     (sum_postrel_c EqA_OOM
                        (sum_postrel_c EqA_Exc
                           (sum_postrel_c EqA_UB
                              (sum_postrel_c EqA_Debug EqA_Failure))))))))).

  Definition EqE_CFG : prerel CFGEtop CFGEtop :=
    sum_prerel_c EqE_Call EqE_MCFG.

  Definition EqA_CFG : postrel CFGEtop CFGEtop :=
    sum_postrel_c EqA_Call EqA_MCFG.

  Definition EqE_bot : prerel MCFGEbot MCFGEbot :=
    sum_prerel_c EqE_ExternalCall
      (sum_prerel_c EqE_OOM
         (sum_prerel_c EqE_Exc
            (sum_prerel_c EqE_UB
               (sum_prerel_c EqE_Debug EqE_Failure)))).

  Definition EqA_bot : postrel MCFGEbot MCFGEbot :=
    sum_postrel_c EqA_ExternalCall
      (sum_postrel_c EqA_OOM
         (sum_postrel_c EqA_Exc
            (sum_postrel_c EqA_UB
               (sum_postrel_c EqA_Debug EqA_Failure)))).

  Lemma EqE_MCFG_refl {A} (e : MCFGEtop A) : EqE_MCFG A A e e.
  Proof using.
    destruct_sum1 e; destruct e; cbn; auto.
  Qed.

  Lemma EqA_MCFG_refl {A} (e : MCFGEtop A) (a : A) : EqA_MCFG A A e a e a.
  Proof using.
    destruct_sum1 e; destruct e; cbn; try destruct a; reflexivity.
  Qed.

  Lemma EqE_CFG_refl {A} (e : CFGEtop A) : EqE_CFG A A e e.
  Proof using.
    destruct e as [c | m]; [destruct c; cbn; auto | apply EqE_MCFG_refl].
  Qed.

  Lemma EqE_bot_refl {A} (e : MCFGEbot A) : EqE_bot A A e e.
  Proof using.
    destruct_sum1 e; destruct e; cbn; auto.
  Qed.

  Lemma EqE_bot_trans {A B C} (e1 : MCFGEbot A) (e2 : MCFGEbot B) (e3 : MCFGEbot C) :
    EqE_bot A B e1 e2 -> EqE_bot B C e2 e3 -> EqE_bot A C e1 e3.
  Proof using.
    intros H12 H23; destruct_sum3 e1 e2 e3 H12 H23;
      destruct e1; destruct e2; destruct e3; cbn in *; try contradiction; intuition congruence.
  Qed.

  Lemma EqA_MCFG_eq {A} (e : MCFGEtop A) (a1 a2 : A) :
    EqA_MCFG A A e a1 e a2 -> a1 = a2.
  Proof using.
    destruct_sum1 e; destruct e; cbn;
      intros HA; match type of a1 with void => destruct a1 | _ => exact HA end.
  Qed.

  Lemma EqA_CFG_eq {A} (e : CFGEtop A) (a1 a2 : A) :
    EqA_CFG A A e a1 e a2 -> a1 = a2.
  Proof using.
    destruct e as [c | m]; [destruct c; cbn; intros HA; exact HA | apply EqA_MCFG_eq].
  Qed.

  Lemma EqA_bot_eq {A} (e : MCFGEbot A) (a1 a2 : A) :
    EqA_bot A A e a1 e a2 -> a1 = a2.
  Proof using.
    destruct_sum1 e; destruct e; cbn;
      intros HA; match type of a1 with void => destruct a1 | _ => exact HA end.
  Qed.

  Lemma EqA_bot_refl_diag {A B} (e1 : MCFGEbot A) (e2 : MCFGEbot B) (a : A) :
    EqE_bot A B e1 e2 ->
    exists b : B, EqA_bot A B e1 a e2 b.
  Proof using.
    intros HE; destruct_sum2 e1 e2 HE;
      destruct e1; destruct e2; cbn in HE |- *; try contradiction;
      match type of a with void => destruct a | _ => exists a; reflexivity end.
  Qed.

  Lemma EqA_bot_trans {A B C}
    (e1 : MCFGEbot A) (e2 : MCFGEbot B) (e3 : MCFGEbot C)
    (a1 : A) (a3 : C) :
    EqE_bot A B e1 e2 ->
    EqE_bot B C e2 e3 ->
    EqA_bot A C e1 a1 e3 a3 ->
    exists a2 : B, EqA_bot A B e1 a1 e2 a2 /\ EqA_bot B C e2 a2 e3 a3.
  Proof using.
    intros H12 H23 Ha13; destruct_sum3 e1 e2 e3 H12 H23;
      destruct e1; destruct e2; destruct e3; cbn in H12, H23, Ha13 |- *;
      try contradiction;
      match type of a1 with
      | void => destruct a1
      | _ => exists a3; split; [exact Ha13 | reflexivity]
      end.
  Qed.

  (** ** Cut-Aware [CFGtop] & [MCFGtop] Refinements *)

  Definition refine_cfg {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : CFGtop R1) (t2 : CFGtop R2) : Prop :=
    ruttc cutUB_rel cutNone EqE_CFG EqA_CFG RR t1 t2.

  Definition refine_mcfg {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : MCFGtop R1) (t2 : MCFGtop R2) : Prop :=
    ruttc cutUB_rel cutNone EqE_MCFG EqA_MCFG RR t1 t2.

  Lemma refine_cfg_refl {R} (t : CFGtop R) :
    refine_cfg Logic.eq t t.
  Proof using.
    revert t; ginit; gcofix CIH; intros t.
    destruct (observe t) eqn:Hot.
    - gstep; red; rewrite Hot; constructor; reflexivity.
    - gstep; red; rewrite Hot; constructor; gfinal; left; apply CIH.
    - gstep; red; rewrite Hot; constructor.
      + apply EqE_CFG_refl.
      + intros a1 a2 Ha; apply EqA_CFG_eq in Ha; subst a2.
        gfinal; left; apply CIH.
  Qed.

  Lemma refine_mcfg_refl {R} (t : MCFGtop R) :
    refine_mcfg Logic.eq t t.
  Proof using.
    revert t; ginit; gcofix CIH; intros t.
    destruct (observe t) eqn:Hot.
    - gstep; red; rewrite Hot; constructor; reflexivity.
    - gstep; red; rewrite Hot; constructor; gfinal; left; apply CIH.
    - gstep; red; rewrite Hot; constructor.
      + apply EqE_MCFG_refl.
      + intros a1 a2 Ha; apply EqA_MCFG_eq in Ha; subst a2.
        gfinal; left; apply CIH.
  Qed.

  Variant refine_EOU {A1 A2} (RR : A1 -> A2 -> Prop) : EOU A1 -> EOU A2 -> Prop :=
    | Refine_EOU_ret a1 a2 : RR a1 a2 -> refine_EOU RR (raise_ret a1) (raise_ret a2)
    | Refine_EOU_err s1 s2 : refine_EOU RR (raise_error s1) (raise_error s2)
    | Refine_EOU_oom s1 s2 : refine_EOU RR (raise_oom s1) (raise_oom s2)
    | Refine_EOU_ub s m2   : refine_EOU RR (raise_ub s) m2.

  Lemma refine_EOU_refl {A} (m : EOU A) :
    refine_EOU Logic.eq m m.
  Proof using.
    destruct m; constructor; reflexivity.
  Qed.

  Lemma refine_EOU_to_cfg {A1 A2} (RR : A1 -> A2 -> Prop) (m1 : EOU A1) (m2 : EOU A2) :
    refine_EOU RR m1 m2 ->
    refine_cfg RR (EOU_to_itree m1) (EOU_to_itree m2).
  Proof using.
    intros H; destruct H; cbn [EOU_to_itree].
    - apply ruttc_ret; assumption.
    - unfold raise, trigger_cast; eapply ruttc_trigger';
        [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
    - unfold raiseOOM, trigger_cast; eapply ruttc_trigger';
        [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
    - unfold raiseUB, trigger_cast; apply ruttc_trigger_cutl; exact (CutUB_rel (print_msg s)).
  Qed.

  Lemma refine_EOU_to_mcfg {A1 A2} (RR : A1 -> A2 -> Prop) (m1 : EOU A1) (m2 : EOU A2) :
    refine_EOU RR m1 m2 ->
    refine_mcfg RR (EOU_to_itree m1) (EOU_to_itree m2).
  Proof using.
    intros H; destruct H; cbn [EOU_to_itree].
    - apply ruttc_ret; assumption.
    - unfold raise, trigger_cast; eapply ruttc_trigger';
        [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
    - unfold raiseOOM, trigger_cast; eapply ruttc_trigger';
        [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
    - unfold raiseUB, trigger_cast; apply ruttc_trigger_cutl; exact (CutUB_rel (print_msg s)).
  Qed.

  Lemma unfold_run_exc_obs {A} (t : CFGtop A) :
    run_exc t ≅
      match observe t with
      | RetF a => Ret (inr a)
      | TauF u' => Tau (run_exc u')
      | VisF _ e k =>
          match exc_of_event e with
          | Some x => Ret (inl x)
          | None => Vis e (fun y => Tau (run_exc (k y)))
          end
      end.
  Proof using.
    unfold run_exc; rewrite unfold_iter.
    destruct (observe t) as [a | u' | X e k]; cbn.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - destruct (exc_of_event e) as [x |].
      + rewrite Eqit.bind_ret_l; reflexivity.
      + rewrite bind_vis; apply eqit_Vis; intros y; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma cutUB_exc_none {X} (e : CFGEtop X) :
    cutUB_rel e -> exc_of_event e = None.
  Proof using.
    intros Hcut; destruct Hcut; reflexivity.
  Qed.

  Lemma EqE_CFG_exc_of_event {A B} (e1 : CFGEtop A) (e2 : CFGEtop B) :
    EqE_CFG A B e1 e2 -> exc_of_event e1 = exc_of_event e2.
  Proof using.
    intros HE; destruct_sum2 e1 e2 HE;
      destruct e1; destruct e2; cbn in HE |- *; try contradiction; try reflexivity; subst; reflexivity.
  Qed.

  Lemma refine_cfg_run_exc {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : CFGtop R1) (t2 : CFGtop R2) :
    refine_cfg RR t1 t2 ->
    refine_cfg (sum_rel Logic.eq RR) (run_exc t1) (run_exc t2).
  Proof using.
    revert t1 t2; ginit; gcofix CIH; intros t1 t2 HR.
    rewrite 2 unfold_run_exc_obs.
    punfold HR; red in HR.
    induction HR; pclearbot.
    - gstep; constructor; constructor; assumption.
    - gstep; constructor; gfinal; left; apply CIH; assumption.
    - rewrite (EqE_CFG_exc_of_event e1 e2 H).
      destruct (exc_of_event e2) as [x |].
      + gstep; constructor; constructor; reflexivity.
      + gstep; constructor; [exact H |].
        intros a b Hab; gstep; constructor; gfinal; left; apply CIH, H0, Hab.
    - rewrite tau_euttge, unfold_run_exc_obs; exact IHHR.
    - rewrite tau_euttge, unfold_run_exc_obs; exact IHHR.
    - rewrite (cutUB_exc_none e H); gstep; constructor; exact H.
    - inversion H.
  Qed.

  Lemma refine_cfg_denote_function (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (Hproto : df_prototype df1 = df_prototype df2)
    (Hargs  : df_args df1 = df_args df2)
    (Hbody  : forall va, refine_cfg Logic.eq (denote_cfg (df_instrs df1) va)
                                             (denote_cfg (df_instrs df2) va)) :
    forall cc args,
      refine_cfg Logic.eq (denote_function df1 cc args) (denote_function df2 cc args).
  Proof using.
    intros cc args.
    unfold denote_function.
    rewrite Hproto.
    destruct (dc_param_attrs (df_prototype df2)) as [ret_attrs args_attrs].
    eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
    eapply ruttc_bind; [apply refine_cfg_refl | intros args' _ <-].
    eapply ruttc_bind; [unfold push_call_frame; rewrite Hargs; apply refine_cfg_refl | intros varg _ <-].
    eapply ruttc_bind.
    { eapply ruttc_weaken; cycle -1.
      - apply refine_cfg_run_exc; apply (Hbody (Some varg)).
      - auto.
      - auto.
      - auto.
      - auto.
      - intros r1 r2 [x1 x2 <- | y1 y2 <-]; reflexivity. }
    intros rv _ <-.
    eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
    apply refine_cfg_refl.
  Qed.

  Definition fn_ctx_refines (ctx1 ctx2 : IntMap function_denotation) : Prop :=
    forall k,
      option_rel (fun f1 f2 => forall cc args, refine_cfg Logic.eq (f1 cc args) (f2 cc args))
        (lookup k ctx1) (lookup k ctx2).

  Lemma cutUB_cfg_sum {A} (e : (CallE +' MCFGEtop) A) :
    cutUB_rel e <-> sum_pred1 (@FF1 CallE) (@cutUB_rel MCFGEtop _) A e.
  Proof using.
    split; intros H.
    - destruct H as [u]; constructor; exact (CutUB_rel u).
    - destruct H as [? ? [] | ? ? HC]; destruct HC as [u]; exact (CutUB_rel u).
  Qed.

  Lemma cutNone_cfg_sum {A} (e : (CallE +' MCFGEtop) A) :
    cutNone e <-> sum_pred1 (@FF1 CallE) (@cutNone MCFGEtop) A e.
  Proof using.
    split; intros H; [inversion H | destruct H as [? ? [] | ? ? HC]; inversion HC].
  Qed.

  Lemma refine_mcfg_denote_mcfg (ctx1 ctx2 : IntMap function_denotation)
    (dt : dtyp) (fv : dvalue) (args : list dvalue)
    (Hctx : fn_ctx_refines ctx1 ctx2) :
    refine_mcfg Logic.eq (denote_mcfg ctx1 dt fv args) (denote_mcfg ctx2 dt fv args).
  Proof using.
    unfold refine_mcfg, denote_mcfg.
    eapply ruttc_weaken with (Rcutl := cutUB_rel) (Rcutr := cutNone) (REv := EqE_MCFG) (RAns := EqA_MCFG); cycle -1.
    { eapply ruttc_mrec with (RCall := EqE_Call) (RCall' := EqA_Call).
      2: { cbn; auto. }
      intros A B [dt1 cc1 fv1 fas1] [dt2 cc2 fv2 fas2] HC.
      cbn in HC; destruct HC as (<- & <- & <- & <-).
      eapply ruttc_weaken with
        (Rcutl := cutUB_rel) (Rcutr := cutNone) (REv := EqE_CFG) (RAns := EqA_CFG)
        (RR := @Logic.eq (exc + dvalue)).
      { intros ? e Hcut; exact (proj1 (cutUB_cfg_sum e) Hcut). }
      { intros ? e Hcut; exact (proj1 (cutNone_cfg_sum e) Hcut). }
      { intros * HE; destruct e1 as [c1 | m1], e2 as [c2 | m2]; cbn in HE; try contradiction; constructor; exact HE. }
      { intros * HA; destruct HA; exact H. }
      { intros r1 r2 <-; cbn; reflexivity. }
      eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
      unfold lookup_defn.
      destruct fv1 as [[p | | | | | | |] | |]; try apply refine_cfg_refl.
      pose proof (Hctx (ptr_to_int p)) as Hlk.
      destruct (lookup (ptr_to_int p) ctx1) as [f1 |],
               (lookup (ptr_to_int p) ctx2) as [f2 |]; inversion Hlk; subst.
      - apply H1.
      - apply refine_cfg_refl. }
    all: cbn; auto.
  Qed.

  Lemma refine_mcfg_interp_intrinsics {R} (t1 t2 : MCFGtop R) :
    refine_mcfg Logic.eq t1 t2 ->
    refine_mcfg Logic.eq (interp_intrinsics t1) (interp_intrinsics t2).
  Proof using.
    intros HR.
    apply ruttc_interp_itree; auto.
    - intros A1 e1 Hcut; destruct Hcut as [u]; reflexivity.
    - intros A2 e2 Hcut; inversion Hcut.
    - intros A1 A2 e1 e2 HEv.
      destruct e1 as [e1 | e1], e2 as [e2 | e2]; cbn in HEv; try contradiction.
      + cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ E_trigger]; unfold trigger.
        apply ruttc_trigger; [cbn; exact HEv | intros a b Hab; exact Hab].
      + destruct e1 as [i1 | f1], e2 as [i2 | f2]; cbn in HEv; try contradiction.
        * destruct i1 as [dt1 fn1 args1 va1], i2 as [dt2 fn2 args2 va2].
          destruct HEv as (<- & <- & <- & <-).
          cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
          eapply ruttc_weaken; cycle -1; [apply refine_mcfg_refl | auto | auto | auto | auto |].
          intros r1 r2 <-; cbn; reflexivity.
        * cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger]; unfold trigger.
          apply ruttc_trigger; [cbn; exact HEv | intros a b Hab; exact Hab].
  Qed.

End EventRelations.

(** * 6. Provenance-Choice Model Semantics ([ProvE]) & [prog_refines] [PreOrder] *)

Variant ProvE : Type -> Type :=
  | FreshProv : ProvE N.

Section ModelSemantics.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  Existing Instance MemoryModelStateV.
  Existing Instance MemoryModelPrimitivesV.

  Definition ProvBotE : Type -> Type := ProvE +' (@MCFGEbot (@ParamsV IP IPT)).

  (** Collect all concrete provenance IDs occurring inside a [dvalue]. *)
  Definition ptr_provs (p : @ptr ProvenanceV (@PointerV IP)) : list N :=
    match snd p with
    | None => []
    | Some ps => ps
    end.

  Definition mem_bit_provs (b : @memory_bit (@ParamsV IP IPT)) : list N :=
    match b with
    | Bit_ptr p _ => ptr_provs p
    | Bit_psn | Bit_bit _ => []
    end.

  Definition dvalue_bv_provs {sz} (bv : @dvalue_bv (@ParamsV IP IPT) sz) : list N :=
    match bv with
    | BYTE_I _ => []
    | BYTE_Pointer p _ => ptr_provs p
    | BYTE_Mixed bits => flat_map mem_bit_provs bits
    end.

  Definition dvalue_base_provs (db : @dvalue_base (@ParamsV IP IPT)) : list N :=
    match db with
    | DVALUE_Pointer p => ptr_provs p
    | DVALUE_B _ bv => dvalue_bv_provs bv
    | _ => []
    end.

  Fixpoint dvalue_provs (dv : @dvalue (@ParamsV IP IPT)) : list N :=
    let fix list_provs (l : list (@dvalue (@ParamsV IP IPT))) : list N :=
      match l with
      | [] => []
      | x :: xs => dvalue_provs x ++ list_provs xs
      end
    in
    match dv with
    | DVALUE_Base db => dvalue_base_provs db
    | DVALUE_Struct _ fs => list_provs fs
    | DVALUE_Array _ es => list_provs es
    end.

  Definition bot_ans_provs {X} (e : @MCFGEbot (@ParamsV IP IPT) X) (a : X) : list N :=
    match e return X -> list N with
    | inl1 ec =>
        match ec in ExternalCallE Y return Y -> list N with
        | ExternalCall _ _ _ => dvalue_provs
        | IO_stdout _ => fun _ => []
        | IO_stderr _ => fun _ => []
        end
    | inr1 _ => fun _ => []
    end a.

  Lemma bot_ans_provs_eq {A B}
    (e1 : @MCFGEbot (@ParamsV IP IPT) A) (e2 : @MCFGEbot (@ParamsV IP IPT) B)
    (a1 : A) (a2 : B) :
    EqE_bot A B e1 e2 ->
    EqA_bot A B e1 a1 e2 a2 ->
    bot_ans_provs e1 a1 = bot_ans_provs e2 a2.
  Proof using.
    intros HE HA; destruct_sum2 e1 e2 HE;
      destruct e1; destruct e2; cbn in HE, HA |- *;
      try contradiction; subst; reflexivity.
  Qed.

  (** ** Model Memory & Fused Interpreter (Generalizing [interp_mcfg]) *)

  Fixpoint memM_interp_prov : @memM (@ParamsV IP IPT) _ ~> Monads.stateT state (itree ProvBotE) :=
    fun T m σ =>
      match m with
      | Mret x => Ret (σ, x)
      | Moom s => raiseOOM s
      | Mub s => raiseUB s
      | Merr s => raise s
      | Mget k => memM_interp_prov T (k σ) σ
      | Mput σ' k => memM_interp_prov T (k tt) σ'
      | Mchoose (Cnext_key _ align) k =>
          memM_interp_prov T
            (k (next_key_with_alignment σ.(state_memory_stack).(Memory_stack_memory) align))
            σ
      | Mchoose Cfresh_prov k =>
          ITree.bind (ITree.trigger (inl1 FreshProv)) (fun p =>
            memM_interp_prov T (k p)
              {| state_memory_stack := σ.(state_memory_stack);
                 state_provenance   := p |})
      | Mchoose Cexposed_prov k => memM_interp_prov T (k None) σ
      end.

  Arguments memM_interp_prov [T] _ _.

  Definition on_mem_prov {T} (f : Monads.stateT state (itree ProvBotE) T)
    : Monads.stateT FusedS (itree ProvBotE) T :=
    fun '(m, rest) => ITree.bind (f m) (fun '(m', r) => Ret ((m', rest), r)).

  Definition lift_bot_prov {T} (t : itree MCFGEbot T) : itree ProvBotE T :=
    translate inr1 t.

  Definition on_ls_prov {T} (f : Monads.stateT (stack_frame * stack) (itree MCFGEbot) T)
    : Monads.stateT FusedS (itree ProvBotE) T :=
    fun '(m, (ls, g)) =>
      ITree.bind (lift_bot_prov (f ls)) (fun '(ls', r) => Ret ((m, (ls', g)), r)).

  Definition on_genv_prov {T} (f : Monads.stateT global_env (itree MCFGEbot) T)
    : Monads.stateT FusedS (itree ProvBotE) T :=
    fun '(m, (ls, g)) =>
      ITree.bind (lift_bot_prov (f g)) (fun '(g', r) => Ret ((m, (ls, g')), r)).

  Definition fused_trigger_prov {F} `{F -< ProvBotE}
    : forall T, F T -> Monads.stateT FusedS (itree ProvBotE) T :=
    fun _ e s => ITree.bind (ITree.trigger (subevent _ e)) (fun r => Ret (s, r)).

  Definition fused_intrinsic_prov : IntrinsicE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_mem_prov (handle_intrinsic memM_interp_prov e).
  Definition fused_global_prov : GlobalE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_genv_prov (handle_global_debug e).
  Definition fused_local_prov : LocalE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_ls_prov (handle_local_stack handle_local_debug e).
  Definition fused_stack_prov : StackE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_ls_prov (handle_stack e).
  Definition fused_memory_prov : MemoryE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_mem_prov (handle_memory memM_interp_prov e).
  Definition fused_draw_prov : DrawE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e s => ITree.bind (lift_bot_prov (handle_draw e)) (fun r => Ret (s, r)).

  Definition interp_vellvm_prov_h : MCFGEtop ~> Monads.stateT FusedS (itree ProvBotE) :=
    case_ (fused_trigger_prov (F := ExternalCallE))
   (case_ fused_intrinsic_prov
   (case_ fused_global_prov
   (case_ (case_ fused_local_prov fused_stack_prov)
   (case_ fused_memory_prov
   (case_ fused_draw_prov
   (case_ (fused_trigger_prov (F := OOME))
   (case_ (fused_trigger_prov (F := LLVMExcE))
   (case_ (fused_trigger_prov (F := UBE))
   (case_ (fused_trigger_prov (F := DebugE))
          (fused_trigger_prov (F := FailureE))))))))))).

  Arguments interp_vellvm_prov_h [T] _ _.

  Definition interp_mcfg_model {R} (t : MCFGtop R) (s : FusedS) : itree ProvBotE (Res R) :=
    interp_state interp_vellvm_prov_h (interp_intrinsics t) s.

  Definition init_fused_state : FusedS :=
    (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).

  Definition run_mcfg_model (ret_typ : dtyp) (entry : function_id)
    (args : list dvalue) (M : CFG.mcfg dtyp) : itree ProvBotE (Res dvalue) :=
    interp_mcfg_model (denote_vellvm ret_typ entry args M) init_fused_state.

  (** ** Deterministic Specialization Equivalence ([interp_mcfg_model] -> [interp_mcfg]) *)

  Definition det_prov_h
    : ProvBotE ~> Monads.stateT N (itree (@MCFGEbot (@ParamsV IP IPT))) :=
    case_
      ((fun T (e : ProvE T) (pr : N) =>
          match e in ProvE Y return itree (@MCFGEbot (@ParamsV IP IPT)) (N * Y) with
          | FreshProv => let p' := N.succ pr in Ret (p', p')
          end) : ProvE ~> Monads.stateT N (itree (@MCFGEbot (@ParamsV IP IPT))))
      ((fun T (e : @MCFGEbot (@ParamsV IP IPT) T) (pr : N) =>
          ITree.bind (ITree.trigger e) (fun r => Ret (pr, r)))
       : @MCFGEbot (@ParamsV IP IPT) ~> Monads.stateT N (itree (@MCFGEbot (@ParamsV IP IPT)))).

  Lemma det_prov_h_inl1 (pr : N) :
    det_prov_h N (inl1 FreshProv) pr = Ret (N.succ pr, N.succ pr).
  Proof using. reflexivity. Qed.

  Lemma det_prov_h_inr1 {X} (e : @MCFGEbot (@ParamsV IP IPT) X) (pr : N) :
    det_prov_h X (inr1 e) pr = ITree.bind (ITree.trigger e) (fun r => Ret (pr, r)).
  Proof using. reflexivity. Qed.

  Local Opaque det_prov_h.

  Lemma interp_det_prov_lift_bot {R} (t : itree MCFGEbot R) (pr : N) :
    interp_state det_prov_h (lift_bot_prov t) pr ≈ ITree.map (fun r => (pr, r)) t.
  Proof using.
    unfold lift_bot_prov, ITree.map.
    revert t pr; ginit; gcofix CIH; intros t pr.
    destruct (observe t) as [rv | m | X e k] eqn:Hot.
    - gclo; econstructor; auto_ctrans_eq.
      + rewrite unfold_translate, Hot; cbn -[det_prov_h];
          rewrite interp_state_ret; reflexivity.
      + rewrite unfold_bind, Hot; cbn; reflexivity.
      + gstep; constructor; reflexivity.
    - gclo; econstructor; auto_ctrans_eq.
      + rewrite unfold_translate, Hot; cbn -[det_prov_h];
          rewrite interp_state_tau; reflexivity.
      + rewrite unfold_bind, Hot; cbn; reflexivity.
      + gstep; constructor; gfinal; left; exact (CIH m pr).
    - gclo; econstructor; auto_ctrans_eq.
      + rewrite unfold_translate, Hot; cbn -[det_prov_h].
        rewrite interp_state_vis, det_prov_h_inr1; unfold ITree.trigger.
        rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity.
      + rewrite unfold_bind, Hot; cbn; reflexivity.
      + gstep; constructor; intros x.
        gclo; econstructor; auto_ctrans_eq.
        * rewrite 2 Eqit.bind_ret_l; cbn [fst snd]; apply eqit_Tau_l; reflexivity.
        * reflexivity.
        * gfinal; left; exact (CIH (k x) pr).
  Qed.

  Local Transparent det_prov_h.

  Fixpoint memM_put_preserves_prov {R} (m : memM R) (σ : state) : Prop :=
    match m with
    | Mret _ | Moom _ | Mub _ | Merr _ => True
    | Mget k => memM_put_preserves_prov (k σ) σ
    | Mput σ' k =>
        σ'.(state_provenance) = σ.(state_provenance) /\
        memM_put_preserves_prov (k tt) σ'
    | Mchoose (Cnext_key _ align) k =>
        memM_put_preserves_prov
          (k (next_key_with_alignment σ.(state_memory_stack).(Memory_stack_memory) align)) σ
    | Mchoose Cfresh_prov k =>
        forall p,
          memM_put_preserves_prov (k p)
            {| state_memory_stack := σ.(state_memory_stack);
               state_provenance   := p |}
    | Mchoose Cexposed_prov k => memM_put_preserves_prov (k None) σ
    end.

  Definition memM_wf_prov {R} (m : memM R) : Prop :=
    forall σ, memM_put_preserves_prov m σ.

  Local Lemma memM_put_preserves_prov_bind {X Y}
    (m : memM X) (f : X -> memM Y) (σ : state)
    (Hm : memM_put_preserves_prov m σ)
    (Hf : forall x, memM_wf_prov (f x)) :
    memM_put_preserves_prov (ExtLib.Structures.Monad.bind m f) σ.
  Proof using.
    revert σ Hm; induction m as [x | s | s | s | k IH | σ' k IH | c k IH]; intros σ Hm; cbn in *.
    - exact (Hf x σ).
    - exact I.
    - exact I.
    - exact I.
    - exact (IH σ σ Hm).
    - destruct Hm as [Heq Hm']; exact (conj Heq (IH tt σ' Hm')).
    - destruct c as [sz align | |];
        [exact (IH _ σ Hm) | intros p; exact (IH p _ (Hm p)) | exact (IH None σ Hm)].
  Qed.

  Local Lemma memM_wf_prov_bind {X Y}
    (m : memM X) (f : X -> memM Y)
    (Hm : memM_wf_prov m) (Hf : forall x, memM_wf_prov (f x)) :
    memM_wf_prov (ExtLib.Structures.Monad.bind m f).
  Proof using.
    intros σ; exact (memM_put_preserves_prov_bind m f σ (Hm σ) Hf).
  Qed.

  Local Lemma memM_wf_prov_ret {X} (x : X) :
    memM_wf_prov (ExtLib.Structures.Monad.ret x).
  Proof using.
    intros σ; exact I.
  Qed.

  Local Lemma memM_wf_prov_lift {X} (c : EOU X) :
    memM_wf_prov (Vellvm.Semantics.Interfaces.Memory.lift c).
  Proof using.
    destruct c; intros σ; exact I.
  Qed.

  Local Lemma memM_wf_prov_loop_monad {A B} (f : A -> memM B) (l : list A)
    (Hf : forall a, memM_wf_prov (f a)) :
    memM_wf_prov (loop_monad f l).
  Proof using.
    induction l as [| a l' IH]; cbn [loop_monad];
      [apply memM_wf_prov_ret
      | apply memM_wf_prov_bind; [exact (Hf a) | intros _; exact IH]].
  Qed.

  Local Lemma memM_wf_prov_map_monad {A B} (f : A -> memM B) (l : list A)
    (Hf : forall a, memM_wf_prov (f a)) :
    memM_wf_prov (map_monad f l).
  Proof using.
    induction l as [| a l' IH]; cbn [map_monad]; [apply memM_wf_prov_ret |].
    apply memM_wf_prov_bind; [exact (Hf a) | intros b].
    apply memM_wf_prov_bind; [exact IH | intros bs; apply memM_wf_prov_ret].
  Qed.

  Local Lemma memM_wf_prov_map_monad_acc {A B} (f : A -> memM B) (l : list A)
    (Hf : forall a, memM_wf_prov (f a)) :
    memM_wf_prov (map_monad_acc f l).
  Proof using.
    unfold map_monad_acc.
    lazymatch goal with
    | |- memM_wf_prov (?go [] l) =>
        cut (forall acc : list B, memM_wf_prov (go acc l)); [intros H; exact (H []) |]
    end.
    induction l as [| a l' IH]; intros acc;
      [apply memM_wf_prov_ret
      | apply memM_wf_prov_bind; [exact (Hf a) | intros b; exact (IH (b :: acc))]].
  Qed.

  Local Lemma Read_byte_wf_prov (p : ptr) :
    memM_wf_prov (Read_byte p).
  Proof using.
    unfold Read_byte, read_byte_raw; cbn zeta; apply memM_wf_prov_bind.
    - intros σ;
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind get
             ExtLib.Structures.Monad.ret memM_put_preserves_prov];
        destruct (read_byte_raw_mem _ _); exact I.
    - intros [b0 aid]; destruct (access_allowed _ _); intros σ; exact I.
  Qed.

  Local Lemma Write_byte_wf_prov (p : ptr) (b : memory_byte) :
    memM_wf_prov (Write_byte p b).
  Proof using.
    unfold Write_byte, read_byte_raw; cbn zeta; apply memM_wf_prov_bind.
    - intros σ;
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind get
             ExtLib.Structures.Monad.ret memM_put_preserves_prov];
        destruct (read_byte_raw_mem _ _); exact I.
    - intros [b0 aid]; destruct (access_allowed _ _); [| intros σ; exact I].
      unfold set_byte_raw; apply memM_wf_prov_bind;
        [intros σ; exact I | intros m0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma get_free_block_wf_prov (size align : N) (pr : provenance) :
    memM_wf_prov (get_free_block size align pr).
  Proof using.
    unfold get_free_block; cbn zeta;
      apply memM_wf_prov_bind; [intros σ; exact I | intros addr].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros p].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros ptrs; apply memM_wf_prov_ret].
  Qed.

  Local Lemma add_block_wf_prov (aid : allocationId) (p : ptr) (ptrs : list ptr) (init_bytes : list memory_byte) :
    memM_wf_prov (add_block aid p ptrs init_bytes).
  Proof using.
    unfold add_block; cbn zeta.
    apply memM_wf_prov_bind; [intros σ; exact I | intros m0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma Allocate_bytes_with_pr_wf_prov (init_bytes : list memory_byte) (align : N) (pr : provenance) :
    memM_wf_prov (Allocate_bytes_with_pr init_bytes align pr).
  Proof using.
    unfold Allocate_bytes_with_pr; cbn zeta.
    apply memM_wf_prov_bind; [apply get_free_block_wf_prov | intros [p ptrs]].
    apply memM_wf_prov_bind; [| intros u0; apply memM_wf_prov_ret].
    unfold add_block_to_stack, add_ptrs_to_frame.
    apply memM_wf_prov_bind; [apply add_block_wf_prov | intros u0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma Malloc_bytes_with_pr_wf_prov (init_bytes : list memory_byte) (align : N) (pr : provenance) :
    memM_wf_prov (Malloc_bytes_with_pr init_bytes align pr).
  Proof using.
    unfold Malloc_bytes_with_pr; cbn zeta.
    apply memM_wf_prov_bind; [apply get_free_block_wf_prov | intros [p ptrs]].
    apply memM_wf_prov_bind; [| intros u0; apply memM_wf_prov_ret].
    unfold add_block_to_heap, add_ptrs_to_heap.
    apply memM_wf_prov_bind; [apply add_block_wf_prov | intros u0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma Mempop_wf_prov :
    memM_wf_prov Mempop.
  Proof using.
    unfold Mempop; apply memM_wf_prov_bind.
    - unfold get_frame; apply memM_wf_prov_bind;
        [intros σ; exact I | intros [f0 | s0 f0]; apply memM_wf_prov_ret].
    - intros f; apply memM_wf_prov_bind.
      + unfold app_frame_stack_eob; apply memM_wf_prov_bind; [intros σ; exact I | intros fs].
        apply memM_wf_prov_bind;
          [apply memM_wf_prov_lift | intros fs' σ; exact (conj Logic.eq_refl I)].
      + intros u0 σ; exact (conj Logic.eq_refl I).
  Qed.

  Local Lemma Free_wf_prov (p : ptr) :
    memM_wf_prov (Free p).
  Proof using.
    unfold Free; cbn zeta; apply memM_wf_prov_bind; [intros σ; exact I | intros h].
    lazymatch goal with
    | |- memM_wf_prov match ?e with _ => _ end => destruct e as [blk |]
    end; [| intros σ; exact I].
    cbn zeta; apply memM_wf_prov_bind;
      [intros σ; exact (conj Logic.eq_refl I) | intros u0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma read_bytes_wf_prov (p : ptr) (size : N) :
    memM_wf_prov (read_bytes p size).
  Proof using.
    unfold read_bytes; cbn [read_byte MemoryModelPrimitivesV].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros ptrs].
    apply memM_wf_prov_map_monad_acc, Read_byte_wf_prov.
  Qed.

  Local Lemma write_bytes_wf_prov (p : ptr) (bytes : list memory_byte) :
    memM_wf_prov (write_bytes p bytes).
  Proof using.
    unfold write_bytes; cbn zeta; cbn [write_byte MemoryModelPrimitivesV].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros ptrs].
    apply memM_wf_prov_loop_monad; intros [q b]; exact (Write_byte_wf_prov q b).
  Qed.

  Local Lemma convert_impure_base_wf_prov
    (conv : impure_conversion) (tf : dtyp_base) (dv : dvalue_base) (tt0 : dtyp_base) :
    memM_wf_prov (convert_impure_base conv tf dv tt0).
  Proof using.
    unfold convert_impure_base; destruct conv.
    - apply memM_wf_prov_bind.
      + unfold assert_inttoptr_types_ok; destruct tf, tt0; intros σ; exact I.
      + intros u0; destruct dv; apply memM_wf_prov_lift.
    - destruct dv, tt0; try apply memM_wf_prov_lift; intros σ; exact I.
    - destruct dv, tt0; try apply memM_wf_prov_lift; intros σ; exact I.
    - intros σ; exact I.
  Qed.

  Local Lemma convert_impure_wf_prov
    (conv : impure_conversion) (tf : dtyp) (dv : dvalue) (tt0 : dtyp) :
    memM_wf_prov (convert_impure conv tf dv tt0).
  Proof using.
    unfold convert_impure; destruct dv as [db | ? ? | vc elts]; try (intros σ; exact I).
    - destruct (get_base_conversion_type tf tt0) as [[tf' tt'] |]; [| intros σ; exact I].
      cbn [Functor.fmap Functor_Monad].
      apply memM_wf_prov_bind; [apply convert_impure_base_wf_prov | intros db'; apply memM_wf_prov_ret].
    - destruct vc; [| intros σ; exact I].
      destruct (get_vector_conversion_type tf tt0) as [[tf' tt'] |]; [| intros σ; exact I].
      apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros elts'].
      apply memM_wf_prov_bind.
      + apply memM_wf_prov_map_monad; intros v; apply convert_impure_base_wf_prov.
      + intros val; apply memM_wf_prov_ret.
  Qed.

  Local Lemma handle_memoryM_wf_prov {T} (e : MemoryE T) :
    memM_wf_prov (handle_memoryM e).
  Proof using.
    destruct e as [| | dt n al | dt a | dt a v | ct tf v tt0]; cbn [handle_memoryM].
    - intros σ; exact (conj Logic.eq_refl I).
    - exact Mempop_wf_prov.
    - cbn zeta; apply memM_wf_prov_bind; [| intros p; apply memM_wf_prov_ret].
      unfold allocate_dtyp; destruct (dtyp_eqb dt DTYPE_Void); [intros σ; exact I |].
      cbn zeta; unfold allocate_bytes; cbn [allocate_bytes_with_pr MemoryModelPrimitivesV].
      apply memM_wf_prov_bind; [intros σ p; exact I | intros pr; apply Allocate_bytes_with_pr_wf_prov].
    - destruct a as [[p | | | | | | |] | |]; try (intros σ; exact I).
      unfold read_dvalue; apply memM_wf_prov_bind;
        [apply read_bytes_wf_prov | intros bs; apply memM_wf_prov_lift].
    - destruct a as [[p | | | | | | |] | |]; try (intros σ; exact I).
      unfold write_dvalue; apply memM_wf_prov_bind;
        [apply memM_wf_prov_lift | intros bs; apply write_bytes_wf_prov].
    - apply convert_impure_wf_prov.
  Qed.

  Local Lemma handle_memtransfer_wf_prov (overlap_ok : bool) (args : list dvalue_base) :
    memM_wf_prov (handle_memtransfer overlap_ok args).
  Proof using.
    unfold handle_memtransfer; cbn zeta.
    destruct args as [| dst [| src [| len [| vol rest]]]]; try (intros σ; exact I).
    destruct vol, rest; try (intros σ; exact I).
    apply memM_wf_prov_bind.
    - destruct len; intros σ; exact I.
    - intros size; destruct dst, src; try (intros σ; exact I);
        try (destruct (size =? 0)%N; intros σ; exact I).
      destruct overlap_ok.
      + unfold memmove; apply memM_wf_prov_bind;
          [apply read_bytes_wf_prov | intros bs; apply write_bytes_wf_prov].
      + unfold memcpy; destruct (orb _ _); [| intros σ; exact I].
        apply memM_wf_prov_bind;
          [apply read_bytes_wf_prov | intros bs; apply write_bytes_wf_prov].
  Qed.

  Local Lemma handle_memset_wf_prov (args : list dvalue_base) :
    memM_wf_prov (handle_memset args).
  Proof using.
    unfold handle_memset.
    destruct args as [| dst [| val [| len [| vol rest]]]]; try (intros σ; exact I).
    destruct vol, rest; try (intros σ; exact I).
    apply memM_wf_prov_bind.
    - destruct val; try (intros σ; exact I).
      destruct (Pos.eqb _ 8); intros σ; exact I.
    - intros byte; apply memM_wf_prov_bind.
      + destruct len; intros σ; exact I.
      + intros size; destruct dst; try (intros σ; exact I).
        * unfold memset; apply write_bytes_wf_prov.
        * destruct (size =? 0)%N; intros σ; exact I.
  Qed.

  Local Lemma handle_malloc_wf_prov (args : list dvalue_base) (align : N) :
    memM_wf_prov (handle_malloc args align).
  Proof using.
    unfold handle_malloc.
    destruct args as [| a0 rest]; [intros σ; exact I |].
    destruct a0, rest; try (intros σ; exact I);
      (unfold malloc_bytes; cbn [malloc_bytes_with_pr MemoryModelPrimitivesV];
       apply memM_wf_prov_bind; [intros σ p; exact I | intros pr; apply Malloc_bytes_with_pr_wf_prov]).
  Qed.

  Local Lemma handle_free_wf_prov (args : list dvalue_base) :
    memM_wf_prov (handle_free args).
  Proof using.
    unfold handle_free; cbn [free MemoryModelPrimitivesV].
    destruct args as [| a0 rest]; [intros σ; exact I |].
    destruct a0, rest; try (intros σ; exact I).
    destruct (_ =? _)%Z; [apply memM_wf_prov_ret | apply Free_wf_prov].
  Qed.

  Local Lemma handle_intrinsicM_wf_prov {T} (e : IntrinsicE T) :
    memM_wf_prov (handle_intrinsicM e).
  Proof using.
    destruct e as [t name args ?]; cbn [handle_intrinsicM].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros args'].
    destruct (is_memcpy_name name);
      [apply memM_wf_prov_bind;
       [apply handle_memtransfer_wf_prov | intros r; apply memM_wf_prov_ret] |].
    destruct (is_memmove_name name);
      [apply memM_wf_prov_bind;
       [apply handle_memtransfer_wf_prov | intros r; apply memM_wf_prov_ret] |].
    destruct (is_memset_name name);
      [apply memM_wf_prov_bind;
       [apply handle_memset_wf_prov | intros r; apply memM_wf_prov_ret] |].
    destruct (Numeric.Rocqlib.proj_sumbool (string_dec name "malloc"));
      [apply memM_wf_prov_bind;
       [apply handle_malloc_wf_prov | intros r; apply memM_wf_prov_ret] |].
    destruct (Numeric.Rocqlib.proj_sumbool (string_dec name "free"));
      [apply memM_wf_prov_bind;
       [apply handle_free_wf_prov | intros r; apply memM_wf_prov_ret]
      | intros σ; exact I].
  Qed.

  Lemma memM_interp_prov_det {R} (m : memM R) (σ : state)
    (Hwf : memM_put_preserves_prov m σ) :
    interp_state det_prov_h (memM_interp_prov m σ) σ.(state_provenance) ≈
      ITree.map (fun '(σ', r) => (σ'.(state_provenance), (σ', r))) (memM_interp m σ).
  Proof using.
    revert σ Hwf; induction m as [x | s | s | s | k IH | σ' k IH | c k IH]; intros σ Hwf;
      cbn [memM_interp_prov memM_interp memM_put_preserves_prov
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree] in Hwf |- *.
    - rewrite interp_state_ret; unfold ITree.map; rewrite Eqit.bind_ret_l; reflexivity.
    - unfold raiseOOM, trigger_cast, ITree.map;
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; apply eqit_Vis; intros [].
    - unfold raiseUB, trigger_cast, ITree.map;
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; apply eqit_Vis; intros [].
    - unfold raise, trigger_cast, ITree.map;
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; apply eqit_Vis; intros [].
    - exact (IH σ σ Hwf).
    - destruct Hwf as [Heq Hwf']; rewrite <- Heq; exact (IH tt σ' Hwf').
    - destruct c as [sz align | |];
        cbn [memM_interp_prov memM_interp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      + exact (IH _ σ Hwf).
      + rewrite interp_state_bind, interp_state_trigger, det_prov_h_inl1, Eqit.bind_ret_l.
        unfold fresh_provenance, ITree.map;
          cbn [next_provenance ProvenanceV MemoryModelPrimitivesV ParamsV
               ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        rewrite Eqit.bind_bind, Eqit.bind_ret_l.
        exact (IH (N.succ (state_provenance σ))
                  {| state_memory_stack := state_memory_stack σ;
                     state_provenance   := N.succ (state_provenance σ) |}
                  (Hwf (N.succ (state_provenance σ)))).
      + exact (IH None σ Hwf).
  Qed.

  Lemma interp_vellvm_prov_h_det {T} (e : MCFGEtop T) (s : FusedS) :
    interp_state det_prov_h (interp_vellvm_prov_h e s) (fst s).(state_provenance) ≈
      ITree.map (fun '(s', r) => ((fst s').(state_provenance), (s', r))) (interp_vellvm_h e s).
  Proof using.
    destruct s as [m [[sf stk] g]]; cbn [fst].
    unfold interp_vellvm_prov_h, interp_vellvm_h.
    destruct_sum1 e; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
    - (* ExternalCallE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* IntrinsicE *)
      unfold fused_intrinsic_prov, fused_intrinsic, on_mem_prov, on_mem, handle_intrinsic;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, (memM_interp_prov_det _ _ (handle_intrinsicM_wf_prov e m)).
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [m' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* GlobalE *)
      unfold fused_global_prov, fused_global, on_genv_prov, on_genv;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, interp_det_prov_lift_bot.
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [g' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* LocalE *)
      unfold fused_local_prov, fused_local, on_ls_prov, on_ls;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, interp_det_prov_lift_bot.
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [ls' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* StackE *)
      unfold fused_stack_prov, fused_stack, on_ls_prov, on_ls;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, interp_det_prov_lift_bot.
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [ls' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* MemoryE *)
      unfold fused_memory_prov, fused_memory, on_mem_prov, on_mem, handle_memory;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, (memM_interp_prov_det _ _ (handle_memoryM_wf_prov e m)).
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [m' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* DrawE *)
      unfold fused_draw_prov, fused_draw;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, interp_det_prov_lift_bot.
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros r; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* OOME *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* LLVMExcE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* UBE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* DebugE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* FailureE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
  Qed.

  Local Opaque det_prov_h.

  Lemma interp_vellvm_prov_h_det_rel {T} (e : MCFGEtop T) (s : FusedS) :
    eutt (fun '(pr', sx1) (sx2 : FusedS * T) => pr' = (fst (fst sx2)).(state_provenance) /\ sx1 = sx2)
      (interp_state det_prov_h (interp_vellvm_prov_h e s) (fst s).(state_provenance))
      (interp_vellvm_h e s).
  Proof using.
    rewrite interp_vellvm_prov_h_det; unfold ITree.map.
    bind_ret_r2_eutt.
    eapply Eqit.eqit_bind'; [reflexivity |].
    intros [s' r] ? <-; apply Eqit.eqit_Ret; split; reflexivity.
  Qed.

  Theorem interp_mcfg_model_det {R} (t : MCFGtop R) (s : FusedS) :
    ITree.map snd (interp_state det_prov_h (interp_mcfg_model t s) (fst s).(state_provenance)) ≈
      interp_mcfg t s.
  Proof using.
    unfold interp_mcfg_model, interp_mcfg, ITree.map.
    generalize (interp_intrinsics t) as u; intros u.
    revert u s; ginit; gcofix CIH; intros u s.
    destruct (observe u) as [rv | m | X e k] eqn:Hou.
    - assert (Hu : u ≅ Ret rv) by (rewrite (itree_eta u), Hou; reflexivity).
      gclo; econstructor; auto_ctrans_eq.
      + rewrite Hu, 2 interp_state_ret, Eqit.bind_ret_l; reflexivity.
      + rewrite Hu, interp_state_ret; reflexivity.
      + gstep; constructor; reflexivity.
    - assert (Hu : u ≅ Tau m) by (rewrite (itree_eta u), Hou; reflexivity).
      gclo; econstructor; auto_ctrans_eq.
      + rewrite Hu, 2 interp_state_tau, Eqit.bind_tau; reflexivity.
      + rewrite Hu, interp_state_tau; reflexivity.
      + gstep; constructor; gfinal; left; exact (CIH m s).
    - assert (Hu : u ≅ Vis e k) by (rewrite (itree_eta u), Hou; reflexivity).
      gclo; econstructor; auto_ctrans_eq.
      + rewrite Hu, interp_state_vis;
          cbn [ExtLib.Structures.Monad.bind Monad_itree];
          rewrite interp_state_bind, Eqit.bind_bind; reflexivity.
      + rewrite Hu, interp_state_vis;
          cbn [ExtLib.Structures.Monad.bind Monad_itree]; reflexivity.
      + guclo eqit_clo_bind; econstructor.
        * exact (interp_vellvm_prov_h_det_rel e s).
        * intros [pr' [s' x]] [s2 x2] [-> Hsx]; inversion Hsx; subst s2 x2; clear Hsx; cbn [fst snd].
          gclo; econstructor; auto_ctrans_eq.
          -- rewrite interp_state_tau, Eqit.bind_tau; reflexivity.
          -- reflexivity.
          -- gstep; constructor; gfinal; left; exact (CIH (k x) s').
  Qed.

  (** ** Coinductive Provenance-Elastic Refinement ([refine_prov]) *)

  Definition is_ub_bot {X} (e : MCFGEbot X) : bool :=
    match e with
    | inr1 (inl1 (ThrowOOM _)) => true
    | inr1 (inr1 (inr1 (inl1 (ThrowUB _)))) => true
    | _ => false
    end.

  Definition is_ub_prov {X} (e : ProvBotE X) : bool :=
    match e with
    | inl1 _ => false
    | inr1 b => is_ub_bot b
    end.

  Lemma EqE_bot_is_ub {A B} (b1 : MCFGEbot A) (b2 : MCFGEbot B) :
    EqE_bot A B b1 b2 -> is_ub_bot b1 = is_ub_bot b2.
  Proof using.
    intros HE; destruct_sum2 b1 b2 HE;
      destruct b1; destruct b2; reflexivity.
  Qed.

  Definition match_vis_both {R1 R2}
    (r : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop)
    (U : list N)
    {X1} (e1 : ProvBotE X1) (k1 : X1 -> itree ProvBotE R1)
    {X2} (e2 : ProvBotE X2) (k2 : X2 -> itree ProvBotE R2) : Prop :=
    match e1 return (X1 -> itree ProvBotE R1) -> Prop with
    | inl1 p1 => fun k1' =>
        match e2 return (X2 -> itree ProvBotE R2) -> Prop with
        | inl1 p2 => fun k2' =>
            match p1 in ProvE Y1 return (Y1 -> itree ProvBotE R1) -> Prop with
            | FreshProv => fun k1'' =>
                match p2 in ProvE Y2 return (Y2 -> itree ProvBotE R2) -> Prop with
                | FreshProv => fun k2'' =>
                    forall p : N, ~ In p U -> r (p :: U) (k1'' p) (k2'' p)
                end k2'
            end k1'
        | inr1 _ => fun _ => False
        end k2
    | inr1 b1 => fun k1' =>
        match e2 return (X2 -> itree ProvBotE R2) -> Prop with
        | inl1 _ => fun _ => False
        | inr1 b2 => fun k2' =>
            EqE_bot _ _ b1 b2 /\
            forall a1 a2, EqA_bot _ _ b1 a1 b2 a2 ->
              r (bot_ans_provs b1 a1 ++ U) (k1' a1) (k2' a2)
        end k2
    end k1.

  Definition rp_step_body {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop)
    (U : list N)
    (ot1 : itree' ProvBotE R1) (ot2 : itree' ProvBotE R2) (t2 : itree ProvBotE R2) : Prop :=
    match ot1 with
    | RetF r1 =>
        match ot2 with
        | RetF r2 => RR U r1 r2
        | _ => False
        end
    | TauF m1 =>
        match ot2 with
        | TauF m2 => r U m1 m2
        | _ => False
        end
    | VisF _ e1 k1 =>
        is_ub_prov e1 = true
        \/ (match e1 with
            | inl1 p1 =>
                match p1 in ProvE Y1 return (Y1 -> itree ProvBotE R1) -> Prop with
                | FreshProv => fun k1' =>
                    forall p : N, ~ In p U -> r (p :: U) (k1' p) t2
                end
            | inr1 _ => fun _ => False
            end k1)
        \/ (match ot2 with
            | VisF _ e2 k2 => match_vis_both r U e1 k1 e2 k2
            | _ => False
            end)
    end.

  Inductive refine_prov_ {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop)
    : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop :=
  | RP_Step U t1 t2 :
      rp_step_body RR r U (observe t1) (observe t2) t2 ->
      refine_prov_ RR r U t1 t2
  | RP_TauL U t1 m1 t2 :
      observe t1 = TauF m1 ->
      refine_prov_ RR r U m1 t2 ->
      refine_prov_ RR r U t1 t2
  | RP_TauR U t1 t2 m2 :
      observe t2 = TauF m2 ->
      refine_prov_ RR r U t1 m2 ->
      refine_prov_ RR r U t1 t2.

  Lemma refine_prov__mon {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    monotone3 (refine_prov_ RR).
  Proof using.
    intros U t1 t2 r r' IN LE.
    induction IN as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH].
    - apply RP_Step.
      unfold rp_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + exact Hstep.
      + destruct (observe t2); [exact Hstep | apply LE, Hstep | exact Hstep].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left.
          destruct e1 as [p1 | b1]; [| contradiction].
          destruct p1; intros p Hp; apply LE, Hleft, Hp.
        * right; right.
          destruct (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; apply LE, Hboth, Hp.
          -- destruct Hboth as [HE HA]; split; [exact HE | intros a1 a2 Ha; apply LE, HA, Ha].
    - eapply RP_TauL; [exact Ht1 | exact IH].
    - eapply RP_TauR; [exact Ht2 | exact IH].
  Qed.
  #[local] Hint Resolve refine_prov__mon : paco.

  Definition refine_prov {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) : Prop :=
    paco3 (refine_prov_ RR) bot3 U t1 t2.

  Lemma refine_prov_antitone {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (HRR : forall U U' r1 r2, incl U U' -> RR U r1 r2 -> RR U' r1 r2) :
    forall U U' t1 t2,
      incl U U' ->
      refine_prov RR U t1 t2 ->
      refine_prov RR U' t1 t2.
  Proof using.
    pcofix CIH.
    intros U U' t1 t2 Hincl Hrel.
    pstep; punfold Hrel.
    revert U' Hincl; induction Hrel as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH];
      intros U' Hincl.
    - apply RP_Step; unfold rp_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + destruct (observe t2); try contradiction; eapply HRR; eassumption.
      + destruct (observe t2); try contradiction; pclearbot; right; eapply CIH; eassumption.
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp.
          assert (HpU : ~ In p U) by (intros Hx; apply Hp, Hincl, Hx).
          specialize (Hleft p HpU); pclearbot; right; eapply CIH; [| exact Hleft].
          intros z [<- | Hz]; [left; reflexivity | right; apply Hincl, Hz].
        * right; right; destruct (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp.
             assert (HpU : ~ In p U) by (intros Hx; apply Hp, Hincl, Hx).
             specialize (Hboth p HpU); pclearbot; right; eapply CIH; [| exact Hboth].
             intros z [<- | Hz]; [left; reflexivity | right; apply Hincl, Hz].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot; right; eapply CIH; [| exact HA].
             intros z Hz; apply in_app_iff in Hz; apply in_app_iff.
             destruct Hz as [Hz | Hz]; [left; exact Hz | right; apply Hincl, Hz].
    - eapply RP_TauL; [exact Ht1 | apply IH, Hincl].
    - eapply RP_TauR; [exact Ht2 | apply IH, Hincl].
  Qed.

  Lemma refine_prov_inv_Tau_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    U (m1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    refine_prov RR U (Tau m1) t2 ->
    refine_prov RR U m1 t2.
  Proof using.
    intros H; punfold H.
    remember (Tau m1) as tm1 eqn:Etm1.
    assert (Hot1 : observe tm1 = TauF m1) by (subst tm1; reflexivity).
    clear Etm1.
    revert m1 Hot1; induction H as [U t1 t2 Hstep | U t1 m1' t2 Ht1 Hrel _ | U t1 t2 m2 Ht2 _ IH];
      intros m1 Hot1.
    - unfold rp_step_body in Hstep; rewrite Hot1 in Hstep.
      destruct (observe t2) as [x2 | m2 | X2 e2 k2] eqn:Hot2; try contradiction.
      pclearbot; punfold Hstep.
      pstep; eapply RP_TauR; [exact Hot2 | eapply refine_prov__mon; [exact Hstep | auto]].
    - rewrite Hot1 in Ht1; inversion Ht1; subst m1'.
      pstep; eapply refine_prov__mon; [exact Hrel | auto].
    - specialize (IH m1 Hot1); punfold IH.
      pstep; eapply RP_TauR; [exact Ht2 | eapply refine_prov__mon; [exact IH | auto]].
  Qed.

  Lemma observe_bind {E : Type -> Type} {R S : Type}
    (t : itree E R) (k : R -> itree E S) :
    observe (ITree.bind t k) =
      match observe t with
      | RetF r => observe (k r)
      | TauF m => TauF (ITree.bind m k)
      | VisF _ e h => VisF e (fun x => ITree.bind (h x) k)
      end.
  Proof using.
    unfold ITree.bind, ITree.subst; unfold observe at 1; cbn.
    destruct (observe t); reflexivity.
  Qed.

  Lemma observe_translate {E F : Type -> Type} {R : Type}
    (h : E ~> F) (t : itree E R) :
    observe (translate h t) =
      match observe t with
      | RetF r => RetF r
      | TauF m => TauF (translate h m)
      | VisF _ e k => VisF (h _ e) (fun x => translate h (k x))
      end.
  Proof using.
    unfold translate; unfold observe at 1; cbn; destruct (observe t); reflexivity.
  Qed.

  Lemma eqitF_inv_Ret_l {E : Type -> Type} {R1 R2 : Type}
    {RR : R1 -> R2 -> Prop}
    {vsim : (itree E R1 -> itree E R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop}
    {sim : itree E R1 -> itree E R2 -> Prop}
    (r1 : R1) (ot2 : itree' E R2) :
    eqitF RR false false vsim sim (RetF r1) ot2 ->
    exists r2 : R2, ot2 = RetF r2 /\ RR r1 r2.
  Proof using.
    intros H.
    change (match RetF r1 : itree' E R1 with
            | RetF x1 => exists r2 : R2, ot2 = RetF r2 /\ RR x1 r2
            | _ => True
            end).
    generalize (RetF r1 : itree' E R1) H; clear H; intros ot1 H.
    destruct H as [x1 x2 Hrr | | | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; cbn; try exact I.
    exists x2; split; [reflexivity | exact Hrr].
  Qed.

  Lemma eqitF_inv_Tau_l {E : Type -> Type} {R1 R2 : Type}
    {RR : R1 -> R2 -> Prop}
    {vsim : (itree E R1 -> itree E R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop}
    {sim : itree E R1 -> itree E R2 -> Prop}
    (m1 : itree E R1) (ot2 : itree' E R2) :
    eqitF RR false false vsim sim (TauF m1) ot2 ->
    exists m2 : itree E R2, ot2 = TauF m2 /\ sim m1 m2.
  Proof using.
    intros H.
    change (match TauF m1 : itree' E R1 with
            | TauF u1 => exists m2 : itree E R2, ot2 = TauF m2 /\ sim u1 m2
            | _ => True
            end).
    generalize (TauF m1 : itree' E R1) H; clear H; intros ot1 H.
    destruct H as [| u1 u2 Hsim | | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; cbn; try exact I.
    exists u2; split; [reflexivity | exact Hsim].
  Qed.

  Lemma eqitF_inv_Vis_l {E : Type -> Type} {R1 R2 : Type}
    {RR : R1 -> R2 -> Prop}
    {sim : itree E R1 -> itree E R2 -> Prop}
    {X : Type} (e : E X) (k1 : X -> itree E R1) (ot2 : itree' E R2) :
    eqitF RR false false id sim (VisF e k1) ot2 ->
    exists k2 : X -> itree E R2,
      ot2 = VisF e k2 /\ forall x : X, sim (k1 x) (k2 x).
  Proof using.
    intros H.
    change (match VisF e k1 : itree' E R1 with
            | VisF Y e1 h1 =>
                exists k2 : Y -> itree E R2,
                  ot2 = VisF e1 k2 /\ forall x : Y, sim (h1 x) (k2 x)
            | _ => True
            end).
    generalize (VisF e k1 : itree' E R1) H; clear H; intros ot1 H.
    destruct H as [| | Y e0 h1 h2 Hrel | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; cbn; try exact I.
    exists h2; split; [reflexivity | exact Hrel].
  Qed.

  Lemma refine_prov__obs_eq {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r r' : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop)
    (Hr_eq : forall U a1 a1' a2 a2',
               a1 ≅ a1' -> a2 ≅ a2' -> r U a1 a2 -> r' U a1' a2') :
    forall U (t1 t1' : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2),
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      refine_prov_ RR r U t1 t2 ->
      refine_prov_ RR r' U t1' t2'.
  Proof using.
    intros U t1 t1' t2 t2' E1 E2 Hrel.
    revert t1' t2' E1 E2;
      induction Hrel as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH];
      intros t1' t2' E1 E2.
    - punfold E1; red in E1; punfold E2; red in E2.
      apply RP_Step; unfold rp_step_body in *.
      destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
        try inversion Hchk; pclearbot.
      + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; exact Hstep.
      + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp).
          eapply Hr_eq; [apply Hk1 | pstep; exact E2 | exact Hleft].
        * right; right.
          destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp).
             eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hboth].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha).
             eapply Hr_eq; [apply Hk1 | apply Hk2 | exact HA].
    - punfold E1; red in E1; rewrite Ht1 in E1;
        apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
      eapply RP_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
    - punfold E2; red in E2; rewrite Ht2 in E2;
        apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
      eapply RP_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
  Qed.

  Lemma refine_prov_obs_eq {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    forall U (t1 t1' : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2),
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      refine_prov RR U t1 t2 ->
      refine_prov RR U t1' t2'.
  Proof using.
    pcofix CIH.
    intros U t1 t1' t2 t2' E1 E2 Hrel.
    pstep; punfold Hrel.
    eapply refine_prov__obs_eq; [| exact E1 | exact E2 | exact Hrel].
    intros U0 a1 a1' a2 a2' Ea1 Ea2 Hr; pclearbot.
    right; eapply CIH; [exact Ea1 | exact Ea2 | exact Hr].
  Qed.

  Lemma refine_prov_inv_Tau_r {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    forall U (t1 : itree ProvBotE R1) (m2 : itree ProvBotE R2),
      refine_prov RR U t1 (Tau m2) ->
      refine_prov RR U t1 m2.
  Proof using.
    pcofix CIH.
    intros U t1 m2 H; pstep; punfold H.
    remember (Tau m2) as tm2 eqn:Etm2.
    assert (Hot2 : observe tm2 = TauF m2) by (subst tm2; reflexivity).
    clear Etm2.
    revert m2 Hot2; induction H as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2' Ht2 Hrel _];
      intros m2 Hot2.
    - unfold rp_step_body in Hstep; rewrite Hot2 in Hstep.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1] eqn:Hot1; try contradiction.
      + pclearbot; punfold Hstep.
        eapply RP_TauL;
          [exact Hot1
          | eapply refine_prov__mon;
              [exact Hstep | intros ? ? ? [Hl | []]; left; eapply paco3_mon; [exact Hl | intros ? ? ? []]]].
      + apply RP_Step; unfold rp_step_body; rewrite Hot1.
        destruct Hstep as [Hub | [Hleft | Hboth]]; [left; exact Hub | | contradiction].
        right; left.
        destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
        intros p Hp; specialize (Hleft p Hp); pclearbot.
        right; apply CIH.
        eapply refine_prov_obs_eq; [apply reflexivity | | exact Hleft].
        rewrite (itree_eta t2), Hot2; reflexivity.
    - eapply RP_TauL; [exact Ht1 | apply IH, Hot2].
    - rewrite Hot2 in Ht2; inversion Ht2; subst m2'.
      eapply refine_prov__mon;
        [exact Hrel | intros ? ? ? [Hl | []]; left; eapply paco3_mon; [exact Hl | intros ? ? ? []]].
  Qed.

  Lemma refine_prov_bind {R1 R2 S1 S2}
    (RR : list N -> R1 -> R2 -> Prop) (RS : list N -> S1 -> S2 -> Prop)
    (U : list N)
    (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2)
    (k1 : R1 -> itree ProvBotE S1) (k2 : R2 -> itree ProvBotE S2)
    (Ht : refine_prov RR U t1 t2)
    (Hk : forall U' r1 r2, incl U U' -> RR U' r1 r2 -> refine_prov RS U' (k1 r1) (k2 r2)) :
    refine_prov RS U (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using.
    revert U t1 t2 Ht Hk; pcofix CIH; intros U t1 t2 Ht Hk.
    punfold Ht.
    revert Hk; induction Ht as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH]; intros Hk.
    - unfold rp_step_body in Hstep.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1'] eqn:Hot1.
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        eapply paco3_mon;
          [eapply refine_prov_obs_eq;
             [symmetry; rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity
             | symmetry; rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity
             | exact (Hk U r1 r2 (incl_refl U) Hstep)]
          | intros ? ? ? []].
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        pclearbot; pstep; apply RP_Step; unfold rp_step_body.
        rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2.
        right; eapply CIH; [exact Hstep | exact Hk].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * pstep; apply RP_Step; unfold rp_step_body; rewrite (observe_bind t1 k1), Hot1; left; exact Hub.
        * pstep; apply RP_Step; unfold rp_step_body; rewrite (observe_bind t1 k1), Hot1; right; left.
          destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          right; eapply CIH; [exact Hleft |].
          intros U' r1 r2 Hincl HR; eapply Hk; [| exact HR].
          intros z Hz; apply Hincl; right; exact Hz.
        * destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          pstep; apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2; right; right.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
             right; eapply CIH; [exact Hboth |].
             intros U' r1 r2 Hincl HR; eapply Hk; [| exact HR].
             intros z Hz; apply Hincl; right; exact Hz.
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
             right; eapply CIH; [exact HA |].
             intros U' r1 r2 Hincl HR; eapply Hk; [| exact HR].
             intros z Hz; apply Hincl, in_app_iff; right; exact Hz.
    - specialize (IH Hk); punfold IH; pstep.
      eapply RP_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply RP_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | exact IH].
  Qed.

  Lemma refine_prov_refl {R} (RR : list N -> R -> R -> Prop)
    (HRR : forall U r, RR U r r) :
    forall U (t : itree ProvBotE R), refine_prov RR U t t.
  Proof using.
    pcofix CIH; intros U t; pstep; apply RP_Step; unfold rp_step_body.
    destruct (observe t) as [x | m | X e k].
    - apply HRR.
    - right; apply CIH.
    - right; right.
      destruct e as [p | b]; cbn.
      + destruct p; intros q _; right; apply CIH.
      + split; [apply EqE_bot_refl |].
        intros a1 a2 Ha; apply EqA_bot_eq in Ha; subst a2; right; apply CIH.
  Qed.

  Lemma refine_prov_trans {R} (f : R -> dvalue) :
    let RR := fun (_ : list N) (r1 r2 : R) => f r1 = f r2 in
    forall U (t1 t2 t3 : itree ProvBotE R),
      refine_prov RR U t1 t2 ->
      refine_prov RR U t2 t3 ->
      refine_prov RR U t1 t3.
  Proof using.
    cbv zeta; set (RR := fun (_ : list N) (r1 r2 : R) => f r1 = f r2).
    assert (HRR_anti : forall U1 U2 r1 r2, incl U1 U2 -> RR U1 r1 r2 -> RR U2 r1 r2)
      by (intros ? ? ? ? _ H; exact H).
    pcofix CIH.
    intros U t1 t2 t3 H12 H23.
    pstep; punfold H12.
    revert t3 H23;
      induction H12 as [U t1 t2 Hstep12 | U t1 m1 t2 Ht1 _ IH12 | U t1 t2 m2 Ht2 _ IH12];
      intros t3 H23.
    - unfold rp_step_body in Hstep12.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1] eqn:Hot1.
      + (* observe t1 = RetF r1 *)
        destruct (observe t2) as [r2 | m2 | X2 e2 k2] eqn:Hot2; try contradiction.
        punfold H23.
        revert Hot2 Hstep12;
          induction H23 as [U t2_ t3 Hstep23 | U t2_ m2' t3 Ht2_ _ _ | U t2_ t3 m3 Ht3 _ IH23];
          intros Hot2 Hstep12.
        * unfold rp_step_body in Hstep23; rewrite Hot2 in Hstep23.
          destruct (observe t3) as [r3 | m3 | X3 e3 k3] eqn:Hot3; try contradiction.
          apply RP_Step; unfold rp_step_body; rewrite Hot1, Hot3.
          unfold RR in *; congruence.
        * congruence.
        * eapply RP_TauR; [exact Ht3 | apply IH23; assumption].
      + (* observe t1 = TauF m1 *)
        destruct (observe t2) as [r2 | m2 | X2 e2 k2] eqn:Hot2; try contradiction.
        pclearbot.
        assert (Hm23 : refine_prov RR U m2 t3).
        { apply refine_prov_inv_Tau_l.
          eapply refine_prov_obs_eq; [| apply reflexivity | exact H23].
          rewrite (itree_eta t2), Hot2; reflexivity. }
        destruct (observe t3) as [r3 | m3 | X3 e3 k3] eqn:Hot3.
        * (* observe t3 = RetF r3 *)
          eapply RP_TauL; [exact Hot1 |].
          punfold Hm23.
          revert m1 Hstep12 Hot3;
            induction Hm23 as [U m2_ t3_ Hs23 | U m2_ m2' t3_ Hm2_ _ IHm23 | U m2_ t3_ m3' Ht3_ _ _];
            intros m1 Hm12 Hot3.
          -- unfold rp_step_body in Hs23; rewrite Hot3 in Hs23.
             destruct (observe m2_) as [r2 | mm | X2 e2 k2] eqn:Hotm2; try contradiction.
             ++ punfold Hm12.
                revert Hotm2 Hs23;
                  induction Hm12 as [U m1_ m2__ Hs12 | U m1_ m1' m2__ Hm1_ _ IHm12 | U m1_ m2__ mm2 Hm2__ _ _];
                  intros Hotm2 Hs23; try congruence.
                ** unfold rp_step_body in Hs12; rewrite Hotm2 in Hs12.
                   destruct (observe m1_) as [r1 | mm1 | X1 e1 k1] eqn:Hotm1; try contradiction.
                   --- apply RP_Step; unfold rp_step_body; rewrite Hotm1, Hot3; unfold RR in *; congruence.
                   --- apply RP_Step; unfold rp_step_body; rewrite Hotm1, Hot3.
                       destruct Hs12 as [Hub | [Hl | Hb]]; [left; exact Hub | | contradiction].
                       right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
                       intros p Hp; specialize (Hl p Hp); pclearbot.
                       right; eapply CIH; [exact Hl |].
                       pstep; apply RP_Step; unfold rp_step_body; rewrite Hotm2, Hot3; exact Hs23.
                ** eapply RP_TauL; [exact Hm1_ | apply IHm12; assumption].
             ++ destruct Hs23 as [Hub2 | [Hl2 | Hb2]]; [| | contradiction].
                ** punfold Hm12.
                   revert Hotm2 Hub2;
                     induction Hm12 as [U m1_ m2__ Hs12 | U m1_ m1' m2__ Hm1_ _ IHm12 | U m1_ m2__ mm2 Hm2__ _ _];
                     intros Hotm2 Hub2; try congruence.
                   --- unfold rp_step_body in Hs12; rewrite Hotm2 in Hs12.
                       destruct (observe m1_) as [r1 | mm1 | X1 e1 k1] eqn:Hotm1; try contradiction.
                       apply RP_Step; unfold rp_step_body; rewrite Hotm1.
                       destruct Hs12 as [Hub1 | [Hl1 | Hb1]].
                       +++ left; exact Hub1.
                       +++ right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
                           intros p Hp; specialize (Hl1 p Hp); pclearbot; right; eapply CIH; [exact Hl1 |].
                           pstep; apply RP_Step; unfold rp_step_body; rewrite Hotm2; left; exact Hub2.
                       +++ left; destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction;
                           [destruct p1; discriminate | destruct Hb1 as [HE _]; rewrite (EqE_bot_is_ub _ _ HE); exact Hub2].
                   --- eapply RP_TauL; [exact Hm1_ | apply IHm12; assumption].
                ** punfold Hm12.
                   revert Hotm2 Hl2;
                     induction Hm12 as [U m1_ m2__ Hs12 | U m1_ m1' m2__ Hm1_ _ IHm12 | U m1_ m2__ mm2 Hm2__ _ _];
                     intros Hotm2 Hl2; try congruence.
                   --- unfold rp_step_body in Hs12; rewrite Hotm2 in Hs12.
                       destruct (observe m1_) as [r1 | mm1 | X1 e1 k1] eqn:Hotm1; try contradiction.
                       apply RP_Step; unfold rp_step_body; rewrite Hotm1.
                       destruct Hs12 as [Hub1 | [Hl1 | Hb1]].
                       +++ left; exact Hub1.
                       +++ right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
                           intros p Hp; specialize (Hl1 p Hp); pclearbot; right; eapply CIH; [exact Hl1 |].
                           pstep; apply RP_Step; unfold rp_step_body; rewrite Hotm2; right; left.
                           destruct e2 as [p2 | b2]; [| contradiction]; destruct p2.
                           intros q Hq; assert (HqU : ~ In q U) by (intros Hx; apply Hq; right; exact Hx).
                           specialize (Hl2 q HqU); pclearbot; left.
                           eapply refine_prov_antitone; [exact HRR_anti | | exact Hl2].
                           intros z [<- | Hz]; [left; reflexivity | right; right; exact Hz].
                       +++ right; left; destruct e2 as [p2 | b2]; [| contradiction]; destruct p2.
                           destruct e1 as [p1 | b1]; [| cbn in Hb1; contradiction]; destruct p1.
                           intros p Hp; specialize (Hb1 p Hp); specialize (Hl2 p Hp); pclearbot.
                           right; eapply CIH; [exact Hb1 | exact Hl2].
                   --- eapply RP_TauL; [exact Hm1_ | apply IHm12; assumption].
          -- apply IHm23; [| exact Hot3].
             apply refine_prov_inv_Tau_r.
             eapply refine_prov_obs_eq; [apply reflexivity | | exact Hm12].
             rewrite (itree_eta m2_), Hm2_; reflexivity.
          -- congruence.
        * (* observe t3 = TauF m3 *)
          apply RP_Step; unfold rp_step_body; rewrite Hot1, Hot3.
          right; eapply CIH; [exact Hstep12 |].
          apply refine_prov_inv_Tau_r.
          eapply refine_prov_obs_eq; [apply reflexivity | | exact Hm23].
          rewrite (itree_eta t3), Hot3; reflexivity.
        * (* observe t3 = VisF e3 k3 *)
          eapply RP_TauL; [exact Hot1 |].
          punfold Hm23.
          revert m1 Hstep12 Hot3;
            induction Hm23 as [U m2_ t3_ Hs23 | U m2_ m2' t3_ Hm2_ _ IHm23 | U m2_ t3_ m3' Ht3_ _ _];
            intros m1 Hm12 Hot3.
          -- unfold rp_step_body in Hs23; rewrite Hot3 in Hs23.
             destruct (observe m2_) as [r2 | mm | X2 e2 k2] eqn:Hotm2; try contradiction.
             punfold Hm12.
             revert Hotm2 Hs23;
               induction Hm12 as [U m1_ m2__ Hs12 | U m1_ m1' m2__ Hm1_ _ IHm12 | U m1_ m2__ mm2 Hm2__ _ _];
               intros Hotm2 Hs23; try congruence.
             ++ unfold rp_step_body in Hs12; rewrite Hotm2 in Hs12.
                destruct (observe m1_) as [r1 | mm1 | X1 e1 k1] eqn:Hotm1; try contradiction.
                apply RP_Step; unfold rp_step_body; rewrite Hotm1, Hot3.
                destruct Hs12 as [Hub1 | [Hl1 | Hb1]].
                ** left; exact Hub1.
                ** right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
                   intros p Hp; specialize (Hl1 p Hp); pclearbot; right; eapply CIH; [exact Hl1 |].
                   eapply refine_prov_antitone; [exact HRR_anti | intros z Hz; right; exact Hz |].
                   pstep; apply RP_Step; unfold rp_step_body; rewrite Hotm2, Hot3; exact Hs23.
                ** destruct Hs23 as [Hub2 | [Hl2 | Hb2]].
                   --- left; destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction;
                       [destruct p1; discriminate | destruct Hb1 as [HE _]; rewrite (EqE_bot_is_ub _ _ HE); exact Hub2].
                   --- right; left; destruct e2 as [p2 | b2]; [| contradiction]; destruct p2.
                       destruct e1 as [p1 | b1]; [| cbn in Hb1; contradiction]; destruct p1.
                       intros p Hp; specialize (Hb1 p Hp); specialize (Hl2 p Hp); pclearbot.
                       right; eapply CIH; [exact Hb1 | exact Hl2].
                   --- right; right.
                       destruct e1 as [p1 | b1], e2 as [p2 | b2], e3 as [p3 | b3];
                         cbn in *; try contradiction.
                       +++ destruct p1, p2, p3; intros p Hp.
                           specialize (Hb1 p Hp); specialize (Hb2 p Hp); pclearbot.
                           right; eapply CIH; [exact Hb1 | exact Hb2].
                       +++ destruct Hb1 as [HE12 HA12], Hb2 as [HE23 HA23].
                           split; [eapply EqE_bot_trans; eassumption |].
                           intros a1 a3 Ha13.
                           destruct (EqA_bot_trans b1 b2 b3 a1 a3 HE12 HE23 Ha13) as [a2 [Ha12 Ha23]].
                           specialize (HA12 a1 a2 Ha12); specialize (HA23 a2 a3 Ha23); pclearbot.
                           rewrite (bot_ans_provs_eq b1 b2 a1 a2 HE12 Ha12).
                           right; eapply CIH; [exact HA12 | exact HA23].
             ++ eapply RP_TauL; [exact Hm1_ | apply IHm12; assumption].
          -- apply IHm23; [| exact Hot3].
             apply refine_prov_inv_Tau_r.
             eapply refine_prov_obs_eq; [apply reflexivity | | exact Hm12].
             rewrite (itree_eta m2_), Hm2_; reflexivity.
          -- congruence.
      + (* observe t1 = VisF e1 k1 *)
        destruct Hstep12 as [Hub1 | [Hl1 | Hb1]].
        * apply RP_Step; unfold rp_step_body; rewrite Hot1; left; exact Hub1.
        * apply RP_Step; unfold rp_step_body; rewrite Hot1; right; left.
          destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hl1 p Hp); pclearbot; right; eapply CIH; [exact Hl1 |].
          eapply refine_prov_antitone; [exact HRR_anti | intros z Hz; right; exact Hz | exact H23].
        * destruct (observe t2) as [r2 | m2 | X2 e2 k2] eqn:Hot2; try contradiction.
          punfold H23.
          revert Hot2 Hb1;
            induction H23 as [U t2_ t3 Hs23 | U t2_ m2' t3 Ht2_ _ _ | U t2_ t3 m3 Ht3 _ IH23];
            intros Hot2 Hb1; try congruence.
          -- unfold rp_step_body in Hs23; rewrite Hot2 in Hs23.
             apply RP_Step; unfold rp_step_body; rewrite Hot1.
             destruct Hs23 as [Hub2 | [Hl2 | Hb2]].
             ++ left; destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction;
                [destruct p1; discriminate | destruct Hb1 as [HE _]; rewrite (EqE_bot_is_ub _ _ HE); exact Hub2].
             ++ right; left; destruct e2 as [p2 | b2]; [| contradiction]; destruct p2.
                destruct e1 as [p1 | b1]; [| cbn in Hb1; contradiction]; destruct p1.
                intros p Hp; specialize (Hb1 p Hp); specialize (Hl2 p Hp); pclearbot.
                right; eapply CIH; [exact Hb1 | exact Hl2].
             ++ right; right.
                destruct (observe t3) as [r3 | m3 | X3 e3 k3] eqn:Hot3; try contradiction.
                destruct e1 as [p1 | b1], e2 as [p2 | b2], e3 as [p3 | b3];
                  cbn in *; try contradiction.
                ** destruct p1, p2, p3; intros p Hp.
                   specialize (Hb1 p Hp); specialize (Hb2 p Hp); pclearbot.
                   right; eapply CIH; [exact Hb1 | exact Hb2].
                ** destruct Hb1 as [HE12 HA12], Hb2 as [HE23 HA23].
                   split; [eapply EqE_bot_trans; eassumption |].
                   intros a1 a3 Ha13.
                   destruct (EqA_bot_trans b1 b2 b3 a1 a3 HE12 HE23 Ha13) as [a2 [Ha12 Ha23]].
                   specialize (HA12 a1 a2 Ha12); specialize (HA23 a2 a3 Ha23); pclearbot.
                   rewrite (bot_ans_provs_eq b1 b2 a1 a2 HE12 Ha12).
                   right; eapply CIH; [exact HA12 | exact HA23].
          -- eapply RP_TauR; [exact Ht3 | apply IH23; assumption].
    - eapply RP_TauL; [exact Ht1 | apply IH12, H23].
    - apply IH12, refine_prov_inv_Tau_l.
      eapply refine_prov_obs_eq; [| apply reflexivity | exact H23].
      rewrite (itree_eta t2), Ht2; reflexivity.
  Qed.

  (** ** Lifting [refine_mcfg] to [interp_mcfg_model] *)

  Lemma refine_mcfg_lift_bot_prov {R} (t : itree MCFGEbot R) (U : list N) :
    refine_prov (fun _ r1 r2 => r1 = r2) U (lift_bot_prov t) (lift_bot_prov t).
  Proof using.
    apply refine_prov_refl; intros; reflexivity.
  Qed.

  Lemma interp_vellvm_prov_h_refines_same {T}
    (e : MCFGEtop T) (s : FusedS) (U : list N) :
    refine_prov
      (fun _ '(s1', r1) '(s2', r2) => s1' = s2' /\ EqA_MCFG T T e r1 e r2)
      U (interp_vellvm_prov_h e s) (interp_vellvm_prov_h e s).
  Proof using.
    apply refine_prov_refl; intros U' [s' r]; split; [reflexivity | apply EqA_MCFG_refl].
  Qed.

  Lemma interp_vellvm_prov_h_refines {T1 T2}
    (e1 : MCFGEtop T1) (e2 : MCFGEtop T2)
    (HE : EqE_MCFG T1 T2 e1 e2)
    (s : FusedS) (U : list N) :
    refine_prov
      (fun _ '(s1', r1) '(s2', r2) => s1' = s2' /\ EqA_MCFG T1 T2 e1 r1 e2 r2)
      U (interp_vellvm_prov_h e1 s) (interp_vellvm_prov_h e2 s).
  Proof using.
    destruct_sum2 e1 e2 HE.
    - destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; try contradiction; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - destruct e1, e2; cbn in HE; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
      right; right; split; [exact I | intros [] [] _].
      left; eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      pstep; apply RP_Step; cbn; split; reflexivity.
    - destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Definition model_step_state (R : Type) : Type :=
    (FusedS * R) + (FusedS * @MCFGtop (@ParamsV IP IPT) R).

  Definition model_cont (R : Type) (x : model_step_state R)
    : itree ProvBotE (FusedS * R) :=
    match x with
    | inl sr => Ret sr
    | inr (s', t') => Tau (interp_state interp_vellvm_prov_h t' s')
    end.

  Definition model_step_rel {R1 R2} (RR : R1 -> R2 -> Prop)
    : list N -> model_step_state R1 -> model_step_state R2 -> Prop :=
    fun _ x1 x2 =>
      match x1, x2 with
      | inl (s1, r1), inl (s2, r2) => s1 = s2 /\ RR r1 r2
      | inr (s1, t1), inr (s2, t2) =>
          s1 = s2 /\ ruttc cutUB_rel cutNone EqE_MCFG EqA_MCFG RR t1 t2
      | _, _ => False
      end.

  Lemma interp_state_decomp {R} (t : MCFGtop R) (s : FusedS) :
    exists w : itree ProvBotE (model_step_state R),
      interp_state interp_vellvm_prov_h t s ≅ ITree.bind w (model_cont R).
  Proof using.
    rewrite (unfold_interp_state interp_vellvm_prov_h t s).
    destruct (observe t) as [r | m | X e k]; cbn -[interp_vellvm_prov_h].
    - exists (Ret (inl (s, r))); rewrite Eqit.bind_ret_l; reflexivity.
    - exists (Ret (inr (s, m))); rewrite Eqit.bind_ret_l; reflexivity.
    - exists (ITree.bind (interp_vellvm_prov_h e s) (fun '(s', x) => Ret (inr (s', k x)))).
      rewrite Eqit.bind_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma ruttc_model_step_decomp {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : MCFGtop R1) (t2 : MCFGtop R2)
    (HR : ruttc cutUB_rel cutNone EqE_MCFG EqA_MCFG RR t1 t2)
    (s : FusedS) (U : list N) :
    exists w1 w2,
      interp_state interp_vellvm_prov_h t1 s ≅ ITree.bind w1 (model_cont R1) /\
      interp_state interp_vellvm_prov_h t2 s ≅ ITree.bind w2 (model_cont R2) /\
      refine_prov (model_step_rel RR) U w1 w2.
  Proof using.
    punfold HR; red in HR.
    remember (observe t1) as ot1 eqn:Hot1.
    remember (observe t2) as ot2 eqn:Hot2.
    revert t1 t2 Hot1 Hot2 s U;
      induction HR as [r1 r2 HRR | m1 m2 Hm | X1 X2 e1 e2 k1 k2 HE Hk
                       | m1 ot2_ _ IH | ot1_ m2 _ IH
                       | X1 e1 k1 ot2_ Hcut | X2 ot1_ e2 k2 Hcut];
      intros t1 t2 Hot1 Hot2 s U; pclearbot.
    - exists (Ret (inl (s, r1))), (Ret (inl (s, r2))).
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_ret_l; reflexivity.
      + split.
        * rewrite (unfold_interp_state interp_vellvm_prov_h t2 s), <- Hot2; cbn -[interp_vellvm_prov_h].
          rewrite Eqit.bind_ret_l; reflexivity.
        * pstep; apply RP_Step; cbn; split; [reflexivity | exact HRR].
    - exists (Ret (inr (s, m1))), (Ret (inr (s, m2))).
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_ret_l; reflexivity.
      + split.
        * rewrite (unfold_interp_state interp_vellvm_prov_h t2 s), <- Hot2; cbn -[interp_vellvm_prov_h].
          rewrite Eqit.bind_ret_l; reflexivity.
        * pstep; apply RP_Step; cbn; split; [reflexivity | exact Hm].
    - exists (ITree.bind (interp_vellvm_prov_h e1 s) (fun '(s', x) => Ret (inr (s', k1 x)))),
             (ITree.bind (interp_vellvm_prov_h e2 s) (fun '(s', x) => Ret (inr (s', k2 x)))).
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
      + split.
        * rewrite (unfold_interp_state interp_vellvm_prov_h t2 s), <- Hot2; cbn -[interp_vellvm_prov_h].
          rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
          intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
        * eapply refine_prov_bind; [apply interp_vellvm_prov_h_refines, HE |].
          intros U' [s1' a1] [s2' a2] _ [<- HA].
          specialize (Hk a1 a2 HA); pclearbot.
          pstep; apply RP_Step; cbn; split; [reflexivity | exact Hk].
    - destruct (IH m1 t2 Logic.eq_refl Hot2 s U) as (w1' & w2' & Ew1 & Ew2 & Hw).
      exists (Tau w1'), w2'.
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_tau, Ew1; reflexivity.
      + split; [exact Ew2 |].
        punfold Hw; pstep; eapply RP_TauL; [reflexivity | exact Hw].
    - destruct (IH t1 m2 Hot1 Logic.eq_refl s U) as (w1' & w2' & Ew1 & Ew2 & Hw).
      exists w1', (Tau w2').
      split; [exact Ew1 |].
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t2 s), <- Hot2; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_tau, Ew2; reflexivity.
      + punfold Hw; pstep; eapply RP_TauR; [reflexivity | exact Hw].
    - destruct (interp_state_decomp t2 s) as [w2 Ew2].
      exists (ITree.bind (interp_vellvm_prov_h e1 s) (fun '(s', x) => Ret (inr (s', k1 x)))), w2.
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
      + split; [exact Ew2 |].
        clear Hot1; destruct Hcut as [u].
        pstep; apply RP_Step; unfold rp_step_body.
        rewrite !observe_bind; cbn; left; reflexivity.
    - inversion Hcut.
  Qed.

  Lemma refine_mcfg_to_model_aux {R1 R2} (RR : R1 -> R2 -> Prop) :
    forall (U : list N)
      (w1 : itree ProvBotE (model_step_state R1))
      (w2 : itree ProvBotE (model_step_state R2))
      (t1 : itree ProvBotE (FusedS * R1))
      (t2 : itree ProvBotE (FusedS * R2)),
      ITree.bind w1 (model_cont R1) ≅ t1 ->
      ITree.bind w2 (model_cont R2) ≅ t2 ->
      refine_prov (model_step_rel RR) U w1 w2 ->
      refine_prov (fun _ '(s1, r1) '(s2, r2) => s1 = s2 /\ RR r1 r2) U t1 t2.
  Proof using.
    pcofix CIH.
    intros U w1 w2 t1 t2 Et1 Et2 Hw.
    pstep.
    eapply refine_prov__mon with
      (r := fun U0 a1 a2 =>
              exists v1 v2,
                ITree.bind v1 (model_cont R1) ≅ a1 /\
                ITree.bind v2 (model_cont R2) ≅ a2 /\
                refine_prov (model_step_rel RR) U0 v1 v2);
      [| intros U0 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
         right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
    eapply refine_prov__obs_eq;
      [intros U0 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
       exists v1, v2;
       split; [etransitivity; [exact Ev1 | exact Ea1] |];
       split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
      | exact Et1 | exact Et2 |].
    punfold Hw; clear t1 t2 Et1 Et2 CIH r.
    induction Hw as [U w1 w2 Hstep | U w1 mw1 w2 Hw1 _ IH | U w1 w2 mw2 Hw2 _ IH].
    - unfold rp_step_body in Hstep.
      destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
        destruct x1 as [[s1 r1] | [s1 u1']], x2 as [[s2 r2] | [s2 u2']]; cbn in Hstep; try contradiction.
        * apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind w1 (model_cont R1)), How1,
                  (observe_bind w2 (model_cont R2)), How2; cbn.
          exact Hstep.
        * destruct Hstep as [<- HR'].
          apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind w1 (model_cont R1)), How1,
                  (observe_bind w2 (model_cont R2)), How2; cbn.
          destruct (ruttc_model_step_decomp RR u1' u2' HR' s1 U) as (v1 & v2 & Ev1 & Ev2 & Hv).
          exists v1, v2; split; [symmetry; exact Ev1 | split; [symmetry; exact Ev2 | exact Hv]].
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction; pclearbot.
        apply RP_Step; unfold rp_step_body.
        rewrite (observe_bind w1 (model_cont R1)), How1,
                (observe_bind w2 (model_cont R2)), How2.
        exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + apply RP_Step; unfold rp_step_body.
        rewrite (observe_bind w1 (model_cont R1)), How1.
        destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct ev1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          exists (kw1 p), w2; split; [reflexivity | split; [reflexivity | exact Hleft]].
        * right; right.
          destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 (model_cont R2)), How2.
          destruct ev1 as [p1 | b1], ev2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
             exists (kw1 p), (kw2 p); split; [reflexivity | split; [reflexivity | exact Hboth]].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
             exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
    - eapply RP_TauL; [rewrite (observe_bind w1 (model_cont R1)), Hw1; reflexivity | exact IH].
    - eapply RP_TauR; [rewrite (observe_bind w2 (model_cont R2)), Hw2; reflexivity | exact IH].
  Qed.

  Lemma refine_mcfg_to_model {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : MCFGtop R1) (t2 : MCFGtop R2)
    (HR : ruttc cutUB_rel cutNone EqE_MCFG EqA_MCFG RR t1 t2) :
    forall (s : FusedS) (U : list N),
      refine_prov (fun _ '(s1, r1) '(s2, r2) => s1 = s2 /\ RR r1 r2) U
        (interp_state interp_vellvm_prov_h t1 s)
        (interp_state interp_vellvm_prov_h t2 s).
  Proof using.
    intros s U.
    destruct (ruttc_model_step_decomp RR t1 t2 HR s U) as (w1 & w2 & Ew1 & Ew2 & Hw).
    eapply refine_mcfg_to_model_aux; [symmetry; exact Ew1 | symmetry; exact Ew2 | exact Hw].
  Qed.

  (** ** Whole-Program Refinement ([prog_refines]) & [PreOrder] *)

  Definition prog_refines (M1 M2 : CFG.mcfg dtyp) : Prop :=
    forall (ret_typ : dtyp) (entry : function_id)
           (args : list (@dvalue (@ParamsV IP IPT))) (U : list N),
      refine_prov (fun _ r1 r2 => snd r1 = snd r2) U
        (run_mcfg_model ret_typ entry args M1)
        (run_mcfg_model ret_typ entry args M2).

  Lemma prog_refines_refl (M : CFG.mcfg dtyp) :
    prog_refines M M.
  Proof using.
    intros ret_typ entry args U.
    apply refine_prov_refl; intros; reflexivity.
  Qed.

  Lemma prog_refines_trans (M1 M2 M3 : CFG.mcfg dtyp) :
    prog_refines M1 M2 ->
    prog_refines M2 M3 ->
    prog_refines M1 M3.
  Proof using.
    intros H12 H23 ret_typ entry args U.
    eapply (refine_prov_trans snd); [apply H12 | apply H23].
  Qed.

  #[export] Instance prog_refines_PreOrder : PreOrder prog_refines :=
    {| PreOrder_Reflexive  := prog_refines_refl;
       PreOrder_Transitive := prog_refines_trans |}.

  Lemma refine_vellvm_to_prog (M1 M2 : CFG.mcfg dtyp)
    (Hden : forall ret_typ entry args,
              @refine_mcfg (@ParamsV IP IPT) _ _ Logic.eq
                (denote_vellvm ret_typ entry args M1)
                (denote_vellvm ret_typ entry args M2)) :
    prog_refines M1 M2.
  Proof using.
    intros ret_typ entry args U.
    unfold run_mcfg_model, interp_mcfg_model.
    eapply refine_prov_antitone with (U := U);
      [intros _ _ [s1 r1] [s2 r2] _ [<- <-]; reflexivity | apply incl_refl |].
    apply refine_mcfg_to_model.
    apply refine_mcfg_interp_intrinsics.
    apply Hden.
  Qed.

  (** ** Modular Per-CFG Lifter ([lift_cfg_pass]) *)

  Lemma of_list_fn_ctx_refines
    (l1 l2 : list (Z * @function_denotation (@ParamsV IP IPT)))
    (Hl : Forall2
            (fun '(k1, f1) '(k2, f2) =>
               k1 = k2 /\
               forall cc args, refine_cfg Logic.eq (f1 cc args) (f2 cc args))
            l1 l2) :
    fn_ctx_refines (IntMaps.IP.of_list l1) (IntMaps.IP.of_list l2).
  Proof using.
    induction Hl as [| [k1 f1] [k2 f2] l1' l2' [<- Hf] _ IH]; intros k.
    - cbn; constructor.
    - cbn [IntMaps.IP.of_list fold_right fst snd]; unfold lookup.
      destruct (Z.eq_dec k1 k) as [<- | Hne].
      + rewrite !IntMaps.IP.F.add_eq_o by reflexivity.
        constructor; exact Hf.
      + rewrite !IntMaps.IP.F.add_neq_o by exact Hne.
        apply IH.
  Qed.

  Lemma map_monad_address_one_function_refines
    (f : CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hbody : forall c va,
               @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                 (denote_cfg c va) (denote_cfg (f c) va))
    (defs : list (definition dtyp (CFG.cfg dtyp))) :
    refine_mcfg
      (Forall2
         (fun '(k1, fn1) '(k2, fn2) =>
            k1 = k2 /\
            forall cc args, refine_cfg Logic.eq (fn1 cc args) (fn2 cc args)))
      (map_monad address_one_function defs)
      (map_monad address_one_function (List.map (map_defn_cfg f) defs)).
  Proof using.
    induction defs as [| df defs' IH]; cbn [List.map map_monad].
    - apply ruttc_ret; constructor.
    - eapply ruttc_bind.
      + unfold address_one_function; cbn [map_defn_cfg df_prototype].
        eapply ruttc_bind; [apply refine_mcfg_refl | intros fv _ <-].
        destruct fv as [[p | | | | | | |] | |]; try apply refine_mcfg_refl.
        * apply ruttc_ret; split; [reflexivity |].
          apply refine_cfg_denote_function; [reflexivity | reflexivity |].
          intros va; apply Hbody.
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
        * unfold raise, trigger_cast; eapply ruttc_trigger';
            [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
      + intros [k1 fn1] [k2 fn2] Hhd.
        eapply ruttc_bind; [exact IH |].
        intros tl1 tl2 Htl; apply ruttc_ret; constructor; assumption.
  Qed.

  Lemma Forall2_fn_refl (l : list (Z * @function_denotation (@ParamsV IP IPT))) :
    Forall2
      (fun '(k1, fn1) '(k2, fn2) =>
         k1 = k2 /\
         forall cc args, refine_cfg Logic.eq (fn1 cc args) (fn2 cc args))
      l l.
  Proof using.
    induction l as [| [k fn] l' IH]; constructor; [| exact IH].
    split; [reflexivity | intros; apply refine_cfg_refl].
  Qed.

  Theorem lift_cfg_pass (f : CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hba : forall c,
             flat_map block_block_addresses (blks (f c)) =
             flat_map block_block_addresses (blks c))
    (Hbody : forall c va,
               @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                 (denote_cfg c va) (denote_cfg (f c) va)) :
    forall M : CFG.mcfg dtyp, prog_refines M (map_mcfg_cfg f M).
  Proof using.
    intros M; apply refine_vellvm_to_prog; intros ret_typ entry args.
    unfold denote_vellvm.
    assert (Hbg : @build_global_environment (@ParamsV IP IPT) (map_mcfg_cfg f M) =
                  @build_global_environment (@ParamsV IP IPT) M).
    { unfold build_global_environment.
      rewrite map_mcfg_cfg_prototypes, (map_mcfg_cfg_block_addresses f M Hba).
      reflexivity. }
    rewrite Hbg.
    eapply ruttc_bind; [apply refine_mcfg_refl | intros [] _ <-].
    cbn [m_definitions m_declarations map_mcfg_cfg].
    eapply ruttc_bind; [apply (map_monad_address_one_function_refines f Hbody) |].
    intros defns1 defns2 Hdefns.
    eapply ruttc_bind; [apply refine_mcfg_refl | intros libs _ <-].
    eapply ruttc_bind; [apply refine_mcfg_refl | intros addr _ <-].
    eapply ruttc_bind.
    - apply refine_mcfg_denote_mcfg.
      apply of_list_fn_ctx_refines.
      apply Forall2_app; [exact Hdefns | apply Forall2_fn_refl].
    - intros rv _ <-; destruct rv; apply refine_mcfg_refl.
  Qed.

  (** ** Scalar Runtime Type Guarantees & Local-Environment Simulation ([cfg_local_sim]) *)

  Definition is_scalar_dtyp_base (dtb : dtyp_base) : bool :=
    match dtb with
    | DTYPE_I _ => true
    | DTYPE_Pointer => true
    | DTYPE_FP FP_float => true
    | DTYPE_FP FP_double => true
    | _ => false
    end.

  Definition is_scalar_dtyp (dt : dtyp) : bool :=
    match dt with
    | DTYPE_Base dtb => is_scalar_dtyp_base dtb
    | _ => false
    end.

  Lemma memory_bytes_to_dvalue_scalar_typ
    (dbs : list (@memory_byte (@ParamsV IP IPT))) (dt : dtyp)
    (dv : @dvalue (@ParamsV IP IPT))
    (Hsc : is_scalar_dtyp dt = true)
    (Hrd : memory_bytes_to_dvalue dbs dt = raise_ret dv) :
    dvalue_has_dtyp dv dt.
  Proof using.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc.
    cbn [memory_bytes_to_dvalue] in Hrd.
    destruct dtb as [sz | | | | fp | | | | | | bsz];
      try discriminate Hsc; cbn [memory_bytes_to_dvalue_base] in Hrd.
    - unfold absorb_pois in Hrd.
      destruct (memory_bytes_to_int sz dbs) as [| | | [| z]]; cbn in Hrd; try discriminate Hrd;
        inversion Hrd; subst dv; [apply DVALUE_Poison_typ_agg | apply DVALUE_Base_typ; cbn; [apply Pos.eqb_refl | reflexivity]].
    - unfold absorb_pois in Hrd.
      destruct (memory_bytes_to_pointer dbs) as [| | | [| p]]; cbn in Hrd; try discriminate Hrd;
        inversion Hrd; subst dv; [apply DVALUE_Poison_typ_agg | apply DVALUE_Base_typ; reflexivity].
    - destruct fp; try discriminate Hsc; cbn [memory_bytes_to_dvalue_base] in Hrd;
        unfold absorb_pois in Hrd;
        destruct (map_monad memory_byte_to_Z dbs) as [| | | l]; cbn in Hrd; try discriminate Hrd.
      + destruct (sequence_Pois l) as [| zs]; cbn in Hrd; inversion Hrd; subst dv;
          [apply DVALUE_Poison_typ_agg | apply DVALUE_Base_typ; reflexivity].
      + destruct (sequence_Pois l) as [| zs]; cbn in Hrd; inversion Hrd; subst dv;
          [apply DVALUE_Poison_typ_agg | apply DVALUE_Base_typ; reflexivity].
  Qed.

  Lemma default_dvalue_scalar_typ (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT))
    (Hsc : is_scalar_dtyp dt = true)
    (Hdef : default_dvalue_of_dtyp dt = raise_ret dv) :
    dvalue_has_dtyp dv dt.
  Proof using.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc; cbn [default_dvalue_of_dtyp] in Hdef.
    destruct dtb as [sz | | | | fp | | | | | | bsz]; try discriminate Hsc;
      try (destruct fp; try discriminate Hsc);
      cbn in Hdef; inversion Hdef; subst dv;
      apply DVALUE_Base_typ; cbn; try apply Pos.eqb_refl; reflexivity.
  Qed.

  Fixpoint memM_all_ret {X : Type} (P : X -> Prop)
    (m : @memM (@ParamsV IP IPT) _ X) : Prop :=
    match m with
    | Mret x => P x
    | Moom _ | Mub _ | Merr _ => True
    | Mget k => forall σ, memM_all_ret P (k σ)
    | Mput _ k => memM_all_ret P (k tt)
    | Mchoose _ k => forall c, memM_all_ret P (k c)
    end.

  Lemma memM_all_ret_bind {X Y : Type} (P : X -> Prop) (Q : Y -> Prop)
    (m : @memM (@ParamsV IP IPT) _ X)
    (f : X -> @memM (@ParamsV IP IPT) _ Y)
    (Hm : memM_all_ret P m)
    (Hf : forall x, P x -> memM_all_ret Q (f x)) :
    memM_all_ret Q (ExtLib.Structures.Monad.bind m f).
  Proof using.
    induction m as [x | s | s | s | k IH | σ' k IH | c k IH]; cbn in *;
      [apply Hf, Hm | exact I | exact I | exact I
      | intros σ; apply IH, Hm
      | apply IH, Hm
      | intros ch; apply IH, Hm].
  Qed.

  Lemma memM_all_ret_true {X : Type} (m : @memM (@ParamsV IP IPT) _ X) :
    memM_all_ret (fun _ => True) m.
  Proof using.
    induction m; cbn; auto.
  Qed.

  Definition mcfg_event_post {X : Type} (e : @MCFGEtop (@ParamsV IP IPT) X) (a : X) : Prop :=
    match e return X -> Prop with
    | inl1 _ => fun _ => True
    | inr1 e1 =>
        match e1 return X -> Prop with
        | inl1 _ => fun _ => True
        | inr1 e2 =>
            match e2 return X -> Prop with
            | inl1 _ => fun _ => True
            | inr1 e3 =>
                match e3 return X -> Prop with
                | inl1 _ => fun _ => True
                | inr1 e4 =>
                    match e4 return X -> Prop with
                    | inl1 me =>
                        match me in MemoryE Y return Y -> Prop with
                        | Load dt _ => fun dv => is_scalar_dtyp dt = true -> dvalue_has_dtyp dv dt
                        | Alloca _ _ _ => fun dv => dvalue_has_dtyp dv (DTYPE_Base DTYPE_Pointer)
                        | _ => fun _ => True
                        end
                    | inr1 e5 =>
                        match e5 return X -> Prop with
                        | inl1 de =>
                            match de in DrawE Y return Y -> Prop with
                            | Draw dt => fun dv => is_scalar_dtyp dt = true -> dvalue_has_dtyp dv dt
                            end
                        | inr1 _ => fun _ => True
                        end
                    end
                end
            end
        end
    end a.

  Definition cfg_event_post {X : Type} (e : @CFGEtop (@ParamsV IP IPT) X) (a : X) : Prop :=
    match e return X -> Prop with
    | inl1 _ => fun _ => True
    | inr1 m => mcfg_event_post m
    end a.

  Lemma handle_memoryM_post {X : Type} (me : @MemoryE (@ParamsV IP IPT) X) :
    memM_all_ret
      (match me in MemoryE Y return Y -> Prop with
       | Load dt _ => fun dv => is_scalar_dtyp dt = true -> dvalue_has_dtyp dv dt
       | Alloca _ _ _ => fun dv => dvalue_has_dtyp dv (DTYPE_Base DTYPE_Pointer)
       | _ => fun _ => True
       end)
      (handle_memoryM me).
  Proof using.
    destruct me as [| | t n al | dt a | dt a v | cv tf v tt0]; cbn [handle_memoryM];
      try apply memM_all_ret_true.
    - eapply memM_all_ret_bind; [apply memM_all_ret_true |].
      intros ptr _; cbn; apply DVALUE_Base_typ; reflexivity.
    - destruct a as [[p | | | | | | |] | |]; cbn; try exact I.
      unfold read_dvalue.
      eapply memM_all_ret_bind; [apply memM_all_ret_true |].
      intros bytes _.
      destruct (memory_bytes_to_dvalue bytes dt) as [| | | dv] eqn:Erd; cbn; auto.
      intros Hsc; eapply memory_bytes_to_dvalue_scalar_typ; eassumption.
  Qed.

  Definition not_local_or_stack_push_pop_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inl1 _))) => false
    | _ => true
    end.

  (** Note: [StackRaise] and [StackGetExc] touch only [stack_exc], leaving
      [stack_vars] and the caller stack [stk] intact; we allow them in
      [sync_non_local_mcfg] alongside all non-[LocalE]/[StackE] events. *)
  Definition sync_non_local_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inl1 (inl1 _)))) => false
    | inr1 (inr1 (inr1 (inl1 (inr1 (StackPush _))))) => false
    | inr1 (inr1 (inr1 (inl1 (inr1 StackPop)))) => false
    | _ => true
    end.

  Definition sync_non_local_cfg {X} (e : @CFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inl1 _ => true
    | inr1 m => sync_non_local_mcfg m
    end.

  Definition is_ub_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (ThrowUB _))))))))) => true
    | _ => false
    end.

  Definition is_ub_cfg {X} (e : @CFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inl1 _ => false
    | inr1 m => is_ub_mcfg m
    end.

  Lemma lookup_add_eq {V} (k : raw_id) (v : V) (m : rmap V) :
    Maps.lookup k (Maps.add k v m) = Some v.
  Proof using.
    change (RM.find k (RM.add k v m) = Some v).
    apply RMF.F.add_eq_o; reflexivity.
  Qed.

  Lemma lookup_add_neq {V} (k k' : raw_id) (v : V) (m : rmap V) :
    k <> k' ->
    Maps.lookup k' (Maps.add k v m) = Maps.lookup k' m.
  Proof using.
    intros Hne.
    change (RM.find k' (RM.add k v m) = RM.find k' m).
    apply RMF.F.add_neq_o; exact Hne.
  Qed.

  Lemma lookup_empty {V} (k : raw_id) :
    Maps.lookup k (@Maps.empty raw_id V (rmap V) _) = None.
  Proof using.
    change (RM.find k (@RM.empty V) = None).
    apply RMF.F.empty_o.
  Qed.

  Definition init_local_env
    (bs : list (local_id * @dvalue (@ParamsV IP IPT))) : @local_env (@ParamsV IP IPT) :=
    List.fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty bs.

  Lemma init_local_env_in (bs : list (local_id * @dvalue (@ParamsV IP IPT))) (x : local_id) :
    In x (List.map fst bs) ->
    exists v, Maps.lookup x (init_local_env bs) = Some v.
  Proof using.
    induction bs as [| [k dv] rest IH]; intros Hin; [contradiction |].
    cbn [List.map fst] in Hin; cbn [init_local_env fold_right].
    destruct (RawIDOrd.eq_dec k x) as [<- | Hne].
    - exists dv; apply lookup_add_eq.
    - destruct Hin as [Heq | Hin]; [contradiction |].
      destruct (IH Hin) as [v Hv]; exists v.
      rewrite lookup_add_neq by exact Hne; exact Hv.
  Qed.

  Lemma combine_lists_varargs_dom {A B} (l1 : list A) (l2 : list B)
    (bs : list (A * B)) (vs : list B) :
    combine_lists_varargs l1 l2 = raise_ret (bs, vs) ->
    List.map fst bs = l1.
  Proof using.
    revert l2 bs vs; induction l1 as [| x xs IH]; intros [| y ys] bs vs Hc; cbn in Hc.
    - inversion Hc; reflexivity.
    - inversion Hc; reflexivity.
    - discriminate Hc.
    - destruct (combine_lists_varargs xs ys) as [| | | [l vargs]] eqn:E; cbn in Hc; try discriminate Hc.
      inversion Hc; subst; cbn; f_equal; eapply IH, E.
  Qed.

  (** *** Per-CFG Local-Environment Simulation ([cfg_local_sim]) *)

  Definition cls_vis_both {R1 R2}
    (r : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
         @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop)
    (env1 env2 : @local_env (@ParamsV IP IPT))
    {X1} (e1 : @CFGEtop (@ParamsV IP IPT) X1) (k1 : X1 -> @CFGtop (@ParamsV IP IPT) R1)
    {X2} (e2 : @CFGEtop (@ParamsV IP IPT) X2) (k2 : X2 -> @CFGtop (@ParamsV IP IPT) R2) : Prop :=
    (sync_non_local_cfg e1 = true /\
     EqE_CFG X1 X2 e1 e2 /\
     forall a1 a2,
       EqA_CFG X1 X2 e1 a1 e2 a2 ->
       cfg_event_post e1 a1 ->
       r env1 env2 (k1 a1) (k2 a2))
    \/
    (match e1 return (X1 -> @CFGtop (@ParamsV IP IPT) R1) -> Prop with
     | inr1 (inr1 (inr1 (inr1 (inl1 (inl1 le1))))) => fun k10 =>
         match e2 return (X2 -> @CFGtop (@ParamsV IP IPT) R2) -> Prop with
         | inr1 (inr1 (inr1 (inr1 (inl1 (inl1 le2))))) => fun k20 =>
             match le1 in LocalE Y1 return (Y1 -> @CFGtop (@ParamsV IP IPT) R1) -> Prop with
             | LocalRead x1 => fun k1' =>
                 match le2 in LocalE Y2 return (Y2 -> @CFGtop (@ParamsV IP IPT) R2) -> Prop with
                 | LocalRead x2 => fun k2' =>
                     x1 = x2 /\
                     Maps.lookup x1 env1 = Maps.lookup x1 env2 /\
                     forall v, Maps.lookup x1 env1 = Some v -> r env1 env2 (k1' v) (k2' v)
                 | _ => fun _ => False
                 end k20
             | _ => fun _ => False
             end k10
         | _ => fun _ => False
         end k2
     | _ => fun _ => False
     end k1).

  Definition cls_step_body {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (r : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
         @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop)
    (env1 env2 : @local_env (@ParamsV IP IPT))
    (ot1 : itree' (@CFGEtop (@ParamsV IP IPT)) R1)
    (ot2 : itree' (@CFGEtop (@ParamsV IP IPT)) R2) : Prop :=
    match ot1 with
    | RetF r1 =>
        match ot2 with
        | RetF r2 => RR env1 env2 r1 r2
        | _ => False
        end
    | TauF m1 =>
        match ot2 with
        | TauF m2 => r env1 env2 m1 m2
        | _ => False
        end
    | VisF _ e1 k1 =>
        is_ub_cfg e1 = true \/
        match ot2 with
        | VisF _ e2 k2 => cls_vis_both r env1 env2 e1 k1 e2 k2
        | _ => False
        end
    end.

  Inductive cfg_local_sim_ {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (r : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
         @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop)
    : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
      @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop :=
  | CLS_Step env1 env2 t1 t2 :
      cls_step_body RR r env1 env2 (observe t1) (observe t2) ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_TauL env1 env2 t1 m1 t2 :
      observe t1 = TauF m1 ->
      cfg_local_sim_ RR r env1 env2 m1 t2 ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_TauR env1 env2 t1 t2 m2 :
      observe t2 = TauF m2 ->
      cfg_local_sim_ RR r env1 env2 t1 m2 ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_ReadL env1 env2 t1 x v k1 t2 :
      t1 ≅ ITree.bind (ITree.trigger (LocalRead x)) k1 ->
      Maps.lookup x env1 = Some v ->
      cfg_local_sim_ RR r env1 env2 (k1 v) t2 ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_ReadR env1 env2 t1 t2 x v k2 :
      t2 ≅ ITree.bind (ITree.trigger (LocalRead x)) k2 ->
      Maps.lookup x env2 = Some v ->
      cfg_local_sim_ RR r env1 env2 t1 (k2 v) ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_WriteL env1 env2 t1 x v k1 t2 :
      t1 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) k1 ->
      cfg_local_sim_ RR r (Maps.add x v env1) env2 (k1 tt) t2 ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_WriteR env1 env2 t1 t2 x v k2 :
      t2 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) k2 ->
      cfg_local_sim_ RR r env1 (Maps.add x v env2) t1 (k2 tt) ->
      cfg_local_sim_ RR r env1 env2 t1 t2.

  Lemma cfg_local_sim__mon {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    monotone4 (cfg_local_sim_ RR).
  Proof using.
    intros env1 env2 t1 t2 r r' IN LE.
    induction IN as [env1 env2 t1 t2 Hstep
                     | env1 env2 t1 m1 t2 Ht1 _ IH
                     | env1 env2 t1 t2 m2 Ht2 _ IH
                     | env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                     | env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                     | env1 env2 t1 x v k1 t2 Ht1 _ IH
                     | env1 env2 t1 t2 x v k2 Ht2 _ IH].
    - apply CLS_Step; unfold cls_step_body in *.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + exact Hstep.
      + destruct (observe t2); [exact Hstep | apply LE, Hstep | exact Hstep].
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE | intros a1 a2 Ha Hp; apply LE, (HA a1 a2 Ha Hp)]].
        * right.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [x1 |]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [x2 |]; try contradiction.
          destruct Hrd as (Hx & Hlk & Hk); split; [exact Hx | split; [exact Hlk | intros v Hv; apply LE, Hk, Hv]].
    - eapply CLS_TauL; [exact Ht1 | exact IH].
    - eapply CLS_TauR; [exact Ht2 | exact IH].
    - eapply CLS_ReadL; [exact Ht1 | exact Hlk | exact IH].
    - eapply CLS_ReadR; [exact Ht2 | exact Hlk | exact IH].
    - eapply CLS_WriteL; [exact Ht1 | exact IH].
    - eapply CLS_WriteR; [exact Ht2 | exact IH].
  Qed.
  #[local] Hint Resolve cfg_local_sim__mon : paco.

  Definition cfg_local_sim {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env (@ParamsV IP IPT))
    (t1 : @CFGtop (@ParamsV IP IPT) R1)
    (t2 : @CFGtop (@ParamsV IP IPT) R2) : Prop :=
    paco4 (cfg_local_sim_ RR) bot4 env1 env2 t1 t2.

  Lemma cfg_local_sim__obs_eq {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (r r' : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
            @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop)
    (Hr_eq : forall env1 env2 a1 a1' a2 a2',
               a1 ≅ a1' -> a2 ≅ a2' -> r env1 env2 a1 a2 -> r' env1 env2 a1' a2') :
    forall env1 env2 t1 t1' t2 t2',
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      cfg_local_sim_ RR r env1 env2 t1 t2 ->
      cfg_local_sim_ RR r' env1 env2 t1' t2'.
  Proof using.
    intros env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
    revert t1' t2' E1 E2;
      induction Hsim as [env1 env2 t1 t2 Hstep
                         | env1 env2 t1 m1 t2 Ht1 _ IH
                         | env1 env2 t1 t2 m2 Ht2 _ IH
                         | env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                         | env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                         | env1 env2 t1 x v k1 t2 Ht1 _ IH
                         | env1 env2 t1 t2 x v k2 Ht2 _ IH];
      intros t1' t2' E1 E2.
    - punfold E1; red in E1; punfold E2; red in E2.
      apply CLS_Step; unfold cls_step_body in *.
      destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
        try inversion Hchk; pclearbot.
      + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; exact Hstep.
      + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA a1 a2 Ha Hp)].
        * right.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [x1 |]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [x2 |]; try contradiction.
          destruct Hrd as (Hx & Hlk & Hk); split; [exact Hx | split; [exact Hlk |]].
          intros v Hv; eapply Hr_eq; [apply Hk1 | apply Hk2 | apply Hk, Hv].
    - punfold E1; red in E1; rewrite Ht1 in E1;
        apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
      eapply CLS_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
    - punfold E2; red in E2; rewrite Ht2 in E2;
        apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
      eapply CLS_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
    - eapply CLS_ReadL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | exact Hlk | apply IH; [reflexivity | exact E2]].
    - eapply CLS_ReadR; [symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | exact Hlk | apply IH; [exact E1 | reflexivity]].
    - eapply CLS_WriteL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
    - eapply CLS_WriteR; [symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | apply IH; [exact E1 | reflexivity]].
  Qed.

  Lemma cfg_local_sim_obs_eq {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall env1 env2 t1 t1' t2 t2',
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      cfg_local_sim RR env1 env2 t1 t2 ->
      cfg_local_sim RR env1 env2 t1' t2'.
  Proof using.
    pcofix CIH.
    intros env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
    pstep; punfold Hsim.
    eapply cfg_local_sim__obs_eq; [| exact E1 | exact E2 | exact Hsim].
    intros e1 e2 a1 a1' a2 a2' Ea1 Ea2 Hr; pclearbot.
    right; eapply CIH; [exact Ea1 | exact Ea2 | exact Hr].
  Qed.

  Lemma cfg_local_sim_ret {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    env1 env2 (r1 : R1) (r2 : R2) :
    RR env1 env2 r1 r2 ->
    cfg_local_sim RR env1 env2 (Ret r1) (Ret r2).
  Proof using.
    intros HRR; pstep; apply CLS_Step; cbn; exact HRR.
  Qed.

  Lemma cfg_local_sim_bind {R1 R2 S1 S2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (RS : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> S1 -> S2 -> Prop)
    env1 env2
    (t1 : @CFGtop (@ParamsV IP IPT) R1) (t2 : @CFGtop (@ParamsV IP IPT) R2)
    (k1 : R1 -> @CFGtop (@ParamsV IP IPT) S1) (k2 : R2 -> @CFGtop (@ParamsV IP IPT) S2)
    (Ht : cfg_local_sim RR env1 env2 t1 t2)
    (Hk : forall env1' env2' r1 r2,
            RR env1' env2' r1 r2 -> cfg_local_sim RS env1' env2' (k1 r1) (k2 r2)) :
    cfg_local_sim RS env1 env2 (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using.
    revert env1 env2 t1 t2 Ht Hk; pcofix CIH; intros env1 env2 t1 t2 Ht Hk.
    punfold Ht.
    revert Hk;
      induction Ht as [env1 env2 t1 t2 Hstep
                       | env1 env2 t1 m1 t2 Ht1 _ IH
                       | env1 env2 t1 t2 m2 Ht2 _ IH
                       | env1 env2 t1 x v k1' t2 Ht1 Hlk _ IH
                       | env1 env2 t1 t2 x v k2' Ht2 Hlk _ IH
                       | env1 env2 t1 x v k1' t2 Ht1 _ IH
                       | env1 env2 t1 t2 x v k2' Ht2 _ IH];
      intros Hk.
    - unfold cls_step_body in Hstep.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1'] eqn:Hot1.
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        eapply paco4_mon;
          [eapply cfg_local_sim_obs_eq;
             [symmetry; rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity
             | symmetry; rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity
             | exact (Hk env1 env2 r1 r2 Hstep)]
          | intros ? ? ? ? []].
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction; pclearbot.
        pstep; apply CLS_Step; unfold cls_step_body.
        rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2.
        right; eapply CIH; [exact Hstep | exact Hk].
      + pstep; apply CLS_Step; unfold cls_step_body.
        rewrite (observe_bind t1 k1), Hot1.
        destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        rewrite (observe_bind t2 k2), Hot2.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot.
          right; eapply CIH; [exact HA | exact Hk].
        * right.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [x1 |]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [x2 |]; try contradiction.
          destruct Hrd as (Hx & Hlk & Hrd'); split; [exact Hx | split; [exact Hlk |]].
          intros v Hv; specialize (Hrd' v Hv); pclearbot.
          right; eapply CIH; [exact Hrd' | exact Hk].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_ReadL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_ReadR; [rewrite Ht2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_WriteL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_WriteR; [rewrite Ht2, Eqit.bind_bind; reflexivity | exact IH].
  Qed.

  Lemma cfg_local_sim_weaken {R1 R2}
    (RR RS : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (HRR : forall env1 env2 r1 r2, RR env1 env2 r1 r2 -> RS env1 env2 r1 r2) :
    forall env1 env2 t1 t2,
      cfg_local_sim RR env1 env2 t1 t2 ->
      cfg_local_sim RS env1 env2 t1 t2.
  Proof using.
    intros env1 env2 t1 t2 Hsim.
    rewrite <- (Eqit.bind_ret_r t1), <- (Eqit.bind_ret_r t2).
    eapply cfg_local_sim_bind; [exact Hsim |].
    intros e1 e2 r1 r2 Hr; apply cfg_local_sim_ret, HRR, Hr.
  Qed.

  Section IterSim.
    Context {I1 I2 R1 R2 : Type}.
    Variable (RI : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> I1 -> I2 -> Prop).
    Variable (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop).
    Variable (body1 : I1 -> @CFGtop (@ParamsV IP IPT) (I1 + R1)).
    Variable (body2 : I2 -> @CFGtop (@ParamsV IP IPT) (I2 + R2)).

    Definition iter_cont1 (lr : I1 + R1) : @CFGtop (@ParamsV IP IPT) R1 :=
      match lr with
      | inl j1 => Tau (ITree.iter body1 j1)
      | inr r1 => Ret r1
      end.

    Definition iter_cont2 (lr : I2 + R2) : @CFGtop (@ParamsV IP IPT) R2 :=
      match lr with
      | inl j2 => Tau (ITree.iter body2 j2)
      | inr r2 => Ret r2
      end.

    Definition iter_step_rel
      (e1 e2 : @local_env (@ParamsV IP IPT)) (s1 : I1 + R1) (s2 : I2 + R2) : Prop :=
      match s1, s2 with
      | inl j1, inl j2 => RI e1 e2 j1 j2
      | inr r1, inr r2 => RR e1 e2 r1 r2
      | _, _ => False
      end.

    Lemma cfg_local_sim_iter_aux
      (Hbody : forall env1 env2 i1 i2,
                 RI env1 env2 i1 i2 ->
                 cfg_local_sim iter_step_rel env1 env2 (body1 i1) (body2 i2)) :
      forall env1 env2
        (w1 : @CFGtop (@ParamsV IP IPT) (I1 + R1))
        (w2 : @CFGtop (@ParamsV IP IPT) (I2 + R2))
        (t1 : @CFGtop (@ParamsV IP IPT) R1)
        (t2 : @CFGtop (@ParamsV IP IPT) R2),
        ITree.bind w1 iter_cont1 ≅ t1 ->
        ITree.bind w2 iter_cont2 ≅ t2 ->
        cfg_local_sim iter_step_rel env1 env2 w1 w2 ->
        cfg_local_sim RR env1 env2 t1 t2.
    Proof using.
      pcofix CIH.
      intros env1 env2 w1 w2 t1 t2 Et1 Et2 Hw.
      pstep.
      eapply cfg_local_sim__mon with
        (r := fun e1 e2 a1 a2 =>
                exists v1 v2,
                  ITree.bind v1 iter_cont1 ≅ a1 /\
                  ITree.bind v2 iter_cont2 ≅ a2 /\
                  cfg_local_sim iter_step_rel e1 e2 v1 v2);
        [| intros e1 e2 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
           right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
      eapply cfg_local_sim__obs_eq;
        [intros e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
         exists v1, v2;
         split; [etransitivity; [exact Ev1 | exact Ea1] |];
         split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
        | exact Et1 | exact Et2 |].
      punfold Hw; clear t1 t2 Et1 Et2 CIH r.
      induction Hw as [e1 e2 w1 w2 Hstep
                       | e1 e2 w1 mw1 w2 Hw1 _ IH
                       | e1 e2 w1 w2 mw2 Hw2 _ IH
                       | e1 e2 w1 x v kw1 w2 Hw1 Hlk _ IH
                       | e1 e2 w1 w2 x v kw2 Hw2 Hlk _ IH
                       | e1 e2 w1 x v kw1 w2 Hw1 _ IH
                       | e1 e2 w1 w2 x v kw2 Hw2 _ IH].
      - unfold cls_step_body in Hstep.
        destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          destruct x1 as [j1 | r1], x2 as [j2 | r2]; cbn in Hstep; try contradiction.
          * apply CLS_Step; unfold cls_step_body.
            rewrite (observe_bind w1 iter_cont1), How1,
                    (observe_bind w2 iter_cont2), How2; cbn.
            exists (body1 j1), (body2 j2).
            split; [symmetry; apply unfold_iter |].
            split; [symmetry; apply unfold_iter |].
            apply Hbody, Hstep.
          * apply CLS_Step; unfold cls_step_body.
            rewrite (observe_bind w1 iter_cont1), How1,
                    (observe_bind w2 iter_cont2), How2; cbn.
            exact Hstep.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction; pclearbot.
          apply CLS_Step; unfold cls_step_body.
          rewrite (observe_bind w1 iter_cont1), How1,
                  (observe_bind w2 iter_cont2), How2.
          exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + apply CLS_Step; unfold cls_step_body.
          rewrite (observe_bind w1 iter_cont1), How1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 iter_cont2), How2.
          destruct Hvis as [(Hsync & HE & HA) | Hrd].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot.
            exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
          * right.
            destruct_sum1 ev1; try contradiction;
              destruct ev1 as [x1 |]; try contradiction;
              destruct_sum1 ev2; try contradiction;
              destruct ev2 as [x2 |]; try contradiction.
            destruct Hrd as (Hx & Hlk & Hrd'); split; [exact Hx | split; [exact Hlk |]].
            intros v Hv; specialize (Hrd' v Hv); pclearbot.
            exists (kw1 v), (kw2 v); split; [reflexivity | split; [reflexivity | exact Hrd']].
      - eapply CLS_TauL; [rewrite (observe_bind w1 iter_cont1), Hw1; reflexivity | exact IH].
      - eapply CLS_TauR; [rewrite (observe_bind w2 iter_cont2), Hw2; reflexivity | exact IH].
      - eapply CLS_ReadL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply CLS_ReadR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply CLS_WriteL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply CLS_WriteR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact IH].
    Qed.
  End IterSim.

  Lemma cfg_local_sim_iter {I1 I2 R1 R2}
    (RI : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> I1 -> I2 -> Prop)
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (body1 : I1 -> @CFGtop (@ParamsV IP IPT) (I1 + R1))
    (body2 : I2 -> @CFGtop (@ParamsV IP IPT) (I2 + R2))
    (Hbody : forall env1 env2 i1 i2,
               RI env1 env2 i1 i2 ->
               cfg_local_sim (iter_step_rel RI RR) env1 env2 (body1 i1) (body2 i2)) :
    forall env1 env2 i1 i2,
      RI env1 env2 i1 i2 ->
      cfg_local_sim RR env1 env2 (ITree.iter body1 i1) (ITree.iter body2 i2).
  Proof using.
    intros env1 env2 i1 i2 Hi.
    eapply (cfg_local_sim_iter_aux RI RR body1 body2 Hbody).
    - symmetry; apply unfold_iter.
    - symmetry; apply unfold_iter.
    - apply Hbody, Hi.
  Qed.

  Lemma is_ub_cfg_exc_none {X} (e : @CFGEtop (@ParamsV IP IPT) X) :
    is_ub_cfg e = true -> exc_of_event e = None.
  Proof using.
    destruct e as [c | m]; [discriminate |].
    destruct_sum1 m; try discriminate; destruct m; reflexivity.
  Qed.

  Lemma cfg_local_sim_run_exc_aux {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    let Rexc := fun e1 e2 (s1 : exc + R1) (s2 : exc + R2) =>
                  match s1, s2 with
                  | inl x1, inl x2 => x1 = x2
                  | inr r1, inr r2 => RR e1 e2 r1 r2
                  | _, _ => False
                  end in
    forall env1 env2
      (u1 : @CFGtop (@ParamsV IP IPT) R1)
      (u2 : @CFGtop (@ParamsV IP IPT) R2)
      (t1 : @CFGtop (@ParamsV IP IPT) (exc + R1))
      (t2 : @CFGtop (@ParamsV IP IPT) (exc + R2)),
      run_exc u1 ≅ t1 ->
      run_exc u2 ≅ t2 ->
      cfg_local_sim RR env1 env2 u1 u2 ->
      cfg_local_sim Rexc env1 env2 t1 t2.
  Proof using.
    cbv zeta; set (Rexc := fun e1 e2 (s1 : exc + R1) (s2 : exc + R2) =>
                             match s1, s2 with
                             | inl x1, inl x2 => x1 = x2
                             | inr r1, inr r2 => RR e1 e2 r1 r2
                             | _, _ => False
                             end).
    pcofix CIH.
    intros env1 env2 u1 u2 t1 t2 Et1 Et2 Hsim.
    pstep.
    eapply cfg_local_sim__mon with
      (r := fun e1 e2 a1 a2 =>
              exists v1 v2,
                run_exc v1 ≅ a1 /\
                run_exc v2 ≅ a2 /\
                cfg_local_sim RR e1 e2 v1 v2);
      [| intros e1 e2 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
         right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
    eapply cfg_local_sim__obs_eq;
      [intros e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
       exists v1, v2;
       split; [etransitivity; [exact Ev1 | exact Ea1] |];
       split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
      | exact Et1 | exact Et2 |].
    punfold Hsim; clear t1 t2 Et1 Et2 CIH r.
    induction Hsim as [e1 e2 u1 u2 Hstep
                       | e1 e2 u1 mu1 u2 Hu1 _ IH
                       | e1 e2 u1 u2 mu2 Hu2 _ IH
                       | e1 e2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | e1 e2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | e1 e2 u1 x v k1 u2 Hu1 _ IH
                       | e1 e2 u1 u2 x v k2 Hu2 _ IH].
    - eapply cfg_local_sim__obs_eq;
        [intros e1' e2' a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
         exists v1, v2;
         split; [etransitivity; [exact Ev1 | exact Ea1] |];
         split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
        | symmetry; apply unfold_run_exc_obs
        | symmetry; apply unfold_run_exc_obs |].
      unfold cls_step_body in Hstep.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply CLS_Step; cbn; exact Hstep.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction; pclearbot.
        apply CLS_Step; cbn.
        exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + destruct Hstep as [Hub | Hvis].
        * rewrite (is_ub_cfg_exc_none ev1 Hub).
          apply CLS_Step; cbn; left; exact Hub.
        * destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | Hrd].
          -- rewrite (EqE_CFG_exc_of_event ev1 ev2 HE).
             destruct (exc_of_event ev2) as [ex |].
             ++ apply CLS_Step; cbn; reflexivity.
             ++ apply CLS_Step; cbn; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot.
                exists (Tau (k1 a1)), (Tau (k2 a2)).
                split; [apply unfold_run_exc_obs |].
                split; [apply unfold_run_exc_obs |].
                pstep; eapply CLS_TauL; [reflexivity |];
                  eapply CLS_TauR; [reflexivity |].
                punfold HA; eapply cfg_local_sim__mon;
                  [exact HA | intros ? ? ? ? [Hl | []]; left; eapply paco4_mon; [exact Hl | intros ? ? ? ? []]].
          -- destruct_sum1 ev1; try contradiction;
               destruct ev1 as [x1 |]; try contradiction;
               destruct_sum1 ev2; try contradiction;
               destruct ev2 as [x2 |]; try contradiction.
             destruct Hrd as (Hx & Hlk & Hrd'); cbn [exc_of_event].
             apply CLS_Step; cbn; right; right.
             split; [exact Hx | split; [exact Hlk |]].
             intros v Hv; specialize (Hrd' v Hv); pclearbot.
             exists (Tau (k1 v)), (Tau (k2 v)).
             split; [apply unfold_run_exc_obs |].
             split; [apply unfold_run_exc_obs |].
             pstep; eapply CLS_TauL; [reflexivity |];
               eapply CLS_TauR; [reflexivity |].
             punfold Hrd'; eapply cfg_local_sim__mon;
               [exact Hrd' | intros ? ? ? ? [Hl | []]; left; eapply paco4_mon; [exact Hl | intros ? ? ? ? []]].
    - eapply cfg_local_sim__obs_eq with (t1 := Tau (run_exc mu1)) (t2 := run_exc u2);
        [intros e1' e2' a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
         exists v1, v2;
         split; [etransitivity; [exact Ev1 | exact Ea1] |];
         split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
        | symmetry; rewrite (unfold_run_exc_obs u1), Hu1; reflexivity
        | reflexivity |].
      eapply CLS_TauL; [reflexivity | exact IH].
    - eapply cfg_local_sim__obs_eq with (t1 := run_exc u1) (t2 := Tau (run_exc mu2));
        [intros e1' e2' a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
         exists v1, v2;
         split; [etransitivity; [exact Ev1 | exact Ea1] |];
         split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
        | reflexivity
        | symmetry; rewrite (unfold_run_exc_obs u2), Hu2; reflexivity |].
      eapply CLS_TauR; [reflexivity | exact IH].
    - eapply CLS_ReadL with (k1 := fun y => Tau (run_exc (k1 y))).
      + rewrite Hu1, bind_trigger, unfold_run_exc_obs; cbn [observe exc_of_event subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
        rewrite bind_trigger; reflexivity.
      + exact Hlk.
      + eapply CLS_TauL; [reflexivity | exact IH].
    - eapply CLS_ReadR with (k2 := fun y => Tau (run_exc (k2 y))).
      + rewrite Hu2, bind_trigger, unfold_run_exc_obs; cbn [observe exc_of_event subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
        rewrite bind_trigger; reflexivity.
      + exact Hlk.
      + eapply CLS_TauR; [reflexivity | exact IH].
    - eapply CLS_WriteL with (k1 := fun y => Tau (run_exc (k1 y))).
      + rewrite Hu1, bind_trigger, unfold_run_exc_obs; cbn [observe exc_of_event subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
        rewrite bind_trigger; reflexivity.
      + eapply CLS_TauL; [reflexivity | exact IH].
    - eapply CLS_WriteR with (k2 := fun y => Tau (run_exc (k2 y))).
      + rewrite Hu2, bind_trigger, unfold_run_exc_obs; cbn [observe exc_of_event subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
        rewrite bind_trigger; reflexivity.
      + eapply CLS_TauR; [reflexivity | exact IH].
  Qed.

  Lemma cfg_local_sim_run_exc {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall env1 env2
      (t1 : @CFGtop (@ParamsV IP IPT) R1)
      (t2 : @CFGtop (@ParamsV IP IPT) R2),
      cfg_local_sim RR env1 env2 t1 t2 ->
      cfg_local_sim
        (fun e1 e2 s1 s2 =>
           match s1, s2 with
           | inl x1, inl x2 => x1 = x2
           | inr r1, inr r2 => RR e1 e2 r1 r2
           | _, _ => False
           end)
        env1 env2 (run_exc t1) (run_exc t2).
  Proof using.
    intros env1 env2 t1 t2 Hsim.
    eapply cfg_local_sim_run_exc_aux; [reflexivity | reflexivity | exact Hsim].
  Qed.

  (** *** Call-Stack Simulation ([cfg_stack_sim] / [mcfg_stack_sim]) & [lift_cfg_local_pass] *)

  Definition env_stack := list (@local_env (@ParamsV IP IPT) * @local_env (@ParamsV IP IPT)).

  Definition css_vis_both {E : Type -> Type}
    (is_sync : forall X, E X -> bool)
    (EqE : prerel E E) (EqA : postrel E E)
    (ev_post : forall X, E X -> X -> Prop)
    (as_local : forall X, E X -> option (LocalE X))
    (as_stack : forall X, E X -> option (@StackE (@ParamsV IP IPT) X))
    {R1 R2}
    (r : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
         itree E R1 -> itree E R2 -> Prop)
    (stk : env_stack)
    (env1 env2 : @local_env (@ParamsV IP IPT))
    {X1} (e1 : E X1) (k1 : X1 -> itree E R1)
    {X2} (e2 : E X2) (k2 : X2 -> itree E R2) : Prop :=
    (is_sync X1 e1 = true /\
     EqE X1 X2 e1 e2 /\
     forall a1 a2,
       EqA X1 X2 e1 a1 e2 a2 ->
       ev_post X1 e1 a1 ->
       r stk env1 env2 (k1 a1) (k2 a2))
    \/
    (match as_local X1 e1, as_local X2 e2 with
     | Some le1, Some le2 =>
         match le1 in LocalE Y1 return (Y1 -> itree E R1) -> Prop with
         | LocalRead x1 => fun k1' =>
             match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
             | LocalRead x2 => fun k2' =>
                 x1 = x2 /\
                 Maps.lookup x1 env1 = Maps.lookup x1 env2 /\
                 forall v, Maps.lookup x1 env1 = Some v -> r stk env1 env2 (k1' v) (k2' v)
             | _ => fun _ => False
             end k2
         | LocalWrite x1 v1 => fun k1' =>
             match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
             | LocalWrite x2 v2 => fun k2' =>
                 x1 = x2 /\ v1 = v2 /\
                 r stk (Maps.add x1 v1 env1) (Maps.add x1 v1 env2) (k1' tt) (k2' tt)
             | _ => fun _ => False
             end k2
         end k1
     | _, _ => False
     end)
    \/
    (match as_stack X1 e1, as_stack X2 e2 with
     | Some se1, Some se2 =>
         match se1 in StackE Y1 return (Y1 -> itree E R1) -> Prop with
         | StackPush bs1 => fun k1' =>
             match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
             | StackPush bs2 => fun k2' =>
                 bs1 = bs2 /\
                 r ((env1, env2) :: stk) (init_local_env bs1) (init_local_env bs1) (k1' tt) (k2' tt)
             | _ => fun _ => False
             end k2
         | StackPop => fun k1' =>
             match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
             | StackPop => fun k2' =>
                 match stk with
                 | (p1, p2) :: rest => r rest p1 p2 (k1' tt) (k2' tt)
                 | [] => True
                 end
             | _ => fun _ => False
             end k2
         | _ => fun _ => False
         end k1
     | _, _ => False
     end).

  Definition as_local_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : option (@LocalE (@ParamsV IP IPT) X) :=
    match e with
    | inr1 (inr1 (inr1 (inl1 (inl1 le)))) => Some le
    | _ => None
    end.

  Definition as_stack_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : option (@StackE (@ParamsV IP IPT) X) :=
    match e with
    | inr1 (inr1 (inr1 (inl1 (inr1 se)))) => Some se
    | _ => None
    end.

  Definition as_local_cfg {X} (e : @CFGEtop (@ParamsV IP IPT) X) : option (@LocalE (@ParamsV IP IPT) X) :=
    match e with
    | inl1 _ => None
    | inr1 m => as_local_mcfg m
    end.

  Definition as_stack_cfg {X} (e : @CFGEtop (@ParamsV IP IPT) X) : option (@StackE (@ParamsV IP IPT) X) :=
    match e with
    | inl1 _ => None
    | inr1 m => as_stack_mcfg m
    end.

  Section GenStackSim.
    Context {E : Type -> Type} `{@LocalE (@ParamsV IP IPT) -< E}.
    Variable (is_ub : forall X, E X -> bool).
    Variable (is_sync : forall X, E X -> bool).
    Variable (EqE : prerel E E).
    Variable (EqA : postrel E E).
    Variable (ev_post : forall X, E X -> X -> Prop).
    Variable (as_loc : forall X, E X -> option (@LocalE (@ParamsV IP IPT) X)).
    Variable (as_stk : forall X, E X -> option (@StackE (@ParamsV IP IPT) X)).

    Definition gss_step_body {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (r : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
           itree E R1 -> itree E R2 -> Prop)
      (stk : env_stack) (env1 env2 : @local_env (@ParamsV IP IPT))
      (ot1 : itree' E R1) (ot2 : itree' E R2) : Prop :=
      match ot1 with
      | RetF r1 =>
          match ot2 with
          | RetF r2 => RR stk env1 env2 r1 r2
          | _ => False
          end
      | TauF m1 =>
          match ot2 with
          | TauF m2 => r stk env1 env2 m1 m2
          | _ => False
          end
      | VisF _ e1 k1 =>
          is_ub _ e1 = true \/
          match ot2 with
          | VisF _ e2 k2 => css_vis_both is_sync EqE EqA ev_post as_loc as_stk r stk env1 env2 e1 k1 e2 k2
          | _ => False
          end
      end.

    Inductive gen_stack_sim_ {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (r : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
           itree E R1 -> itree E R2 -> Prop)
      : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
        itree E R1 -> itree E R2 -> Prop :=
    | GSS_Step stk env1 env2 t1 t2 :
        gss_step_body RR r stk env1 env2 (observe t1) (observe t2) ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_TauL stk env1 env2 t1 m1 t2 :
        observe t1 = TauF m1 ->
        gen_stack_sim_ RR r stk env1 env2 m1 t2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_TauR stk env1 env2 t1 t2 m2 :
        observe t2 = TauF m2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 m2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_ReadL stk env1 env2 t1 x v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (LocalRead x)) k1 ->
        Maps.lookup x env1 = Some v ->
        gen_stack_sim_ RR r stk env1 env2 (k1 v) t2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_ReadR stk env1 env2 t1 t2 x v k2 :
        t2 ≅ ITree.bind (ITree.trigger (LocalRead x)) k2 ->
        Maps.lookup x env2 = Some v ->
        gen_stack_sim_ RR r stk env1 env2 t1 (k2 v) ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_WriteL stk env1 env2 t1 x v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) k1 ->
        gen_stack_sim_ RR r stk (Maps.add x v env1) env2 (k1 tt) t2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_WriteR stk env1 env2 t1 t2 x v k2 :
        t2 ≅ ITree.bind (ITree.trigger (LocalWrite x v)) k2 ->
        gen_stack_sim_ RR r stk env1 (Maps.add x v env2) t1 (k2 tt) ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2.

    Lemma gen_stack_sim__mon {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
      monotone5 (gen_stack_sim_ RR).
    Proof using.
      intros stk env1 env2 t1 t2 r r' IN LE.
      induction IN as [stk env1 env2 t1 t2 Hstep
                       | stk env1 env2 t1 m1 t2 Ht1 _ IH
                       | stk env1 env2 t1 t2 m2 Ht2 _ IH
                       | stk env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                       | stk env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                       | stk env1 env2 t1 x v k1 t2 Ht1 _ IH
                       | stk env1 env2 t1 t2 x v k2 Ht2 _ IH].
      - apply GSS_Step; unfold gss_step_body in *.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1].
        + exact Hstep.
        + destruct (observe t2); [exact Hstep | apply LE, Hstep | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE | intros a1 a2 Ha Hp; apply LE, (HA a1 a2 Ha Hp)]].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk | intros v Hv; apply LE, Hrd, Hv]].
            -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply LE, Hr]].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hbs Hr]; split; [exact Hbs | apply LE, Hr].
            -- destruct stk as [[p1 p2] rest |]; [apply LE, Hstk | exact I].
      - eapply GSS_TauL; [exact Ht1 | exact IH].
      - eapply GSS_TauR; [exact Ht2 | exact IH].
      - eapply GSS_ReadL; [exact Ht1 | exact Hlk | exact IH].
      - eapply GSS_ReadR; [exact Ht2 | exact Hlk | exact IH].
      - eapply GSS_WriteL; [exact Ht1 | exact IH].
      - eapply GSS_WriteR; [exact Ht2 | exact IH].
    Qed.

    Definition gen_stack_sim {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (stk : env_stack) (env1 env2 : @local_env (@ParamsV IP IPT))
      (t1 : itree E R1) (t2 : itree E R2) : Prop :=
      paco5 (gen_stack_sim_ RR) bot5 stk env1 env2 t1 t2.

    Lemma gen_stack_sim__obs_eq {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (r r' : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
              itree E R1 -> itree E R2 -> Prop)
      (Hr_eq : forall stk e1 e2 a1 a1' a2 a2',
                 a1 ≅ a1' -> a2 ≅ a2' -> r stk e1 e2 a1 a2 -> r' stk e1 e2 a1' a2') :
      forall stk env1 env2 t1 t1' t2 t2',
        t1 ≅ t1' ->
        t2 ≅ t2' ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2 ->
        gen_stack_sim_ RR r' stk env1 env2 t1' t2'.
    Proof using.
      intros stk env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
      revert t1' t2' E1 E2;
        induction Hsim as [stk env1 env2 t1 t2 Hstep
                           | stk env1 env2 t1 m1 t2 Ht1 _ IH
                           | stk env1 env2 t1 t2 m2 Ht2 _ IH
                           | stk env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                           | stk env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                           | stk env1 env2 t1 x v k1 t2 Ht1 _ IH
                           | stk env1 env2 t1 t2 x v k2 Ht2 _ IH];
        intros t1' t2' E1 E2.
      - punfold E1; red in E1; punfold E2; red in E2.
        apply GSS_Step; unfold gss_step_body in *.
        destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; pclearbot.
        + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; exact Hstep.
        + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA a1 a2 Ha Hp)].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; eapply Hr_eq; [apply Hk1 | apply Hk2 | apply Hrd, Hv].
            -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hr]]].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hbs Hr]; split; [exact Hbs | eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hr]].
            -- destruct stk as [[p1 p2] rest |]; [eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hstk] | exact I].
      - punfold E1; red in E1; rewrite Ht1 in E1;
          apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
        eapply GSS_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
      - punfold E2; red in E2; rewrite Ht2 in E2;
          apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
        eapply GSS_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
      - eapply GSS_ReadL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | exact Hlk | apply IH; [reflexivity | exact E2]].
      - eapply GSS_ReadR; [symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | exact Hlk | apply IH; [exact E1 | reflexivity]].
      - eapply GSS_WriteL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
      - eapply GSS_WriteR; [symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | apply IH; [exact E1 | reflexivity]].
    Qed.

    Lemma gen_stack_sim_obs_eq {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
      forall stk env1 env2 t1 t1' t2 t2',
        t1 ≅ t1' ->
        t2 ≅ t2' ->
        gen_stack_sim RR stk env1 env2 t1 t2 ->
        gen_stack_sim RR stk env1 env2 t1' t2'.
    Proof using.
      pcofix CIH.
      intros stk env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
      pstep; punfold Hsim.
      eapply gen_stack_sim__obs_eq; [| exact E1 | exact E2 | exact Hsim].
      intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 [Hr | Hr];
        [| inversion Hr].
      right; eapply CIH; [exact Ea1 | exact Ea2 | exact Hr].
    Qed.

    Lemma gen_stack_sim_bind {R1 R2 S1 S2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (RS : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> S1 -> S2 -> Prop)
      stk env1 env2
      (t1 : itree E R1) (t2 : itree E R2)
      (k1 : R1 -> itree E S1) (k2 : R2 -> itree E S2)
      (Ht : gen_stack_sim RR stk env1 env2 t1 t2)
      (Hk : forall stk' e1' e2' r1 r2,
              RR stk' e1' e2' r1 r2 -> gen_stack_sim RS stk' e1' e2' (k1 r1) (k2 r2)) :
      gen_stack_sim RS stk env1 env2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof using.
      pose proof (@gen_stack_sim__mon) as Hmon.
      revert stk env1 env2 t1 t2 Ht Hk; pcofix CIH; intros stk env1 env2 t1 t2 Ht Hk.
      punfold Ht.
      revert Hk;
        induction Ht as [stk env1 env2 t1 t2 Hstep
                         | stk env1 env2 t1 m1 t2 Ht1 _ IH
                         | stk env1 env2 t1 t2 m2 Ht2 _ IH
                         | stk env1 env2 t1 x v k1' t2 Ht1 Hlk _ IH
                         | stk env1 env2 t1 t2 x v k2' Ht2 Hlk _ IH
                         | stk env1 env2 t1 x v k1' t2 Ht1 _ IH
                         | stk env1 env2 t1 t2 x v k2' Ht2 _ IH];
        intros Hk.
      - unfold gss_step_body in Hstep.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1'] eqn:Hot1.
        + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          eapply paco5_mon;
            [eapply gen_stack_sim_obs_eq;
               [symmetry; rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity
               | symmetry; rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity
               | exact (Hk stk env1 env2 r1 r2 Hstep)]
            | intros ? ? ? ? ? []].
        + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          destruct Hstep as [Hstep | Hbot]; [| inversion Hbot].
          pstep; apply GSS_Step; unfold gss_step_body.
          rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2.
          right; eapply CIH; [exact Hstep | exact Hk].
        + pstep; apply GSS_Step; unfold gss_step_body.
          rewrite (observe_bind t1 k1), Hot1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          rewrite (observe_bind t2 k2), Hot2.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
            right; eapply CIH; [exact HA | exact Hk].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
               right; eapply CIH; [exact Hrd | exact Hk].
            -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
               split; [exact Hx | split; [exact Hv | right; eapply CIH; [exact Hr | exact Hk]]].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hbs [Hr | Hb]]; [| inversion Hb].
               split; [exact Hbs | right; eapply CIH; [exact Hr | exact Hk]].
            -- destruct stk as [[p1 p2] rest |]; [| exact I].
               destruct Hstk as [Hr | Hb]; [| inversion Hb].
               right; eapply CIH; [exact Hr | exact Hk].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_ReadL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_ReadR; [rewrite Ht2, Eqit.bind_bind; reflexivity | exact Hlk | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_WriteL; [rewrite Ht1, Eqit.bind_bind; reflexivity | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_WriteR; [rewrite Ht2, Eqit.bind_bind; reflexivity | eapply Hmon; [exact IH | auto]].
    Qed.

    Lemma gen_stack_sim_ret {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      stk env1 env2 (r1 : R1) (r2 : R2) :
      RR stk env1 env2 r1 r2 ->
      gen_stack_sim RR stk env1 env2 (Ret r1) (Ret r2).
    Proof using.
      intros HRR; pstep; apply GSS_Step; cbn; exact HRR.
    Qed.

    Lemma gen_stack_sim_trigger_sync {X} (e : E X)
      (Hsync : is_sync X e = true)
      (Hrefl : EqE X X e e)
      (Heq   : forall a1 a2, EqA X X e a1 e a2 -> a1 = a2)
      stk env1 env2 :
      gen_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (ITree.trigger e) (ITree.trigger e).
    Proof using.
      pstep; apply GSS_Step; unfold gss_step_body, ITree.trigger; cbn.
      right; left; split; [exact Hsync | split; [exact Hrefl |]].
      intros a1 a2 Ha _; apply Heq in Ha; subst a2.
      left; apply gen_stack_sim_ret; repeat split; reflexivity.
    Qed.
  End GenStackSim.

  #[local] Hint Resolve gen_stack_sim__mon : paco.

  Definition cfg_stack_sim {R1 R2} :=
    @gen_stack_sim (@CFGEtop (@ParamsV IP IPT)) _
      (@is_ub_cfg) (@sync_non_local_cfg) EqE_CFG EqA_CFG (@cfg_event_post)
      (@as_local_cfg) (@as_stack_cfg) R1 R2.

  Definition mcfg_stack_sim {R1 R2} :=
    @gen_stack_sim (@MCFGEtop (@ParamsV IP IPT)) _
      (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG (@mcfg_event_post)
      (@as_local_mcfg) (@as_stack_mcfg) R1 R2.

  Lemma cfg_local_to_stack_sim {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall (stk : env_stack) env1 env2
      (t1 : @CFGtop (@ParamsV IP IPT) R1)
      (t2 : @CFGtop (@ParamsV IP IPT) R2),
      cfg_local_sim RR env1 env2 t1 t2 ->
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ RR e1' e2' r1 r2)
        stk env1 env2 t1 t2.
  Proof using.
    intros stk; pcofix CIH; intros env1 env2 t1 t2 Hsim.
    pstep; punfold Hsim.
    induction Hsim as [env1 env2 t1 t2 Hstep
                       | env1 env2 t1 m1 t2 Ht1 _ IH
                       | env1 env2 t1 t2 m2 Ht2 _ IH
                       | env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                       | env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                       | env1 env2 t1 x v k1 t2 Ht1 _ IH
                       | env1 env2 t1 t2 x v k2 Ht2 _ IH].
    - apply GSS_Step; unfold gss_step_body; unfold cls_step_body in Hstep.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + destruct (observe t2); try contradiction; split; [reflexivity | exact Hstep].
      + destruct (observe t2); try contradiction; pclearbot; right; apply CIH, Hstep.
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot; right; apply CIH, HA.
        * right; left.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [x1 |]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [x2 |]; try contradiction.
          cbn [as_local_cfg as_local_mcfg].
          destruct Hrd as (Hx & Hlk & Hrd'); split; [exact Hx | split; [exact Hlk |]].
          intros v Hv; specialize (Hrd' v Hv); pclearbot; right; apply CIH, Hrd'.
    - eapply GSS_TauL; [exact Ht1 | exact IH].
    - eapply GSS_TauR; [exact Ht2 | exact IH].
    - eapply GSS_ReadL; [exact Ht1 | exact Hlk | exact IH].
    - eapply GSS_ReadR; [exact Ht2 | exact Hlk | exact IH].
    - eapply GSS_WriteL; [exact Ht1 | exact IH].
    - eapply GSS_WriteR; [exact Ht2 | exact IH].
  Qed.

  Lemma cfg_stack_sim_EOU {A} (m : EOU A) stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - unfold raiseOOM, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
    - unfold raiseUB, trigger_cast; pstep; apply GSS_Step; cbn; left; reflexivity.
    - unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
    - apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_stack_sim_apply_attrs attrs msg v stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (apply_attrs attrs msg v) (apply_attrs attrs msg v).
  Proof using.
    unfold apply_attrs.
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU |].
    intros ? ? ? v' _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    - unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[on n] |], v' as [[p | | | | | | |] | |];
        try (apply gen_stack_sim_ret; repeat split; reflexivity).
      unfold assert_dereferenceable.
      destruct ((on && (ptr_to_int p =? ptr_to_int null)%Z) || (Z.to_N (denote_int_syntax n) =? 0)%N).
      + apply gen_stack_sim_ret; repeat split; reflexivity.
      + eapply gen_stack_sim_bind.
        * unfold load, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
        * intros ? ? ? _ _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
    - intros ? ? ? [] _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_stack_sim_apply_args_attrs attrss msg args :
    forall stk env1 env2,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (apply_args_attrs attrss msg args) (apply_args_attrs attrss msg args).
  Proof using.
    revert attrss; induction args as [| v vs IH]; intros attrss stk env1 env2; cbn [apply_args_attrs].
    - apply gen_stack_sim_ret; repeat split; reflexivity.
    - destruct attrss as [| a r];
        (eapply gen_stack_sim_bind; [apply cfg_stack_sim_apply_attrs |];
         intros ? ? ? v' _ (-> & -> & -> & <-);
         eapply gen_stack_sim_bind; [apply IH |];
         intros ? ? ? vs' _ (-> & -> & -> & <-);
         apply gen_stack_sim_ret; repeat split; reflexivity).
  Qed.

  Lemma cfg_stack_sim_check_call_return fattrs ret_attrs ranges loc args rv stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2
      (check_call_return fattrs ret_attrs ranges loc args rv)
      (check_call_return fattrs ret_attrs ranges loc args rv).
  Proof using.
    unfold check_call_return.
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU |].
    intros ? ? ? [] _ (-> & -> & -> & <-).
    destruct rv as [ex | v].
    - apply gen_stack_sim_ret; repeat split; reflexivity.
    - eapply gen_stack_sim_bind; [apply cfg_stack_sim_apply_attrs |].
      intros ? ? ? v' _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_stack_sim_EOU_ret {A} (m : EOU A) stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 =>
         stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ m = raise_ret r1)
      stk env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply GSS_Step; cbn.
      right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _]].
    - unfold raiseUB, trigger_cast; pstep; apply GSS_Step; cbn; left; reflexivity.
    - unfold raise, trigger_cast, ITree.trigger; pstep; apply GSS_Step; cbn.
      right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _]].
    - apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_stack_sim_denote_function (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (Hproto : df_prototype df1 = df_prototype df2)
    (Hargs  : df_args df1 = df_args df2)
    (Hbody  : forall env va,
                (forall x, In x (df_args df1) -> exists v, Maps.lookup x env = Some v) ->
                cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                  env env (denote_cfg (df_instrs df1) va) (denote_cfg (df_instrs df2) va)) :
    forall stk env1 env2 cc args,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (denote_function df1 cc args) (denote_function df2 cc args).
  Proof using.
    intros stk env1 env2 cc args.
    unfold denote_function, push_call_frame, pop_call_frame.
    rewrite Hproto, Hargs.
    destruct (dc_param_attrs (df_prototype df2)) as [ret_attrs args_attrs].
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_apply_args_attrs | intros ? ? ? args' _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind; reflexivity | symmetry; rewrite !Eqit.bind_bind; reflexivity |].
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU_ret | intros ? ? ? [bs vs] _ (-> & -> & -> & <- & Ecomb)].
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU | intros ? ? ? dts _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_bind.
    { unfold mem_push, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
    intros ? ? ? [] _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    { unfold stack_push, trigger_cast; pstep; apply GSS_Step; unfold gss_step_body, ITree.trigger; cbn.
      right; right; right; split; [reflexivity |].
      left; apply gen_stack_sim_ret; repeat split; reflexivity. }
    intros ? ? ? [] _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    { unfold alloca, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
    intros ? ? ? varargs _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    { unfold store, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
    intros ? ? ? [] _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    { destruct varargs as [[p | | | | | | |] | |];
        try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
             [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]).
      apply gen_stack_sim_ret; repeat split; reflexivity. }
    intros ? ? ? varg _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    { apply cfg_local_to_stack_sim.
      eapply cfg_local_sim_weaken;
        [intros e1 e2 s1 s2 Hs; destruct s1, s2; try contradiction; f_equal; exact Hs |].
      apply cfg_local_sim_run_exc.
      apply Hbody.
      intros x Hx; rewrite Hargs in Hx.
      apply init_local_env_in.
      rewrite (combine_lists_varargs_dom _ _ _ _ Ecomb); exact Hx. }
    intros ? final_e1 final_e2 rv _ (-> & <-).
    eapply gen_stack_sim_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind; reflexivity | symmetry; rewrite !Eqit.bind_bind; reflexivity |].
    eapply gen_stack_sim_bind.
    { unfold stack_pop, trigger_cast; pstep; apply GSS_Step; unfold gss_step_body, ITree.trigger; cbn.
      right; right; right.
      left; apply gen_stack_sim_ret; repeat split; reflexivity. }
    intros ? ? ? [] _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    { unfold mem_pop, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
    intros ? ? ? [] _ (-> & -> & -> & <-).
    apply cfg_stack_sim_check_call_return.
  Qed.

  #[local] Definition mrec_ctx
    (fundefs : IntMap (@function_denotation (@ParamsV IP IPT)))
    : @CallE (@ParamsV IP IPT) ~> @CFGtop (@ParamsV IP IPT) :=
    fun T call_ev =>
      match call_ev with
      | Call dt cc fv args =>
          @ExtLib.Structures.Monad.bind (@CFGtop (@ParamsV IP IPT)) _ _ _
            (EOU_to_itree (check_callee fv))
            (fun _ =>
               match lookup_defn fv fundefs with
               | Some f_den => f_den cc args
               | None => Functor.fmap inr (external_call dt fv args)
               end)
      end.

  #[local] Lemma denote_mcfg_eq_interp_mrec
    (fundefs : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT))
    (args : list (@dvalue (@ParamsV IP IPT))) :
    denote_mcfg fundefs dt fv args =
    interp_mrec (mrec_ctx fundefs) (mrec_ctx fundefs _ (Call dt CC_Ccc fv args)).
  Proof using.
    unfold denote_mcfg, mrec; reflexivity.
  Qed.

  #[local] Lemma cfg_stack_sim_mrec_ctx
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk env1 env2 cc args,
                     cfg_stack_sim
                       (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                       stk env1 env2 (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall stk env1 env2 X (c1 c2 : @CallE (@ParamsV IP IPT) X),
      EqE_Call X X c1 c2 ->
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (mrec_ctx ctx1 X c1) (mrec_ctx ctx2 X c2).
  Proof using.
    intros stk env1 env2 X [dt1 cc1 fv1 fas1] [dt2 cc2 fv2 fas2] (<- & <- & <- & <-).
    unfold mrec_ctx; cbn [ExtLib.Structures.Monad.bind Monad_itree].
    eapply gen_stack_sim_bind;
      [apply cfg_stack_sim_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
    assert (Hext :
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2
        (Functor.fmap inr (external_call dt1 fv1 fas1))
        (Functor.fmap inr (external_call dt1 fv1 fas1))).
    { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
      eapply gen_stack_sim_bind.
      - apply gen_stack_sim_trigger_sync; [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
      - intros ? ? ? dv _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity. }
    unfold lookup_defn.
    destruct fv1 as [[p | | | | | | |] | |]; try exact Hext.
    pose proof (Hctx (ptr_to_int p)) as Hlk.
    destruct (lookup (ptr_to_int p) ctx1) as [f1 |],
             (lookup (ptr_to_int p) ctx2) as [f2 |];
      inversion Hlk as [? ? Hf12 |]; subst.
    - apply Hf12.
    - exact Hext.
  Qed.

  (** Lift [cfg_stack_sim] across [interp_mrec] (`denote_mcfg`). *)
  Lemma cfg_to_mcfg_stack_sim_mrec
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk env1 env2 cc args,
                     cfg_stack_sim
                       (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                       stk env1 env2 (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      stk env1 env2
      (u1 : @CFGtop (@ParamsV IP IPT) R1)
      (u2 : @CFGtop (@ParamsV IP IPT) R2)
      (t1 : @MCFGtop (@ParamsV IP IPT) R1)
      (t2 : @MCFGtop (@ParamsV IP IPT) R2),
      interp_mrec (mrec_ctx ctx1) u1 ≅ t1 ->
      interp_mrec (mrec_ctx ctx2) u2 ≅ t2 ->
      cfg_stack_sim RR stk env1 env2 u1 u2 ->
      mcfg_stack_sim RR stk env1 env2 t1 t2.
  Proof using.
    intros R1 R2 RR.
    pose proof (cfg_stack_sim_mrec_ctx ctx1 ctx2 Hctx) as Hcall.
    pcofix CIH.
    intros stk env1 env2 u1 u2 t1 t2 Et1 Et2 Hsim.
    pstep.
    eapply gen_stack_sim__mon with
      (r := fun s0 e1 e2 a1 a2 =>
              exists v1 v2,
                interp_mrec (mrec_ctx ctx1) v1 ≅ a1 /\
                interp_mrec (mrec_ctx ctx2) v2 ≅ a2 /\
                cfg_stack_sim RR s0 e1 e2 v1 v2);
      [| intros s0 e1 e2 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
         right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
    eapply gen_stack_sim__obs_eq;
      [intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
       exists v1, v2;
       split; [etransitivity; [exact Ev1 | exact Ea1] |];
       split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
      | exact Et1 | exact Et2 |].
    punfold Hsim; clear t1 t2 Et1 Et2 CIH r.
    induction Hsim as [stk env1 env2 u1 u2 Hstep
                       | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 _ IH].
    - eapply gen_stack_sim__obs_eq;
        [intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
         exists v1, v2;
         split; [etransitivity; [exact Ev1 | exact Ea1] |];
         split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
        | symmetry; apply unfold_interp_mrec
        | symmetry; apply unfold_interp_mrec |].
      unfold gss_step_body in Hstep.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply GSS_Step; cbn; exact Hstep.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hstep as [Hstep | Hb]; [| inversion Hb].
        apply GSS_Step; cbn.
        exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + destruct Hstep as [Hub | Hvis].
        * destruct ev1 as [ce1 | me1]; [discriminate Hub |].
          apply GSS_Step; cbn; left; exact Hub.
        * destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          -- destruct ev1 as [ce1 | me1], ev2 as [ce2 | me2]; cbn in HE; try contradiction.
             ++ (* CallE! [unfold_interp_mrec] produces [Tau (interp_mrec ... (bind ...))]! *)
                destruct ce1 as [dt1 cc1 fv1 fas1], ce2 as [dt2 cc2 fv2 fas2].
                destruct HE as (<- & <- & <- & <-).
                apply GSS_Step; cbn.
                exists (ITree.bind (mrec_ctx ctx1 _ (Call dt1 cc1 fv1 fas1)) k1),
                       (ITree.bind (mrec_ctx ctx2 _ (Call dt1 cc1 fv1 fas1)) k2).
                split; [reflexivity | split; [reflexivity |]].
                eapply gen_stack_sim_bind.
                ** apply Hcall; repeat split; reflexivity.
                ** intros ? ? ? rv1 rv2 (-> & -> & -> & <-).
                   specialize (HA rv1 rv1 Logic.eq_refl I); destruct HA as [HA | Hb]; [exact HA | inversion Hb].
             ++ (* Non-Call MCFGEtop sync event *)
                apply GSS_Step; cbn; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
                exists (Tau (k1 a1)), (Tau (k2 a2)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold HA; eapply gen_stack_sim__mon;
                  [exact HA | intros ? ? ? ? ? [Hl | []]; left; eapply paco5_mon; [exact Hl | intros ? ? ? ? ? []]].
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn in Hloc; try contradiction.
             destruct (as_local_mcfg me1) as [le1 |] eqn:Ele1,
                      (as_local_mcfg me2) as [le2 |] eqn:Ele2; try contradiction.
             destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
             ++ destruct Hloc as (Hx & Hlk & Hrd).
                apply GSS_Step; cbn; right; right; left.
                rewrite Ele1, Ele2; split; [exact Hx | split; [exact Hlk |]].
                intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
                exists (Tau (k1 v)), (Tau (k2 v)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold Hrd; eapply gen_stack_sim__mon;
                  [exact Hrd | intros ? ? ? ? ? [Hl | []]; left; eapply paco5_mon; [exact Hl | intros ? ? ? ? ? []]].
             ++ destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
                apply GSS_Step; cbn; right; right; left.
                rewrite Ele1, Ele2; split; [exact Hx | split; [exact Hv |]].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold Hr; eapply gen_stack_sim__mon;
                  [exact Hr | intros ? ? ? ? ? [Hl | []]; left; eapply paco5_mon; [exact Hl | intros ? ? ? ? ? []]].
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn in Hstk; try contradiction.
             destruct (as_stack_mcfg me1) as [se1 |] eqn:Ese1,
                      (as_stack_mcfg me2) as [se2 |] eqn:Ese2; try contradiction.
             destruct se1, se2; try contradiction.
             ++ destruct Hstk as [Hbs [Hr | Hb]]; [| inversion Hb].
                apply GSS_Step; cbn; right; right; right; rewrite Ese1, Ese2.
                split; [exact Hbs |].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold Hr; eapply gen_stack_sim__mon;
                  [exact Hr | intros ? ? ? ? ? [Hl | []]; left; eapply paco5_mon; [exact Hl | intros ? ? ? ? ? []]].
             ++ apply GSS_Step; cbn; right; right; right; rewrite Ese1, Ese2.
                destruct stk as [[p1 p2] rest |]; [| exact I].
                destruct Hstk as [Hr | Hb]; [| inversion Hb].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold Hr; eapply gen_stack_sim__mon;
                  [exact Hr | intros ? ? ? ? ? [Hl | []]; left; eapply paco5_mon; [exact Hl | intros ? ? ? ? ? []]].
    - eapply gen_stack_sim__obs_eq with (t1 := Tau (interp_mrec (mrec_ctx ctx1) mu1))
                                        (t2 := interp_mrec (mrec_ctx ctx2) u2);
        [intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
         exists v1, v2;
         split; [etransitivity; [exact Ev1 | exact Ea1] |];
         split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
        | symmetry; rewrite unfold_interp_mrec, Hu1; reflexivity
        | reflexivity |].
      eapply GSS_TauL; [reflexivity | exact IH].
    - eapply gen_stack_sim__obs_eq with (t1 := interp_mrec (mrec_ctx ctx1) u1)
                                        (t2 := Tau (interp_mrec (mrec_ctx ctx2) mu2));
        [intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv);
         exists v1, v2;
         split; [etransitivity; [exact Ev1 | exact Ea1] |];
         split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]
        | reflexivity
        | symmetry; rewrite unfold_interp_mrec, Hu2; reflexivity |].
      eapply GSS_TauR; [reflexivity | exact IH].
    - eapply GSS_ReadL with (k1 := fun y => Tau (interp_mrec (mrec_ctx ctx1) (k1 y))).
      + rewrite Hu1, bind_trigger, unfold_interp_mrec; cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
        rewrite bind_trigger; reflexivity.
      + exact Hlk.
      + eapply GSS_TauL; [reflexivity | exact IH].
    - eapply GSS_ReadR with (k2 := fun y => Tau (interp_mrec (mrec_ctx ctx2) (k2 y))).
      + rewrite Hu2, bind_trigger, unfold_interp_mrec; cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
        rewrite bind_trigger; reflexivity.
      + exact Hlk.
      + eapply GSS_TauR; [reflexivity | exact IH].
    - eapply GSS_WriteL with (k1 := fun y => Tau (interp_mrec (mrec_ctx ctx1) (k1 y))).
      + rewrite Hu1, bind_trigger, unfold_interp_mrec; cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
        rewrite bind_trigger; reflexivity.
      + eapply GSS_TauL; [reflexivity | exact IH].
    - eapply GSS_WriteR with (k2 := fun y => Tau (interp_mrec (mrec_ctx ctx2) (k2 y))).
      + rewrite Hu2, bind_trigger, unfold_interp_mrec; cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
        rewrite bind_trigger; reflexivity.
      + eapply GSS_TauR; [reflexivity | exact IH].
  Qed.

  (** Lift [mcfg_stack_sim] across [interp_intrinsics]. *)
  Lemma mcfg_stack_sim_EOU {A} (m : EOU A) stk env1 env2 :
    mcfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - unfold raiseOOM, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
    - unfold raiseUB, trigger_cast; pstep; apply GSS_Step; cbn; left; reflexivity.
    - unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
    - apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Definition sem_fn_sync (sem : @semantic_function (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _) : Prop :=
    forall args va stk env1 env2,
      mcfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (sem args va) (sem args va).

  Lemma pure_to_semantic_sync pf :
    sem_fn_sync (pure_to_semantic pf).
  Proof using.
    intros args va stk env1 env2; unfold pure_to_semantic; apply mcfg_stack_sim_EOU.
  Qed.

  Lemma pure_base_to_semantic_sync pbf :
    sem_fn_sync (pure_base_to_semantic pbf).
  Proof using.
    unfold pure_base_to_semantic; apply pure_to_semantic_sync.
  Qed.

  Lemma Forall_map_pure_to_semantic {A} (f : A -> declaration dtyp * _) (l : list A)
    (Hf : forall x, sem_fn_sync (snd (f x))) :
    Forall (fun p => sem_fn_sync (snd p)) (List.map f l).
  Proof using.
    induction l as [| x xs IH]; constructor; [apply Hf | exact IH].
  Qed.

  Lemma defined_intrinsics_sync :
    Forall (fun p => sem_fn_sync (snd p))
      (@defined_intrinsics (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _).
  Proof using.
    unfold defined_intrinsics, extra_fp_intrinsics, extra_int_intrinsics,
           mk_int_unop_defs, mk_int_unop_flag_defs, mk_int_binop_defs,
           mk_expect_int_defs, mk_int_ternop_defs, mk_int_ovf_binop_defs.
    repeat apply Forall_app;
      try (apply Forall_map_pure_to_semantic; intros; cbn [snd];
           first [apply pure_to_semantic_sync | apply pure_base_to_semantic_sync]);
      try (repeat constructor; cbn [snd]; apply pure_base_to_semantic_sync).
    repeat constructor; cbn [snd]; try apply pure_base_to_semantic_sync.
    - (* llvm_va_start *)
      intros args va stk env1 env2; unfold llvm_va_start.
      destruct args as [| a [| ? ?]], va as [vp |];
        try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
             [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]).
      destruct a as [[p | | | | | | |] | |];
        try (eapply gen_stack_sim_bind;
             [unfold store, trigger_cast; apply gen_stack_sim_trigger_sync;
              [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]
             | intros ? ? ? [] _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity]).
      unfold raiseUB, trigger_cast; pstep; apply GSS_Step; cbn; left; reflexivity.
    - (* llvm_va_end *)
      intros args va stk env1 env2; unfold llvm_va_end; apply gen_stack_sim_ret; repeat split; reflexivity.
    - (* llvm_va_copy *)
      intros args va stk env1 env2; unfold llvm_va_copy.
      destruct args as [| dst [| src [| ? ?]]];
        try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
             [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]).
      eapply gen_stack_sim_bind.
      + unfold load, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
      + intros ? ? ? vargs _ (-> & -> & -> & <-).
        eapply gen_stack_sim_bind.
        * unfold store, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? [] _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma handle_intrinsics_sync {X} (ie : @IntrinsicE (@ParamsV IP IPT) X) stk env1 env2 :
    mcfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2
      (handle_intrinsics ie) (handle_intrinsics ie).
  Proof using.
    destruct ie as [dt fname args va]; cbn [handle_intrinsics].
    pose proof defined_intrinsics_sync as Hdefs.
    unfold defs_assoc.
    induction Hdefs as [| [decl sem] rest Hsem _ IH]; cbn [List.map].
    - cbn; unfold ITree.trigger; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
    - cbn [snd] in Hsem.
      set (nm := match dc_name decl with Name s => s | _ => ""%string end).
      cbn [assoc].
      destruct (Eqv.eqv_dec_p fname nm) as [_ | _].
      + apply Hsem.
      + exact IH.
  Qed.

  Definition intr_cont {R : Type} (x : R + @MCFGtop (@ParamsV IP IPT) R)
    : @MCFGtop (@ParamsV IP IPT) R :=
    match x with
    | inl r => Ret r
    | inr u => Tau (interp_intrinsics u)
    end.

  Definition decomp_intr {R : Type} (u : @MCFGtop (@ParamsV IP IPT) R)
    : @MCFGtop (@ParamsV IP IPT) (R + @MCFGtop (@ParamsV IP IPT) R) :=
    match observe u with
    | RetF r => Ret (inl r)
    | TauF m => Ret (inr m)
    | VisF _ ev k => ITree.bind (interp_intrinsics_h ev) (fun x => Ret (inr (k x)))
    end.

  Lemma decomp_intr_spec {R : Type} (u : @MCFGtop (@ParamsV IP IPT) R) :
    ITree.bind (decomp_intr u) intr_cont ≅ interp_intrinsics u.
  Proof using.
    unfold interp_intrinsics, decomp_intr; rewrite unfold_interp.
    destruct (observe u) as [r | m | X ev k]; cbn -[interp_intrinsics_h].
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros x ? <-; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma mcfg_stack_sim_interp_intrinsics {R1 R2}
    (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall stk env1 env2
      (u1 : @MCFGtop (@ParamsV IP IPT) R1)
      (u2 : @MCFGtop (@ParamsV IP IPT) R2),
      mcfg_stack_sim RR stk env1 env2 u1 u2 ->
      mcfg_stack_sim RR stk env1 env2 (interp_intrinsics u1) (interp_intrinsics u2).
  Proof using.
    set (intr_rel := fun s0 e1 e2 (x1 : R1 + @MCFGtop (@ParamsV IP IPT) R1)
                                  (x2 : R2 + @MCFGtop (@ParamsV IP IPT) R2) =>
                       match x1, x2 with
                       | inl r1, inl r2 => RR s0 e1 e2 r1 r2
                       | inr v1, inr v2 => mcfg_stack_sim RR s0 e1 e2 v1 v2
                       | _, _ => False
                       end).
    assert (Hstep_decomp :
      forall stk env1 env2
        (u1 : @MCFGtop (@ParamsV IP IPT) R1)
        (u2 : @MCFGtop (@ParamsV IP IPT) R2),
        gss_step_body (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
          (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg)
          RR (upaco5 (gen_stack_sim_ (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
                        (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg) RR) bot5)
          stk env1 env2 (observe u1) (observe u2) ->
        mcfg_stack_sim intr_rel stk env1 env2 (decomp_intr u1) (decomp_intr u2)).
    { intros stk env1 env2 u1 u2 Hstep.
      unfold gss_step_body, decomp_intr in *.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply gen_stack_sim_ret; exact Hstep.
      - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hstep as [Hstep | Hb]; [| inversion Hb].
        apply gen_stack_sim_ret; exact Hstep.
      - destruct Hstep as [Hub | Hvis].
        + destruct_sum1 ev1; try discriminate Hub; destruct ev1 as [u].
          pstep; apply GSS_Step; unfold gss_step_body; rewrite observe_bind; cbn; left; reflexivity.
        + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * destruct ev1 as [ec1 | [ie1 | re1]], ev2 as [ec2 | [ie2 | re2]]; cbn in HE; try contradiction.
            -- cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ E_trigger]; unfold ITree.trigger.
               pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
               right; left; split; [reflexivity | split; [exact HE |]].
               intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
               left; eapply gen_stack_sim_obs_eq;
                 [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
               apply gen_stack_sim_ret; exact HA.
            -- destruct ie1 as [dt1 fn1 args1 va1], ie2 as [dt2 fn2 args2 va2].
               destruct HE as (<- & <- & <- & <-); cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
               eapply gen_stack_sim_bind; [apply handle_intrinsics_sync |].
               intros ? ? ? a1 _ (-> & -> & -> & <-).
               specialize (HA a1 a1 Logic.eq_refl I); destruct HA as [HA | Hb]; [| inversion Hb].
               apply gen_stack_sim_ret; exact HA.
            -- cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger]; unfold ITree.trigger.
               pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
               right; left; split; [exact Hsync | split; [exact HE |]].
               intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
               left; eapply gen_stack_sim_obs_eq;
                 [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
               apply gen_stack_sim_ret; exact HA.
          * destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                     (as_local_mcfg ev2) as [le2 |] eqn:Ele2; try contradiction.
            destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction;
              destruct_sum1 ev1; try discriminate Ele1;
              destruct_sum1 ev2; try discriminate Ele2;
              inversion Ele1; subst; inversion Ele2; subst;
              cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger]; unfold ITree.trigger.
            -- destruct Hloc as (<- & Hlk & Hrd).
               pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
               right; right; left; split; [reflexivity | split; [exact Hlk |]].
               intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
               left; eapply gen_stack_sim_obs_eq;
                 [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
               apply gen_stack_sim_ret; exact Hrd.
            -- destruct Hloc as (<- & <- & [Hr | Hb]); [| inversion Hb].
               pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
               right; right; left; split; [reflexivity | split; [reflexivity |]].
               left; eapply gen_stack_sim_obs_eq;
                 [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
               apply gen_stack_sim_ret; exact Hr.
          * destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                     (as_stack_mcfg ev2) as [se2 |] eqn:Ese2; try contradiction.
            destruct se1, se2; try contradiction;
              destruct_sum1 ev1; try discriminate Ese1;
              destruct_sum1 ev2; try discriminate Ese2;
              inversion Ese1; subst; inversion Ese2; subst;
              cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger]; unfold ITree.trigger.
            -- destruct Hstk as [<- [Hr | Hb]]; [| inversion Hb].
               pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
               right; right; right; split; [reflexivity |].
               left; eapply gen_stack_sim_obs_eq;
                 [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
               apply gen_stack_sim_ret; exact Hr.
            -- pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
               right; right; right.
               destruct stk as [[p1 p2] rest |]; [| exact I].
               destruct Hstk as [Hr | Hb]; [| inversion Hb].
               left; eapply gen_stack_sim_obs_eq;
                 [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
               apply gen_stack_sim_ret; exact Hr. }
    set (r_both := fun s0 e1 e2 (a1 : @MCFGtop (@ParamsV IP IPT) R1)
                                (a2 : @MCFGtop (@ParamsV IP IPT) R2) =>
                     (exists v1 v2,
                        interp_intrinsics v1 ≅ a1 /\
                        interp_intrinsics v2 ≅ a2 /\
                        mcfg_stack_sim RR s0 e1 e2 v1 v2) \/
                     (exists w1 w2,
                        ITree.bind w1 intr_cont ≅ a1 /\
                        ITree.bind w2 intr_cont ≅ a2 /\
                        mcfg_stack_sim intr_rel s0 e1 e2 w1 w2)).
    assert (Hr_eq :
      forall s0 e1 e2 a1 a1' a2 a2',
        a1 ≅ a1' -> a2 ≅ a2' -> r_both s0 e1 e2 a1 a2 -> r_both s0 e1 e2 a1' a2').
    { intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 [(v1 & v2 & Ev1 & Ev2 & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - left; exists v1, v2; split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hv]].
      - right; exists w1, w2; split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hw]]. }
    assert (Hbranch_b :
      forall stk env1 env2 w1 w2 t1 t2,
        ITree.bind w1 intr_cont ≅ t1 ->
        ITree.bind w2 intr_cont ≅ t2 ->
        mcfg_stack_sim intr_rel stk env1 env2 w1 w2 ->
        gen_stack_sim_ (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
          (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg) RR r_both
          stk env1 env2 t1 t2).
    { intros stk env1 env2 w1 w2 t1 t2 Et1 Et2 Hw.
      eapply gen_stack_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hw; clear t1 t2 Et1 Et2.
      induction Hw as [stk env1 env2 w1 w2 Hstep
                       | stk env1 env2 w1 mw1 w2 Hw1 _ IH
                       | stk env1 env2 w1 w2 mw2 Hw2 _ IH
                       | stk env1 env2 w1 x v kw1 w2 Hw1 Hlk _ IH
                       | stk env1 env2 w1 w2 x v kw2 Hw2 Hlk _ IH
                       | stk env1 env2 w1 x v kw1 w2 Hw1 _ IH
                       | stk env1 env2 w1 w2 x v kw2 Hw2 _ IH].
      - unfold gss_step_body in Hstep.
        destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          destruct x1 as [r1 | v1], x2 as [r2 | v2]; cbn in Hstep; try contradiction.
          * apply GSS_Step; unfold gss_step_body; rewrite !observe_bind, How1, How2; cbn; exact Hstep.
          * apply GSS_Step; unfold gss_step_body; rewrite !observe_bind, How1, How2; cbn.
            left; exists v1, v2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          destruct Hstep as [Hstep | Hb]; [| inversion Hb].
          apply GSS_Step; unfold gss_step_body; rewrite !observe_bind, How1, How2.
          right; exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + apply GSS_Step; unfold gss_step_body; rewrite (observe_bind w1 intr_cont), How1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 intr_cont), How2.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
            right; exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
          * right; left.
            destruct (as_local_mcfg ev1) as [le1 |], (as_local_mcfg ev2) as [le2 |]; try contradiction.
            destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction.
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
               right; exists (kw1 v), (kw2 v); split; [reflexivity | split; [reflexivity | exact Hrd]].
            -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
               split; [exact Hx | split; [exact Hv | right; exists (kw1 tt), (kw2 tt); split; [reflexivity | split; [reflexivity | exact Hr]]]].
          * right; right.
            destruct (as_stack_mcfg ev1) as [se1 |], (as_stack_mcfg ev2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hbs [Hr | Hb]]; [| inversion Hb].
               split; [exact Hbs | right; exists (kw1 tt), (kw2 tt); split; [reflexivity | split; [reflexivity | exact Hr]]].
            -- destruct stk as [[p1 p2] rest |]; [| exact I].
               destruct Hstk as [Hr | Hb]; [| inversion Hb].
               right; exists (kw1 tt), (kw2 tt); split; [reflexivity | split; [reflexivity | exact Hr]].
      - eapply GSS_TauL; [rewrite (observe_bind w1 intr_cont), Hw1; reflexivity | exact IH].
      - eapply GSS_TauR; [rewrite (observe_bind w2 intr_cont), Hw2; reflexivity | exact IH].
      - eapply GSS_ReadL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GSS_ReadR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GSS_WriteL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GSS_WriteR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact IH]. }
    assert (Hbranch_a :
      forall stk env1 env2 u1 u2 t1 t2,
        interp_intrinsics u1 ≅ t1 ->
        interp_intrinsics u2 ≅ t2 ->
        mcfg_stack_sim RR stk env1 env2 u1 u2 ->
        gen_stack_sim_ (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
          (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg) RR r_both
          stk env1 env2 t1 t2).
    { intros stk env1 env2 u1 u2 t1 t2 Et1 Et2 Hu.
      eapply gen_stack_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hu; clear t1 t2 Et1 Et2.
      induction Hu as [stk env1 env2 u1 u2 Hstep
                       | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 _ IH].
      - eapply Hbranch_b; [apply decomp_intr_spec | apply decomp_intr_spec | apply Hstep_decomp, Hstep].
      - eapply gen_stack_sim__obs_eq with (t1 := Tau (interp_intrinsics mu1))
                                          (t2 := interp_intrinsics u2);
          [exact Hr_eq | symmetry; unfold interp_intrinsics; rewrite unfold_interp, Hu1; reflexivity | reflexivity |].
        eapply GSS_TauL; [reflexivity | exact IH].
      - eapply gen_stack_sim__obs_eq with (t1 := interp_intrinsics u1)
                                          (t2 := Tau (interp_intrinsics mu2));
          [exact Hr_eq | reflexivity | symmetry; unfold interp_intrinsics; rewrite unfold_interp, Hu2; reflexivity |].
        eapply GSS_TauR; [reflexivity | exact IH].
      - eapply GSS_ReadL with (k1 := fun y => Tau (interp_intrinsics (k1 y))).
        + unfold interp_intrinsics; rewrite Hu1, bind_trigger, unfold_interp;
            cbn [observe interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun inr1 inl1].
          rewrite bind_trigger; reflexivity.
        + exact Hlk.
        + eapply GSS_TauL; [reflexivity | exact IH].
      - eapply GSS_ReadR with (k2 := fun y => Tau (interp_intrinsics (k2 y))).
        + unfold interp_intrinsics; rewrite Hu2, bind_trigger, unfold_interp;
            cbn [observe interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun inr1 inl1].
          rewrite bind_trigger; reflexivity.
        + exact Hlk.
        + eapply GSS_TauR; [reflexivity | exact IH].
      - eapply GSS_WriteL with (k1 := fun y => Tau (interp_intrinsics (k1 y))).
        + unfold interp_intrinsics; rewrite Hu1, bind_trigger, unfold_interp;
            cbn [observe interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun inr1 inl1].
          rewrite bind_trigger; reflexivity.
        + eapply GSS_TauL; [reflexivity | exact IH].
      - eapply GSS_WriteR with (k2 := fun y => Tau (interp_intrinsics (k2 y))).
        + unfold interp_intrinsics; rewrite Hu2, bind_trigger, unfold_interp;
            cbn [observe interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun inr1 inl1].
          rewrite bind_trigger; reflexivity.
        + eapply GSS_TauR; [reflexivity | exact IH]. }
    assert (Hmain :
      forall stk env1 env2 t1 t2,
        r_both stk env1 env2 t1 t2 ->
        mcfg_stack_sim RR stk env1 env2 t1 t2).
    { pcofix CIH.
      intros stk env1 env2 t1 t2 Hrb; pstep.
      eapply gen_stack_sim__mon with (r := r_both);
        [| intros s0 e1 e2 a1 a2 Hr; right; apply CIH, Hr].
      destruct Hrb as [(v1 & v2 & Ev1 & Ev2 & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - eapply Hbranch_a; eassumption.
      - eapply Hbranch_b; eassumption. }
    intros stk env1 env2 u1 u2 Hsim.
    apply Hmain; left; exists u1, u2; split; [reflexivity | split; [reflexivity | exact Hsim]].
  Qed.

  (** ***Lowering [mcfg_stack_sim] to [interp_state interp_vellvm_prov_h] *)

  Definition sf_match (e1 e2 : @local_env (@ParamsV IP IPT))
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) : Prop :=
    sf1.(stack_vars) = e1 /\
    sf2.(stack_vars) = e2 /\
    sf1.(stack_exc) = sf2.(stack_exc) /\
    sf1.(stack_loc) = sf2.(stack_loc).

  Inductive stk_frames_match :
    env_stack -> list (@stack_frame (@ParamsV IP IPT)) -> list (@stack_frame (@ParamsV IP IPT)) -> Prop :=
  | SFM_nil : stk_frames_match [] [] []
  | SFM_cons p1 p2 sf1 sf2 rest fstk1 fstk2 :
      sf_match p1 p2 sf1 sf2 ->
      stk_frames_match rest fstk1 fstk2 ->
      stk_frames_match ((p1, p2) :: rest) (sf1 :: fstk1) (sf2 :: fstk2).

  Definition fused_state_match
    (stk : env_stack) (env1 env2 : @local_env (@ParamsV IP IPT))
    (s1 s2 : FusedS) : Prop :=
    let '(m1, ((sf1, fstk1), g1)) := s1 in
    let '(m2, ((sf2, fstk2), g2)) := s2 in
    m1 = m2 /\
    g1 = g2 /\
    sf_match env1 env2 sf1 sf2 /\
    stk_frames_match stk fstk1 fstk2.

  Lemma lift_bot_prov_ret {T} (x : T) :
    lift_bot_prov (Ret x) ≅ Ret x.
  Proof using.
    unfold lift_bot_prov; rewrite unfold_translate; reflexivity.
  Qed.

  Lemma fused_local_prov_read_some (x : local_id) (v : @dvalue (@ParamsV IP IPT)) (s : FusedS)
    (Hlk : let '(_, ((sf, _), _)) := s in Maps.lookup x sf.(stack_vars) = Some v) :
    fused_local_prov _ (LocalRead x) s ≅ Ret (s, v).
  Proof using.
    destruct s as [m [[sf fstk] g]].
    unfold fused_local_prov, on_ls_prov, handle_local_stack, handle_local_debug,
           handle_local, update_locals_ref; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
    rewrite Hlk, !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l.
    destruct sf; cbn [upd_local_sf stack_vars stack_exc stack_loc]; reflexivity.
  Qed.

  Lemma fused_local_prov_read_none (x : local_id) (s : FusedS)
    (Hlk : let '(_, ((sf, _), _)) := s in Maps.lookup x sf.(stack_vars) = None) :
    exists msg k,
      fused_local_prov _ (LocalRead x) s ≅
        Vis (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (Throw msg))))))) k.
  Proof using.
    destruct s as [m [[sf fstk] g]].
    unfold fused_local_prov, on_ls_prov, handle_local_stack, handle_local_debug,
           handle_local, update_locals_ref, raise, trigger_cast, ITree.trigger;
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
    rewrite Hlk, !Eqit.bind_vis.
    unfold lift_bot_prov; rewrite unfold_translate; cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
    rewrite Eqit.bind_vis.
    eexists _, _; reflexivity.
  Qed.

  Lemma fused_local_prov_write (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (m : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    fused_local_prov _ (LocalWrite x v) (m, ((sf, fstk), g)) ≅
      Ret ((m, ((upd_local_sf sf (Maps.add x v sf.(stack_vars)), fstk), g)), tt).
  Proof using.
    unfold fused_local_prov, on_ls_prov, handle_local_stack, handle_local_debug,
           handle_local, update_locals_ref; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
    rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma memM_interp_prov_post {X} (P : X -> Prop)
    (m : @memM (@ParamsV IP IPT) _ X) (Hm : memM_all_ret P m) :
    forall (σ : state) (U : list N),
      refine_prov (fun _ '(σ1, r1) '(σ2, r2) => σ1 = σ2 /\ r1 = r2 /\ P r1)
        U (memM_interp_prov m σ) (memM_interp_prov m σ).
  Proof using.
    induction m as [x | s | s | s | k IH | σ' k IH | c k IH]; intros σ U; cbn in *.
    - pstep; apply RP_Step; cbn; split; [reflexivity | split; [reflexivity | exact Hm]].
    - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn.
      right; right; split; [exact I | intros [] [] _].
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn; left; reflexivity.
    - unfold raise, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn.
      right; right; split; [exact I | intros [] [] _].
    - apply IH, Hm.
    - apply (IH tt Hm).
    - destruct c as [sz align | |]; cbn in *.
      + apply IH, Hm.
      + pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
        right; right; intros p _.
        left; eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l | apply IH, Hm].
      + apply IH, Hm.
  Qed.

  Lemma interp_vellvm_prov_h_stack_sync {X1 X2}
    (e1 : @MCFGEtop (@ParamsV IP IPT) X1) (e2 : @MCFGEtop (@ParamsV IP IPT) X2)
    (Hsync : sync_non_local_mcfg e1 = true)
    (HE : EqE_MCFG X1 X2 e1 e2)
    stk env1 env2 (s1 s2 : FusedS)
    (Hmatch : fused_state_match stk env1 env2 s1 s2)
    (U : list N) :
    refine_prov
      (fun _ '(s1', a1) '(s2', a2) =>
         fused_state_match stk env1 env2 s1' s2' /\
         EqA_MCFG X1 X2 e1 a1 e2 a2 /\
         mcfg_event_post e1 a1)
      U (interp_vellvm_prov_h e1 s1) (interp_vellvm_prov_h e2 s2).
  Proof using.
    destruct s1 as [m1 [[sf1 fstk1] g1]], s2 as [m2 [[sf2 fstk2] g2]].
    destruct Hmatch as (<- & <- & Hsf & Hsfm).
    destruct_sum2 e1 e2 HE; try discriminate Hsync.
    - (* ExternalCallE *)
      destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov;
        (eapply refine_prov_bind;
         [apply refine_prov_refl with (RR := fun _ a1 a2 => a1 = a2); intros; reflexivity
         | intros U' a1 a2 _ <-; pstep; apply RP_Step; cbn;
           repeat (first [exact Hsf | exact Hsfm | reflexivity | split])]).
    - (* IntrinsicE *)
      destruct e1, e2; destruct HE as (<- & <- & <- & <-).
      unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_intrinsic_prov, on_mem_prov.
      eapply refine_prov_bind;
        [apply refine_prov_refl with (RR := fun _ p1 p2 => p1 = p2); intros; reflexivity |].
      intros U' [m' r] _ _ <-; pstep; apply RP_Step; cbn.
      repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
    - (* GlobalE *)
      destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_global_prov, on_genv_prov;
        (eapply refine_prov_bind;
         [apply refine_prov_refl with (RR := fun _ p1 p2 => p1 = p2); intros; reflexivity
         | intros U' [g' r] _ _ <-; pstep; apply RP_Step; cbn;
           repeat (first [exact Hsf | exact Hsfm | reflexivity | split])]).
    - (* StackE: only StackRaise / StackGetExc satisfy Hsync *)
      destruct e1, e2; cbn in HE; try contradiction; try discriminate Hsync.
      + subst; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_stack_prov, on_ls_prov, handle_stack.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
        destruct Hsf as (Hv1 & Hv2 & Hexc & Hloc).
        pstep; apply RP_Step; cbn; repeat split; try exact Hv1; try exact Hv2; try exact Hloc; try exact Hsfm; reflexivity.
      + unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_stack_prov, on_ls_prov, handle_stack.
        destruct Hsf as (Hv1 & Hv2 & Hexc & Hloc).
        rewrite <- Hexc.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
        pstep; apply RP_Step; cbn; repeat split; try exact Hv1; try exact Hv2; try exact Hloc; try exact Hsfm; reflexivity.
    - (* MemoryE *)
      assert (Hme_eq : e1 = e2) by
        (destruct e1, e2; cbn in HE; try contradiction;
         repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst; reflexivity).
      subst e2.
      unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_memory_prov, on_mem_prov, handle_memory.
      eapply refine_prov_bind.
      + apply (memM_interp_prov_post _ (handle_memoryM e1) (handle_memoryM_post e1)).
      + intros U' [m1' r1] [m2' r2] _ (-> & <- & Hpost).
        pstep; apply RP_Step; cbn [rp_step_body observe fused_state_match mcfg_event_post].
        split; [repeat (first [exact Hsf | exact Hsfm | reflexivity | split]) |].
        split; [destruct e1; cbn; reflexivity | exact Hpost].
    - (* DrawE *)
      destruct e1 as [dt1], e2 as [dt2]; cbn in HE; subst dt2.
      unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_draw_prov, handle_draw.
      destruct (default_dvalue_of_dtyp dt1) as [s | s | s | dv] eqn:Edef; cbn [EOU_to_itree].
      + unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
        pstep; apply RP_Step; unfold rp_step_body.
        repeat (rewrite observe_bind || rewrite observe_translate); cbn; right; right; split; [exact I | intros [] [] _].
      + unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
        pstep; apply RP_Step; unfold rp_step_body.
        repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
      + unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
        pstep; apply RP_Step; unfold rp_step_body.
        repeat (rewrite observe_bind || rewrite observe_translate); cbn; right; right; split; [exact I | intros [] [] _].
      + eapply refine_prov_obs_eq;
          [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
        pstep; apply RP_Step; cbn.
        split; [repeat (first [exact Hsf | exact Hsfm | reflexivity | split]) |].
        split; [reflexivity | intros Hsc; eapply default_dvalue_scalar_typ; eassumption].
    - (* OOME *)
      destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; right; right; split; [exact I | intros [] [] _].
    - (* LLVMExcE *)
      destruct e1, e2; cbn in HE; subst; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; right; right; split; [reflexivity | intros [] [] _].
    - (* UBE *)
      destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - (* DebugE *)
      destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
      right; right; split; [exact I | intros [] [] _].
      left; eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      pstep; apply RP_Step; cbn.
      repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
    - (* FailureE *)
      destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Definition decomp_model {R : Type} (u : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS)
    : itree ProvBotE (model_step_state R) :=
    match observe u with
    | RetF r => Ret (inl (s, r))
    | TauF m => Ret (inr (s, m))
    | VisF _ e k => ITree.bind (interp_vellvm_prov_h e s) (fun '(s', x) => Ret (inr (s', k x)))
    end.

  Lemma decomp_model_spec {R : Type} (u : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    ITree.bind (decomp_model u s) (model_cont R) ≅ interp_state interp_vellvm_prov_h u s.
  Proof using.
    unfold decomp_model; rewrite (unfold_interp_state interp_vellvm_prov_h u s).
    destruct (observe u) as [r | m | X e k]; cbn -[interp_vellvm_prov_h].
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Definition model_stack_step_rel {R1 R2}
    (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    : list N -> model_step_state R1 -> model_step_state R2 -> Prop :=
    fun _ x1 x2 =>
      match x1, x2 with
      | inl (s1, r1), inl (s2, r2) =>
          exists stk e1 e2, fused_state_match stk e1 e2 s1 s2 /\ RR stk e1 e2 r1 r2
      | inr (s1, u1), inr (s2, u2) =>
          exists stk e1 e2, fused_state_match stk e1 e2 s1 s2 /\ mcfg_stack_sim RR stk e1 e2 u1 u2
      | _, _ => False
      end.

  Lemma mcfg_stack_sim_to_model {R1 R2}
    (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall U stk env1 env2 (s1 s2 : FusedS)
      (u1 : @MCFGtop (@ParamsV IP IPT) R1)
      (u2 : @MCFGtop (@ParamsV IP IPT) R2),
      fused_state_match stk env1 env2 s1 s2 ->
      mcfg_stack_sim RR stk env1 env2 u1 u2 ->
      refine_prov
        (fun _ '(s1', r1) '(s2', r2) =>
           exists stk' e1' e2', fused_state_match stk' e1' e2' s1' s2' /\ RR stk' e1' e2' r1 r2)
        U
        (interp_state interp_vellvm_prov_h u1 s1)
        (interp_state interp_vellvm_prov_h u2 s2).
  Proof using.
    set (RR_out := fun (_ : list N) '(s1', r1) '(s2', r2) =>
                     exists stk' e1' e2',
                       fused_state_match stk' e1' e2' s1' s2' /\ RR stk' e1' e2' r1 r2).
    assert (Hstep_decomp :
      forall U stk env1 env2 (s1 s2 : FusedS)
        (u1 : @MCFGtop (@ParamsV IP IPT) R1)
        (u2 : @MCFGtop (@ParamsV IP IPT) R2),
        fused_state_match stk env1 env2 s1 s2 ->
        gss_step_body (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
          (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg)
          RR (upaco5 (gen_stack_sim_ (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
                        (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg) RR) bot5)
          stk env1 env2 (observe u1) (observe u2) ->
        refine_prov (model_stack_step_rel RR) U (decomp_model u1 s1) (decomp_model u2 s2)).
    { intros U stk env1 env2 s1 s2 u1 u2 Hmatch Hstep.
      unfold gss_step_body, decomp_model in *.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        pstep; apply RP_Step; cbn; exists stk, env1, env2; split; assumption.
      - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hstep as [Hstep | Hb]; [| inversion Hb].
        pstep; apply RP_Step; cbn; exists stk, env1, env2; split; assumption.
      - destruct Hstep as [Hub | Hvis].
        + destruct_sum1 ev1; try discriminate Hub; destruct ev1 as [u].
          pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
        + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * eapply refine_prov_bind;
              [eapply interp_vellvm_prov_h_stack_sync; eassumption |].
            intros U' [s1' a1] [s2' a2] _ (Hm' & Ha & Hp).
            specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
            pstep; apply RP_Step; cbn; exists stk, env1, env2; split; [exact Hm' | exact HA].
          * destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                     (as_local_mcfg ev2) as [le2 |] eqn:Ele2; try contradiction.
            destruct le1 as [x1 | x1 v1], le2 as [x2 | x2 v2]; try contradiction;
              destruct_sum1 ev1; try discriminate Ele1;
              destruct_sum1 ev2; try discriminate Ele2;
              inversion Ele1; subst; inversion Ele2; subst;
              unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
              destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
            -- destruct Hloc as (<- & Hlk_eq & Hrd).
               pose proof Hmatch as (Hmm & Hgg & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
               destruct (Maps.lookup x1 env1) as [v |] eqn:Elkv.
               ++ assert (Elkv2 : Maps.lookup x1 env2 = Some v) by congruence.
                  eapply refine_prov_obs_eq.
                  ** symmetry; rewrite (fused_local_prov_read_some x1 v (mm1, ((sf1, fstk1), gg1))
                                         (ltac:(rewrite Hvars1; exact Elkv))), Eqit.bind_ret_l; reflexivity.
                  ** symmetry; rewrite (fused_local_prov_read_some x1 v (mm2, ((sf2, fstk2), gg2))
                                         (ltac:(rewrite Hvars2; exact Elkv2))), Eqit.bind_ret_l; reflexivity.
                  ** specialize (Hrd v Elkv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
                     pstep; apply RP_Step; cbn; exists stk, env1, env2; split; [exact Hmatch | exact Hrd].
               ++ assert (Elkv2 : Maps.lookup x1 env2 = None) by congruence.
                  destruct (fused_local_prov_read_none x1 (mm1, ((sf1, fstk1), gg1))
                              (ltac:(rewrite Hvars1; exact Elkv))) as (msg1 & kf1 & Ef1).
                  destruct (fused_local_prov_read_none x1 (mm2, ((sf2, fstk2), gg2))
                              (ltac:(rewrite Hvars2; exact Elkv2))) as (msg2 & kf2 & Ef2).
                  eapply refine_prov_obs_eq;
                    [symmetry; rewrite Ef1, Eqit.bind_vis; reflexivity
                    | symmetry; rewrite Ef2, Eqit.bind_vis; reflexivity |].
                  pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
            -- destruct Hloc as (<- & <- & [Hr | Hb]); [| inversion Hb].
               destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
               eapply refine_prov_obs_eq;
                 [symmetry; rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity
                 | symmetry; rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity |].
               pstep; apply RP_Step; cbn.
               exists stk, (Maps.add x1 v1 env1), (Maps.add x1 v1 env2); split; [| exact Hr].
               rewrite Hvars1, Hvars2; repeat split; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
          * destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                     (as_stack_mcfg ev2) as [se2 |] eqn:Ese2; try contradiction.
            destruct se1, se2; try contradiction;
              destruct_sum1 ev1; try discriminate Ese1;
              destruct_sum1 ev2; try discriminate Ese2;
              inversion Ese1; subst; inversion Ese2; subst;
              unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
              destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]];
              destruct Hmatch as (<- & <- & Hsf & Hsfm).
            -- destruct Hstk as [<- [Hr | Hb]]; [| inversion Hb].
               unfold fused_stack_prov, on_ls_prov, handle_stack; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
               eapply refine_prov_obs_eq;
                 [symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity
                 | symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity |].
               pstep; apply RP_Step; cbn.
               exists ((env1, env2) :: stk), (init_local_env l), (init_local_env l).
               split; [| exact Hr].
               repeat split; try reflexivity.
               apply SFM_cons; [exact Hsf | exact Hsfm].
            -- destruct stk as [[p1 p2] rest |].
               ++ destruct Hstk as [Hr | Hb]; [| inversion Hb].
                  inversion Hsfm as [| ? ? sf1' sf2' ? fstk1' fstk2' Hsf' Hsfm']; subst.
                  unfold fused_stack_prov, on_ls_prov, handle_stack; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
                  eapply refine_prov_obs_eq;
                    [symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity
                    | symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity |].
                  pstep; apply RP_Step; cbn.
                  exists rest, p1, p2; split; [| exact Hr].
                  repeat (first [exact Hsf' | exact Hsfm' | reflexivity | split]).
               ++ inversion Hsfm; subst.
                  unfold fused_stack_prov, on_ls_prov, handle_stack, raise, trigger_cast, ITree.trigger, lift_bot_prov;
                    cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_stateT Monad_itree].
                  pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn.
                  right; right; split; [exact I | intros [] [] _]. }
    set (r_both := fun U0 (a1 : itree ProvBotE (FusedS * R1)) (a2 : itree ProvBotE (FusedS * R2)) =>
                     (exists stk e1 e2 s1 s2 v1 v2,
                        interp_state interp_vellvm_prov_h v1 s1 ≅ a1 /\
                        interp_state interp_vellvm_prov_h v2 s2 ≅ a2 /\
                        fused_state_match stk e1 e2 s1 s2 /\
                        mcfg_stack_sim RR stk e1 e2 v1 v2) \/
                     (exists w1 w2,
                        ITree.bind w1 (model_cont R1) ≅ a1 /\
                        ITree.bind w2 (model_cont R2) ≅ a2 /\
                        refine_prov (model_stack_step_rel RR) U0 w1 w2)).
    assert (Hr_eq :
      forall U0 a1 a1' a2 a2',
        a1 ≅ a1' -> a2 ≅ a2' -> r_both U0 a1 a2 -> r_both U0 a1' a2').
    { intros U0 a1 a1' a2 a2' Ea1 Ea2
        [(stk & e1 & e2 & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - left; exists stk, e1, e2, s1, s2, v1, v2.
        split; [etransitivity; eassumption | split; [etransitivity; eassumption | split; assumption]].
      - right; exists w1, w2.
        split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hw]]. }
    assert (Hbranch_b :
      forall U0 w1 w2 t1 t2,
        ITree.bind w1 (model_cont R1) ≅ t1 ->
        ITree.bind w2 (model_cont R2) ≅ t2 ->
        refine_prov (model_stack_step_rel RR) U0 w1 w2 ->
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
          * destruct Hstep as (stk & e1 & e2 & Hm & Hv).
            apply RP_Step; unfold rp_step_body; rewrite !observe_bind, How1, How2; cbn.
            left; exists stk, e1, e2, s1, s2, v1, v2;
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
      forall U0 stk env1 env2 s1 s2 u1 u2 t1 t2,
        interp_state interp_vellvm_prov_h u1 s1 ≅ t1 ->
        interp_state interp_vellvm_prov_h u2 s2 ≅ t2 ->
        fused_state_match stk env1 env2 s1 s2 ->
        mcfg_stack_sim RR stk env1 env2 u1 u2 ->
        refine_prov_ RR_out r_both U0 t1 t2).
    { intros U0 stk env1 env2 s1 s2 u1 u2 t1 t2 Et1 Et2 Hmatch Hu.
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hu; clear t1 t2 Et1 Et2.
      revert s1 s2 Hmatch;
        induction Hu as [stk env1 env2 u1 u2 Hstep
                         | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                         | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                         | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                         | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                         | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                         | stk env1 env2 u1 u2 x v k2 Hu2 _ IH];
        intros s1 s2 Hmatch.
      - eapply Hbranch_b;
          [apply decomp_model_spec | apply decomp_model_spec | eapply Hstep_decomp; eassumption].
      - eapply refine_prov__obs_eq with (t1 := Tau (interp_state interp_vellvm_prov_h mu1 s1))
                                        (t2 := interp_state interp_vellvm_prov_h u2 s2);
          [exact Hr_eq
          | symmetry; rewrite (unfold_interp_state interp_vellvm_prov_h u1 s1), Hu1; reflexivity
          | reflexivity |].
        eapply RP_TauL; [reflexivity | apply IH, Hmatch].
      - eapply refine_prov__obs_eq with (t1 := interp_state interp_vellvm_prov_h u1 s1)
                                        (t2 := Tau (interp_state interp_vellvm_prov_h mu2 s2));
          [exact Hr_eq
          | reflexivity
          | symmetry; rewrite (unfold_interp_state interp_vellvm_prov_h u2 s2), Hu2; reflexivity |].
        eapply RP_TauR; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        pose proof Hmatch as (_ & _ & (Hvars1 & _) & _).
        eapply refine_prov__obs_eq with (t1 := Tau (interp_state interp_vellvm_prov_h (k1 v) (mm1, ((sf1, fstk1), gg1))))
                                        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis; cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun inr1 inl1].
          rewrite (fused_local_prov_read_some x v (mm1, ((sf1, fstk1), gg1)) (ltac:(rewrite Hvars1; exact Hlk))),
                  Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        pose proof Hmatch as (_ & _ & (_ & Hvars2 & _) & _).
        eapply refine_prov__obs_eq with (t1 := interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)))
                                        (t2 := Tau (interp_state interp_vellvm_prov_h (k2 v) (mm2, ((sf2, fstk2), gg2)))).
        + exact Hr_eq.
        + reflexivity.
        + symmetry; rewrite Hu2, bind_trigger, interp_state_vis; cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun inr1 inl1].
          rewrite (fused_local_prov_read_some x v (mm2, ((sf2, fstk2), gg2)) (ltac:(rewrite Hvars2; exact Hlk))),
                  Eqit.bind_ret_l; reflexivity.
        + eapply RP_TauR; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                        (mm1, ((upd_local_sf sf1 (Maps.add x v sf1.(stack_vars)), fstk1), gg1))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm1, ((sf2, fstk2), gg1))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis; cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun inr1 inl1].
          rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH].
          rewrite Hvars1; repeat split; try exact Hvars2; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
        eapply refine_prov__obs_eq with
          (t1 := interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)))
          (t2 := Tau (interp_state interp_vellvm_prov_h (k2 tt)
                        (mm1, ((upd_local_sf sf2 (Maps.add x v sf2.(stack_vars)), fstk2), gg1)))).
        + exact Hr_eq.
        + reflexivity.
        + symmetry; rewrite Hu2, bind_trigger, interp_state_vis; cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun inr1 inl1].
          rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity.
        + eapply RP_TauR; [reflexivity | apply IH].
          rewrite Hvars2; repeat split; try exact Hvars1; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity. }
    assert (Hmain :
      forall U0 t1 t2,
        r_both U0 t1 t2 ->
        refine_prov RR_out U0 t1 t2).
    { pcofix CIH.
      intros U0 t1 t2 Hrb; pstep.
      eapply refine_prov__mon with (r := r_both);
        [| intros U1 a1 a2 Hr; right; apply CIH, Hr].
      destruct Hrb as [(stk & e1 & e2 & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - eapply Hbranch_a; eassumption.
      - eapply Hbranch_b; eassumption. }
    intros U stk env1 env2 s1 s2 u1 u2 Hmatch Hsim.
    apply Hmain; left; exists stk, env1, env2, s1, s2, u1, u2;
      split; [reflexivity | split; [reflexivity | split; assumption]].
  Qed.

  (** ** Modular Per-CFG Local-Environment Lifter ([lift_cfg_with_args_local_pass] & [lift_cfg_local_pass]) *)

  Lemma mcfg_stack_sim_refl_diag {R} :
    forall stk env (t : @MCFGtop (@ParamsV IP IPT) R),
      Forall (fun '(p1, p2) => p1 = p2) stk ->
      mcfg_stack_sim
        (fun stk' e1' e2' r1 r2 =>
           Forall (fun '(p1, p2) => p1 = p2) stk' /\ e1' = e2' /\ r1 = r2)
        stk env env t t.
  Proof using.
    pcofix CIH.
    intros stk env t Hstk; pstep; apply GSS_Step; unfold gss_step_body.
    destruct (observe t) as [x | m | X ev k].
    - split; [exact Hstk | split; reflexivity].
    - right; apply CIH, Hstk.
    - right.
      destruct (sync_non_local_mcfg ev) eqn:Esync.
      + left; split; [exact Esync | split; [apply EqE_MCFG_refl |]].
        intros a1 a2 Ha _; apply EqA_MCFG_eq in Ha; subst a2; right; apply CIH, Hstk.
      + destruct_sum1 ev; try discriminate Esync.
        * destruct ev as [x | x v]; right; left; cbn.
          -- split; [reflexivity | split; [reflexivity | intros v _; right; apply CIH, Hstk]].
          -- split; [reflexivity | split; [reflexivity | right; apply CIH, Hstk]].
        * destruct ev as [bs | | |]; try discriminate Esync; right; right; cbn.
          -- split; [reflexivity | right; apply CIH; constructor; [reflexivity | exact Hstk]].
          -- destruct stk as [[p1 p2] rest |]; [| exact I].
             inversion Hstk as [| ? ? Heq Hrest]; subst; cbn in Heq; subst p2.
             right; apply CIH, Hrest.
  Qed.

  Lemma i8_str_index_stack_sync strptr index stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (i8_str_index strptr index) (i8_str_index strptr index).
  Proof using.
    unfold i8_str_index.
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU | intros ? ? ? iptr _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU | intros ? ? ? addr _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_bind.
    { unfold load, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
    intros ? ? ? d_byte _ (-> & -> & -> & <-).
    destruct d_byte as [[| sz b | | | | | |] | |];
      try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
           [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]).
    destruct sz as [p | p |];
      try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
           [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]);
      destruct p as [p | p |];
      try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
           [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]);
      destruct p as [p | p |];
      try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
           [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]);
      destruct p as [p | p |];
      try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
           [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]).
    apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma i8_str_index_local_sync strptr index env1 env2 :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (i8_str_index strptr index) (i8_str_index strptr index).
  Proof using.
    assert (Heou : forall A (m : EOU A) e1 e2,
              cfg_local_sim (fun e1' e2' r1 r2 => e1' = e1 /\ e2' = e2 /\ r1 = r2)
                e1 e2 (EOU_to_itree m) (EOU_to_itree m)).
    { intros A [s | s | s | x] e1 e2; cbn [EOU_to_itree].
      - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn;
          right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
      - unfold raiseUB, trigger_cast; pstep; apply CLS_Step; cbn; left; reflexivity.
      - unfold raise, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn;
          right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
      - apply cfg_local_sim_ret; repeat split; reflexivity. }
    assert (Herr : forall msg A e1 e2,
              cfg_local_sim (fun e1' e2' (r1 r2 : A) => e1' = e1 /\ e2' = e2 /\ r1 = r2)
                e1 e2 (raise msg) (raise msg)).
    { intros msg A e1 e2; unfold raise, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]]. }
    unfold i8_str_index.
    eapply cfg_local_sim_bind; [apply Heou | intros ? ? iptr _ (-> & -> & <-)].
    eapply cfg_local_sim_bind; [apply Heou | intros ? ? addr _ (-> & -> & <-)].
    eapply cfg_local_sim_bind.
    { unfold load, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
      intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2; left; apply cfg_local_sim_ret; repeat split; reflexivity. }
    intros ? ? d_byte _ (-> & -> & <-).
    destruct d_byte as [[| sz b | | | | | |] | |]; try apply Herr.
    destruct sz as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr.
    apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma putchar_denotation_sync :
    forall stk env1 env2 cc args,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (putchar_denotation cc args) (putchar_denotation cc args).
  Proof using.
    intros stk env1 env2 cc args; unfold putchar_denotation.
    destruct args as [| ch [| ? ?]];
      try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
           [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]).
    cbn [Functor.fmap Functor_itree ITree.map].
    eapply gen_stack_sim_bind; [| intros ? ? ? dv _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity].
    destruct ch as [[| sz x32 | | | | | |] | |];
      try (unfold raiseUB, trigger_cast; pstep; apply GSS_Step; cbn; left; reflexivity).
    destruct (Pos.eq_dec 32 sz) as [<- | _];
      [| unfold raiseUB, trigger_cast; pstep; apply GSS_Step; cbn; left; reflexivity].
    eapply gen_stack_sim_bind.
    - unfold io_stdout, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
    - intros ? ? ? _ _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma puts_denotation_sync :
    forall stk env1 env2 cc args,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (puts_denotation cc args) (puts_denotation cc args).
  Proof using.
    intros stk env1 env2 cc args; unfold puts_denotation.
    destruct args as [| u_strptr [| ? ?]];
      try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
           [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]).
    cbn [Functor.fmap Functor_itree ITree.map].
    eapply gen_stack_sim_bind; [| intros ? ? ? dv _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity].
    destruct u_strptr as [[strptr | | | | | | |] | |];
      try (unfold raiseUB, trigger_cast; pstep; apply GSS_Step; cbn; left; reflexivity).
    eapply gen_stack_sim_bind; [apply i8_str_index_stack_sync |].
    intros ? ? ? ch _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    - eapply gen_stack_sim_bind with
        (RR := fun stk' e1' e2' r1 r2 => stk' = stk /\ (e1' = env1 /\ e2' = env2 /\ r1 = r2)).
      + apply cfg_local_to_stack_sim.
        eapply cfg_local_sim_iter with
          (RI := fun e1' e2' s1 s2 => e1' = env1 /\ e2' = env2 /\ s1 = s2)
          (RR := fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2);
          [| repeat split; reflexivity].
        intros e1' e2' [[c bytes] offset] _ (-> & -> & <-).
        destruct (@Integers.eq 8 c (@Integers.zero 8)).
        * apply cfg_local_sim_ret; cbn; repeat split; reflexivity.
        * eapply cfg_local_sim_bind; [apply i8_str_index_local_sync |].
          intros ? ? next_char _ (-> & -> & <-); apply cfg_local_sim_ret; cbn; repeat split; reflexivity.
      + intros ? ? ? bytes _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
    - intros ? ? ? bytes _ (-> & -> & -> & <-).
      eapply gen_stack_sim_bind.
      + unfold io_stdout, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
      + intros ? ? ? _ _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma library_functions_stack_sync (decls : list (declaration dtyp)) :
    Forall
      (fun '(_, den) =>
         forall stk env1 env2 cc args,
           cfg_stack_sim
             (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
             stk env1 env2 (den cc args) (den cc args))
      (library_functions decls).
  Proof using.
    unfold library_functions, _LIBRARIES; cbn [List.filter].
    destruct (existsb _ _); destruct (existsb _ _);
      repeat constructor;
      first [apply puts_denotation_sync | apply putchar_denotation_sync].
  Qed.

  Definition map_defn_with_args {T : Set}
    (f : list local_id -> CFG.cfg T -> CFG.cfg T)
    (df : definition T (CFG.cfg T)) : definition T (CFG.cfg T) :=
    {| df_prototype := df_prototype df;
       df_args      := df_args df;
       df_instrs    := f (df_args df) (df_instrs df) |}.

  Definition map_mcfg_with_args {T : Set}
    (f : list local_id -> CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T) : CFG.mcfg T :=
    {| m_name         := m_name M;
       m_target       := m_target M;
       m_datalayout   := m_datalayout M;
       m_type_defs    := m_type_defs M;
       m_globals      := m_globals M;
       m_declarations := m_declarations M;
       m_definitions  := List.map (map_defn_with_args f) (m_definitions M) |}.

  Lemma map_mcfg_with_args_prototypes {T : Set}
    (f : list local_id -> CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T) :
    List.map df_prototype (m_definitions (map_mcfg_with_args f M)) =
    List.map df_prototype (m_definitions M).
  Proof using.
    cbn [map_mcfg_with_args m_definitions]; rewrite map_map; reflexivity.
  Qed.

  Lemma map_mcfg_with_args_block_addresses {T : Set}
    (f : list local_id -> CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T)
    (Hba : forall fargs c,
             flat_map block_block_addresses (blks (f fargs c)) =
             flat_map block_block_addresses (blks c)) :
    mcfg_block_addresses (map_mcfg_with_args f M) = mcfg_block_addresses M.
  Proof using.
    unfold mcfg_block_addresses; cbn [map_mcfg_with_args m_globals m_definitions].
    f_equal.
    induction (m_definitions M) as [| d ds IH]; [reflexivity |].
    cbn [List.map flat_map map_defn_with_args df_instrs].
    rewrite Hba, IH; reflexivity.
  Qed.

  Lemma of_list_fn_ctx_stack_sim
    (l1 l2 : list (Z * @function_denotation (@ParamsV IP IPT)))
    (Hl : Forall2
            (fun '(k1, f1) '(k2, f2) =>
               k1 = k2 /\
               forall stk env1 env2 cc args,
                 cfg_stack_sim
                   (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                   stk env1 env2 (f1 cc args) (f2 cc args))
            l1 l2) :
    forall k,
      option_rel
        (fun f1 f2 =>
           forall stk env1 env2 cc args,
             cfg_stack_sim
               (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
               stk env1 env2 (f1 cc args) (f2 cc args))
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

  Lemma map_monad_address_one_function_stack_sim
    (f : list local_id -> CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hbody : forall fargs c env va,
               (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
               cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                 env env (denote_cfg c va) (denote_cfg (f fargs c) va)) :
    forall (defs : list (definition dtyp (CFG.cfg dtyp))) stk env1 env2,
      mcfg_stack_sim
        (fun stk' e1' e2' l1 l2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_stack_sim
                    (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                    s0 a1 a2 (fn1 cc args) (fn2 cc args))
             l1 l2)
        stk env1 env2
        (map_monad address_one_function defs)
        (map_monad address_one_function (List.map (map_defn_with_args f) defs)).
  Proof using.
    induction defs as [| df defs' IH]; intros stk env1 env2; cbn [List.map map_monad].
    - apply gen_stack_sim_ret; repeat split; constructor.
    - eapply gen_stack_sim_bind.
      + unfold address_one_function; cbn [map_defn_with_args df_prototype].
        eapply gen_stack_sim_bind.
        * unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? fv _ (-> & -> & -> & <-).
          destruct fv as [[p | | | | | | |] | |];
            try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
                 [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]).
          apply gen_stack_sim_ret; repeat split; try reflexivity.
          apply cfg_stack_sim_denote_function; [reflexivity | reflexivity |].
          intros env0 va Henv0; apply Hbody, Henv0.
      + intros ? ? ? [k1 fn1] [k2 fn2] (-> & -> & -> & Hhd).
        eapply gen_stack_sim_bind; [apply IH |].
        intros ? ? ? tl1 tl2 (-> & -> & -> & Htl).
        apply gen_stack_sim_ret; repeat split; constructor; assumption.
  Qed.

  Lemma map_monad_address_library_stack_sim
    (libs : list (function_id * @function_denotation (@ParamsV IP IPT)))
    (Hlibs : Forall
               (fun '(_, den) =>
                  forall stk env1 env2 cc args,
                    cfg_stack_sim
                      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                      stk env1 env2 (den cc args) (den cc args))
               libs) :
    forall stk env1 env2,
      mcfg_stack_sim
        (fun stk' e1' e2' l1 l2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_stack_sim
                    (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                    s0 a1 a2 (fn1 cc args) (fn2 cc args))
             l1 l2)
        stk env1 env2
        (map_monad address_one_library_function libs)
        (map_monad address_one_library_function libs).
  Proof using.
    induction Hlibs as [| [fid den] rest Hden _ IH]; intros stk env1 env2; cbn [map_monad].
    - apply gen_stack_sim_ret; repeat split; constructor.
    - eapply gen_stack_sim_bind.
      + unfold address_one_library_function.
        eapply gen_stack_sim_bind.
        * unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? fv _ (-> & -> & -> & <-).
          destruct fv as [[p | | | | | | |] | |];
            try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
                 [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]).
          apply gen_stack_sim_ret; repeat split; exact Hden.
      + intros ? ? ? [k1 fn1] [k2 fn2] (-> & -> & -> & Hhd).
        eapply gen_stack_sim_bind; [apply IH |].
        intros ? ? ? tl1 tl2 (-> & -> & -> & Htl).
        apply gen_stack_sim_ret; repeat split; constructor; assumption.
  Qed.

  Theorem lift_cfg_with_args_local_pass
    (f : list local_id -> CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hba : forall fargs c,
             flat_map block_block_addresses (blks (f fargs c)) =
             flat_map block_block_addresses (blks c))
    (Hbody : forall fargs c env va,
               (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
               cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                 env env (denote_cfg c va) (denote_cfg (f fargs c) va)) :
    forall M : CFG.mcfg dtyp, prog_refines M (map_mcfg_with_args f M).
  Proof using.
    intros M ret_typ entry args U.
    unfold run_mcfg_model, interp_mcfg_model.
    eapply refine_prov_antitone with (U := U);
      [intros _ _ [s1 r1] [s2 r2] _ (_ & _ & _ & _ & <-); reflexivity | apply incl_refl |].
    eapply mcfg_stack_sim_to_model with (stk := []) (env1 := Maps.empty) (env2 := Maps.empty).
    { unfold init_fused_state, fused_state_match; repeat split; try reflexivity; constructor. }
    apply mcfg_stack_sim_interp_intrinsics.
    unfold denote_vellvm.
    assert (Hbg : @build_global_environment (@ParamsV IP IPT) (map_mcfg_with_args f M) =
                  @build_global_environment (@ParamsV IP IPT) M).
    { unfold build_global_environment.
      rewrite map_mcfg_with_args_prototypes, (map_mcfg_with_args_block_addresses f M Hba).
      reflexivity. }
    rewrite Hbg.
    eapply gen_stack_sim_bind;
      [apply mcfg_stack_sim_refl_diag; constructor |].
    intros stk1 e1 e2 [] _ (Hstk1 & <- & _).
    cbn [m_definitions m_declarations map_mcfg_with_args].
    eapply gen_stack_sim_bind;
      [apply (map_monad_address_one_function_stack_sim f Hbody) |].
    intros ? ? ? defns1 defns2 (-> & -> & -> & Hdefns).
    eapply gen_stack_sim_bind;
      [apply (map_monad_address_library_stack_sim _ (library_functions_stack_sync (m_declarations M))) |].
    intros ? ? ? libs1 libs2 (-> & -> & -> & Hlibs).
    eapply gen_stack_sim_bind.
    { unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]. }
    intros ? ? ? addr _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    - rewrite !denote_mcfg_eq_interp_mrec.
      assert (Hctx : forall k,
                option_rel
                  (fun f1 f2 =>
                     forall stk env1 env2 cc fargs,
                       cfg_stack_sim
                         (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                         stk env1 env2 (f1 cc fargs) (f2 cc fargs))
                  (lookup k (IntMaps.IP.of_list (defns1 ++ libs1)))
                  (lookup k (IntMaps.IP.of_list (defns2 ++ libs2)))).
      { apply of_list_fn_ctx_stack_sim, Forall2_app; assumption. }
      eapply cfg_to_mcfg_stack_sim_mrec with
        (ctx1 := IntMaps.IP.of_list (defns1 ++ libs1))
        (ctx2 := IntMaps.IP.of_list (defns2 ++ libs2));
        [exact Hctx | reflexivity | reflexivity |].
      apply (cfg_stack_sim_mrec_ctx _ _ Hctx); repeat split; reflexivity.
    - intros ? ? ? rv _ (-> & -> & -> & <-).
      destruct rv as [ex | v].
      + unfold raiseLLVM, trigger_cast; pstep; apply GSS_Step; unfold gss_step_body, ITree.trigger; cbn.
        right; left; split; [reflexivity | split; [reflexivity | intros [] [] _ _]].
      + apply gen_stack_sim_ret; reflexivity.
  Qed.

  Theorem lift_cfg_local_pass
    (f : CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hba : forall c,
             flat_map block_block_addresses (blks (f c)) =
             flat_map block_block_addresses (blks c))
    (Hbody : forall c env va,
               cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                 env env (denote_cfg c va) (denote_cfg (f c) va)) :
    forall M : CFG.mcfg dtyp, prog_refines M (map_mcfg_cfg f M).
  Proof using.
    intros M.
    change (map_mcfg_cfg f M) with (map_mcfg_with_args (fun _ => f) M).
    apply lift_cfg_with_args_local_pass;
      [intros _ c; apply Hba | intros _ c env va _; apply Hbody].
  Qed.

End ModelSemantics.

(** Well-behaved pointer-integer models ([IPZ] in [IPtrInfinite.v] and
    [IP64Bit] in [IPtrFinite.v]) never return [raise_error] ([FailureE]) or
    [raise_ub] from [from_Z]: integer-to-address conversion either succeeds
    ([raise_ret]) or signals out-of-memory ([raise_oom]). Capturing this as a
    [Prop] typeclass allows [Mem2Reg] to delete dead stack allocations without
    weakening [is_ub_bot] to cut [FailureE]. *)
Class IPtrWellBehaved (IP : IPtr) : Prop := {
  from_Z_ret_or_oom :
    forall z : Z,
      (exists i : @iptr IP, @from_Z IP z = raise_ret i) \/
      (exists msg : string, @from_Z IP z = raise_oom msg)
}.

#[export] Instance IPZ_WellBehaved : IPtrWellBehaved IPZ.
Proof.
  constructor; intros z; left; exists z; reflexivity.
Qed.

#[export] Instance IPtrWellBehaved_IPZ : IPtrWellBehaved IPZ := IPZ_WellBehaved.

#[export] Instance IP64Bit_WellBehaved : IPtrWellBehaved IP64Bit.
Proof.
  constructor; intros z; cbn [from_Z IP64Bit]; unfold from_Z_bits.
  destruct ((z <=? @Integers.max_unsigned 64)%Z && (z >=? 0)%Z).
  - left; eexists; reflexivity.
  - right; eexists; reflexivity.
Qed.

