(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Dead Code & Dead Phi Elimination Specification ([CertPasses.DCESpec])

    Purpose:
      Defines finite ID-set utilities, a nested [exp] induction principle
      ([exp_ind_nested]), forward reachability and scalar-type/definedness
      analysis with validator ([check_fwd_cfg]), backward liveness with
      validator ([check_live_cfg]), and CFG rewriting ([dce_cfg_once]).

    Trust Contract & Fail-Closed Boundary:
      Computational specification re-exported by [CertPasses.DCE] for OCaml
      extraction. [dce_cfg_once] gates on [cfg_no_block_addresses],
      [nodup_raw_ids], [check_fwd_cfg], and [check_live_cfg], falling back to
      the identity CFG [c] if any check fails.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, and
      [CertPasses.PassCommon]; zero custom axioms.

    Section Outline:
      (1) Finite ID-set & sublist utilities; (2) [exp_ind_nested];
      (3) Forward reachability, scalar safety, & [check_fwd_cfg];
      (4) Backward liveness, [dce_code]/[dce_phis], [check_live_cfg], &
      [dce_cfg_once]. *)

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
  Structures.Monads.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  Semantics.VellvmIntegers
  Semantics.VellvmFloats
  ScopeTheory
  Utils.rutt_cutoff
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
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.

(** * 1. Finite ID-Set, Association-List, and Sublist Utilities *)

Fixpoint nodup_raw_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (in_raw_ids x rest) && nodup_raw_ids rest
  end.

Lemma nodup_raw_ids_spec (xs : list raw_id) :
  nodup_raw_ids xs = true -> NoDup xs.
Proof.
  induction xs as [| x rest IH]; intros Hnd; [constructor |].
  cbn [nodup_raw_ids] in Hnd.
  apply andb_true_iff in Hnd as [Hnin Hrest].
  apply negb_true_iff, in_raw_ids_false in Hnin.
  constructor; [exact Hnin | apply IH, Hrest].
Qed.

Definition add_raw_id (x : raw_id) (s : list raw_id) : list raw_id :=
  if in_raw_ids x s then s else x :: s.

Lemma in_add_raw_id (y x : raw_id) (s : list raw_id) :
  in_raw_ids y (add_raw_id x s) = true <-> y = x \/ in_raw_ids y s = true.
Proof.
  unfold add_raw_id.
  destruct (in_raw_ids x s) eqn:Ex.
  - split.
    + intros Hy; right; exact Hy.
    + intros [-> | Hy]; [exact Ex | exact Hy].
  - cbn [in_raw_ids existsb].
    rewrite orb_true_iff, raw_id_eqb_spec.
    reflexivity.
Qed.

Definition add_raw_ids (xs s : list raw_id) : list raw_id :=
  fold_right add_raw_id s xs.

Lemma in_add_raw_ids (y : raw_id) (xs s : list raw_id) :
  in_raw_ids y (add_raw_ids xs s) = true <-> In y xs \/ in_raw_ids y s = true.
Proof.
  induction xs as [| x rest IH]; cbn [add_raw_ids fold_right].
  - split; [intros H; right; exact H | intros [[] | H]; exact H].
  - rewrite in_add_raw_id, IH; cbn [In].
    split; [intros [-> | [H | H]]; auto | intros [[<- | H] | H]; auto].
Qed.

Definition remove_raw_id (x : raw_id) (s : list raw_id) : list raw_id :=
  List.filter (fun y => negb (raw_id_eqb y x)) s.

Lemma in_remove_raw_id (y x : raw_id) (s : list raw_id) :
  in_raw_ids y (remove_raw_id x s) = true <-> y <> x /\ in_raw_ids y s = true.
Proof.
  unfold remove_raw_id.
  rewrite !in_raw_ids_spec, filter_In, negb_true_iff, raw_id_eqb_neq.
  tauto.
Qed.

Definition remove_raw_ids (xs s : list raw_id) : list raw_id :=
  fold_right remove_raw_id s xs.

Lemma in_remove_raw_ids (y : raw_id) (xs s : list raw_id) :
  in_raw_ids y (remove_raw_ids xs s) = true <-> ~ In y xs /\ in_raw_ids y s = true.
Proof.
  induction xs as [| x rest IH]; cbn [remove_raw_ids fold_right].
  - split; [intros H; split; [intros [] | exact H] | intros [_ H]; exact H].
  - rewrite in_remove_raw_id, IH; cbn [In].
    split.
    + intros [Hne [Hnin Hs]]; split; [intros [<- | Hin]; contradiction | exact Hs].
    + intros [Hnin Hs]; split; [intros ->; apply Hnin; left; reflexivity | split; [intros Hin; apply Hnin; right; exact Hin | exact Hs]].
Qed.

Definition raw_ids_subset (s1 s2 : list raw_id) : bool :=
  forallb (fun x => in_raw_ids x s2) s1.

Lemma raw_ids_subset_spec (s1 s2 : list raw_id) :
  raw_ids_subset s1 s2 = true ->
  forall x, in_raw_ids x s1 = true -> in_raw_ids x s2 = true.
Proof.
  unfold raw_ids_subset; rewrite forallb_forall.
  intros Hsub x Hx; apply in_raw_ids_spec in Hx; apply Hsub, Hx.
Qed.

Definition raw_ids_eqb (s1 s2 : list raw_id) : bool :=
  raw_ids_subset s1 s2 && raw_ids_subset s2 s1.

Lemma assoc_raw_id_in {B : Type} (k : raw_id) (l : list (raw_id * B)) (v : B) :
  assoc k l = Some v -> In (k, v) l.
Proof.
  unfold assoc.
  induction l as [| [k' b] rest IH]; intros H; cbn in H; [discriminate H |].
  destruct (RelDec.rel_dec k k') eqn:E.
  - unfold RelDec.rel_dec, eq_dec_raw_id, RelDec.RelDec_from_dec in E.
    destruct (RawIDOrd.eq_dec k k') as [<- |]; [| discriminate E].
    inversion H; subst b; left; reflexivity.
  - right; apply IH, H.
Qed.

Lemma assoc_raw_id_uses (bid : block_id) (args : list (block_id * exp dtyp))
  (op : exp dtyp) (x : raw_id) :
  assoc bid args = Some op ->
  In x (full_exp_uses op) ->
  In x (flat_map (fun '(_, ex) => full_exp_uses ex) args).
Proof.
  intros Hassoc Hx.
  apply assoc_raw_id_in in Hassoc.
  apply in_flat_map; exists (bid, op); split; [exact Hassoc | exact Hx].
Qed.

Lemma find_option_ann_num_elements_uses
  (anns : list (annotation dtyp)) (te : texp dtyp) (x : raw_id) :
  find_option ann_num_elements anns = Some te ->
  In x (full_texp_uses te) ->
  In x (flat_map full_ann_uses anns).
Proof.
  induction anns as [| a rest IH]; intros Hfind Hx; cbn in Hfind; [discriminate Hfind |].
  cbn [flat_map]; apply in_or_app.
  destruct a; cbn in Hfind; try (right; exact (IH Hfind Hx)).
  inversion Hfind; subst t; left; exact Hx.
Qed.

Inductive is_sublist {A : Type} : list A -> list A -> Prop :=
| Sublist_nil : is_sublist [] []
| Sublist_keep (x : A) (l1 l2 : list A) :
    is_sublist l1 l2 -> is_sublist (x :: l1) (x :: l2)
| Sublist_drop (x : A) (l1 l2 : list A) :
    is_sublist l1 l2 -> is_sublist l1 (x :: l2).

Lemma flat_map_nil_sublist {A B : Type} (f : A -> list B) (sub l : list A) :
  is_sublist sub l ->
  flat_map f l = [] ->
  flat_map f sub = [].
Proof.
  intros Hsub; induction Hsub as [| x l1 l2 _ IH | x l1 l2 _ IH]; intros Hnil; [reflexivity | |].
  - cbn [flat_map] in Hnil |- *.
    apply app_eq_nil in Hnil as [Hx Hl2].
    rewrite Hx, (IH Hl2); reflexivity.
  - cbn [flat_map] in Hnil.
    apply app_eq_nil in Hnil as [_ Hl2].
    apply IH, Hl2.
Qed.

Definition term_successors {T : Set} (tm : terminator T) : list block_id :=
  match tm with
  | TERM_Ret _ | TERM_Ret_void | TERM_Resume _ | TERM_Unreachable => []
  | TERM_Br _ br1 br2 => [br1; br2]
  | TERM_Br_1 br => [br]
  | TERM_Switch _ def_dest brs => def_dest :: List.map snd brs
  | TERM_IndirectBr _ brs _ => brs
  | TERM_Invoke _ _ to_l unwind_l _ _ => [to_l; unwind_l]
  end.

Definition block_successors {T : Set} (bk : block T) : list block_id :=
  let '(_, tm, _) := blk_term bk in term_successors tm.

(** * 2. Guarded Structural Induction Principle for [exp] *)

Section ExpIndNested.
  Context {T : Set}.
  Variable P : exp T -> Prop.

  Hypothesis H_Ident : forall id : ident, P (EXP_Ident id).
  Hypothesis H_Integer : forall x : int_syntax, P (EXP_Integer x).
  Hypothesis H_Float : forall f : float_syntax, P (EXP_Float f).
  Hypothesis H_Bool : forall b : bool, P (EXP_Bool b).
  Hypothesis H_Null : P EXP_Null.
  Hypothesis H_Zero_init : P EXP_Zero_initializer.
  Hypothesis H_Cstring :
    forall elts : list (T * exp T),
      Forall (fun p => P (snd p)) elts -> P (EXP_Cstring elts).
  Hypothesis H_Undef : P EXP_Undef.
  Hypothesis H_Poison : P EXP_Poison.
  Hypothesis H_Struct :
    forall fields : list (T * exp T),
      Forall (fun p => P (snd p)) fields -> P (EXP_Struct fields).
  Hypothesis H_Packed_struct :
    forall fields : list (T * exp T),
      Forall (fun p => P (snd p)) fields -> P (EXP_Packed_struct fields).
  Hypothesis H_Array :
    forall elts : list (T * exp T),
      Forall (fun p => P (snd p)) elts -> P (EXP_Array elts).
  Hypothesis H_Vector :
    forall elts : list (T * exp T),
      Forall (fun p => P (snd p)) elts -> P (EXP_Vector elts).
  Hypothesis H_IBinop :
    forall (iop : ibinop) (t : T) (e1 e2 : exp T),
      P e1 -> P e2 -> P (OP_IBinop iop t e1 e2).
  Hypothesis H_ICmp :
    forall (samesign : bool) (cmp : icmp) (t : T) (e1 e2 : exp T),
      P e1 -> P e2 -> P (OP_ICmp samesign cmp t e1 e2).
  Hypothesis H_FBinop :
    forall (fop : fbinop) (fm : list fast_math) (t : T) (e1 e2 : exp T),
      P e1 -> P e2 -> P (OP_FBinop fop fm t e1 e2).
  Hypothesis H_Fneg :
    forall (flags : list fast_math) (dt : T) (e1 : exp T),
      P e1 -> P (OP_Fneg flags (dt, e1)).
  Hypothesis H_FCmp :
    forall (cmp : fcmp) (fm : list fast_math) (t : T) (e1 e2 : exp T),
      P e1 -> P e2 -> P (OP_FCmp cmp fm t e1 e2).
  Hypothesis H_Conversion :
    forall (conv : conversion_type) (t_from : T) (e1 : exp T) (t_to : T),
      P e1 -> P (OP_Conversion conv t_from e1 t_to).
  Hypothesis H_GetElementPtr :
    forall (flags : gep_flags) (t dt_p : T) (ep : exp T) (idxs : list (T * exp T)),
      P ep -> Forall (fun p => P (snd p)) idxs ->
      P (OP_GetElementPtr flags t (dt_p, ep) idxs).
  Hypothesis H_ExtractElement :
    forall (dt_v : T) (ev : exp T) (dt_i : T) (ei : exp T),
      P ev -> P ei -> P (OP_ExtractElement (dt_v, ev) (dt_i, ei)).
  Hypothesis H_InsertElement :
    forall (dt_v : T) (ev : exp T) (dt_e : T) (ee : exp T) (dt_i : T) (ei : exp T),
      P ev -> P ee -> P ei ->
      P (OP_InsertElement (dt_v, ev) (dt_e, ee) (dt_i, ei)).
  Hypothesis H_ShuffleVector :
    forall (dt1 : T) (e1 : exp T) (dt2 : T) (e2 : exp T) (dtm : T) (em : exp T),
      P e1 -> P e2 -> P em ->
      P (OP_ShuffleVector (dt1, e1) (dt2, e2) (dtm, em)).
  Hypothesis H_ExtractValue :
    forall (dt_s : T) (es : exp T) (idxs : list int_syntax),
      P es -> P (OP_ExtractValue (dt_s, es) idxs).
  Hypothesis H_InsertValue :
    forall (dt_s : T) (es : exp T) (dt_e : T) (ee : exp T) (idxs : list int_syntax),
      P es -> P ee -> P (OP_InsertValue (dt_s, es) (dt_e, ee) idxs).
  Hypothesis H_Select :
    forall (fm : list fast_math) (dt_c : T) (ec : exp T)
           (dt1 : T) (e1 : exp T) (dt2 : T) (e2 : exp T),
      P ec -> P e1 -> P e2 ->
      P (OP_Select fm (dt_c, ec) (dt1, e1) (dt2, e2)).
  Hypothesis H_Freeze :
    forall (dt : T) (e1 : exp T), P e1 -> P (OP_Freeze (dt, e1)).
  Hypothesis H_Asm :
    forall (se al idia uw : bool) (tmpl cstr : string),
      P (EXP_Asm se al idia uw tmpl cstr).
  Hypothesis H_Metadata_Const :
    forall (dt : T) (e1 : exp T), P e1 -> P (EXP_Metadata (METADATA_Const (dt, e1))).
  Hypothesis H_Metadata_Other :
    forall m : metadata T,
      (forall dt e1, m <> METADATA_Const (dt, e1)) -> P (EXP_Metadata m).
  Hypothesis H_Splat :
    forall (dt : T) (e1 : exp T), P e1 -> P (EXP_Splat (dt, e1)).
  Hypothesis H_BlockAddress :
    forall (fn : function_id) (blk : block_id), P (EXP_BlockAddress fn blk).

  Lemma exp_ind_nested : forall e : exp T, P e.
  Proof.
    exact
      (fix IH_exp (e : exp T) {struct e} : P e :=
         let fix go_list (l : list (T * exp T)) {struct l} : Forall (fun p => P (snd p)) l :=
           match l with
           | [] => Forall_nil _
           | (dt, ex) :: rest =>
               @Forall_cons (T * exp T) (fun p => P (snd p)) (dt, ex) rest
                 (IH_exp ex) (go_list rest)
           end
         in
         match e with
         | EXP_Ident id => H_Ident id
         | EXP_Integer x => H_Integer x
         | EXP_Float f => H_Float f
         | EXP_Bool b => H_Bool b
         | EXP_Null => H_Null
         | EXP_Zero_initializer => H_Zero_init
         | EXP_Cstring elts => H_Cstring elts (go_list elts)
         | EXP_Undef => H_Undef
         | EXP_Poison => H_Poison
         | EXP_Struct fields => H_Struct fields (go_list fields)
         | EXP_Packed_struct fields => H_Packed_struct fields (go_list fields)
         | EXP_Array elts => H_Array elts (go_list elts)
         | EXP_Vector elts => H_Vector elts (go_list elts)
         | OP_IBinop iop t e1 e2 => H_IBinop iop t e1 e2 (IH_exp e1) (IH_exp e2)
         | OP_ICmp samesign cmp t e1 e2 => H_ICmp samesign cmp t e1 e2 (IH_exp e1) (IH_exp e2)
         | OP_FBinop fop fm t e1 e2 => H_FBinop fop fm t e1 e2 (IH_exp e1) (IH_exp e2)
         | OP_Fneg flags (dt, e1) => H_Fneg flags dt e1 (IH_exp e1)
         | OP_FCmp cmp fm t e1 e2 => H_FCmp cmp fm t e1 e2 (IH_exp e1) (IH_exp e2)
         | OP_Conversion conv t_from e1 t_to =>
             H_Conversion conv t_from e1 t_to (IH_exp e1)
         | OP_GetElementPtr flags t (dt_p, ep) idxs =>
             H_GetElementPtr flags t dt_p ep idxs (IH_exp ep) (go_list idxs)
         | OP_ExtractElement (dt_v, ev) (dt_i, ei) =>
             H_ExtractElement dt_v ev dt_i ei (IH_exp ev) (IH_exp ei)
         | OP_InsertElement (dt_v, ev) (dt_e, ee) (dt_i, ei) =>
             H_InsertElement dt_v ev dt_e ee dt_i ei (IH_exp ev) (IH_exp ee) (IH_exp ei)
         | OP_ShuffleVector (dt1, e1) (dt2, e2) (dtm, em) =>
             H_ShuffleVector dt1 e1 dt2 e2 dtm em (IH_exp e1) (IH_exp e2) (IH_exp em)
         | OP_ExtractValue (dt_s, es) idxs =>
             H_ExtractValue dt_s es idxs (IH_exp es)
         | OP_InsertValue (dt_s, es) (dt_e, ee) idxs =>
             H_InsertValue dt_s es dt_e ee idxs (IH_exp es) (IH_exp ee)
         | OP_Select fm (dt_c, ec) (dt1, e1) (dt2, e2) =>
             H_Select fm dt_c ec dt1 e1 dt2 e2 (IH_exp ec) (IH_exp e1) (IH_exp e2)
         | OP_Freeze (dt, e1) => H_Freeze dt e1 (IH_exp e1)
         | EXP_Asm se al idia uw tmpl cstr => H_Asm se al idia uw tmpl cstr
         | EXP_Metadata m => IH_md m
         | EXP_Splat (dt, e1) => H_Splat dt e1 (IH_exp e1)
         | EXP_BlockAddress fn blk => H_BlockAddress fn blk
         end
       with IH_md (m : metadata T) {struct m} : P (EXP_Metadata m) :=
         match m with
         | METADATA_Const (dt, e1) => H_Metadata_Const dt e1 (IH_exp e1)
         | METADATA_Null =>
             H_Metadata_Other METADATA_Null (fun _ _ Hc => ltac:(discriminate Hc))
         | METADATA_Id id =>
             H_Metadata_Other (METADATA_Id id) (fun _ _ Hc => ltac:(discriminate Hc))
         | METADATA_Node mds =>
             H_Metadata_Other (METADATA_Node mds) (fun _ _ Hc => ltac:(discriminate Hc))
         | METADATA_Pair m1 m2 =>
             H_Metadata_Other (METADATA_Pair m1 m2) (fun _ _ Hc => ltac:(discriminate Hc))
         | METADATA_Debug s1 s2 =>
             H_Metadata_Other (METADATA_Debug s1 s2) (fun _ _ Hc => ltac:(discriminate Hc))
         | METADATA_File_info fi =>
             H_Metadata_Other (METADATA_File_info fi) (fun _ _ Hc => ltac:(discriminate Hc))
         end
       for IH_exp).
  Qed.

End ExpIndNested.

(** * 3. Forward Reachability & Typed-Definedness Dataflow + Validator *)

(** [None] denotes an initialized SSA register holding any [dvalue];
    [Some dt] denotes an initialized SSA register holding a scalar [dvalue]
    satisfying [is_scalar_dtyp dt = true /\ dvalue_has_dtyp v dt]. *)
Definition ty_info : Type := option dtyp.
Definition ty_env : Type := list (local_id * ty_info).

Fixpoint lookup_ty (x : local_id) (te : ty_env) : option ty_info :=
  match te with
  | [] => None
  | (y, oty) :: rest =>
      if raw_id_eqb x y then Some oty else lookup_ty x rest
  end.

Lemma lookup_ty_in (x : local_id) (te : ty_env) (oty : ty_info) :
  lookup_ty x te = Some oty -> In (x, oty) te.
Proof.
  induction te as [| [y oty'] rest IH]; intros H; cbn in H; [discriminate H |].
  destruct (raw_id_eqb x y) eqn:E.
  - apply raw_id_eqb_spec in E; subst y.
    inversion H; subst oty'; left; reflexivity.
  - right; apply IH, H.
Qed.

Definition remove_ty (x : local_id) (te : ty_env) : ty_env :=
  List.filter (fun '(y, _) => negb (raw_id_eqb y x)) te.

Lemma lookup_remove_ty_eq (x : local_id) (te : ty_env) :
  lookup_ty x (remove_ty x te) = None.
Proof.
  induction te as [| [y oty] rest IH]; [reflexivity |].
  cbn [remove_ty List.filter].
  destruct (raw_id_eqb y x) eqn:Eyx; cbn [negb].
  - exact IH.
  - cbn [lookup_ty].
    rewrite raw_id_eqb_sym, Eyx; exact IH.
Qed.

Lemma lookup_remove_ty_neq (x z : local_id) (te : ty_env) :
  z <> x ->
  lookup_ty z (remove_ty x te) = lookup_ty z te.
Proof.
  intros Hne.
  induction te as [| [y oty] rest IH]; [reflexivity |].
  cbn [remove_ty List.filter lookup_ty].
  destruct (raw_id_eqb y x) eqn:Eyx; cbn [negb].
  - apply raw_id_eqb_spec in Eyx; subst y.
    destruct (raw_id_eqb z x) eqn:Ezx.
    + apply raw_id_eqb_spec in Ezx; contradiction.
    + exact IH.
  - cbn [lookup_ty].
    destruct (raw_id_eqb z y); [reflexivity | exact IH].
Qed.

Definition normalize_oty (oty : ty_info) : ty_info :=
  match oty with
  | Some dt => if is_scalar_dtyp dt then Some dt else None
  | None => None
  end.

Definition set_ty (x : local_id) (oty : ty_info) (te : ty_env) : ty_env :=
  (x, normalize_oty oty) :: remove_ty x te.

Lemma lookup_set_ty_eq (x : local_id) (oty : ty_info) (te : ty_env) :
  lookup_ty x (set_ty x oty te) = Some (normalize_oty oty).
Proof.
  cbn [set_ty lookup_ty]; rewrite raw_id_eqb_refl; reflexivity.
Qed.

Lemma lookup_set_ty_neq (x z : local_id) (oty : ty_info) (te : ty_env) :
  z <> x ->
  lookup_ty z (set_ty x oty te) = lookup_ty z te.
Proof.
  intros Hne; cbn [set_ty lookup_ty].
  destruct (raw_id_eqb z x) eqn:Ezx.
  - apply raw_id_eqb_spec in Ezx; contradiction.
  - apply lookup_remove_ty_neq, Hne.
Qed.

Definition oty_valid (oty : ty_info) : bool :=
  match oty with
  | None => true
  | Some dt => is_scalar_dtyp dt
  end.

Definition oty_subsumes (gen spec : ty_info) : bool :=
  match gen, spec with
  | None, _ => true
  | Some dt1, Some dt2 => is_scalar_dtyp dt1 && dtyp_eqb dt1 dt2
  | Some _, None => false
  end.

Definition tenv_subsumes (te_gen te_spec : ty_env) : bool :=
  forallb
    (fun '(x, oty_g) =>
       oty_valid oty_g &&
       match lookup_ty x te_spec with
       | Some oty_s => oty_subsumes oty_g oty_s
       | None => false
       end)
    te_gen.

Definition meet_oty (o1 o2 : ty_info) : ty_info :=
  match o1, o2 with
  | Some dt1, Some dt2 =>
      if is_scalar_dtyp dt1 && dtyp_eqb dt1 dt2 then Some dt1 else None
  | _, _ => None
  end.

Fixpoint meet_ty_env_fuel (fuel : nat) (te1 te2 : ty_env) : ty_env :=
  match fuel with
  | O => []
  | S fuel' =>
      match te1 with
      | [] => []
      | (x, o1) :: rest =>
          match lookup_ty x te2 with
          | Some o2 => (x, meet_oty o1 o2) :: meet_ty_env_fuel fuel' (remove_ty x rest) te2
          | None => meet_ty_env_fuel fuel' rest te2
          end
      end
  end.

Definition meet_ty_env (te1 te2 : ty_env) : ty_env :=
  meet_ty_env_fuel (List.length te1) te1 te2.

(** ** Scalar Type & Failure-Freedom Predicates *)

Definition is_int_dtyp (dt : dtyp) : bool :=
  match dt with
  | DTYPE_Base (DTYPE_I _) => true
  | _ => false
  end.

Definition is_ptr_dtyp (dt : dtyp) : bool :=
  match dt with
  | DTYPE_Base DTYPE_Pointer => true
  | _ => false
  end.

Definition is_fp_dtyp (dt : dtyp) : bool :=
  match dt with
  | DTYPE_Base (DTYPE_FP FP_float) => true
  | DTYPE_Base (DTYPE_FP FP_double) => true
  | _ => false
  end.

Definition is_i1_dtyp (dt : dtyp) : bool :=
  match dt with
  | DTYPE_Base (DTYPE_I xH) => true
  | _ => false
  end.

Definition is_valid_float_lit (dt : dtyp) (f : float_syntax) : bool :=
  match dt with
  | DTYPE_Base (DTYPE_FP FP_float) =>
      match float32_of_float_syntax f with
      | Some _ => true
      | None => false
      end
  | DTYPE_Base (DTYPE_FP FP_double) =>
      match float_of_float_syntax f with
      | Some _ => true
      | None => false
      end
  | _ => false
  end.

(** Syntactic integer constants that never evaluate to [DVALUE_Poison] when
    denoted at [Some (DTYPE_Base (DTYPE_I sz))]. Used to guard [SDiv]/[SRem]
    where Vellvm raises [FailureE] on [(DVALUE_Poison, DVALUE_Poison)]. *)
Definition is_nonpoison_int_lit (dt : dtyp) (e : exp dtyp) : bool :=
  match e with
  | EXP_Integer _ | EXP_Zero_initializer => is_int_dtyp dt
  | EXP_Bool _ => is_i1_dtyp dt
  | _ => false
  end.

Definition is_safe_ibinop_for (dt : dtyp) (iop : ibinop) (e2 : exp dtyp) : bool :=
  is_int_dtyp dt &&
  match iop with
  | SDiv _ | SRem => is_nonpoison_int_lit dt e2
  | _ => true
  end.

Definition is_ptr_safe_icmp (cmp : icmp) : bool :=
  match cmp with
  | Eq | Ne | Ugt | Uge | Ult | Ule => true
  | Sgt | Sge | Slt | Sle => false
  end.

Definition is_safe_icmp_ty (cmp : icmp) (dt : dtyp) : bool :=
  if is_int_dtyp dt then true
  else if is_ptr_dtyp dt then is_ptr_safe_icmp cmp
  else false.

Definition is_safe_fbinop (fop : fbinop) : bool :=
  match fop with
  | FAdd | FSub | FMul | FDiv => true
  | FRem => false
  end.

Definition is_safe_pure_conv (pc : pure_conversion) (dt_from dt_to : dtyp) : bool :=
  match pc with
  | Trunc _ _ =>
      match dt_from, dt_to with
      | DTYPE_Base (DTYPE_I sz1), DTYPE_Base (DTYPE_I sz2) => (sz2 <? sz1)%positive
      | _, _ => false
      end
  | Zext _ | Sext =>
      match dt_from, dt_to with
      | DTYPE_Base (DTYPE_I sz1), DTYPE_Base (DTYPE_I sz2) => (sz1 <? sz2)%positive
      | _, _ => false
      end
  | Uitofp _ | Sitofp => is_int_dtyp dt_from && is_fp_dtyp dt_to
  | Fptoui | Fptosi => is_fp_dtyp dt_from && is_int_dtyp dt_to
  | Fpext _ =>
      match dt_from, dt_to with
      | DTYPE_Base (DTYPE_FP FP_float), DTYPE_Base (DTYPE_FP FP_double) => true
      | _, _ => false
      end
  | Fptrunc _ =>
      match dt_from, dt_to with
      | DTYPE_Base (DTYPE_FP FP_double), DTYPE_Base (DTYPE_FP FP_float) => true
      | _, _ => false
      end
  end.

(** Checks that [denote_exp' (Some dt) e] executes purely via defined local
    reads and pure operations (or cuts [ThrowUB]), producing a value satisfying
    [dvalue_has_dtyp v dt] with [is_scalar_dtyp dt = true]. *)
Fixpoint check_scalar_texp (te : ty_env) (dt : dtyp) (e : exp dtyp) {struct e} : bool :=
  is_scalar_dtyp dt &&
  match e with
  | EXP_Ident (ID_Local x) =>
      match lookup_ty x te with
      | Some (Some dt') => dtyp_eqb dt' dt
      | _ => false
      end
  | EXP_Integer _ => is_int_dtyp dt
  | EXP_Float f => is_valid_float_lit dt f
  | EXP_Bool _ => is_i1_dtyp dt
  | EXP_Null => is_ptr_dtyp dt
  | EXP_Zero_initializer | EXP_Undef | EXP_Poison => true
  | OP_IBinop iop dt' e1 e2 =>
      dtyp_eqb dt' dt
      && is_safe_ibinop_for dt' iop e2
      && check_scalar_texp te dt' e1
      && check_scalar_texp te dt' e2
  | OP_ICmp _ cmp dt' e1 e2 =>
      is_i1_dtyp dt
      && is_safe_icmp_ty cmp dt'
      && check_scalar_texp te dt' e1
      && check_scalar_texp te dt' e2
  | OP_FBinop fop _ dt' e1 e2 =>
      is_fp_dtyp dt
      && dtyp_eqb dt' dt
      && is_safe_fbinop fop
      && check_scalar_texp te dt' e1
      && check_scalar_texp te dt' e2
  | OP_Fneg _ (dt', e1) =>
      is_fp_dtyp dt
      && dtyp_eqb dt' dt
      && check_scalar_texp te dt' e1
  | OP_FCmp _ _ dt' e1 e2 =>
      is_i1_dtyp dt
      && is_fp_dtyp dt'
      && check_scalar_texp te dt' e1
      && check_scalar_texp te dt' e2
  | OP_Conversion (CONV_Pure pc) dt_from e1 dt_to =>
      dtyp_eqb dt_to dt
      && is_safe_pure_conv pc dt_from dt_to
      && check_scalar_texp te dt_from e1
  | OP_Conversion CONV_Bitcast dt_from e1 dt_to =>
      dtyp_eqb dt_to dt
      && dtyp_eqb dt_from dt_to
      && check_scalar_texp te dt_from e1
  | OP_Select _ (dt_c, ec) (dt1, e1) (dt2, e2) =>
      is_i1_dtyp dt_c
      && dtyp_eqb dt1 dt
      && dtyp_eqb dt2 dt
      && check_scalar_texp te dt_c ec
      && check_scalar_texp te dt1 e1
      && check_scalar_texp te dt2 e2
  | _ => false
  end.

(** Checks that [denote_exp' (Some dt) e] executes purely via defined local
    reads and pure operations (or cuts [ThrowUB]) to some [dvalue] (not
    necessarily scalar, e.g. copies/selects/phis of function parameters or
    aggregates). *)
Fixpoint check_any_texp (te : ty_env) (dt : dtyp) (e : exp dtyp) {struct e} : bool :=
  match e with
  | EXP_Ident (ID_Local x) =>
      match lookup_ty x te with
      | Some _ => true
      | None => false
      end
  | EXP_Bool _ | EXP_Null | EXP_Undef | EXP_Poison => true
  | EXP_Integer _ => is_int_dtyp dt
  | EXP_Float f => is_valid_float_lit dt f
  | EXP_Zero_initializer => is_scalar_dtyp dt
  | OP_Conversion CONV_Bitcast dt_from e1 dt_to =>
      dtyp_eqb dt_from dt_to && check_any_texp te dt_from e1
  | OP_Select _ (dt_c, ec) (dt1, e1) (dt2, e2) =>
      is_i1_dtyp dt_c
      && check_scalar_texp te dt_c ec
      && check_any_texp te dt1 e1
      && check_any_texp te dt2 e2
  | _ => check_scalar_texp te dt e
  end.

(** Candidate result type for expressions whose [denote_exp None e] is
    definitionally identical to [denote_exp (Some dt) e]. *)
Definition op_cand_dtyp (e : exp dtyp) : option dtyp :=
  match e with
  | EXP_Bool _ => Some (DTYPE_Base (DTYPE_I xH))
  | EXP_Null => Some (DTYPE_Base DTYPE_Pointer)
  | OP_IBinop _ dt _ _ => Some dt
  | OP_ICmp _ _ _ _ _ => Some (DTYPE_Base (DTYPE_I xH))
  | OP_FBinop _ _ dt _ _ => Some dt
  | OP_Fneg _ (dt, _) => Some dt
  | OP_FCmp _ _ _ _ _ => Some (DTYPE_Base (DTYPE_I xH))
  | OP_Conversion (CONV_Pure _) _ _ dt_to => Some dt_to
  | OP_Conversion CONV_Bitcast _ _ dt_to => Some dt_to
  | OP_GetElementPtr _ _ _ _ => Some (DTYPE_Base DTYPE_Pointer)
  | OP_Select _ _ (dt1, _) _ => Some dt1
  | OP_Freeze (dt, _) => Some dt
  | _ => None
  end.

(** Checks that top-level [denote_exp' None op] in [INSTR_Op op] is safe to
    eliminate when dead (note: bare [EXP_Integer], [EXP_Float], and
    [EXP_Zero_initializer] raise [FailureE] at [top = None], so they are
    rejected here). *)
Definition check_safe_op (te : ty_env) (op : exp dtyp) : bool :=
  match op with
  | EXP_Ident (ID_Local x) =>
      match lookup_ty x te with
      | Some _ => true
      | None => false
      end
  | EXP_Bool _ | EXP_Null | EXP_Undef | EXP_Poison => true
  | OP_Conversion CONV_Bitcast dt_from e1 dt_to =>
      dtyp_eqb dt_from dt_to && check_any_texp te dt_from e1
  | OP_Select _ (dt_c, ec) (dt1, e1) (dt2, e2) =>
      is_i1_dtyp dt_c
      && check_scalar_texp te dt_c ec
      && check_any_texp te dt1 e1
      && check_any_texp te dt2 e2
  | _ =>
      match op_cand_dtyp op with
      | Some dt => check_scalar_texp te dt op
      | None => false
      end
  end.

(** Checks that WHENEVER [denote_exp' (Some dt) e] returns a value [v]
    (whether kept or deleted), [v] satisfies [dvalue_has_dtyp v dt] with
    [is_scalar_dtyp dt = true]. Covers kept [SDiv]/[SRem], [OP_GetElementPtr],
    [OP_Freeze], and [CONV_Bitcast] in addition to all [check_scalar_texp]
    forms so downstream dead instructions can rely on their scalar types. *)
Fixpoint guarantees_scalar_dtyp (te : ty_env) (dt : dtyp) (e : exp dtyp) {struct e} : bool :=
  is_scalar_dtyp dt &&
  match e with
  | EXP_Ident (ID_Local x) =>
      match lookup_ty x te with
      | Some (Some dt') => dtyp_eqb dt' dt
      | _ => false
      end
  | EXP_Integer _ => is_int_dtyp dt
  | EXP_Float _ => is_fp_dtyp dt
  | EXP_Bool _ => is_i1_dtyp dt
  | EXP_Null => is_ptr_dtyp dt
  | EXP_Zero_initializer | EXP_Undef | EXP_Poison => true
  | OP_IBinop _ dt' e1 e2 =>
      is_int_dtyp dt
      && dtyp_eqb dt' dt
      && guarantees_scalar_dtyp te dt' e1
      && guarantees_scalar_dtyp te dt' e2
  | OP_ICmp _ _ dt' e1 _ =>
      is_i1_dtyp dt
      && (is_int_dtyp dt' || is_ptr_dtyp dt')
      && guarantees_scalar_dtyp te dt' e1
  | OP_FBinop _ _ dt' e1 _ =>
      is_fp_dtyp dt
      && dtyp_eqb dt' dt
      && guarantees_scalar_dtyp te dt' e1
  | OP_Fneg _ (dt', e1) =>
      is_fp_dtyp dt
      && dtyp_eqb dt' dt
      && guarantees_scalar_dtyp te dt' e1
  | OP_FCmp _ _ dt' e1 _ =>
      is_i1_dtyp dt
      && is_fp_dtyp dt'
      && guarantees_scalar_dtyp te dt' e1
  | OP_Conversion (CONV_Pure _) _ _ dt_to =>
      dtyp_eqb dt_to dt
  | OP_Conversion CONV_Bitcast dt_from e1 dt_to =>
      dtyp_eqb dt_to dt
      && (if dtyp_eqb dt_from dt_to
          then guarantees_scalar_dtyp te dt_from e1
          else true)
  | OP_GetElementPtr _ _ _ _ =>
      is_ptr_dtyp dt
  | OP_Select _ (dt_c, ec) (dt1, e1) (dt2, e2) =>
      is_i1_dtyp dt_c
      && dtyp_eqb dt1 dt
      && dtyp_eqb dt2 dt
      && guarantees_scalar_dtyp te dt_c ec
      && guarantees_scalar_dtyp te dt1 e1
      && guarantees_scalar_dtyp te dt2 e2
  | OP_Freeze (dt', e1) =>
      dtyp_eqb dt' dt
      && guarantees_scalar_dtyp te dt' e1
  | _ => false
  end.

Definition infer_op_oty (te : ty_env) (op : exp dtyp) : ty_info :=
  match op with
  | EXP_Ident (ID_Local x) =>
      match lookup_ty x te with
      | Some oty => oty
      | None => None
      end
  | _ =>
      match op_cand_dtyp op with
      | Some dt => if guarantees_scalar_dtyp te dt op then Some dt else None
      | None => None
      end
  end.

(** ** Forward Transfer Functions for Instructions, Code, Phis, and Terminators *)

Definition step_tenv_instr
  (te : ty_env) (ins : instr_id * instr dtyp * list (metadata dtyp)) : ty_env :=
  let '(iid, i, _) := ins in
  match iid, i with
  | IId id, INSTR_Op op => set_ty id (infer_op_oty te op) te
  | IId id, INSTR_Alloca _ _ => set_ty id (Some (DTYPE_Base DTYPE_Pointer)) te
  | IId id, INSTR_Load dt _ _ => set_ty id (Some dt) te
  | IId id, INSTR_Call _ _ _ _ => set_ty id None te
  | IId id, INSTR_VAArg _ _ => set_ty id None te
  | IId id, INSTR_AtomicCmpXchg _ => set_ty id None te
  | IId id, INSTR_AtomicRMW _ => set_ty id None te
  | IId id, INSTR_LandingPad _ _ _ => set_ty id None te
  | _, _ => te
  end.

Fixpoint step_tenv_code (te : ty_env) (cs : code dtyp) : ty_env :=
  match cs with
  | [] => te
  | ins :: rest => step_tenv_code (step_tenv_instr te ins) rest
  end.

Definition step_tenv_term
  (trm : instr_id * terminator dtyp * list (metadata dtyp))
  (succ : block_id) (te : ty_env) : ty_env :=
  let '(iid, tm, _) := trm in
  match iid, tm with
  | IId id, TERM_Invoke _ _ to_l unwind_l _ _ =>
      if raw_id_eqb succ to_l && negb (raw_id_eqb succ unwind_l) then
        set_ty id None te
      else if negb (raw_id_eqb succ to_l) then
        te
      else
        remove_ty id te
  | _, _ => te
  end.

Definition phi_res_oty (bid_from : block_id) (te_pred : ty_env) (p : phi dtyp) : ty_info :=
  let 'Phi _ dt args := p in
  match assoc bid_from args with
  | Some op => if guarantees_scalar_dtyp te_pred dt op then Some dt else None
  | None => None
  end.

Fixpoint apply_phi_writes (writes : list (local_id * ty_info)) (te : ty_env) : ty_env :=
  match writes with
  | [] => te
  | (id, oty) :: rest => apply_phi_writes rest (set_ty id oty te)
  end.

Definition step_tenv_phis_from
  (bid_from : block_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  (te_pred : ty_env) : ty_env :=
  let writes :=
    List.map (fun '(id, p, _) => (id, phi_res_oty bid_from te_pred p)) phis in
  apply_phi_writes writes te_pred.

Fixpoint init_tenv (fargs : list local_id) : ty_env :=
  match fargs with
  | [] => []
  | x :: rest => set_ty x None (init_tenv rest)
  end.

(** ** Fuel-Bounded Reachability & Forward Type Fixpoint + Boolean Validator *)

Definition fwd_map : Type := list (block_id * ty_env).

Fixpoint lookup_fwd (bid : block_id) (fm : fwd_map) : ty_env :=
  match fm with
  | [] => []
  | (b, te) :: rest => if raw_id_eqb bid b then te else lookup_fwd bid rest
  end.

Fixpoint compute_reach_loop
  (fuel : nat) (bks : ocfg dtyp) (reach : list block_id) : list block_id :=
  match fuel with
  | O => reach
  | S fuel' =>
      let reach' :=
        fold_left
          (fun acc bk =>
             if in_raw_ids (blk_id bk) acc
             then add_raw_ids (block_successors bk) acc
             else acc)
          bks reach in
      if raw_ids_subset reach' reach then reach
      else compute_reach_loop fuel' bks reach'
  end.

Definition compute_reach (c : CFG.cfg dtyp) : list block_id :=
  compute_reach_loop (S (List.length (blks c))) (blks c) [init c].

(** Collects all reachable incoming edges [(bid_from, te_before_phis)] into
    target block ID [bid_tgt], including [(init c, init_tenv fargs)] when
    [bid_tgt = init c]. *)
Definition incoming_edges_for
  (fargs : list local_id) (reach : list block_id) (fm : fwd_map)
  (c : CFG.cfg dtyp) (bid_tgt : block_id) : list (block_id * ty_env) :=
  let entry_edges :=
    if raw_id_eqb bid_tgt (init c) then [(init c, init_tenv fargs)] else [] in
  let pred_edges :=
    flat_map
      (fun bk =>
         if in_raw_ids (blk_id bk) reach && in_raw_ids bid_tgt (block_successors bk) then
           let te_end := step_tenv_code (lookup_fwd (blk_id bk) fm) (blk_code bk) in
           [(blk_id bk, step_tenv_term (blk_term bk) bid_tgt te_end)]
         else [])
      (blks c) in
  entry_edges ++ pred_edges.

Definition meet_incoming_for_block
  (fargs : list local_id) (reach : list block_id) (fm : fwd_map)
  (c : CFG.cfg dtyp) (bk : block dtyp) : ty_env :=
  let edges := incoming_edges_for fargs reach fm c (blk_id bk) in
  let post_phis :=
    List.map (fun '(pred, te_e) => step_tenv_phis_from pred (blk_phis bk) te_e) edges in
  match post_phis with
  | [] => []
  | te0 :: rest => fold_left meet_ty_env rest te0
  end.

Fixpoint compute_fwd_loop
  (fuel : nat) (fargs : list local_id) (reach : list block_id)
  (c : CFG.cfg dtyp) (fm : fwd_map) : fwd_map :=
  match fuel with
  | O => fm
  | S fuel' =>
      let fm' :=
        List.map
          (fun bk =>
             if in_raw_ids (blk_id bk) reach then
               (blk_id bk, meet_incoming_for_block fargs reach fm c bk)
             else (blk_id bk, []))
          (blks c) in
      if forallb
           (fun '(b, te_new) =>
              let te_old := lookup_fwd b fm in
              tenv_subsumes te_old te_new && tenv_subsumes te_new te_old)
           fm'
      then fm'
      else compute_fwd_loop fuel' fargs reach c fm'
  end.

Definition compute_fwd_tenv
  (fargs : list local_id) (reach : list block_id) (c : CFG.cfg dtyp) : fwd_map :=
  let all_defs :=
    fargs ++ flat_map full_block_defs (blks c) in
  let top_te := List.map (fun x => (x, None)) all_defs in
  let fm0 := List.map (fun bk => (blk_id bk, top_te)) (blks c) in
  compute_fwd_loop (S (S (List.length (blks c) * 2))) fargs reach c fm0.

(** Boolean validator [PS-10] for reachability and per-block-code-entry
    type environments. *)
Definition check_fwd_cfg
  (fargs : list local_id) (reach : list block_id) (fm : fwd_map)
  (c : CFG.cfg dtyp) : bool :=
  in_raw_ids (init c) reach
  && (match find_block (blks c) (init c) with
      | Some bk_init =>
          tenv_subsumes
            (lookup_fwd (init c) fm)
            (step_tenv_phis_from (init c) (blk_phis bk_init) (init_tenv fargs))
      | None => true
      end)
  && forallb
       (fun bk =>
          if in_raw_ids (blk_id bk) reach then
            let te_end := step_tenv_code (lookup_fwd (blk_id bk) fm) (blk_code bk) in
            forallb
              (fun succ =>
                 in_raw_ids succ reach &&
                 match find_block (blks c) succ with
                 | Some bk_succ =>
                     let te_edge := step_tenv_term (blk_term bk) succ te_end in
                     tenv_subsumes
                       (lookup_fwd succ fm)
                       (step_tenv_phis_from (blk_id bk) (blk_phis bk_succ) te_edge)
                 | None => true
                 end)
              (block_successors bk)
          else true)
       (blks c).

(** * 4. Backward Liveness, Dead Instruction / Phi Elimination, & Validator *)

Definition instr_must_kill (iid : instr_id) (i : instr dtyp) : option local_id :=
  match iid, i with
  | IId x, INSTR_Op _ => Some x
  | IId x, INSTR_Alloca _ _ => Some x
  | IId x, INSTR_Load _ _ _ => Some x
  | IId x, INSTR_Call _ _ _ _ => Some x
  | IId x, INSTR_VAArg _ _ => Some x
  | IId x, INSTR_AtomicCmpXchg _ => Some x
  | IId x, INSTR_AtomicRMW _ => Some x
  | IId x, INSTR_LandingPad _ _ _ => Some x
  | _, _ => None
  end.

(** Single-pass forward-type / backward-liveness instruction sweep:
    propagates [te] forward and [live] backward, deleting dead [INSTR_Op]
    instructions (including multi-instruction intra-block dead chains). *)
Fixpoint dce_code
  (te : ty_env) (cs : code dtyp) (live_after : list raw_id)
  : list raw_id * code dtyp :=
  match cs with
  | [] => (live_after, [])
  | ins :: rest =>
      let '(live_mid, rest') :=
        dce_code (step_tenv_instr te ins) rest live_after in
      match ins with
      | (IId x, INSTR_Op op, _) =>
          if negb (in_raw_ids x live_mid) && check_safe_op te op then
            (live_mid, rest')
          else
            (add_raw_ids (full_instr_uses (INSTR_Op op)) (remove_raw_id x live_mid),
             ins :: rest')
      | (iid, i, _) =>
          let live_killed :=
            match instr_must_kill iid i with
            | Some x => remove_raw_id x live_mid
            | None => live_mid
            end in
          (add_raw_ids (full_instr_uses i) live_killed, ins :: rest')
      end
  end.

Lemma dce_code_sublist (te : ty_env) (cs : code dtyp) (live_after : list raw_id) :
  is_sublist (snd (dce_code te cs live_after)) cs.
Proof.
  revert te live_after; induction cs as [| ins rest IH]; intros te live_after; [constructor |].
  cbn [dce_code].
  specialize (IH (step_tenv_instr te ins) live_after).
  destruct (dce_code (step_tenv_instr te ins) rest live_after) as [live_mid rest']; cbn [snd] in IH.
  destruct ins as [[iid i] md].
  destruct iid as [x | vid], i;
    try (cbn [snd]; constructor; exact IH).
  destruct (negb (in_raw_ids x live_mid) && check_safe_op te op); cbn [snd];
    [apply Sublist_drop, IH | apply Sublist_keep, IH].
Qed.

Definition is_safe_phi_on_edge
  (bid_from : block_id) (te_edge : ty_env) (p : phi dtyp) : bool :=
  let 'Phi _ dt args := p in
  match assoc bid_from args with
  | Some op => check_any_texp te_edge dt op
  | None => false
  end.

Fixpoint dce_phis
  (edges : list (block_id * ty_env))
  (live_after_phis : list raw_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  : list (local_id * phi dtyp * list (metadata dtyp)) :=
  match phis with
  | [] => []
  | (id, p, md) :: rest =>
      let rest' := dce_phis edges live_after_phis rest in
      if negb (in_raw_ids id live_after_phis)
         && forallb (fun '(pred, te_e) => is_safe_phi_on_edge pred te_e p) edges
      then rest'
      else (id, p, md) :: rest'
  end.

Lemma dce_phis_sublist
  (edges : list (block_id * ty_env)) (live_after_phis : list raw_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp))) :
  is_sublist (dce_phis edges live_after_phis phis) phis.
Proof.
  induction phis as [| [[id p] md] rest IH]; [constructor |].
  cbn [dce_phis].
  destruct (negb (in_raw_ids id live_after_phis) && _);
    [apply Sublist_drop, IH | apply Sublist_keep, IH].
Qed.

Definition kept_phis_uses_from
  (bid_from : block_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp))) : list raw_id :=
  flat_map
    (fun '(_, Phi _ _ args, _) =>
       match assoc bid_from args with
       | Some op => full_exp_uses op
       | None => []
       end)
    phis.

Definition kept_phi_defs
  (phis : list (local_id * phi dtyp * list (metadata dtyp))) : list raw_id :=
  List.map (fun '(id, _, _) => id) phis.

Definition edge_live_req
  (bid_from : block_id)
  (phis_kept : list (local_id * phi dtyp * list (metadata dtyp)))
  (live_code_in : list raw_id) : list raw_id :=
  add_raw_ids
    (kept_phis_uses_from bid_from phis_kept)
    (remove_raw_ids (kept_phi_defs phis_kept) live_code_in).

(** ** Backward Liveness Fixpoint, Block Transform, & Validator *)

Definition live_map : Type := list (block_id * list raw_id).

Fixpoint lookup_live (bid : block_id) (lm : live_map) : list raw_id :=
  match lm with
  | [] => []
  | (b, lv) :: rest => if raw_id_eqb bid b then lv else lookup_live bid rest
  end.

Definition block_live_before_term
  (bk : block dtyp) (lm : live_map) : list raw_id :=
  let '(_, tm, _) := blk_term bk in
  add_raw_ids (full_term_uses tm) (lookup_live (blk_id bk) lm).

Definition dce_block_info
  (fargs : list local_id) (reach : list block_id) (fm : fwd_map)
  (lm : live_map) (c : CFG.cfg dtyp) (bk : block dtyp)
  : list raw_id * block dtyp :=
  if in_raw_ids (blk_id bk) reach then
    let te_in := lookup_fwd (blk_id bk) fm in
    let live_end := block_live_before_term bk lm in
    let '(live_code, code') := dce_code te_in (blk_code bk) live_end in
    let edges := incoming_edges_for fargs reach fm c (blk_id bk) in
    let phis' := dce_phis edges live_code (blk_phis bk) in
    (live_code,
     {| blk_id       := blk_id bk;
        blk_phis     := phis';
        blk_code     := code';
        blk_term     := blk_term bk;
        blk_comments := blk_comments bk |})
  else
    ([], bk).

Definition dce_block
  (fargs : list local_id) (reach : list block_id) (fm : fwd_map)
  (lm : live_map) (c : CFG.cfg dtyp) (bk : block dtyp) : block dtyp :=
  snd (dce_block_info fargs reach fm lm c bk).

Lemma dce_block_id
  (fargs : list local_id) (reach : list block_id) (fm : fwd_map)
  (lm : live_map) (c : CFG.cfg dtyp) (bk : block dtyp) :
  blk_id (dce_block fargs reach fm lm c bk) = blk_id bk.
Proof.
  unfold dce_block, dce_block_info.
  destruct (in_raw_ids (blk_id bk) reach); [| reflexivity].
  destruct (dce_code _ _ _); reflexivity.
Qed.

Fixpoint compute_live_loop
  (fuel : nat) (fargs : list local_id) (reach : list block_id)
  (fm : fwd_map) (c : CFG.cfg dtyp) (lm : live_map) : live_map :=
  match fuel with
  | O => lm
  | S fuel' =>
      let lm' :=
        List.map
          (fun bk =>
             if in_raw_ids (blk_id bk) reach then
               let lv :=
                 fold_left
                   (fun acc succ =>
                      match find_block (blks c) succ with
                      | Some bk_succ =>
                          let '(live_code_s, bk_dce_s) :=
                            dce_block_info fargs reach fm lm c bk_succ in
                          add_raw_ids
                            (edge_live_req (blk_id bk) (blk_phis bk_dce_s) live_code_s)
                            acc
                      | None => acc
                      end)
                   (block_successors bk)
                   (lookup_live (blk_id bk) lm) in
               (blk_id bk, lv)
             else (blk_id bk, []))
          (blks c) in
      if forallb
           (fun '(b, lv_new) => raw_ids_eqb (lookup_live b lm) lv_new)
           lm'
      then lm'
      else compute_live_loop fuel' fargs reach fm c lm'
  end.

Definition compute_live_out
  (fargs : list local_id) (reach : list block_id)
  (fm : fwd_map) (c : CFG.cfg dtyp) : live_map :=
  let lm0 := List.map (fun bk => (blk_id bk, [])) (blks c) in
  compute_live_loop (S (S (List.length (blks c) * 2))) fargs reach fm c lm0.

(** Boolean validator [PS-10] for backward liveness across all reachable CFG
    edges. *)
Definition check_live_cfg
  (fargs : list local_id) (reach : list block_id)
  (fm : fwd_map) (lm : live_map) (c : CFG.cfg dtyp) : bool :=
  forallb
    (fun bk =>
       if in_raw_ids (blk_id bk) reach then
         forallb
           (fun succ =>
              match find_block (blks c) succ with
              | Some bk_succ =>
                  let '(live_code_s, bk_dce_s) :=
                    dce_block_info fargs reach fm lm c bk_succ in
                  raw_ids_subset
                    (edge_live_req (blk_id bk) (blk_phis bk_dce_s) live_code_s)
                    (lookup_live (blk_id bk) lm)
              | None => true
              end)
           (block_successors bk)
       else true)
    (blks c).

Definition dce_cfg_once (fargs : list local_id) (c : CFG.cfg dtyp) : CFG.cfg dtyp :=
  if cfg_no_block_addresses c && nodup_raw_ids (List.map blk_id (blks c)) then
    let reach := compute_reach c in
    let fm := compute_fwd_tenv fargs reach c in
    let lm := compute_live_out fargs reach fm c in
    if check_fwd_cfg fargs reach fm c && check_live_cfg fargs reach fm lm c then
      {| init := init c;
         blks := List.map (dce_block fargs reach fm lm c) (blks c);
         args := args c |}
    else c
  else c.

Lemma dce_block_no_block_addresses
  (fargs : list local_id) (reach : list block_id) (fm : fwd_map)
  (lm : live_map) (c : CFG.cfg dtyp) (bk : block dtyp) :
  block_block_addresses bk = [] ->
  block_block_addresses (dce_block fargs reach fm lm c bk) = [].
Proof.
  intros Hbk.
  unfold dce_block, dce_block_info; cbn zeta.
  destruct (in_raw_ids (blk_id bk) reach); [| exact Hbk].
  pose proof (dce_code_sublist (lookup_fwd (blk_id bk) fm) (blk_code bk)
                (block_live_before_term bk lm)) as Hcsub.
  destruct (dce_code (lookup_fwd (blk_id bk) fm) (blk_code bk)
              (block_live_before_term bk lm)) as [live_code code']; cbn [snd] in *.
  unfold block_block_addresses in Hbk |- *; cbn [blk_phis blk_code blk_term].
  apply app_eq_nil in Hbk as [Hphis Hrest].
  apply app_eq_nil in Hrest as [Hcode Hterm].
  rewrite (flat_map_nil_sublist _ _ _ (dce_phis_sublist _ _ _) Hphis).
  rewrite (flat_map_nil_sublist _ _ _ Hcsub Hcode).
  rewrite Hterm; reflexivity.
Qed.

Lemma dce_cfg_once_block_addresses (fargs : list local_id) (c : CFG.cfg dtyp) :
  flat_map block_block_addresses (blks (dce_cfg_once fargs c)) =
  flat_map block_block_addresses (blks c).
Proof.
  unfold dce_cfg_once; cbn zeta.
  destruct (cfg_no_block_addresses c) eqn:Enba; cbn [andb]; [| reflexivity].
  destruct (nodup_raw_ids (List.map blk_id (blks c))); [| reflexivity].
  destruct (check_fwd_cfg _ _ _ _ && check_live_cfg _ _ _ _ _); [| reflexivity].
  apply cfg_no_block_addresses_nil in Enba; rewrite Enba; cbn [blks].
  set (reach := compute_reach c) in *.
  set (fm := compute_fwd_tenv fargs reach c) in *.
  set (lm := compute_live_out fargs reach fm c) in *.
  induction (blks c) as [| bk rest IH]; [reflexivity |].
  cbn [List.map flat_map] in Enba |- *.
  apply app_eq_nil in Enba as [Hbk Hrest].
  rewrite (dce_block_no_block_addresses fargs reach fm lm c bk Hbk).
  cbn [app]; apply IH, Hrest.
Qed.


