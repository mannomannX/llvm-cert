(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Dead Code & Dead Phi Elimination ([CertPasses.DCE])

    Eliminates dead side-effect-free SSA operations ([INSTR_Op]) and dead
    [Phi] nodes across each function CFG using:
    1. A fuel-bounded forward reachability and scalar-type/definedness
       dataflow analysis backed by a boolean validator ([check_fwd_cfg]),
       guaranteeing that every deleted expression or incoming phi operand
       evaluates without raising [FailureE], [OOME], or observable events.
    2. A fuel-bounded backward liveness fixpoint backed by a boolean
       validator ([check_live_cfg]), combined with single-sweep intra-block
       backward dead-chain elimination and multi-round module iteration. *)

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
  - apply RelDec.rel_dec_correct in E; subst k'.
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

Fixpoint meet_ty_env (te1 te2 : ty_env) : ty_env :=
  match te1 with
  | [] => []
  | (x, o1) :: rest =>
      match lookup_ty x te2 with
      | Some o2 => (x, meet_oty o1 o2) :: meet_ty_env (remove_ty x rest) te2
      | None => meet_ty_env rest te2
      end
  end.

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
  destruct (negb (in_raw_ids x live_mid) && check_safe_op te e); cbn [snd];
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


(** * 5. Pure [EOU] Safety & Scalar Runtime Typing Lemmas *)

Section DCESoundness.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Hint Resolve cfg_local_sim__mon : paco.

  Lemma dvalue_ind_nested (P : @dvalue PaV -> Prop)
    (HBase : forall db : @dvalue_base PaV, P (DVALUE_Base db))
    (HStruct : forall (p : bool) (fs : list (@dvalue PaV)),
        Forall P fs -> P (DVALUE_Struct p fs))
    (HArray : forall (v : bool) (es : list (@dvalue PaV)),
        Forall P es -> P (DVALUE_Array v es)) :
    forall dv : @dvalue PaV, P dv.
  Proof.
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

  Lemma is_i1_dtyp_eq (dt : dtyp) :
    is_i1_dtyp dt = true -> dt = DTYPE_Base (DTYPE_I 1%positive).
  Proof.
    destruct dt as [dtb | |]; [| discriminate | discriminate].
    destruct dtb as [sz | | | | | | | | | |]; try discriminate.
    destruct sz as [p | p |]; try discriminate; reflexivity.
  Qed.

  Lemma is_ptr_dtyp_eq (dt : dtyp) :
    is_ptr_dtyp dt = true -> dt = DTYPE_Base DTYPE_Pointer.
  Proof.
    destruct dt as [dtb | |]; [| discriminate | discriminate].
    destruct dtb; try discriminate; reflexivity.
  Qed.

  Lemma is_int_dtyp_inv (dt : dtyp) :
    is_int_dtyp dt = true -> exists sz : positive, dt = DTYPE_Base (DTYPE_I sz).
  Proof.
    destruct dt as [dtb | |]; [| discriminate | discriminate].
    destruct dtb as [sz | | | | | | | | | |]; try discriminate.
    intros _; exists sz; reflexivity.
  Qed.

  Lemma is_fp_dtyp_inv (dt : dtyp) :
    is_fp_dtyp dt = true ->
    dt = DTYPE_Base (DTYPE_FP FP_float) \/ dt = DTYPE_Base (DTYPE_FP FP_double).
  Proof.
    destruct dt as [dtb | |]; [| discriminate | discriminate].
    destruct dtb as [| | | | fp | | | | | |]; try discriminate.
    destruct fp; try discriminate; intros _; [left | right]; reflexivity.
  Qed.

  Lemma check_any_guarantees_scalar (te : ty_env) (e : exp dtyp) :
    forall dt : dtyp,
      check_any_texp te dt e = true ->
      guarantees_scalar_dtyp te dt e = true ->
      check_scalar_texp te dt e = true.
  Proof.
    induction e using exp_ind_nested; intros dt Hany Hguar;
      try exact Hany; try exact Hguar.
    - (* EXP_Ident *)
      destruct id as [g | x]; [exact Hany | exact Hguar].
    - (* EXP_Float *)
      cbn [guarantees_scalar_dtyp] in Hguar.
      apply andb_true_iff in Hguar as [Hsc _].
      cbn [check_scalar_texp]; rewrite Hsc; exact Hany.
    - (* OP_Conversion *)
      destruct conv as [| pc | ic]; [| exact Hany | exact Hany].
      cbn [check_any_texp] in Hany; apply andb_true_iff in Hany as [Heq12 Hany1].
      cbn [guarantees_scalar_dtyp] in Hguar; rewrite Heq12 in Hguar.
      apply andb_true_iff in Hguar as [Hsc Hg].
      apply andb_true_iff in Hg as [Heq2 Hg1].
      cbn [check_scalar_texp]; rewrite Hsc, Heq2, Heq12, (IHe dt_from Hany1 Hg1).
      reflexivity.
    - (* OP_Select *)
      cbn [check_any_texp] in Hany.
      apply andb_true_iff in Hany as [Ha Hany2].
      apply andb_true_iff in Ha as [Ha Hany1].
      apply andb_true_iff in Ha as [Hi1 Hsc_c].
      cbn [guarantees_scalar_dtyp] in Hguar.
      apply andb_true_iff in Hguar as [Hsc Hg].
      apply andb_true_iff in Hg as [Hg Hg2].
      apply andb_true_iff in Hg as [Hg Hg1].
      apply andb_true_iff in Hg as [Hg _].
      apply andb_true_iff in Hg as [Hg Heq2].
      apply andb_true_iff in Hg as [_ Heq1].
      cbn [check_scalar_texp].
      rewrite Hsc, Hi1, Heq1, Heq2, Hsc_c,
              (IHe2 dt1 Hany1 Hg1), (IHe3 dt2 Hany2 Hg2).
      reflexivity.
  Qed.

  (** ** Pure [EOU] Predicates *)

  Definition eou_safe {X : Type} (P : X -> Prop) (m : EOU X) : Prop :=
    match m with
    | raise_ub _ => True
    | raise_ret x => P x
    | raise_error _ | raise_oom _ => False
    end.

  Definition eou_ret_imp {X : Type} (P : X -> Prop) (m : EOU X) : Prop :=
    match m with
    | raise_ret x => P x
    | _ => True
    end.

  Lemma fmap_EOU_ret {A B : Type} (f : A -> B) (x : A) :
    (f <$> (raise_ret x : EOU A)) = raise_ret (f x).
  Proof. reflexivity. Qed.

  Lemma bind_EOU_ret {A B : Type} (x : A) (k : A -> EOU B) :
    ExtLib.Structures.Monad.bind (raise_ret x : EOU A) k = k x.
  Proof. reflexivity. Qed.

  Lemma eou_safe_to_ret_imp {X : Type} (P : X -> Prop) (m : EOU X) :
    eou_safe P m -> eou_ret_imp P m.
  Proof.
    destruct m; cbn; intuition.
  Qed.

  Lemma eou_safe_weaken {X : Type} (P Q : X -> Prop) (m : EOU X) :
    (forall x, P x -> Q x) -> eou_safe P m -> eou_safe Q m.
  Proof.
    intros HPQ; destruct m; cbn; auto.
  Qed.

  Lemma eou_ret_imp_weaken {X : Type} (P Q : X -> Prop) (m : EOU X) :
    (forall x, P x -> Q x) -> eou_ret_imp P m -> eou_ret_imp Q m.
  Proof.
    intros HPQ; destruct m; cbn; auto.
  Qed.

  Lemma eou_safe_fmap {A B : Type} (f : A -> B) (P : B -> Prop) (m : EOU A) :
    eou_safe (fun a => P (f a)) m ->
    eou_safe P (f <$> m).
  Proof.
    destruct m; cbn; auto.
  Qed.

  Lemma eou_ret_imp_fmap {A B : Type} (f : A -> B) (P : B -> Prop) (m : EOU A) :
    eou_ret_imp (fun a => P (f a)) m ->
    eou_ret_imp P (f <$> m).
  Proof.
    destruct m; cbn; auto.
  Qed.

  Lemma eou_ret_imp_vec_poison_l
    (f : @dvalue_base PaV -> @dvalue_base PaV -> EOU (@dvalue_base PaV))
    (HF : forall y, eou_ret_imp (fun b => b = DVALUE_Poison) (f DVALUE_Poison y))
    (dt : dtyp) (elts : list (@dvalue PaV)) :
    eou_ret_imp
      (fun v => dvalue_has_dtyp v dt)
      (ExtLib.Structures.Monad.bind (map_monad (@dvalue_to_dvalue_base PaV) elts)
         (fun elts' =>
            ExtLib.Structures.Monad.bind
              (vec_loop f (List.combine (repeat (@DVALUE_Poison PaV) (Datatypes.length elts')) elts'))
              (fun ans =>
                 ExtLib.Structures.Monad.ret (@canonicalize_vector PaV (List.map (@DVALUE_Base PaV) ans))))).
  Proof.
    destruct (map_monad (@dvalue_to_dvalue_base PaV) elts) as [| | | elts'];
      [exact I | exact I | exact I | cbn [ExtLib.Structures.Monad.bind EOU_monad]].
    assert (Hloop :
      eou_ret_imp (Forall (fun b => b = @DVALUE_Poison PaV))
        (vec_loop f (List.combine (repeat (@DVALUE_Poison PaV) (Datatypes.length elts')) elts'))).
    { unfold vec_loop.
      induction elts' as [| y ys IH];
        cbn [Datatypes.length repeat List.combine monad_fold_right ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad].
      - cbn [eou_ret_imp]; constructor.
      - destruct (monad_fold_right _ (List.combine (repeat (@DVALUE_Poison PaV) (Datatypes.length ys)) ys) [])
          as [| | | acc];
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad eou_ret_imp] in IH |- *; try exact I.
        specialize (HF y).
        destruct (f DVALUE_Poison y) as [| | | r];
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad eou_ret_imp] in HF |- *; try exact I.
        constructor; [exact HF | exact IH]. }
    destruct (vec_loop f (List.combine (repeat (@DVALUE_Poison PaV) (Datatypes.length elts')) elts'))
      as [| | | ans];
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad eou_ret_imp] in Hloop |- *; try exact I.
    rewrite (@canonicalize_vector_all_poison_base PaV ans Hloop).
    apply DVALUE_Poison_typ_agg.
  Qed.

  (** ** [dvalue_has_dtyp] Constructors & Inversions *)

  Lemma dvalue_has_dtyp_Poison (dt : dtyp) :
    @dvalue_has_dtyp PaV (DVALUE_Base DVALUE_Poison) dt.
  Proof. apply DVALUE_Poison_typ_agg. Qed.

  Lemma dvalue_has_dtyp_I (sz : positive) (i : @bit_int sz) :
    @dvalue_has_dtyp PaV (DVALUE_Base (@DVALUE_I PaV sz i)) (DTYPE_Base (DTYPE_I sz)).
  Proof.
    apply DVALUE_Base_typ; [apply Pos.eqb_refl | reflexivity].
  Qed.

  Lemma dvalue_has_dtyp_Ptr (p : @ptr PaV) :
    @dvalue_has_dtyp PaV (DVALUE_Base (DVALUE_Pointer p)) (DTYPE_Base DTYPE_Pointer).
  Proof.
    apply DVALUE_Base_typ; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Float (f : ll_float) :
    @dvalue_has_dtyp PaV (DVALUE_Base (DVALUE_Float f)) (DTYPE_Base (DTYPE_FP FP_float)).
  Proof.
    apply DVALUE_Base_typ; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Double (d : ll_double) :
    @dvalue_has_dtyp PaV (DVALUE_Base (DVALUE_Double d)) (DTYPE_Base (DTYPE_FP FP_double)).
  Proof.
    apply DVALUE_Base_typ; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_I_inv (v : @dvalue PaV) (sz : positive) :
    dvalue_has_dtyp v (DTYPE_Base (DTYPE_I sz)) ->
    v = DVALUE_Base DVALUE_Poison \/
    exists i : @bit_int sz, v = DVALUE_Base (@DVALUE_I PaV sz i).
  Proof.
    intros H; inversion H as [db t Hb _ | | |]; subst; [| left; reflexivity].
    destruct db as [p | sz' i | ip | d | f | | | bsz bv]; cbn in Hb; try discriminate Hb.
    - apply Pos.eqb_eq in Hb; subst sz'; right; exists i; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Ptr_inv (v : @dvalue PaV) :
    dvalue_has_dtyp v (DTYPE_Base DTYPE_Pointer) ->
    v = DVALUE_Base DVALUE_Poison \/
    exists p : @ptr PaV, v = DVALUE_Base (DVALUE_Pointer p).
  Proof.
    intros H; inversion H as [db t Hb _ | | |]; subst; [| left; reflexivity].
    destruct db as [p | sz' i | ip | d | f | | | bsz bv]; cbn in Hb; try discriminate Hb.
    - right; exists p; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Float_inv (v : @dvalue PaV) :
    dvalue_has_dtyp v (DTYPE_Base (DTYPE_FP FP_float)) ->
    v = DVALUE_Base DVALUE_Poison \/
    exists f : ll_float, v = DVALUE_Base (DVALUE_Float f).
  Proof.
    intros H; inversion H as [db t Hb _ | | |]; subst; [| left; reflexivity].
    destruct db as [p | sz' i | ip | d | f | | | bsz bv]; cbn in Hb; try discriminate Hb.
    - right; exists f; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Double_inv (v : @dvalue PaV) :
    dvalue_has_dtyp v (DTYPE_Base (DTYPE_FP FP_double)) ->
    v = DVALUE_Base DVALUE_Poison \/
    exists d : ll_double, v = DVALUE_Base (DVALUE_Double d).
  Proof.
    intros H; inversion H as [db t Hb _ | | |]; subst; [| left; reflexivity].
    destruct db as [p | sz' i | ip | d | f | | | bsz bv]; cbn in Hb; try discriminate Hb.
    - right; exists d; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_scalar_base_inv (v : @dvalue PaV) (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    dvalue_has_dtyp v dt ->
    exists db : @dvalue_base PaV,
      v = DVALUE_Base db /\
      (db = DVALUE_Poison \/
       (forall bsz bv, db <> @DVALUE_B PaV bsz bv)).
  Proof.
    intros Hsc Hty.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc.
    inversion Hty as [db t Hb _ | | |]; subst.
    - exists db; split; [reflexivity |].
      destruct db as [p | sz i | ip | d | f | | | bsz bv];
        try (right; intros ? ? Hc; discriminate Hc).
      + left; reflexivity.
      + destruct dtb as [| | | | fp | | | | | |]; try discriminate Hsc;
          try (destruct fp; try discriminate Hsc); cbn in Hb; discriminate Hb.
    - exists DVALUE_Poison; split; [reflexivity | left; reflexivity].
  Qed.

  (** ** Constants, Arithmetic, Comparisons, Conversions, Select, GEP, & Attrs *)

  Lemma denote_int_syntax_as_int_safe (dt : dtyp) (x : int_syntax) :
    is_int_dtyp dt = true ->
    exists (sz : positive) (i : @bit_int sz),
      dt = DTYPE_Base (DTYPE_I sz) /\
      @denote_int_syntax_as_int PaV dt x = raise_ret (DVALUE_Base (@DVALUE_I PaV sz i)).
  Proof.
    intros Hint.
    destruct (is_int_dtyp_inv dt Hint) as [sz ->].
    exists sz, (@Integers.repr sz (denote_int_syntax x)).
    split; [reflexivity | reflexivity].
  Qed.

  Lemma denote_float_syntax_safe (dt : dtyp) (f : float_syntax) :
    is_valid_float_lit dt f = true ->
    eou_safe (fun v => dvalue_has_dtyp v dt) (@denote_float_syntax_as_float PaV dt f).
  Proof.
    intros Hfl.
    destruct dt as [dtb | |]; [| discriminate Hfl | discriminate Hfl].
    destruct dtb as [| | | | fp | | | | | |]; try discriminate Hfl.
    destruct fp; try discriminate Hfl; cbn in Hfl |- *.
    - destruct (float32_of_float_syntax f) as [fl |]; [| discriminate Hfl].
      cbn; apply dvalue_has_dtyp_Float.
    - destruct (float_of_float_syntax f) as [db |]; [| discriminate Hfl].
      cbn; apply dvalue_has_dtyp_Double.
  Qed.

  Lemma denote_float_syntax_ret_imp (dt : dtyp) (f : float_syntax) :
    is_fp_dtyp dt = true ->
    eou_ret_imp (fun v => dvalue_has_dtyp v dt) (@denote_float_syntax_as_float PaV dt f).
  Proof.
    intros Hfp.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->]; cbn.
    - destruct (float32_of_float_syntax f) as [fl |]; cbn;
        [apply dvalue_has_dtyp_Float | exact I].
    - destruct (float_of_float_syntax f) as [db |]; cbn;
        [apply dvalue_has_dtyp_Double | exact I].
  Qed.

  Lemma default_dvalue_scalar_safe (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    exists dv : @dvalue PaV,
      @default_dvalue_of_dtyp PaV dt = raise_ret dv /\
      dvalue_has_dtyp dv dt /\
      (is_int_dtyp dt = true -> dv <> DVALUE_Base DVALUE_Poison).
  Proof.
    intros Hsc.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc.
    destruct dtb as [sz | | | | fp | | | | | |]; try discriminate Hsc.
    - eexists; split; [reflexivity |].
      split; [apply dvalue_has_dtyp_I | intros _ Hc; discriminate Hc].
    - eexists; split; [reflexivity |].
      split; [apply dvalue_has_dtyp_Ptr | intros H; discriminate H].
    - destruct fp; try discriminate Hsc.
      + eexists; split; [reflexivity |].
        split; [apply dvalue_has_dtyp_Float | intros H; discriminate H].
      + eexists; split; [reflexivity |].
        split; [apply dvalue_has_dtyp_Double | intros H; discriminate H].
  Qed.

  Lemma eval_int_op_bit_safe (sz : positive) (iop : ibinop) (x y : @bit_int sz) :
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I sz)))
      (@eval_int_op PaV (@bit_int sz) _ _ iop x y).
  Proof.
    destruct iop; unfold eval_int_op, dvp;
      cbn [madd msub mmul mdivs mmods mshl mnegative mbitwidth mdtyp_of_int tdb
           VIntVMemInt VInt_Bounded ToDvalue_Int option_pred];
      repeat (
        rewrite ?fmap_EOU_ret, ?bind_EOU_ret;
        first [ match goal with
                | |- context [dtyp_base_eq_dec ?a ?b] =>
                    destruct (dtyp_base_eq_dec a b); [discriminate |]
                | |- context [if ?b then _ else _] => destruct b
                end ]
      );
      rewrite ?fmap_EOU_ret, ?bind_EOU_ret;
      cbn [eou_safe];
      first [exact I | apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
  Qed.

  Lemma eval_iop_integer_base_I_I
    (iop : ibinop) (sz1 sz2 : positive) (i1 : @bit_int sz1) (i2 : @bit_int sz2)
    (Hsz : sz1 = sz2) :
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I sz1)))
      (@eval_iop_integer_base PaV iop (@DVALUE_I PaV sz1 i1) (@DVALUE_I PaV sz2 i2)).
  Proof.
    unfold eval_iop_integer_base.
    destruct (Pos.eq_dec sz1 sz2) as [Heq | Hne].
    - clear Hsz; subst; cbn [eq_rect eq_rect_r eq_sym].
      apply eval_int_op_bit_safe.
    - contradiction (Hne Hsz).
  Qed.

  Lemma eval_iop_safe (iop : ibinop) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_int_dtyp dt = true ->
    (match iop with SDiv _ | SRem => v2 <> DVALUE_Base DVALUE_Poison | _ => True end) ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_safe (fun v => dvalue_has_dtyp v dt) (@eval_iop PaV iop v1 v2).
  Proof.
    intros Hint Hnp Hv1 Hv2.
    destruct (is_int_dtyp_inv dt Hint) as [sz ->].
    destruct (dvalue_has_dtyp_I_inv v1 sz Hv1) as [-> | [i1 ->]];
      destruct (dvalue_has_dtyp_I_inv v2 sz Hv2) as [-> | [i2 ->]];
      cbn [eval_iop]; apply eou_safe_fmap.
    - (* Poison, Poison *)
      unfold eval_iop_integer_base; destruct (iop_is_div iop) eqn:Ediv; cbn;
        [destruct iop; try discriminate Ediv; try (exfalso; apply Hnp; reflexivity); exact I
        | apply dvalue_has_dtyp_Poison].
    - (* Poison, I *)
      destruct iop; cbn;
        try (destruct (Z.eq_dec (@Integers.signed sz i2) (-1)%Z); cbn;
             [exact I | apply dvalue_has_dtyp_Poison]);
        apply dvalue_has_dtyp_Poison.
    - (* I, Poison *)
      unfold eval_iop_integer_base; destruct (iop_is_div iop); cbn;
        [exact I | apply dvalue_has_dtyp_Poison].
    - (* I, I *)
      exact (eval_iop_integer_base_I_I iop sz sz i1 i2 Logic.eq_refl).
  Qed.

  Lemma eval_iop_ret_imp (iop : ibinop) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_int_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_ret_imp (fun v => dvalue_has_dtyp v dt) (@eval_iop PaV iop v1 v2).
  Proof.
    intros Hint Hv1 Hv2.
    destruct (is_int_dtyp_inv dt Hint) as [sz ->].
    destruct (dvalue_has_dtyp_I_inv v1 sz Hv1) as [-> | [i1 ->]];
      destruct (dvalue_has_dtyp_I_inv v2 sz Hv2) as [-> | [i2 ->]];
      cbn [eval_iop]; apply eou_ret_imp_fmap.
    - unfold eval_iop_integer_base; destruct (iop_is_div iop); cbn;
        [exact I | apply dvalue_has_dtyp_Poison].
    - destruct iop; cbn;
        try (destruct (Z.eq_dec (@Integers.signed sz i2) (-1)%Z); cbn;
             [exact I | apply dvalue_has_dtyp_Poison]);
        apply dvalue_has_dtyp_Poison.
    - unfold eval_iop_integer_base; destruct (iop_is_div iop); cbn;
        [exact I | apply dvalue_has_dtyp_Poison].
    - apply eou_safe_to_ret_imp, (eval_iop_integer_base_I_I iop sz sz i1 i2 Logic.eq_refl).
  Qed.

  Lemma eval_int_icmp_bit_safe
    (samesign : bool) (cmp : icmp) (sz : positive) (x y : @bit_int sz) :
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_int_icmp PaV (@bit_int sz) _ samesign cmp x y).
  Proof.
    destruct cmp; unfold eval_int_icmp, dvp;
      cbn [mdtyp_of_int VIntVMemInt VInt_Bounded];
      try (destruct (dtyp_base_eq_dec (DTYPE_I sz) DTYPE_Iptr); [discriminate |]);
      rewrite bind_EOU_ret; cbn [eou_safe];
      repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
  Qed.

  Lemma eval_int_icmp_any_ret_imp
    {Int : Type} `{VMI : VMemInt Int}
    (samesign : bool) (cmp : icmp) (x y : Int) :
    eou_ret_imp
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_int_icmp PaV Int VMI samesign cmp x y).
  Proof.
    destruct cmp; unfold eval_int_icmp, dvp;
      try (destruct (dtyp_base_eq_dec (@mdtyp_of_int Int VMI) DTYPE_Iptr); [exact I |]);
      rewrite bind_EOU_ret; cbn [eou_ret_imp];
      repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
  Qed.

  Lemma eval_int_icmp_ptr_safe
    {Int : Type} `{VMI : VMemInt Int}
    (samesign : bool) (cmp : icmp) (x y : Int) :
    is_ptr_safe_icmp cmp = true ->
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_int_icmp PaV Int VMI samesign cmp x y).
  Proof.
    intros Hsafe; destruct cmp; try discriminate Hsafe;
      unfold eval_int_icmp, dvp; rewrite bind_EOU_ret; cbn [eou_safe];
      repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
  Qed.

  Lemma eval_icmp_base_I_I
    (samesign : bool) (cmp : icmp) (sz1 sz2 : positive)
    (i1 : @bit_int sz1) (i2 : @bit_int sz2) (Hsz : sz1 = sz2) :
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_icmp_base PaV samesign cmp (@DVALUE_I PaV sz1 i1) (@DVALUE_I PaV sz2 i2)).
  Proof.
    unfold eval_icmp_base.
    destruct (Pos.eq_dec sz1 sz2) as [Heq | Hne].
    - clear Hsz; subst; cbn [eq_rect eq_rect_r eq_sym].
      apply eval_int_icmp_bit_safe.
    - contradiction (Hne Hsz).
  Qed.

  Lemma eval_icmp_safe
    (samesign : bool) (cmp : icmp) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_safe_icmp_ty cmp dt = true ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_safe
      (fun v => dvalue_has_dtyp v (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_icmp PaV samesign cmp v1 v2).
  Proof.
    intros Hsafe Hv1 Hv2; unfold is_safe_icmp_ty in Hsafe.
    destruct (is_int_dtyp dt) eqn:Eint.
    - destruct (is_int_dtyp_inv dt Eint) as [sz ->].
      destruct (dvalue_has_dtyp_I_inv v1 sz Hv1) as [-> | [i1 ->]];
        destruct (dvalue_has_dtyp_I_inv v2 sz Hv2) as [-> | [i2 ->]];
        cbn [eval_icmp]; apply eou_safe_fmap.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + exact (eval_icmp_base_I_I samesign cmp sz sz i1 i2 Logic.eq_refl).
    - destruct (is_ptr_dtyp dt) eqn:Eptr; [| discriminate Hsafe].
      rewrite (is_ptr_dtyp_eq dt Eptr) in Hv1, Hv2.
      destruct (dvalue_has_dtyp_Ptr_inv v1 Hv1) as [-> | [p1 ->]];
        destruct (dvalue_has_dtyp_Ptr_inv v2 Hv2) as [-> | [p2 ->]];
        cbn [eval_icmp]; apply eou_safe_fmap.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + unfold eval_icmp_base; apply eval_int_icmp_ptr_safe, Hsafe.
  Qed.

  Lemma eval_icmp_ret_imp
    (samesign : bool) (cmp : icmp) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    (is_int_dtyp dt || is_ptr_dtyp dt) = true ->
    dvalue_has_dtyp v1 dt ->
    eou_ret_imp
      (fun v => dvalue_has_dtyp v (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_icmp PaV samesign cmp v1 v2).
  Proof.
    intros Hty Hv1.
    apply orb_true_iff in Hty as [Eint | Eptr].
    - destruct (is_int_dtyp_inv dt Eint) as [sz ->].
      destruct (dvalue_has_dtyp_I_inv v1 sz Hv1) as [-> | [i1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_icmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          unfold eval_icmp_base; cbn [is_icmp_operand];
          try exact I; apply dvalue_has_dtyp_Poison.
      + cbn [eval_icmp]; apply eou_ret_imp_vec_poison_l.
        intros y; destruct y; unfold eval_icmp_base;
          cbn [is_icmp_operand eou_ret_imp ExtLib.Structures.Monad.ret EOU_monad];
          first [reflexivity | exact I].
      + cbn [eval_icmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          unfold eval_icmp_base; cbn [is_icmp_operand];
          try exact I; try apply dvalue_has_dtyp_Poison.
        destruct (Pos.eq_dec sz sz2) as [Heq | _]; [| exact I].
        subst sz2; cbn [eq_rect eq_rect_r eq_sym].
        apply eou_safe_to_ret_imp, eval_int_icmp_bit_safe.
    - rewrite (is_ptr_dtyp_eq dt Eptr) in Hv1.
      destruct (dvalue_has_dtyp_Ptr_inv v1 Hv1) as [-> | [p1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_icmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          unfold eval_icmp_base; cbn [is_icmp_operand];
          try exact I; apply dvalue_has_dtyp_Poison.
      + cbn [eval_icmp]; apply eou_ret_imp_vec_poison_l.
        intros y; destruct y; unfold eval_icmp_base;
          cbn [is_icmp_operand eou_ret_imp ExtLib.Structures.Monad.ret EOU_monad];
          first [reflexivity | exact I].
      + cbn [eval_icmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          unfold eval_icmp_base; cbn [is_icmp_operand];
          try exact I; try apply dvalue_has_dtyp_Poison.
        apply eval_int_icmp_any_ret_imp.
  Qed.

  Lemma eval_fop_safe (fop : fbinop) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    is_safe_fbinop fop = true ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_safe (fun v => dvalue_has_dtyp v dt) (@eval_fop PaV fop v1 v2).
  Proof.
    intros Hfp Hsf Hv1 Hv2.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        destruct (dvalue_has_dtyp_Float_inv v2 Hv2) as [-> | [f2 ->]];
        cbn [eval_fop]; apply eou_safe_fmap.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fop_base]; destruct (fop_is_div fop); cbn;
          [exact I | apply dvalue_has_dtyp_Poison].
      + destruct fop; try discriminate Hsf; cbn; apply dvalue_has_dtyp_Float.
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        destruct (dvalue_has_dtyp_Double_inv v2 Hv2) as [-> | [d2 ->]];
        cbn [eval_fop]; apply eou_safe_fmap.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fop_base]; destruct (fop_is_div fop); cbn;
          [exact I | apply dvalue_has_dtyp_Poison].
      + destruct fop; try discriminate Hsf; cbn; apply dvalue_has_dtyp_Double.
  Qed.

  Lemma eval_fop_ret_imp (fop : fbinop) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    eou_ret_imp (fun v => dvalue_has_dtyp v dt) (@eval_fop PaV fop v1 v2).
  Proof.
    intros Hfp Hv1.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_fop]; apply eou_ret_imp_fmap; cbn; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fop]; apply eou_ret_imp_vec_poison_l; intros y; destruct y; cbn; reflexivity.
      + cbn [eval_fop]; apply eou_ret_imp_fmap.
        destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fop_base]; try exact I.
        * destruct fop; cbn; try exact I; apply dvalue_has_dtyp_Float.
        * destruct (fop_is_div fop); cbn; [exact I | apply dvalue_has_dtyp_Poison].
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_fop]; apply eou_ret_imp_fmap; cbn; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fop]; apply eou_ret_imp_vec_poison_l; intros y; destruct y; cbn; reflexivity.
      + cbn [eval_fop]; apply eou_ret_imp_fmap.
        destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fop_base]; try exact I.
        * destruct fop; cbn; try exact I; apply dvalue_has_dtyp_Double.
        * destruct (fop_is_div fop); cbn; [exact I | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma eval_fneg_safe (dt : dtyp) (v1 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    eou_safe (fun v => dvalue_has_dtyp v dt) (@eval_fneg PaV v1).
  Proof.
    intros Hfp Hv1.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        cbn; [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Float].
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        cbn; [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Double].
  Qed.

  Lemma eval_fcmp_safe (cmp : fcmp) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_safe
      (fun v => dvalue_has_dtyp v (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_fcmp PaV cmp v1 v2).
  Proof.
    intros Hfp Hv1 Hv2.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        destruct (dvalue_has_dtyp_Float_inv v2 Hv2) as [-> | [f2 ->]];
        cbn [eval_fcmp]; apply eou_safe_fmap; cbn [eval_fcmp_base];
        try apply dvalue_has_dtyp_Poison.
      unfold float_cmp;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        apply dvalue_has_dtyp_I.
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        destruct (dvalue_has_dtyp_Double_inv v2 Hv2) as [-> | [d2 ->]];
        cbn [eval_fcmp]; apply eou_safe_fmap; cbn [eval_fcmp_base];
        try apply dvalue_has_dtyp_Poison.
      unfold double_cmp;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        apply dvalue_has_dtyp_I.
  Qed.

  Lemma eval_fcmp_ret_imp (cmp : fcmp) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    eou_ret_imp
      (fun v => dvalue_has_dtyp v (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_fcmp PaV cmp v1 v2).
  Proof.
    intros Hfp Hv1.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_fcmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fcmp_base]; try exact I; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fcmp]; apply eou_ret_imp_vec_poison_l.
        intros y; destruct y; cbn [eval_fcmp_base eou_ret_imp ExtLib.Structures.Monad.ret EOU_monad];
          first [reflexivity | exact I].
      + cbn [eval_fcmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fcmp_base]; try exact I; try apply dvalue_has_dtyp_Poison.
        unfold float_cmp;
          repeat match goal with |- context [if ?b then _ else _] => destruct b end;
          apply dvalue_has_dtyp_I.
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_fcmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fcmp_base]; try exact I; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fcmp]; apply eou_ret_imp_vec_poison_l.
        intros y; destruct y; cbn [eval_fcmp_base eou_ret_imp ExtLib.Structures.Monad.ret EOU_monad];
          first [reflexivity | exact I].
      + cbn [eval_fcmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fcmp_base]; try exact I; try apply dvalue_has_dtyp_Poison.
        unfold double_cmp;
          repeat match goal with |- context [if ?b then _ else _] => destruct b end;
          apply dvalue_has_dtyp_I.
  Qed.

  Lemma convert_pure_safe
    (pc : pure_conversion) (dt_from dt_to : dtyp) (v1 : @dvalue PaV) :
    is_safe_pure_conv pc dt_from dt_to = true ->
    dvalue_has_dtyp v1 dt_from ->
    eou_safe (fun v => dvalue_has_dtyp v dt_to) (@convert_pure PaV pc dt_from v1 dt_to).
  Proof.
    intros Hsafe Hv1.
    destruct pc as [nuw nsw | nneg | | flags | flags | nneg | | |];
      cbn [is_safe_pure_conv] in Hsafe.
    - (* Trunc *)
      destruct dt_from as [[sz1 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct dt_to as [[sz2 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp.
      + cbn; apply dvalue_has_dtyp_Poison.
      + rewrite Pos.eqb_refl, Hsafe; cbn [andb].
        destruct (_ || _); cbn; [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
    - (* Zext *)
      destruct dt_from as [[sz1 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct dt_to as [[sz2 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp.
      + cbn; apply dvalue_has_dtyp_Poison.
      + rewrite Pos.eqb_refl, Hsafe; cbn [andb].
        destruct (_ && _); cbn; [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
    - (* Sext *)
      destruct dt_from as [[sz1 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct dt_to as [[sz2 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp.
      + cbn; apply dvalue_has_dtyp_Poison.
      + rewrite Pos.eqb_refl, Hsafe; cbn; apply dvalue_has_dtyp_I.
    - (* Fptrunc *)
      destruct dt_from as [[| | | | fp1 | | | | | |] | |]; try discriminate Hsafe.
      destruct fp1; try discriminate Hsafe.
      destruct dt_to as [[| | | | fp2 | | | | | |] | |]; try discriminate Hsafe.
      destruct fp2; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp; cbn;
        [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Float].
    - (* Fpext *)
      destruct dt_from as [[| | | | fp1 | | | | | |] | |]; try discriminate Hsafe.
      destruct fp1; try discriminate Hsafe.
      destruct dt_to as [[| | | | fp2 | | | | | |] | |]; try discriminate Hsafe.
      destruct fp2; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp; cbn;
        [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Double].
    - (* Uitofp *)
      apply andb_true_iff in Hsafe as [Hint Hfp].
      destruct (is_int_dtyp_inv dt_from Hint) as [sz1 ->].
      destruct (is_fp_dtyp_inv dt_to Hfp) as [-> | ->];
        destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp; rewrite ?Pos.eqb_refl;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        cbn; first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Float | apply dvalue_has_dtyp_Double].
    - (* Sitofp *)
      apply andb_true_iff in Hsafe as [Hint Hfp].
      destruct (is_int_dtyp_inv dt_from Hint) as [sz1 ->].
      destruct (is_fp_dtyp_inv dt_to Hfp) as [-> | ->];
        destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp; rewrite ?Pos.eqb_refl;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        cbn; first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Float | apply dvalue_has_dtyp_Double].
    - (* Fptoui *)
      apply andb_true_iff in Hsafe as [Hfp Hint].
      destruct (is_int_dtyp_inv dt_to Hint) as [sz2 ->].
      destruct (is_fp_dtyp_inv dt_from Hfp) as [-> | ->].
      + destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
          cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
          unfold convert_pure_base, dvp; [cbn; apply dvalue_has_dtyp_Poison |].
        destruct (ZofB_range _ _ _ _ _); cbn;
          [apply dvalue_has_dtyp_I | apply dvalue_has_dtyp_Poison].
      + destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
          cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
          unfold convert_pure_base, dvp; [cbn; apply dvalue_has_dtyp_Poison |].
        destruct (ZofB_range _ _ _ _ _); cbn;
          [apply dvalue_has_dtyp_I | apply dvalue_has_dtyp_Poison].
    - (* Fptosi *)
      apply andb_true_iff in Hsafe as [Hfp Hint].
      destruct (is_int_dtyp_inv dt_to Hint) as [sz2 ->].
      destruct (is_fp_dtyp_inv dt_from Hfp) as [-> | ->].
      + destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
          cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
          unfold convert_pure_base, dvp; [cbn; apply dvalue_has_dtyp_Poison |].
        destruct (ZofB_range _ _ _ _ _); cbn;
          [apply dvalue_has_dtyp_I | apply dvalue_has_dtyp_Poison].
      + destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
          cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
          unfold convert_pure_base, dvp; [cbn; apply dvalue_has_dtyp_Poison |].
        destruct (ZofB_range _ _ _ _ _); cbn;
          [apply dvalue_has_dtyp_I | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma convert_pure_ret_imp
    (pc : pure_conversion) (dt_from dt_to : dtyp) (v1 : @dvalue PaV) :
    is_scalar_dtyp dt_to = true ->
    eou_ret_imp (fun v => dvalue_has_dtyp v dt_to) (@convert_pure PaV pc dt_from v1 dt_to).
  Proof.
    intros Hsc.
    destruct dt_to as [dtb2 | |]; [| discriminate Hsc | discriminate Hsc].
    destruct dt_from as [dtb1 | | [|] sz1 [| |]];
      try (destruct v1 as [[] | | [|] ?]; exact I).
    destruct v1 as [db1 | | [|] elts1]; try exact I.
    cbn [convert_pure get_base_conversion_type]; apply eou_ret_imp_fmap.
    destruct pc as [nuw nsw | nneg | | flags | flags | nneg | | |];
      unfold convert_pure_base, dvp;
      destruct dtb1 as [sz1 | | | | fp1 | | | | | | bsz1];
      try (destruct fp1);
      destruct db1 as [p1 | sz_from i1 | ip1 | d1 | f1 | | | bsz_v bv1];
      destruct dtb2 as [sz2 | | | | fp2 | | | | | | bsz2];
      try (destruct fp2);
      try exact I;
      try apply dvalue_has_dtyp_Poison;
      repeat match goal with
             | |- context [ZofB_range ?a ?b ?c ?d ?e] =>
                 destruct (ZofB_range a b c d e)
             | |- context [if ?b then _ else _] => destruct b
             end;
      cbn [eou_ret_imp];
      first [ exact I
            | apply dvalue_has_dtyp_Poison
            | apply dvalue_has_dtyp_I
            | apply dvalue_has_dtyp_Float
            | apply dvalue_has_dtyp_Double ].
  Qed.

  Lemma eval_select_safe_P (P : @dvalue PaV -> Prop)
    (HP_pois : P (DVALUE_Base DVALUE_Poison))
    (vc v1 v2 : @dvalue PaV) (dt1 : dtyp) :
    dvalue_has_dtyp vc (DTYPE_Base (DTYPE_I 1%positive)) ->
    P v1 ->
    P v2 ->
    eou_safe P (@eval_select PaV vc dt1 v1 v2).
  Proof.
    intros Hvc Hv1 Hv2.
    destruct (dvalue_has_dtyp_I_inv vc 1%positive Hvc) as [-> | [ic ->]];
      cbn [eval_select eval_select_base_dvalue].
    - exact HP_pois.
    - destruct (@Integers.unsigned 1%positive ic =? 1)%Z; cbn; [exact Hv1 | exact Hv2].
  Qed.

  Lemma eval_gep_ret_imp
    (flags : gep_flags) (t : dtyp) (vptr : @dvalue PaV) (vs : list (@dvalue PaV)) :
    eou_ret_imp
      (fun v => dvalue_has_dtyp v (DTYPE_Base DTYPE_Pointer))
      (@eval_gep PaV flags t vptr vs).
  Proof.
    destruct vptr as [db | |]; try exact I.
    destruct db as [p | sz i | ip | d | f | | | bsz bv]; cbn [eval_gep];
      try exact I; [| apply dvalue_has_dtyp_Poison].
    unfold catch_pois.
    destruct (handle_gep_ptr flags t p vs) as [s | s | s | [p' |]]; cbn;
      try exact I; [apply dvalue_has_dtyp_Ptr | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma value_metadata_range_scalar_typ
    (ranges : option (list (int_syntax * int_syntax)))
    (dt : dtyp) (v : @dvalue PaV) :
    is_scalar_dtyp dt = true ->
    dvalue_has_dtyp v dt ->
    dvalue_has_dtyp (@value_metadata_range PaV ranges v) dt.
  Proof.
    intros Hsc Hv.
    destruct (dvalue_has_dtyp_scalar_base_inv v dt Hsc Hv) as [db [-> _]].
    destruct ranges as [rs |]; [| exact Hv].
    cbn [value_metadata_range value_metadata_range_base].
    destruct db; try exact Hv.
    destruct (in_metadata_ranges _ _ _); [exact Hv | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma value_attrs_poison_scalar_typ
    (attrs : list param_attr) (dt : dtyp) (v : @dvalue PaV) :
    is_scalar_dtyp dt = true ->
    dvalue_has_dtyp v dt ->
    dvalue_has_dtyp (@value_attrs_poison PaV attrs v) dt.
  Proof.
    intros Hsc Hv.
    assert (Hnn : dvalue_has_dtyp (@value_attr_nonnull PaV attrs v) dt).
    { unfold value_attr_nonnull; destruct v as [db | |]; [| exact Hv | exact Hv].
      destruct db; try exact Hv.
      destruct (_ && _); [apply dvalue_has_dtyp_Poison | exact Hv]. }
    assert (Hal : dvalue_has_dtyp (@value_attr_align PaV attrs (@value_attr_nonnull PaV attrs v)) dt).
    { unfold value_attr_align.
      destruct (@value_attr_nonnull PaV attrs v) as [db | |]; try exact Hnn.
      destruct db; try exact Hnn.
      destruct (find_option attr_align attrs); [| exact Hnn].
      destruct (ptr_aligned_to _ _); [exact Hnn | apply dvalue_has_dtyp_Poison]. }
    assert (Hrg : dvalue_has_dtyp
                    (@value_attr_range PaV attrs
                       (@value_attr_align PaV attrs (@value_attr_nonnull PaV attrs v))) dt).
    { unfold value_attr_range.
      exact (value_metadata_range_scalar_typ _ dt _ Hsc Hal). }
    unfold value_attrs_poison, value_attr_nofpclass.
    set (u := @value_attr_range PaV attrs
                (@value_attr_align PaV attrs (@value_attr_nonnull PaV attrs v))) in *.
    destruct (find_option attr_nofpclass attrs) as [mask |]; [| exact Hrg].
    destruct (dvalue_has_dtyp_scalar_base_inv u dt Hsc Hrg) as [db [-> _]].
    cbn [value_nofpclass].
    destruct (fp_class db); [| exact Hrg].
    destruct (Z.land mask _ =? 0)%Z; [exact Hrg | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma apply_value_attrs_scalar_typ
    (attrs : list param_attr) (msg : string) (dt : dtyp) (v : @dvalue PaV) :
    eou_ret_imp
      (fun v' => is_scalar_dtyp dt = true -> dvalue_has_dtyp v dt -> dvalue_has_dtyp v' dt)
      (@apply_value_attrs PaV attrs msg v).
  Proof.
    unfold apply_value_attrs.
    destruct (_ && _); cbn; [exact I | apply value_attrs_poison_scalar_typ].
  Qed.

  (** * 6. Environment Relations, [withCall] Equations, & [cfg_local_sim] Combinators *)

  (** ** Live-Variable Agreement & Forward Type-Environment Soundness *)

  Definition env_agree_on
    (live : list raw_id) (env1 env2 : @local_env PaV) : Prop :=
    forall x : raw_id,
      in_raw_ids x live = true ->
      Maps.lookup x env1 = Maps.lookup x env2.

  Lemma env_agree_on_refl (live : list raw_id) (env : @local_env PaV) :
    env_agree_on live env env.
  Proof. intros _ _; reflexivity. Qed.

  Lemma env_agree_on_eq (live : list raw_id) (env1 env2 : @local_env PaV) :
    env1 = env2 -> env_agree_on live env1 env2.
  Proof. intros ->; apply env_agree_on_refl. Qed.

  Lemma env_agree_on_subset
    (s1 s2 : list raw_id) (env1 env2 : @local_env PaV) :
    (forall x, in_raw_ids x s1 = true -> in_raw_ids x s2 = true) ->
    env_agree_on s2 env1 env2 ->
    env_agree_on s1 env1 env2.
  Proof.
    intros Hsub Hagree x Hx; apply Hagree, Hsub, Hx.
  Qed.

  Lemma env_agree_on_in
    (xs : list raw_id) (env1 env2 : @local_env PaV) (x : raw_id) :
    env_agree_on xs env1 env2 ->
    In x xs ->
    Maps.lookup x env1 = Maps.lookup x env2.
  Proof.
    intros Hagree Hx; apply Hagree, in_raw_ids_spec, Hx.
  Qed.

  Lemma env_agree_on_app_l
    (l1 l2 : list raw_id) (env1 env2 : @local_env PaV) :
    env_agree_on (l1 ++ l2) env1 env2 ->
    env_agree_on l1 env1 env2.
  Proof.
    apply env_agree_on_subset; intros x Hx.
    apply in_raw_ids_spec; apply in_raw_ids_spec in Hx.
    apply in_or_app; left; exact Hx.
  Qed.

  Lemma env_agree_on_app_r
    (l1 l2 : list raw_id) (env1 env2 : @local_env PaV) :
    env_agree_on (l1 ++ l2) env1 env2 ->
    env_agree_on l2 env1 env2.
  Proof.
    apply env_agree_on_subset; intros x Hx.
    apply in_raw_ids_spec; apply in_raw_ids_spec in Hx.
    apply in_or_app; right; exact Hx.
  Qed.

  Lemma env_agree_on_add_raw_ids_split
    (xs s : list raw_id) (env1 env2 : @local_env PaV) :
    env_agree_on (add_raw_ids xs s) env1 env2 ->
    env_agree_on xs env1 env2 /\ env_agree_on s env1 env2.
  Proof.
    intros H; split.
    - intros x Hx; apply H, in_add_raw_ids; left; apply in_raw_ids_spec, Hx.
    - intros x Hx; apply H, in_add_raw_ids; right; exact Hx.
  Qed.

  Lemma env_agree_on_add_both
    (live : list raw_id) (x : raw_id) (v : @dvalue PaV)
    (env1 env2 : @local_env PaV) :
    env_agree_on (remove_raw_id x live) env1 env2 ->
    env_agree_on live (Maps.add x v env1) (Maps.add x v env2).
  Proof.
    intros Hagree y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - rewrite !lookup_add_eq; reflexivity.
    - rewrite !lookup_add_neq by exact Hne.
      apply Hagree, in_remove_raw_id.
      split; [congruence | exact Hy].
  Qed.

  Lemma env_agree_on_add_both_same
    (live : list raw_id) (x : raw_id) (v : @dvalue PaV)
    (env1 env2 : @local_env PaV) :
    env_agree_on live env1 env2 ->
    env_agree_on live (Maps.add x v env1) (Maps.add x v env2).
  Proof.
    intros Hagree; apply env_agree_on_add_both.
    eapply env_agree_on_subset; [| exact Hagree].
    intros y Hy; apply in_remove_raw_id in Hy; exact (snd Hy).
  Qed.

  Lemma env_agree_on_add_dead_l
    (live : list raw_id) (x : raw_id) (v : @dvalue PaV)
    (env1 env2 : @local_env PaV) :
    in_raw_ids x live = false ->
    env_agree_on live env1 env2 ->
    env_agree_on live (Maps.add x v env1) env2.
  Proof.
    intros Hdead Hagree y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - congruence.
    - rewrite lookup_add_neq by exact Hne; apply Hagree, Hy.
  Qed.

  Definition val_matches_oty (oty : ty_info) (v : @dvalue PaV) : Prop :=
    match oty with
    | None => True
    | Some dt => is_scalar_dtyp dt = true /\ dvalue_has_dtyp v dt
    end.

  Lemma val_matches_normalize_oty (dt : dtyp) (v : @dvalue PaV) :
    (is_scalar_dtyp dt = true -> dvalue_has_dtyp v dt) ->
    val_matches_oty (normalize_oty (Some dt)) v.
  Proof.
    intros H; cbn [normalize_oty].
    destruct (is_scalar_dtyp dt) eqn:Esc; cbn [val_matches_oty].
    - split; [reflexivity | apply H, Logic.eq_refl].
    - exact I.
  Qed.

  Definition tenv_sound (te : ty_env) (env : @local_env PaV) : Prop :=
    forall (x : local_id) (oty : ty_info),
      lookup_ty x te = Some oty ->
      exists v : @dvalue PaV,
        Maps.lookup x env = Some v /\ val_matches_oty oty v.

  Lemma tenv_sound_nil (env : @local_env PaV) :
    tenv_sound [] env.
  Proof. intros _ _ H; discriminate H. Qed.

  Lemma tenv_sound_remove_ty_same
    (x : local_id) (te : ty_env) (env : @local_env PaV) :
    tenv_sound te env ->
    tenv_sound (remove_ty x te) env.
  Proof.
    intros Hte z oty Hlk.
    destruct (RawIDOrd.eq_dec z x) as [-> | Hne].
    - rewrite lookup_remove_ty_eq in Hlk; discriminate Hlk.
    - rewrite (lookup_remove_ty_neq x z te Hne) in Hlk; apply Hte, Hlk.
  Qed.

  Lemma tenv_sound_remove_ty_add
    (x : local_id) (v : @dvalue PaV) (te : ty_env) (env : @local_env PaV) :
    tenv_sound te env ->
    tenv_sound (remove_ty x te) (Maps.add x v env).
  Proof.
    intros Hte z oty Hlk.
    destruct (RawIDOrd.eq_dec x z) as [<- | Hne].
    - rewrite lookup_remove_ty_eq in Hlk; discriminate Hlk.
    - rewrite lookup_add_neq by exact Hne.
      rewrite (lookup_remove_ty_neq x z te) in Hlk by congruence.
      apply Hte, Hlk.
  Qed.

  Lemma tenv_sound_set_ty
    (x : local_id) (oty : ty_info) (v : @dvalue PaV)
    (te : ty_env) (env : @local_env PaV) :
    val_matches_oty (normalize_oty oty) v ->
    tenv_sound te env ->
    tenv_sound (set_ty x oty te) (Maps.add x v env).
  Proof.
    intros Hval Hte z oty' Hlk.
    destruct (RawIDOrd.eq_dec x z) as [<- | Hne].
    - rewrite lookup_set_ty_eq in Hlk; inversion Hlk; subst oty'.
      exists v; split; [apply lookup_add_eq | exact Hval].
    - rewrite lookup_add_neq by exact Hne.
      rewrite (lookup_set_ty_neq x z oty te) in Hlk by congruence.
      apply Hte, Hlk.
  Qed.

  Lemma tenv_sound_subsumes
    (te_gen te_spec : ty_env) (env : @local_env PaV) :
    tenv_subsumes te_gen te_spec = true ->
    tenv_sound te_spec env ->
    tenv_sound te_gen env.
  Proof.
    unfold tenv_subsumes; rewrite forallb_forall.
    intros Hsub Hspec x oty_g Hlk_g.
    apply lookup_ty_in in Hlk_g.
    specialize (Hsub (x, oty_g) Hlk_g).
    apply andb_true_iff in Hsub as [Hval Hsub].
    destruct (lookup_ty x te_spec) as [oty_s |] eqn:Elk_s; [| discriminate Hsub].
    destruct (Hspec x oty_s Elk_s) as [v [Henv Hv]].
    exists v; split; [exact Henv |].
    destruct oty_g as [dt_g |]; [| exact I].
    destruct oty_s as [dt_s |]; [| discriminate Hsub].
    cbn [oty_subsumes] in Hsub.
    apply andb_true_iff in Hsub as [Hsc Heq].
    apply dtyp_eqb_eq in Heq; subst dt_s.
    exact Hv.
  Qed.

  Lemma init_tenv_sound (fargs : list local_id) (env : @local_env PaV) :
    (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
    tenv_sound (init_tenv fargs) env.
  Proof.
    induction fargs as [| a rest IH]; intros Henv.
    - apply tenv_sound_nil.
    - intros z oty Hlk; cbn [init_tenv] in Hlk.
      destruct (RawIDOrd.eq_dec z a) as [-> | Hne].
      + rewrite lookup_set_ty_eq in Hlk; inversion Hlk; subst oty.
        destruct (Henv a (or_introl Logic.eq_refl)) as [v Hv].
        exists v; split; [exact Hv | exact I].
      + rewrite (lookup_set_ty_neq a z None _ Hne) in Hlk.
        apply (IH (fun x Hx => Henv x (or_intror Hx)) z oty Hlk).
  Qed.

  (** ** [withCall] Equations & Left-Only Failure-Free Evaluation *)

  Lemma withCall_ret {R : Type} (x : R) :
    @withCall PaV R (Ret x) ≅ Ret x.
  Proof.
    unfold withCall; apply translate_ret.
  Qed.

  Lemma withCall_bind {R S : Type}
    (t : @MCFGtop PaV R) (k : R -> @MCFGtop PaV S) :
    @withCall PaV S (ITree.bind t k) ≅
    ITree.bind (@withCall PaV R t) (fun x => @withCall PaV S (k x)).
  Proof.
    unfold withCall; apply translate_bind.
  Qed.

  Lemma withCall_lread_bind {R : Type} (x : local_id)
    (k : @dvalue PaV -> @CFGtop PaV R) :
    ITree.bind (@withCall PaV (@dvalue PaV) (lread x)) k ≅
    ITree.bind (ITree.trigger (LocalRead x)) k.
  Proof.
    unfold withCall, lread, ITree.trigger.
    rewrite unfold_translate;
      cbn [observe translateF subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
    rewrite !Eqit.bind_vis.
    pstep; red; cbn [observe]; constructor; intros v; left.
    rewrite translate_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma withCall_lread (x : local_id) :
    @withCall PaV (@dvalue PaV) (lread x) ≅
    ITree.bind (ITree.trigger (LocalRead x)) (fun v => Ret v).
  Proof.
    rewrite <- (Eqit.bind_ret_r (@withCall PaV (@dvalue PaV) (lread x))).
    apply withCall_lread_bind.
  Qed.

  (** [left_evals_to P env1 t1] means that [t1] executes purely via defined
      local reads in [env1] (leaving [env1] untouched) or cuts [ThrowUB], and
      if it returns [v], [P v] holds. *)
  Definition left_evals_to {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (t1 : @CFGtop PaV R) : Prop :=
    forall env2 : @local_env PaV,
      cfg_local_sim
        (fun e1' e2' r1 _ => e1' = env1 /\ e2' = env2 /\ P r1)
        env1 env2 t1 (Ret tt).

  Lemma left_evals_to_obs_eq {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (t1 t1' : @CFGtop PaV R) :
    t1 ≅ t1' ->
    left_evals_to P env1 t1 ->
    left_evals_to P env1 t1'.
  Proof.
    intros Heq H env2.
    eapply cfg_local_sim_obs_eq; [exact Heq | reflexivity | apply H].
  Qed.

  Lemma left_evals_to_ret {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (x : R) :
    P x ->
    left_evals_to P env1 (Ret x).
  Proof.
    intros HP env2; apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | exact HP]].
  Qed.

  Lemma left_evals_to_withCall_ret {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (x : R) :
    P x ->
    left_evals_to P env1 (@withCall PaV R (Ret x)).
  Proof.
    intros HP; eapply left_evals_to_obs_eq; [symmetry; apply withCall_ret |].
    apply left_evals_to_ret, HP.
  Qed.

  Lemma left_evals_to_weaken {R : Type}
    (P Q : R -> Prop) (env1 : @local_env PaV) (t1 : @CFGtop PaV R) :
    (forall x, P x -> Q x) ->
    left_evals_to P env1 t1 ->
    left_evals_to Q env1 t1.
  Proof.
    intros HPQ H env2.
    eapply cfg_local_sim_weaken; [| apply H].
    intros ? ? r1 _ (-> & -> & Hr); split; [reflexivity | split; [reflexivity | apply HPQ, Hr]].
  Qed.

  Lemma left_evals_to_bind {R S : Type}
    (P : R -> Prop) (Q : S -> Prop) (env1 : @local_env PaV)
    (t1 : @CFGtop PaV R) (k1 : R -> @CFGtop PaV S) :
    left_evals_to P env1 t1 ->
    (forall x, P x -> left_evals_to Q env1 (k1 x)) ->
    left_evals_to Q env1 (ITree.bind t1 k1).
  Proof.
    intros Ht Hk env2.
    eapply cfg_local_sim_obs_eq;
      [reflexivity | apply (Eqit.bind_ret_l tt (fun _ : unit => Ret tt)) |].
    eapply cfg_local_sim_bind; [apply Ht |].
    intros ? ? x _ (-> & -> & Hx); apply Hk, Hx.
  Qed.

  Lemma left_evals_to_withCall_bind {R S : Type}
    (P : R -> Prop) (Q : S -> Prop) (env1 : @local_env PaV)
    (t1 : @MCFGtop PaV R) (k1 : R -> @MCFGtop PaV S) :
    left_evals_to P env1 (@withCall PaV R t1) ->
    (forall x, P x -> left_evals_to Q env1 (@withCall PaV S (k1 x))) ->
    left_evals_to Q env1 (@withCall PaV S (ITree.bind t1 k1)).
  Proof.
    intros Ht Hk.
    eapply left_evals_to_obs_eq; [symmetry; apply withCall_bind |].
    eapply left_evals_to_bind; [exact Ht | exact Hk].
  Qed.

  Lemma left_evals_to_withCall_lread
    (P : @dvalue PaV -> Prop) (env1 : @local_env PaV)
    (x : local_id) (v : @dvalue PaV) :
    Maps.lookup x env1 = Some v ->
    P v ->
    left_evals_to P env1 (@withCall PaV (@dvalue PaV) (lread x)).
  Proof.
    intros Hlk HP env2.
    pstep; eapply CLS_ReadL.
    - apply withCall_lread.
    - exact Hlk.
    - left; apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | exact HP]].
  Qed.

  Lemma left_evals_to_withCall_EOU {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (m : EOU R) :
    eou_safe P m ->
    left_evals_to P env1 (@withCall PaV R (EOU_to_itree m)).
  Proof.
    intros Hm env2; destruct m as [s | s | s | x]; cbn in Hm; try contradiction; cbn [EOU_to_itree].
    - unfold withCall, raiseUB, trigger_cast, ITree.trigger.
      pstep; apply CLS_Step; unfold cls_step_body.
      repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
    - eapply cfg_local_sim_obs_eq; [symmetry; apply withCall_ret | reflexivity |].
      apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | exact Hm]].
  Qed.

  Lemma left_evals_to_bind_sim {R1 S1 S2 : Type}
    (P : R1 -> Prop)
    (RS : @local_env PaV -> @local_env PaV -> S1 -> S2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @CFGtop PaV R1)
    (k1 : R1 -> @CFGtop PaV S1)
    (t2 : @CFGtop PaV S2) :
    left_evals_to P env1 t1 ->
    (forall r1, P r1 -> cfg_local_sim RS env1 env2 (k1 r1) t2) ->
    cfg_local_sim RS env1 env2 (ITree.bind t1 k1) t2.
  Proof.
    intros Ht Hk.
    eapply cfg_local_sim_obs_eq;
      [reflexivity | apply (Eqit.bind_ret_l tt (fun _ : unit => t2)) |].
    eapply cfg_local_sim_bind; [apply Ht |].
    intros ? ? r1 _ (-> & -> & Hr); apply Hk, Hr.
  Qed.

  (** ** Lockstep [cfg_local_sim] Combinators *)

  Lemma cfg_local_sim_trigger_post {R : Type}
    (P : R -> Prop)
    (env1 env2 : @local_env PaV)
    (e : @CFGEtop PaV R)
    (Hsync : sync_non_local_cfg e = true)
    (Hpost : forall a : R, cfg_event_post e a -> P a) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ P r1)
      env1 env2 (ITree.trigger e) (ITree.trigger e).
  Proof.
    pstep; apply CLS_Step; unfold cls_step_body, ITree.trigger; cbn [observe].
    right; left; split; [exact Hsync | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha Hp; apply EqA_CFG_eq in Ha; subst a2.
    left; apply cfg_local_sim_ret.
    split; [reflexivity | split; [reflexivity | split; [reflexivity | apply Hpost, Hp]]].
  Qed.

  Lemma cfg_local_sim_raise_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) :
    cfg_local_sim RR env1 env2 (raise msg) (raise msg).
  Proof.
    unfold raise, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_withCall_raise_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) :
    cfg_local_sim RR env1 env2 (@withCall PaV R1 (raise msg)) (@withCall PaV R2 (raise msg)).
  Proof.
    unfold withCall, raise, trigger_cast, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    repeat (rewrite observe_bind || rewrite observe_translate); cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_raiseUB_cut {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) (t2 : @CFGtop PaV R2) :
    cfg_local_sim RR env1 env2 (raiseUB msg) t2.
  Proof.
    unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    left; reflexivity.
  Qed.

  Lemma cfg_local_sim_raiseLLVM_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (ex : @exc PaV) :
    cfg_local_sim RR env1 env2 (raiseLLVM ex) (raiseLLVM ex).
  Proof.
    unfold raiseLLVM, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_EOU_ret_sync {R : Type}
    (P : R -> Prop) (env1 env2 : @local_env PaV) (m : EOU R) :
    eou_ret_imp P m ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ P r1)
      env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof.
    intros Hm; destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply cfg_local_sim_raise_sync.
    - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
    - apply cfg_local_sim_raiseUB_cut.
    - apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hm]]].
  Qed.

  Lemma cfg_local_sim_EOU_sync {R : Type}
    (env1 env2 : @local_env PaV) (m : EOU R) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_EOU_ret_sync (fun _ => True) env1 env2 m); destruct m; exact I].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_EOU_ret_sync {R : Type}
    (P : R -> Prop) (env1 env2 : @local_env PaV) (m : EOU R) :
    eou_ret_imp P m ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ P r1)
      env1 env2 (@withCall PaV R (EOU_to_itree m)) (@withCall PaV R (EOU_to_itree m)).
  Proof.
    intros Hm; destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply cfg_local_sim_withCall_raise_sync.
    - unfold withCall, raiseOOM, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
        unfold cls_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
    - unfold withCall, raiseUB, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
        unfold cls_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hm]]].
  Qed.

  Lemma cfg_local_sim_withCall_EOU_sync {R : Type}
    (env1 env2 : @local_env PaV) (m : EOU R) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV R (EOU_to_itree m)) (@withCall PaV R (EOU_to_itree m)).
  Proof.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_withCall_EOU_ret_sync (fun _ => True) env1 env2 m);
         destruct m; exact I].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_gread_sync
    (env1 env2 : @local_env PaV) (id : raw_id) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (gread id) (gread id).
  Proof.
    unfold gread.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True)); [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_gread_sync
    (env1 env2 : @local_env PaV) (id : raw_id) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (gread id))
                (@withCall PaV (@dvalue PaV) (gread id)).
  Proof.
    unfold withCall, gread, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; eapply cfg_local_sim_obs_eq;
      [symmetry; apply translate_ret | symmetry; apply translate_ret |].
    apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_draw_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\
         (is_scalar_dtyp dt = true -> dvalue_has_dtyp r1 dt))
      env1 env2 (@withCall PaV (@dvalue PaV) (draw dt))
                (@withCall PaV (@dvalue PaV) (draw dt)).
  Proof.
    unfold withCall, draw, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate; cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha Hp; apply EqA_CFG_eq in Ha; subst a2.
    left; eapply cfg_local_sim_obs_eq;
      [symmetry; apply translate_ret | symmetry; apply translate_ret |].
    apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hp]]].
  Qed.

  Lemma cfg_local_sim_withCall_conv_sync
    (env1 env2 : @local_env PaV)
    (ic : impure_conversion) (dt_from : dtyp) (dv : @dvalue PaV) (dt_to : dtyp) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (conv ic dt_from dv dt_to))
                (@withCall PaV (@dvalue PaV) (conv ic dt_from dv dt_to)).
  Proof.
    unfold withCall, conv, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; eapply cfg_local_sim_obs_eq;
      [symmetry; apply translate_ret | symmetry; apply translate_ret |].
    apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_freeze
    (dv : @dvalue PaV) :
    forall (dt : dtyp) (env1 env2 : @local_env PaV),
      cfg_local_sim
        (fun e1' e2' r1 r2 =>
           e1' = env1 /\ e2' = env2 /\ r1 = r2 /\
           (is_scalar_dtyp dt = true -> dvalue_has_dtyp dv dt -> dvalue_has_dtyp r1 dt))
        env1 env2 (@withCall PaV (@dvalue PaV) (freeze dt dv))
                  (@withCall PaV (@dvalue PaV) (freeze dt dv)).
  Proof.
    induction dv as [db | p fs IHfs | v es IHes] using dvalue_ind_nested;
      intros dt env1 env2.
    - (* DVALUE_Base *)
      cbn [freeze freeze_base].
      destruct db as [pt | sz i | ip | d | f | | | bsz bv].
      + cbn [Functor.fmap Functor_itree ITree.map].
        eapply cfg_local_sim_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
          | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + cbn [Functor.fmap Functor_itree ITree.map].
        eapply cfg_local_sim_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
          | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + cbn [Functor.fmap Functor_itree ITree.map].
        eapply cfg_local_sim_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
          | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + cbn [Functor.fmap Functor_itree ITree.map].
        eapply cfg_local_sim_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
          | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + cbn [Functor.fmap Functor_itree ITree.map].
        eapply cfg_local_sim_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
          | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + (* DVALUE_Poison -> draw dt *)
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_draw_sync].
        intros ? ? ? ? (-> & -> & <- & Hdr).
        split; [reflexivity | split; [reflexivity | split; [reflexivity | intros Hsc _; apply Hdr, Hsc]]].
      + cbn [Functor.fmap Functor_itree ITree.map].
        eapply cfg_local_sim_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
          | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + (* DVALUE_B: impossible when dt is scalar *)
        assert (Hnot_sc : forall Hsc : is_scalar_dtyp dt = true,
                  dvalue_has_dtyp (DVALUE_Base (@DVALUE_B PaV bsz bv)) dt -> False).
        { intros Hsc Hty.
          destruct (dvalue_has_dtyp_scalar_base_inv _ dt Hsc Hty) as [db' [Heq Hcases]].
          inversion Heq; subst db'.
          destruct Hcases as [Hc | Hnb]; [discriminate Hc | exact (Hnb bsz bv Logic.eq_refl)]. }
        destruct bv as [bp bidx | bi | bits].
        * cbn [Functor.fmap Functor_itree ITree.map].
          eapply cfg_local_sim_obs_eq;
            [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
            | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
          apply cfg_local_sim_ret; repeat split; auto.
        * cbn [Functor.fmap Functor_itree ITree.map].
          eapply cfg_local_sim_obs_eq;
            [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
            | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
          apply cfg_local_sim_ret; repeat split; auto.
        * destruct (existsb is_poison_bit bits).
          -- eapply cfg_local_sim_obs_eq;
               [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
             eapply cfg_local_sim_bind; [apply cfg_local_sim_withCall_draw_sync |].
             intros ? ? x _ (-> & -> & <- & _).
             eapply cfg_local_sim_obs_eq;
               [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
             apply cfg_local_sim_ret; split;
               [reflexivity | split; [reflexivity | split; [reflexivity | intros Hsc Hty; exfalso; exact (Hnot_sc Hsc Hty)]]].
          -- cbn [Functor.fmap Functor_itree ITree.map].
             eapply cfg_local_sim_obs_eq;
               [symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret
               | symmetry; rewrite Eqit.bind_ret_l; apply withCall_ret |].
             apply cfg_local_sim_ret; repeat split; auto.
    - (* DVALUE_Struct *)
      destruct dt as [| p' dts |];
        try (cbn [freeze]; apply cfg_local_sim_withCall_raise_sync).
      cbn [freeze].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2).
      + lazymatch goal with
        | |- cfg_local_sim ?R ?e1 ?e2 (withCall (?go fields dts [])) (withCall (?go fields dts [])) =>
            cut (forall acc : list (@dvalue PaV),
                    cfg_local_sim R e1 e2 (withCall (go fields dts acc)) (withCall (go fields dts acc)));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert dts env1 env2;
          induction IHfs as [| fv fvs Hfv _ IH];
          intros [| t ts] env1 env2 acc;
          try apply cfg_local_sim_withCall_raise_sync.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
          apply cfg_local_sim_ret; repeat split; reflexivity.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
          eapply cfg_local_sim_bind; [apply (Hfv t env1 env2) |].
          intros ? ? v' _ (-> & -> & <- & _); apply IH.
      + intros ? ? val _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; split;
          [reflexivity | split; [reflexivity | split; [reflexivity | intros Hsc; discriminate Hsc]]].
    - (* DVALUE_Array *)
      destruct dt as [| | v' sz t];
        try (cbn [freeze]; apply cfg_local_sim_withCall_raise_sync).
      cbn [freeze].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2).
      + lazymatch goal with
        | |- cfg_local_sim ?R ?e1 ?e2 (withCall (?go elts [])) (withCall (?go elts [])) =>
            cut (forall acc : list (@dvalue PaV),
                    cfg_local_sim R e1 e2 (withCall (go elts acc)) (withCall (go elts acc)));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert env1 env2;
          induction IHes as [| ev evs Hev _ IH];
          intros env1 env2 acc.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
          apply cfg_local_sim_ret; repeat split; reflexivity.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
          eapply cfg_local_sim_bind; [apply (Hev t env1 env2) |].
          intros ? ? v'' _ (-> & -> & <- & _); apply IH.
      + intros ? ? val _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; split;
          [reflexivity | split; [reflexivity | split; [reflexivity | intros Hsc; discriminate Hsc]]].
  Qed.

  Lemma cfg_local_sim_withCall_lread_sync
    (env1 env2 : @local_env PaV) (x : local_id) :
    Maps.lookup x env1 = Maps.lookup x env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ Maps.lookup x env1 = Some r1)
      env1 env2 (@withCall PaV (@dvalue PaV) (lread x))
                (@withCall PaV (@dvalue PaV) (lread x)).
  Proof.
    intros Hlk.
    unfold withCall, lread, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate;
      cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1 inr1 inl1].
    right; right.
    split; [reflexivity | split; [exact Hlk |]].
    intros v Hv; left.
    eapply cfg_local_sim_obs_eq;
      [symmetry; apply translate_ret | symmetry; apply translate_ret |].
    apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hv]]].
  Qed.

  Lemma cfg_local_sim_lwrite_both
    (env1 env2 : @local_env PaV) (id : local_id) (v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = Maps.add id v env1 /\ e2' = Maps.add id v env2 /\ r1 = r2)
      env1 env2 (lwrite id v) (lwrite id v).
  Proof.
    pstep; eapply CLS_WriteL; [symmetry; apply Eqit.bind_ret_r |].
    eapply CLS_WriteR; [symmetry; apply Eqit.bind_ret_r |].
    left; apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_assert_dereferenceable_sync
    (env1 env2 : @local_env PaV)
    (or_null : bool) (n : N) (v : @dvalue PaV) (msg : string) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (assert_dereferenceable or_null n v msg)
                (assert_dereferenceable or_null n v msg).
  Proof.
    unfold assert_dereferenceable.
    destruct v as [db | |]; try apply cfg_local_sim_raise_sync.
    destruct db as [p | | | | | | |]; try apply cfg_local_sim_raise_sync.
    - destruct (_ || _).
      + apply cfg_local_sim_ret; repeat split; reflexivity.
      + eapply cfg_local_sim_bind.
        * unfold load; apply (cfg_local_sim_trigger_post (fun _ => True));
            [reflexivity | intros; exact I].
        * intros ? ? _ _ (-> & -> & _ & _); apply cfg_local_sim_ret; repeat split; reflexivity.
    - apply cfg_local_sim_raiseUB_cut.
  Qed.

  Lemma cfg_local_sim_apply_attrs_sync
    (env1 env2 : @local_env PaV)
    (attrs : list param_attr) (msg : string) (v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (apply_attrs attrs msg v) (apply_attrs attrs msg v).
  Proof.
    unfold apply_attrs.
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? v' _ (-> & -> & <-).
    eapply cfg_local_sim_bind.
    - unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[or_null n] |];
        [| apply cfg_local_sim_ret; repeat split; reflexivity].
      destruct v' as [db | |]; try (apply cfg_local_sim_ret; repeat split; reflexivity).
      destruct db; try (apply cfg_local_sim_ret; repeat split; reflexivity).
      apply cfg_local_sim_assert_dereferenceable_sync.
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
  Proof.
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
    (chk : @assume_bundle_check PaV CFGEtop _ _ _ _) :
    bundle_check f tag = Some chk ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (chk loc vs) (chk loc vs).
  Proof.
    unfold bundle_check; intros Hb.
    destruct (is_llvm_assume f); [| discriminate Hb].
    cbn [assume_bundle_checks List.find] in Hb.
    repeat match goal with
           | H : context [if String.eqb ?a ?b then _ else _] |- _ =>
               destruct (String.eqb a b)
           end;
      cbn [option_map snd] in Hb; try discriminate Hb;
      inversion Hb; subst chk; clear Hb.
    - (* assume_nonnull *)
      unfold assume_nonnull, assume_violated, assume_malformed.
      destruct vs as [| p [| ? ?]]; try apply cfg_local_sim_raise_sync.
      destruct (dvalue_ptr_address p) as [a |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (a =? 0)%Z;
        [apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_ret; repeat split; reflexivity].
    - (* assume_noundef *)
      unfold assume_noundef, assume_violated, assume_malformed.
      destruct vs as [| v [| ? ?]]; try apply cfg_local_sim_raise_sync.
      destruct (dvalue_well_defined v);
        [apply cfg_local_sim_ret; repeat split; reflexivity | apply cfg_local_sim_raiseUB_cut].
    - (* assume_align *)
      unfold assume_align, assume_violated, assume_malformed.
      destruct vs as [| p [| al off]]; try apply cfg_local_sim_raise_sync.
      cbv zeta.
      destruct (dvalue_ptr_address p) as [a |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (bundle_uint al) as [n |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end) as [o |];
        [| apply cfg_local_sim_raiseUB_cut].
      destruct (if is_power_of_two n then ((a - o) mod n =? 0)%Z else (a =? 0)%Z);
        [apply cfg_local_sim_ret; repeat split; reflexivity | apply cfg_local_sim_raiseUB_cut].
    - (* assume_dereferenceable false *)
      unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]]; try apply cfg_local_sim_raise_sync.
      destruct (dvalue_ptr_address p), (bundle_uint sz); try apply cfg_local_sim_raiseUB_cut.
      destruct (_ =? 0)%Z;
        [apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_assert_dereferenceable_sync].
    - (* assume_dereferenceable true *)
      unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]]; try apply cfg_local_sim_raise_sync.
      destruct (dvalue_ptr_address p), (bundle_uint sz); try apply cfg_local_sim_raiseUB_cut.
      destruct (_ =? 0)%Z;
        [apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_assert_dereferenceable_sync].
  Qed.

  (** * 7. Expression Safety & Lockstep Expression Simulation *)

  Lemma val_matches_oty_normalize (oty : ty_info) (v : @dvalue PaV) :
    val_matches_oty oty v ->
    val_matches_oty (normalize_oty oty) v.
  Proof.
    destruct oty as [dt |]; [| exact id].
    cbn [val_matches_oty normalize_oty].
    intros [Hsc Hv]; rewrite Hsc; cbn [val_matches_oty]; exact (conj Hsc Hv).
  Qed.

  Lemma nonpoison_int_lit_sound
    (dt : dtyp) (e : exp dtyp) (env1 : @local_env PaV) :
    is_nonpoison_int_lit dt e = true ->
    left_evals_to
      (fun v => dvalue_has_dtyp v dt /\ v <> DVALUE_Base DVALUE_Poison)
      env1 (denote_exp' (Some dt) e).
  Proof.
    intros Hlit; destruct e; try discriminate Hlit; cbn [is_nonpoison_int_lit] in Hlit.
    - (* EXP_Integer *)
      destruct (denote_int_syntax_as_int_safe dt x Hlit) as (sz & i & -> & Hden).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hden.
      apply left_evals_to_withCall_EOU; cbn;
        split; [apply dvalue_has_dtyp_I | intros Hc; discriminate Hc].
    - (* EXP_Bool *)
      rewrite (is_i1_dtyp_eq dt Hlit); unfold denote_exp'; cbn [denote_exp].
      destruct b; apply left_evals_to_withCall_ret;
        (split; [apply dvalue_has_dtyp_I | intros Hc; discriminate Hc]).
    - (* EXP_Zero_initializer *)
      assert (Hsc : is_scalar_dtyp dt = true).
      { destruct (is_int_dtyp_inv dt Hlit) as [sz ->]; reflexivity. }
      destruct (default_dvalue_scalar_safe dt Hsc) as (dv & Hdef & Hty & Hnp).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hdef.
      apply left_evals_to_withCall_EOU; cbn;
        split; [exact Hty | apply Hnp, Hlit].
  Qed.

  Lemma check_scalar_texp_sound
    (te : ty_env) (e : exp dtyp) :
    forall (dt : dtyp) (env1 : @local_env PaV),
      check_scalar_texp te dt e = true ->
      tenv_sound te env1 ->
      left_evals_to (fun v => dvalue_has_dtyp v dt) env1 (denote_exp' (Some dt) e).
  Proof.
    induction e as
      [ id
      | x
      | f
      | b
      |
      |
      | elts IHelts
      |
      |
      | fields IHfields
      | fields IHfields
      | elts IHelts
      | elts IHelts
      | iop dt' e1 e2 IHe1 IHe2
      | samesign cmp dt' e1 e2 IHe1 IHe2
      | fop fm dt' e1 e2 IHe1 IHe2
      | flags dt' e1 IHe1
      | cmp fm dt' e1 e2 IHe1 IHe2
      | conv dt_from e1 dt_to IHe1
      | flags t dt_p ep idxs IHep IHidxs
      | dt_v ev dt_i ei IHev IHei
      | dt_v ev dt_e ee dt_i ei IHev IHee IHei
      | dt1 e1 dt2 e2 dtm em IHe1 IHe2 IHem
      | dt_s es idxs IHes
      | dt_s es dt_e ee idxs IHes IHee
      | fm dt_c ec dt1 e1 dt2 e2 IHec IHe1 IHe2
      | dt' e1 IHe1
      | se al idia uw tmpl cstr
      | dt' e1 IHe1
      | m Hm
      | dt' e1 IHe1
      | fn blk ] using exp_ind_nested;
      intros dt env1 Hchk Hte;
      try (cbn [check_scalar_texp] in Hchk; rewrite andb_false_r in Hchk; discriminate Hchk).
    - (* EXP_Ident *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hid].
      destruct id as [g | x]; [discriminate Hid |].
      destruct (lookup_ty x te) as [[dt' |] |] eqn:Elk; try discriminate Hid.
      apply dtyp_eqb_eq in Hid; subst dt'.
      destruct (Hte x (Some dt) Elk) as (v & Hlk & [_ Hv]).
      unfold denote_exp'; cbn [denote_exp lookup_id].
      eapply left_evals_to_withCall_lread; [exact Hlk | exact Hv].
    - (* EXP_Integer *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hint].
      destruct (denote_int_syntax_as_int_safe dt x Hint) as (sz & i & -> & Hden).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hden.
      apply left_evals_to_withCall_EOU; cbn; apply dvalue_has_dtyp_I.
    - (* EXP_Float *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hfl].
      unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_EOU, denote_float_syntax_safe, Hfl.
    - (* EXP_Bool *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hi1].
      rewrite (is_i1_dtyp_eq dt Hi1); unfold denote_exp'; cbn [denote_exp].
      destruct b; apply left_evals_to_withCall_ret, dvalue_has_dtyp_I.
    - (* EXP_Null *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hptr].
      rewrite (is_ptr_dtyp_eq dt Hptr); unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_ret, dvalue_has_dtyp_Ptr.
    - (* EXP_Zero_initializer *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [Hsc _].
      destruct (default_dvalue_scalar_safe dt Hsc) as (dv & Hdef & Hty & _).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hdef.
      apply left_evals_to_withCall_EOU; cbn; exact Hty.
    - (* EXP_Undef *)
      unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_ret, dvalue_has_dtyp_Poison.
    - (* EXP_Poison *)
      unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_ret, dvalue_has_dtyp_Poison.
    - (* OP_IBinop *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Heq Hsafe].
      apply dtyp_eqb_eq in Heq; subst dt'.
      unfold is_safe_ibinop_for in Hsafe; apply andb_true_iff in Hsafe as [Hint Hdiv].
      assert (He2' : left_evals_to
                       (fun v2 => dvalue_has_dtyp v2 dt /\
                                  match iop with
                                  | SDiv _ | SRem => v2 <> DVALUE_Base DVALUE_Poison
                                  | _ => True
                                  end)
                       env1 (denote_exp' (Some dt) e2)).
      { destruct iop;
          try (eapply left_evals_to_weaken; [| exact (IHe2 dt env1 He2 Hte)];
               intros ? H; exact (conj H I));
          apply nonpoison_int_lit_sound, Hdiv. }
      unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact He2' | intros v2 [Hv2 Hnp]].
      apply left_evals_to_withCall_EOU, (eval_iop_safe iop dt v1 v2 Hint Hnp Hv1 Hv2).
    - (* OP_ICmp *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hi1 Hsafe].
      rewrite (is_i1_dtyp_eq dt Hi1); unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt' env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt' env1 He2 Hte) | intros v2 Hv2].
      apply left_evals_to_withCall_EOU, (eval_icmp_safe samesign cmp dt' v1 v2 Hsafe Hv1 Hv2).
    - (* OP_FBinop *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hchk Hsf].
      apply andb_true_iff in Hchk as [Hfp Heq].
      apply dtyp_eqb_eq in Heq; subst dt'; unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt env1 He2 Hte) | intros v2 Hv2].
      apply left_evals_to_withCall_EOU, (eval_fop_safe fop dt v1 v2 Hfp Hsf Hv1 Hv2).
    - (* OP_Fneg *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hfp Heq].
      apply dtyp_eqb_eq in Heq; subst dt'; unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
      apply left_evals_to_withCall_EOU, (eval_fneg_safe dt v1 Hfp Hv1).
    - (* OP_FCmp *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hi1 Hfp].
      rewrite (is_i1_dtyp_eq dt Hi1); unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt' env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt' env1 He2 Hte) | intros v2 Hv2].
      apply left_evals_to_withCall_EOU, (eval_fcmp_safe cmp dt' v1 v2 Hfp Hv1 Hv2).
    - (* OP_Conversion *)
      destruct conv as [| pc | ic].
      + (* CONV_Bitcast *)
        cbn [check_scalar_texp] in Hchk.
        apply andb_true_iff in Hchk as [_ Hchk].
        apply andb_true_iff in Hchk as [Hchk He1].
        apply andb_true_iff in Hchk as [Heq2 Heq12].
        apply dtyp_eqb_eq in Heq2; subst dt_to.
        unfold denote_exp'; cbn [denote_exp convert]; rewrite Heq12.
        apply dtyp_eqb_eq in Heq12; subst dt_from.
        eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
        apply left_evals_to_withCall_ret, Hv1.
      + (* CONV_Pure *)
        cbn [check_scalar_texp] in Hchk.
        apply andb_true_iff in Hchk as [_ Hchk].
        apply andb_true_iff in Hchk as [Hchk He1].
        apply andb_true_iff in Hchk as [Heq2 Hsafe].
        apply dtyp_eqb_eq in Heq2; subst dt_to.
        unfold denote_exp'; cbn [denote_exp convert].
        eapply left_evals_to_withCall_bind; [exact (IHe1 dt_from env1 He1 Hte) | intros v1 Hv1].
        apply left_evals_to_withCall_EOU, (convert_pure_safe pc dt_from dt v1 Hsafe Hv1).
      + (* CONV_Impure *)
        cbn [check_scalar_texp] in Hchk; rewrite andb_false_r in Hchk; discriminate Hchk.
    - (* OP_Select *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hchk Hec].
      apply andb_true_iff in Hchk as [Hchk Heq2].
      apply andb_true_iff in Hchk as [Hi1 Heq1].
      rewrite (is_i1_dtyp_eq dt_c Hi1) in Hec |- *.
      apply dtyp_eqb_eq in Heq1; subst dt1.
      apply dtyp_eqb_eq in Heq2; subst dt2.
      unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHec _ env1 Hec Hte) | intros vc Hvc].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt env1 He2 Hte) | intros v2 Hv2].
      apply left_evals_to_withCall_EOU,
        (eval_select_safe_P _ (dvalue_has_dtyp_Poison dt) vc v1 v2 dt Hvc Hv1 Hv2).
  Qed.

  Lemma check_any_texp_safe
    (te : ty_env) (e : exp dtyp) :
    forall (dt : dtyp) (env1 : @local_env PaV),
      check_any_texp te dt e = true ->
      tenv_sound te env1 ->
      left_evals_to (fun _ => True) env1 (denote_exp' (Some dt) e).
  Proof.
    induction e as
      [ id
      | x
      | f
      | b
      |
      |
      | elts IHelts
      |
      |
      | fields IHfields
      | fields IHfields
      | elts IHelts
      | elts IHelts
      | iop dt' e1 e2 IHe1 IHe2
      | samesign cmp dt' e1 e2 IHe1 IHe2
      | fop fm dt' e1 e2 IHe1 IHe2
      | flags dt' e1 IHe1
      | cmp fm dt' e1 e2 IHe1 IHe2
      | conv dt_from e1 dt_to IHe1
      | flags t dt_p ep idxs IHep IHidxs
      | dt_v ev dt_i ei IHev IHei
      | dt_v ev dt_e ee dt_i ei IHev IHee IHei
      | dt1 e1 dt2 e2 dtm em IHe1 IHe2 IHem
      | dt_s es idxs IHes
      | dt_s es dt_e ee idxs IHes IHee
      | fm dt_c ec dt1 e1 dt2 e2 IHec IHe1 IHe2
      | dt' e1 IHe1
      | se al idia uw tmpl cstr
      | dt' e1 IHe1
      | m Hm
      | dt' e1 IHe1
      | fn blk ] using exp_ind_nested;
      intros dt env1 Hany Hte;
      try (eapply left_evals_to_weaken;
           [intros _ _; exact I | exact (check_scalar_texp_sound te _ dt env1 Hany Hte)]).
    - (* EXP_Ident *)
      destruct id as [g | x]; [discriminate Hany |].
      cbn [check_any_texp] in Hany.
      destruct (lookup_ty x te) as [oty |] eqn:Elk; [| discriminate Hany].
      destruct (Hte x oty Elk) as (v & Hlk & _).
      unfold denote_exp'; cbn [denote_exp lookup_id].
      eapply left_evals_to_withCall_lread; [exact Hlk | exact I].
    - (* EXP_Integer *)
      cbn [check_any_texp] in Hany.
      destruct (denote_int_syntax_as_int_safe dt x Hany) as (sz & i & -> & Hden).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hden.
      apply left_evals_to_withCall_EOU; exact I.
    - (* EXP_Float *)
      cbn [check_any_texp] in Hany; unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_EOU.
      eapply eou_safe_weaken; [| apply (denote_float_syntax_safe dt f Hany)].
      intros _ _; exact I.
    - (* EXP_Bool *)
      unfold denote_exp'; cbn [denote_exp]; destruct b; apply left_evals_to_withCall_ret, I.
    - (* EXP_Null *)
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* EXP_Zero_initializer *)
      cbn [check_any_texp] in Hany.
      destruct (default_dvalue_scalar_safe dt Hany) as (dv & Hdef & _).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hdef.
      apply left_evals_to_withCall_EOU; exact I.
    - (* EXP_Undef *)
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* EXP_Poison *)
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* OP_Conversion *)
      destruct conv as [| pc | ic];
        try (eapply left_evals_to_weaken;
             [intros _ _; exact I | exact (check_scalar_texp_sound te _ dt env1 Hany Hte)]).
      cbn [check_any_texp] in Hany; apply andb_true_iff in Hany as [Heq12 Hany1].
      unfold denote_exp'; cbn [denote_exp convert]; rewrite Heq12.
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt_from env1 Hany1 Hte) | intros v1 _].
      apply left_evals_to_withCall_ret, I.
    - (* OP_Select *)
      cbn [check_any_texp] in Hany.
      apply andb_true_iff in Hany as [Hany Hany2].
      apply andb_true_iff in Hany as [Hany Hany1].
      apply andb_true_iff in Hany as [Hi1 Hsc_c].
      rewrite (is_i1_dtyp_eq dt_c Hi1) in Hsc_c |- *.
      unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind;
        [exact (check_scalar_texp_sound te ec _ env1 Hsc_c Hte) | intros vc Hvc].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt1 env1 Hany1 Hte) | intros v1 _].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt2 env1 Hany2 Hte) | intros v2 _].
      apply left_evals_to_withCall_EOU, (eval_select_safe_P _ I vc v1 v2 dt1 Hvc I I).
  Qed.

  Lemma check_any_texp_sound
    (te : ty_env) (e : exp dtyp) (dt : dtyp) (env1 : @local_env PaV) :
    check_any_texp te dt e = true ->
    tenv_sound te env1 ->
    left_evals_to
      (fun v => guarantees_scalar_dtyp te dt e = true -> dvalue_has_dtyp v dt)
      env1 (denote_exp' (Some dt) e).
  Proof.
    intros Hany Hte.
    destruct (guarantees_scalar_dtyp te dt e) eqn:Eguar.
    - pose proof (check_any_guarantees_scalar te e dt Hany Eguar) as Hsc.
      eapply left_evals_to_weaken; [| exact (check_scalar_texp_sound te e dt env1 Hsc Hte)].
      intros v Hv _; exact Hv.
    - eapply left_evals_to_weaken; [| exact (check_any_texp_safe te e dt env1 Hany Hte)].
      intros _ _ Hc; discriminate Hc.
  Qed.

  Lemma op_cand_dtyp_denote_eq (op : exp dtyp) (dt : dtyp) :
    op_cand_dtyp op = Some dt ->
    @denote_exp' PaV None op = @denote_exp' PaV (Some dt) op.
  Proof.
    destruct op; intros H; try discriminate H; try reflexivity.
    - destruct v; reflexivity.
    - destruct conv; try discriminate H; reflexivity.
    - destruct ptrval; reflexivity.
    - destruct cnd, v1, v2; reflexivity.
    - destruct v; reflexivity.
  Qed.

  Lemma check_safe_op_sound
    (te : ty_env) (op : exp dtyp) (env1 : @local_env PaV) :
    check_safe_op te op = true ->
    tenv_sound te env1 ->
    left_evals_to
      (val_matches_oty (normalize_oty (infer_op_oty te op)))
      env1 (denote_exp' None op).
  Proof.
    intros Hchk Hte.
    assert (Hcand_branch :
      (match op with EXP_Ident (ID_Local _) => False | _ => True end) ->
      match op_cand_dtyp op with
      | Some dt => check_any_texp te dt op = true
      | None => False
      end ->
      left_evals_to
        (val_matches_oty (normalize_oty (infer_op_oty te op)))
        env1 (denote_exp' None op)).
    { intros Hnot_loc Hcand.
      destruct (op_cand_dtyp op) as [dt |] eqn:Ecand; [| contradiction].
      rewrite (op_cand_dtyp_denote_eq op dt Ecand).
      assert (Hinf : infer_op_oty te op =
                     if guarantees_scalar_dtyp te dt op then Some dt else None).
      { destruct op; try (destruct id; [| contradiction]);
          unfold infer_op_oty; rewrite Ecand; reflexivity. }
      rewrite Hinf.
      eapply left_evals_to_weaken; [| exact (check_any_texp_sound te op dt env1 Hcand Hte)].
      intros v Hv.
      destruct (guarantees_scalar_dtyp te dt op) eqn:Eguar.
      - apply val_matches_normalize_oty; intros _; apply Hv, Logic.eq_refl.
      - exact I. }
    destruct op as
      [ id | x | f | b | | | elts | | | fields | fields | elts | elts
      | iop dt1 e1 e2 | samesign cmp dt1 e1 e2 | fop fm dt1 e1 e2
      | flags [dt1 e1] | cmp fm dt1 e1 e2 | conv dt_from e1 dt_to
      | flags t [dt_p ep] idxs | p1 p2 | p1 p2 p3 | p1 p2 p3
      | p1 idxs | p1 p2 idxs | fm [dt_c ec] [dt1 e1] [dt2 e2]
      | [dt1 e1] | se al idia uw tmpl cstr | md | p1 | fn blk ];
      try (cbn [check_safe_op op_cand_dtyp] in Hchk; discriminate Hchk);
      try (apply Hcand_branch; [exact I | exact Hchk]).
    - (* EXP_Ident *)
      destruct id as [g | x]; [discriminate Hchk |].
      cbn [check_safe_op infer_op_oty] in Hchk |- *.
      destruct (lookup_ty x te) as [oty |] eqn:Elk; [| discriminate Hchk].
      destruct (Hte x oty Elk) as (v & Hlk & Hv).
      unfold denote_exp'; cbn [denote_exp lookup_id].
      eapply left_evals_to_withCall_lread; [exact Hlk | apply val_matches_oty_normalize, Hv].
    - (* EXP_Undef *)
      cbn [infer_op_oty op_cand_dtyp normalize_oty].
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* EXP_Poison *)
      cbn [infer_op_oty op_cand_dtyp normalize_oty].
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* OP_Conversion *)
      destruct conv as [| pc | ic].
      + apply Hcand_branch; [exact I | exact Hchk].
      + apply Hcand_branch; [exact I | exact Hchk].
      + discriminate Hchk.
  Qed.

  (** ** Lockstep Expression Denotation Simulation *)

  Lemma cfg_local_sim_withCall_map_monad {A B : Type}
    (f : A -> @MCFGtop PaV B)
    (uses : A -> list raw_id)
    (env1 env2 : @local_env PaV)
    (l : list A)
    (Hl : Forall
            (fun a =>
               env_agree_on (uses a) env1 env2 ->
               cfg_local_sim
                 (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
                 env1 env2 (@withCall PaV B (f a)) (@withCall PaV B (f a)))
            l)
    (Hagree : forall a, In a l -> env_agree_on (uses a) env1 env2) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2
      (@withCall PaV (list B) (map_monad f l))
      (@withCall PaV (list B) (map_monad f l)).
  Proof.
    induction Hl as [| a rest Ha _ IH]; cbn [map_monad].
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [apply Ha, Hagree; left; reflexivity |].
      intros ? ? y _ (-> & -> & <-).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [apply IH; intros z Hz; apply Hagree; right; exact Hz |].
      intros ? ? ys _ (-> & -> & <-).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma env_agree_on_texp_list
    (elts : list (dtyp * exp dtyp)) (env1 env2 : @local_env PaV) :
    env_agree_on
      ((fix go (l : list (dtyp * exp dtyp)) : list raw_id :=
          match l with
          | [] => []
          | (_, ex) :: rest => full_exp_uses ex ++ go rest
          end) elts)
      env1 env2 ->
    forall p, In p elts -> env_agree_on (full_exp_uses (snd p)) env1 env2.
  Proof.
    induction elts as [| [dt ex] rest IH]; intros Hagree p Hin; [contradiction |].
    destruct Hin as [<- | Hin].
    - cbn [snd]; eapply env_agree_on_app_l; exact Hagree.
    - apply IH; [eapply env_agree_on_app_r; exact Hagree | exact Hin].
  Qed.

  Lemma cfg_local_sim_denote_exp_sync
    (te : ty_env) (env1 env2 : @local_env PaV) (e : exp dtyp) :
    tenv_sound te env1 ->
    env_agree_on (full_exp_uses e) env1 env2 ->
    forall top : option dtyp,
      cfg_local_sim
        (fun e1' e2' v1 v2 =>
           e1' = env1 /\ e2' = env2 /\ v1 = v2 /\
           match top with
           | Some dt => guarantees_scalar_dtyp te dt e = true -> dvalue_has_dtyp v1 dt
           | None => True
           end)
        env1 env2 (denote_exp' top e) (denote_exp' top e).
  Proof.
    intros Hte.
    induction e as
      [ id
      | x
      | f
      | b
      |
      |
      | elts IHelts
      |
      |
      | fields IHfields
      | fields IHfields
      | elts IHelts
      | elts IHelts
      | iop dt' e1 e2 IHe1 IHe2
      | samesign cmp dt' e1 e2 IHe1 IHe2
      | fop fm dt' e1 e2 IHe1 IHe2
      | flags dt' e1 IHe1
      | cmp fm dt' e1 e2 IHe1 IHe2
      | conv dt_from e1 dt_to IHe1
      | flags t dt_p ep idxs IHep IHidxs
      | dt_v ev dt_i ei IHev IHei
      | dt_v ev dt_e ee dt_i ei IHev IHee IHei
      | dt1 e1 dt2 e2 dtm em IHe1 IHe2 IHem
      | dt_s es idxs IHes
      | dt_s es dt_e ee idxs IHes IHee
      | fm dt_c ec dt1 e1 dt2 e2 IHec IHe1 IHe2
      | dt' e1 IHe1
      | se al idia uw tmpl cstr
      | dt' e1 IHe1
      | m Hm
      | dt' e1 IHe1
      | fn blk ] using exp_ind_nested;
      intros Hagree top.
    - (* EXP_Ident *)
      destruct id as [g | x]; unfold denote_exp'; cbn [denote_exp lookup_id].
      + eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_gread_sync].
        intros ? ? v _ (-> & -> & <-); repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
      + assert (Hlk : Maps.lookup x env1 = Maps.lookup x env2).
        { apply (env_agree_on_in [x] env1 env2 x Hagree); left; reflexivity. }
        eapply cfg_local_sim_weaken; [| apply (cfg_local_sim_withCall_lread_sync env1 env2 x Hlk)].
        intros ? ? v _ (-> & -> & <- & Hv).
        repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hid].
        destruct (lookup_ty x te) as [[dt' |] |] eqn:Elk; try discriminate Hid.
        apply dtyp_eqb_eq in Hid; subst dt'.
        destruct (Hte x (Some dt) Elk) as (v' & Hlk' & [_ Hv']).
        congruence.
    - (* EXP_Integer *)
      unfold denote_exp'; cbn [denote_exp].
      destruct top as [dt |]; [| apply cfg_local_sim_withCall_raise_sync].
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun v => is_int_dtyp dt = true -> dvalue_has_dtyp v dt))].
      + intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
        cbn [guarantees_scalar_dtyp]; intros Hguar;
          apply andb_true_iff in Hguar as [_ Hint]; apply Hv, Hint.
      + destruct (denote_int_syntax_as_int dt x) as [| | | v] eqn:E; cbn; try exact I.
        intros Hint.
        destruct (denote_int_syntax_as_int_safe dt x Hint) as (sz & i & -> & Hden).
        rewrite Hden in E; inversion E; subst v; apply dvalue_has_dtyp_I.
    - (* EXP_Float *)
      unfold denote_exp'; cbn [denote_exp].
      destruct top as [dt |]; [| apply cfg_local_sim_withCall_raise_sync].
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun v => is_fp_dtyp dt = true -> dvalue_has_dtyp v dt))].
      + intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
        cbn [guarantees_scalar_dtyp]; intros Hguar;
          apply andb_true_iff in Hguar as [_ Hfp]; apply Hv, Hfp.
      + destruct (denote_float_syntax_as_float dt f) as [| | | v] eqn:E; cbn; try exact I.
        intros Hfp; pose proof (denote_float_syntax_ret_imp dt f Hfp) as Hret.
        rewrite E in Hret; exact Hret.
    - (* EXP_Bool *)
      unfold denote_exp'; cbn [denote_exp].
      destruct b;
        (eapply cfg_local_sim_obs_eq;
         [symmetry; apply withCall_ret | symmetry; apply withCall_ret |];
         apply cfg_local_sim_ret; repeat split; try reflexivity;
         destruct top as [dt |]; [| exact I];
         cbn [guarantees_scalar_dtyp]; intros Hguar;
         apply andb_true_iff in Hguar as [_ Hi1];
         rewrite (is_i1_dtyp_eq dt Hi1); apply dvalue_has_dtyp_I).
    - (* EXP_Null *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; intros Hguar.
      apply andb_true_iff in Hguar as [_ Hptr].
      rewrite (is_ptr_dtyp_eq dt Hptr); apply dvalue_has_dtyp_Ptr.
    - (* EXP_Zero_initializer *)
      unfold denote_exp'; cbn [denote_exp].
      destruct top as [dt |]; [| apply cfg_local_sim_withCall_raise_sync].
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun v => is_scalar_dtyp dt = true -> dvalue_has_dtyp v dt))].
      + intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
        cbn [guarantees_scalar_dtyp]; intros Hguar;
          apply andb_true_iff in Hguar as [Hsc _]; apply Hv, Hsc.
      + destruct (default_dvalue_of_dtyp dt) as [| | | v] eqn:E; cbn; try exact I.
        intros Hsc; eapply default_dvalue_scalar_typ; eassumption.
    - (* EXP_Cstring *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHelts].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Undef *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; try reflexivity.
      destruct top as [dt |]; [intros _; apply dvalue_has_dtyp_Poison | exact I].
    - (* EXP_Poison *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; try reflexivity.
      destruct top as [dt |]; [intros _; apply dvalue_has_dtyp_Poison | exact I].
    - (* EXP_Struct *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHfields].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Packed_struct *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [apply cfg_local_sim_withCall_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHfields].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Array *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHelts].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Vector *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHelts].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_IBinop *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt')) |].
      intros ? ? v2 _ (-> & -> & <- & Hv2).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_IBinop iop dt' e1 e2) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_iop iop v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg2].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hint Heq].
        apply dtyp_eqb_eq in Heq; subst dt'.
        pose proof (eval_iop_ret_imp iop dt v1 v2 Hint (Hv1 Hg1) (Hv2 Hg2)) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_ICmp *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt')) |].
      intros ? ? v2 _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_ICmp samesign cmp dt' e1 e2) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_icmp samesign cmp v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hi1 Hty].
        rewrite (is_i1_dtyp_eq dt Hi1).
        pose proof (eval_icmp_ret_imp samesign cmp dt' v1 v2 Hty (Hv1 Hg1)) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_FBinop *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt')) |].
      intros ? ? v2 _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_FBinop fop fm dt' e1 e2) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_fop fop v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hfp Heq].
        apply dtyp_eqb_eq in Heq; subst dt'.
        pose proof (eval_fop_ret_imp fop dt v1 v2 Hfp (Hv1 Hg1)) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_Fneg *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hagree (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_Fneg flags (dt', e1)) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_fneg v1) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hfp Heq].
        apply dtyp_eqb_eq in Heq; subst dt'.
        pose proof (eou_safe_to_ret_imp _ _ (eval_fneg_safe dt v1 Hfp (Hv1 Hg1))) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_FCmp *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt')) |].
      intros ? ? v2 _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_FCmp cmp fm dt' e1 e2) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_fcmp cmp v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hi1 Hfp].
        rewrite (is_i1_dtyp_eq dt Hi1).
        pose proof (eval_fcmp_ret_imp cmp dt' v1 v2 Hfp (Hv1 Hg1)) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_Conversion *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hagree (Some dt_from)) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      destruct conv as [| pc | ic]; cbn [convert].
      + (* CONV_Bitcast *)
        destruct (dtyp_eqb dt_from dt_to) eqn:Eeq12.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
          apply cfg_local_sim_ret; repeat split; try reflexivity.
          destruct top as [dt |]; [| exact I].
          cbn [guarantees_scalar_dtyp]; rewrite Eeq12; intros Hguar.
          apply andb_true_iff in Hguar as [_ Hguar].
          apply andb_true_iff in Hguar as [Heq2 Hg1].
          apply dtyp_eqb_eq in Heq2; subst dt_to.
          apply dtyp_eqb_eq in Eeq12; subst dt_from.
          apply Hv1, Hg1.
        * destruct (bit_sizeof_dtyp dt_from =? bit_sizeof_dtyp dt_to)%N;
            [| apply cfg_local_sim_withCall_raise_sync].
          eapply cfg_local_sim_weaken;
            [| apply (cfg_local_sim_withCall_EOU_ret_sync
                        (fun r => is_scalar_dtyp dt_to = true -> dvalue_has_dtyp r dt_to))].
          -- intros ? ? r _ (-> & -> & <- & Hr); repeat split; try reflexivity.
             destruct top as [dt |]; [| exact I].
             cbn [guarantees_scalar_dtyp]; rewrite Eeq12, andb_true_r; intros Hguar.
             apply andb_true_iff in Hguar as [Hsc Heq2].
             apply dtyp_eqb_eq in Heq2; subst dt_to; apply Hr, Hsc.
          -- destruct (dvalue_to_memory_bytes dt_from v1 None) as [| | | bytes]; cbn; try exact I.
             destruct (memory_bytes_to_dvalue bytes dt_to) as [| | | r] eqn:Erd; cbn; try exact I.
             intros Hsc; eapply memory_bytes_to_dvalue_scalar_typ; eassumption.
      + (* CONV_Pure *)
        eapply cfg_local_sim_weaken;
          [| apply (cfg_local_sim_withCall_EOU_ret_sync
                      (fun r => is_scalar_dtyp dt_to = true -> dvalue_has_dtyp r dt_to))].
        * intros ? ? r _ (-> & -> & <- & Hr); repeat split; try reflexivity.
          destruct top as [dt |]; [| exact I].
          cbn [guarantees_scalar_dtyp]; intros Hguar.
          apply andb_true_iff in Hguar as [Hsc Heq2].
          apply dtyp_eqb_eq in Heq2; subst dt_to; apply Hr, Hsc.
        * destruct (convert_pure pc dt_from v1 dt_to) as [| | | r] eqn:E; cbn; try exact I.
          intros Hsc; pose proof (convert_pure_ret_imp pc dt_from dt_to v1 Hsc) as Hret.
          rewrite E in Hret; exact Hret.
      + (* CONV_Impure *)
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_conv_sync].
        intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_GetElementPtr *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_p.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_i.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHep Hag_p (Some dt_p)) |].
      intros ? ? vptr _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHidxs].
          intros [dt_i ex_i] H_i Hag_k; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_k (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hag_i.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_weaken;
          [| apply (cfg_local_sim_withCall_EOU_ret_sync
                      (fun r => dvalue_has_dtyp r (DTYPE_Base DTYPE_Pointer))
                      env1 env2 _ (eval_gep_ret_imp flags t vptr vs))].
        intros ? ? r _ (-> & -> & <- & Hr); repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hptr].
        rewrite (is_ptr_dtyp_eq dt Hptr); exact Hr.
    - (* OP_ExtractElement *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_v.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_i.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHev Hag_v (Some dt_v)) |].
      intros ? ? vec _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHei Hag_i (Some dt_i)) |].
      intros ? ? idx _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
      intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_InsertElement *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_v.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_ei.
      pose proof (env_agree_on_app_l _ _ _ _ Hag_ei) as Hag_e.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_ei) as Hag_i.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHev Hag_v (Some dt_v)) |].
      intros ? ? vec _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
        eapply cfg_local_sim_bind; [exact (IHee Hag_e (Some dt_e)) |].
        intros ? ? ve _ (-> & -> & <- & _); apply cfg_local_sim_withCall_EOU_sync.
      + intros ? ? elt _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
        eapply cfg_local_sim_bind; [exact (IHei Hag_i (Some dt_i)) |].
        intros ? ? idx _ (-> & -> & <- & _).
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
        intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_ShuffleVector *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2m.
      pose proof (env_agree_on_app_l _ _ _ _ Hag2m) as Hag2.
      pose proof (env_agree_on_app_r _ _ _ _ Hag2m) as Hagm.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt1)) |].
      intros ? ? v1 _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt2)) |].
      intros ? ? v2 _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHem Hagm (Some dtm)) |].
      intros ? ? vm _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
      intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_ExtractValue *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHes Hagree (Some dt_s)) |].
      intros ? ? str _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
      intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_InsertValue *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_s.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_e.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHes Hag_s (Some dt_s)) |].
      intros ? ? str _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHee Hag_e (Some dt_e)) |].
      intros ? ? elt _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
      intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_Select *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_c.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag12.
      pose proof (env_agree_on_app_l _ _ _ _ Hag12) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hag12) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHec Hag_c (Some dt_c)) |].
      intros ? ? vc _ (-> & -> & <- & Hvc).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt1)) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt2)) |].
      intros ? ? v2 _ (-> & -> & <- & Hv2).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_Select fm (dt_c, ec) (dt1, e1) (dt2, e2)) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_select vc dt1 v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg2].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hguar Hgc].
        apply andb_true_iff in Hguar as [Hguar Heq2].
        apply andb_true_iff in Hguar as [Hi1 Heq1].
        apply dtyp_eqb_eq in Heq1; subst dt1.
        apply dtyp_eqb_eq in Heq2; subst dt2.
        assert (Hvc_i1 : dvalue_has_dtyp vc (DTYPE_Base (DTYPE_I 1%positive))).
        { rewrite <- (is_i1_dtyp_eq dt_c Hi1); apply Hvc, Hgc. }
        pose proof (eou_safe_to_ret_imp _ _
                      (eval_select_safe_P _ (dvalue_has_dtyp_Poison dt)
                         vc v1 v2 dt Hvc_i1 (Hv1 Hg1) (Hv2 Hg2))) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_Freeze *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hagree (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_freeze].
      intros ? ? r _ (-> & -> & <- & Hfr); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; intros Hguar.
      apply andb_true_iff in Hguar as [Hsc Hguar].
      apply andb_true_iff in Hguar as [Heq Hg1].
      apply dtyp_eqb_eq in Heq; subst dt'.
      apply Hfr; [exact Hsc | apply Hv1, Hg1].
    - (* EXP_Asm *)
      unfold denote_exp'; cbn [denote_exp]; apply cfg_local_sim_withCall_raise_sync.
    - (* EXP_Metadata METADATA_Const *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_weaken; [| exact (IHe1 Hagree (Some dt'))].
      intros ? ? r _ (-> & -> & <- & _); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Metadata other *)
      unfold denote_exp'; cbn [denote_exp].
      destruct m as [| mid | [dt' e1] | mds | m1 m2 | s1 s2 | fi];
        [| | exfalso; exact (Hm dt' e1 Logic.eq_refl) | | | |];
        (eapply cfg_local_sim_obs_eq;
         [symmetry; apply withCall_ret | symmetry; apply withCall_ret |];
         apply cfg_local_sim_ret; repeat split; try reflexivity;
         destruct top as [dt |]; [| exact I];
         cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc).
    - (* EXP_Splat *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [apply cfg_local_sim_withCall_EOU_sync |].
      intros ? ? [sz t] _ (-> & -> & <-).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hagree (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_BlockAddress *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_gread_sync].
      intros ? ? v _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
  Qed.

  Lemma cfg_local_sim_denote_op_sync
    (te : ty_env) (env1 env2 : @local_env PaV) (op : exp dtyp) :
    tenv_sound te env1 ->
    env_agree_on (full_exp_uses op) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' v1 v2 =>
         e1' = env1 /\ e2' = env2 /\ v1 = v2 /\
         val_matches_oty (normalize_oty (infer_op_oty te op)) v1)
      env1 env2 (denote_exp' None op) (denote_exp' None op).
  Proof.
    intros Hte Hagree.
    assert (Hnon_loc :
      (match op with EXP_Ident (ID_Local _) => False | _ => True end) ->
      cfg_local_sim
        (fun e1' e2' v1 v2 =>
           e1' = env1 /\ e2' = env2 /\ v1 = v2 /\
           val_matches_oty (normalize_oty (infer_op_oty te op)) v1)
        env1 env2 (denote_exp' None op) (denote_exp' None op)).
    { intros Hnl.
      destruct (op_cand_dtyp op) as [dt |] eqn:Ecand.
      - rewrite (op_cand_dtyp_denote_eq op dt Ecand).
        assert (Hinf : infer_op_oty te op =
                       if guarantees_scalar_dtyp te dt op then Some dt else None).
        { destruct op; try (destruct id; [| contradiction]);
            unfold infer_op_oty; rewrite Ecand; reflexivity. }
        rewrite Hinf.
        eapply cfg_local_sim_weaken;
          [| exact (cfg_local_sim_denote_exp_sync te env1 env2 op Hte Hagree (Some dt))].
        intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
        destruct (guarantees_scalar_dtyp te dt op) eqn:Eguar.
        + apply val_matches_normalize_oty; intros _; apply Hv, Logic.eq_refl.
        + exact I.
      - assert (Hinf : infer_op_oty te op = None).
        { destruct op; try (destruct id; [| contradiction]);
            unfold infer_op_oty; rewrite Ecand; reflexivity. }
        rewrite Hinf; cbn [normalize_oty].
        eapply cfg_local_sim_weaken;
          [| exact (cfg_local_sim_denote_exp_sync te env1 env2 op Hte Hagree None)].
        intros ? ? v _ (-> & -> & <- & _); repeat split; try reflexivity; exact I. }
    destruct op; try (apply Hnon_loc; exact I).
    destruct id as [g | x]; [apply Hnon_loc; exact I |].
    assert (Hlk : Maps.lookup x env1 = Maps.lookup x env2).
    { apply (env_agree_on_in [x] env1 env2 x Hagree); left; reflexivity. }
    unfold denote_exp'; cbn [denote_exp lookup_id infer_op_oty].
    eapply cfg_local_sim_weaken; [| apply (cfg_local_sim_withCall_lread_sync env1 env2 x Hlk)].
    intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
    destruct (lookup_ty x te) as [oty |] eqn:Elk; [| exact I].
    destruct (Hte x oty Elk) as (v' & Hlk' & Hv').
    replace v with v' by congruence.
    apply val_matches_oty_normalize, Hv'.
  Qed.

  (** * 8. Instruction, Block, Phi, Terminator, & Whole-CFG Simulation *)

  (** ** Lockstep [CFGtop] Helpers, Call Arguments, Operand Bundles, & Atomics *)

  Lemma cfg_local_sim_map_monad_sync {A B : Type}
    (f : A -> @CFGtop PaV B)
    (env1 env2 : @local_env PaV)
    (l : list A)
    (Hf : forall a,
            In a l ->
            cfg_local_sim
              (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
              env1 env2 (f a) (f a)) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (map_monad f l) (map_monad f l).
  Proof.
    induction l as [| a rest IH]; cbn [map_monad].
    - apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_bind; [apply Hf; left; reflexivity |].
      intros ? ? y _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply IH; intros z Hz; apply Hf; right; exact Hz |].
      intros ? ? ys _ (-> & -> & <-).
      apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_denote_exp_plain_sync
    (env1 env2 : @local_env PaV) (top : option dtyp) (e : exp dtyp) :
    env_agree_on (full_exp_uses e) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' v1 v2 => e1' = env1 /\ e2' = env2 /\ v1 = v2)
      env1 env2 (denote_exp' top e) (denote_exp' top e).
  Proof.
    intros Hagree.
    eapply cfg_local_sim_weaken;
      [| exact (cfg_local_sim_denote_exp_sync [] env1 env2 e
                  (tenv_sound_nil env1) Hagree top)].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_alloca_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (n : N) (align : option N) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\
         dvalue_has_dtyp r1 (DTYPE_Base DTYPE_Pointer))
      env1 env2 (alloca dt n align) (alloca dt n align).
  Proof.
    unfold alloca.
    apply (cfg_local_sim_trigger_post
             (fun r => dvalue_has_dtyp r (DTYPE_Base DTYPE_Pointer)));
      [reflexivity | intros _ H; exact H].
  Qed.

  Lemma cfg_local_sim_load_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (a : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\
         (is_scalar_dtyp dt = true -> dvalue_has_dtyp r1 dt))
      env1 env2 (load dt a) (load dt a).
  Proof.
    unfold load.
    apply (cfg_local_sim_trigger_post
             (fun r => is_scalar_dtyp dt = true -> dvalue_has_dtyp r dt));
      [reflexivity | intros _ H; exact H].
  Qed.

  Lemma cfg_local_sim_store_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (a v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (store dt a v) (store dt a v).
  Proof.
    unfold store.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_call_sync
    (env1 env2 : @local_env PaV)
    (dt : dtyp) (cc : cconv) (fv : @dvalue PaV) (vs : list (@dvalue PaV)) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (call dt cc fv vs) (call dt cc fv vs).
  Proof.
    unfold call.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_intrinsic_sync
    (env1 env2 : @local_env PaV)
    (dt : dtyp) (s : string) (vs : list (@dvalue PaV)) (va : option (@ptr PaV)) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (intrinsic dt s vs va) (intrinsic dt s vs va).
  Proof.
    unfold intrinsic.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_stack_get_exc_sync
    (env1 env2 : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 stack_get_exc stack_get_exc.
  Proof.
    unfold stack_get_exc.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_stack_raise_sync
    (env1 env2 : @local_env PaV) (ex : @exc PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (stack_raise ex) (stack_raise ex).
  Proof.
    unfold stack_raise.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_denote_call_args_sync
    (env1 env2 : @local_env PaV)
    (args : list (texp dtyp * list param_attr)) (msg : string) :
    env_agree_on (flat_map (fun '(te, _) => full_texp_uses te) args) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (denote_call_args args msg) (denote_call_args args msg).
  Proof.
    intros Hagree; unfold denote_call_args.
    apply cfg_local_sim_map_monad_sync; intros [[t op] attrs] Hin.
    eapply cfg_local_sim_bind.
    - apply cfg_local_sim_denote_exp_plain_sync.
      intros x Hx; apply Hagree, in_raw_ids_spec.
      apply in_raw_ids_spec in Hx; apply in_flat_map.
      exists ((t, op), attrs); split; [exact Hin | exact Hx].
    - intros ? ? v _ (-> & -> & <-).
      apply cfg_local_sim_apply_attrs_sync.
  Qed.

  Lemma cfg_local_sim_denote_operand_bundles_sync
    (env1 env2 : @local_env PaV)
    (loc : string) (f : exp dtyp) (obs : list (@operand_bundle dtyp)) :
    env_agree_on (flat_map full_ob_uses obs) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (denote_operand_bundles loc f obs) (denote_operand_bundles loc f obs).
  Proof.
    intros Hagree; unfold denote_operand_bundles.
    eapply cfg_local_sim_bind.
    - apply cfg_local_sim_map_monad_sync; intros ob Hob.
      eapply cfg_local_sim_bind.
      + apply cfg_local_sim_map_monad_sync; intros o Ho.
        destruct o as [[t e] | md].
        * apply cfg_local_sim_denote_exp_plain_sync.
          intros x Hx; apply Hagree, in_raw_ids_spec.
          apply in_raw_ids_spec in Hx; apply in_flat_map.
          exists ob; split; [exact Hob |].
          unfold full_ob_uses; apply in_flat_map.
          exists (SSA_value (t, e)); split; [exact Ho | exact Hx].
        * apply cfg_local_sim_ret; repeat split; reflexivity.
      + intros ? ? vs _ (-> & -> & <-).
        destruct (bundle_check f (ob_tag ob)) as [chk |] eqn:Echk.
        * exact (cfg_local_sim_assume_check_sync env1 env2 f (ob_tag ob) loc vs chk Echk).
        * apply cfg_local_sim_ret; repeat split; reflexivity.
    - intros ? ? _ _ (-> & -> & _); apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_denote_cmpxchg_sync
    (env1 env2 : @local_env PaV) (id : raw_id) (cpx : cmpxchg dtyp) :
    env_agree_on
      (full_texp_uses (c_ptr cpx)
       ++ full_texp_uses (c_cmp cpx)
       ++ full_texp_uses (c_new cpx))
      env1 env2 ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         exists v, e1' = Maps.add id v env1 /\ e2' = Maps.add id v env2)
      env1 env2 (denote_cmpxchg id cpx) (denote_cmpxchg id cpx).
  Proof.
    intros Hagree.
    pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_ptr.
    pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_cn.
    pose proof (env_agree_on_app_l _ _ _ _ Hag_cn) as Hag_cmp.
    pose proof (env_agree_on_app_r _ _ _ _ Hag_cn) as Hag_new.
    unfold denote_cmpxchg.
    destruct (c_ptr cpx) as [ptr_ty ptr_val];
      destruct (c_cmp cpx) as [cmp_ty cmp_val];
      destruct (c_new cpx) as [new_ty new_val];
      cbn [full_texp_uses snd] in Hag_ptr, Hag_cmp, Hag_new;
      cbv beta iota zeta.
    destruct (dtyp_eq_dec cmp_ty new_ty) as [<- | _];
      [| apply cfg_local_sim_raise_sync].
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some ptr_ty) ptr_val Hag_ptr) |].
    intros ? ? ptr_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some cmp_ty) cmp_val Hag_cmp) |].
    intros ? ? cmp_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some cmp_ty) new_val Hag_new) |].
    intros ? ? new_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? _ _ (-> & -> & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
    intros ? ? loaded_v _ (-> & -> & <- & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? dv _ (-> & -> & <-).
    destruct dv as [db | |]; try apply cfg_local_sim_raise_sync.
    destruct db as [p | sz cb | ip | d | f | | | bsz bv];
      try apply cfg_local_sim_raise_sync.
    - destruct sz as [p | p |]; try apply cfg_local_sim_raise_sync.
      match goal with |- context [if ?b then _ else _] => destruct b end.
      + eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _); cbv zeta.
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
        intros ? ? _ _ (-> & -> & _); eexists; split; reflexivity.
      + cbv zeta.
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
        intros ? ? _ _ (-> & -> & _); eexists; split; reflexivity.
    - apply cfg_local_sim_raiseUB_cut.
  Qed.

  Lemma cfg_local_sim_denote_atomic_rmw_op_sync
    (env1 env2 : @local_env PaV)
    (a_op : atomic_rmw_operation) (pv val : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2
      (denote_atomic_rmw_operation a_op pv val)
      (denote_atomic_rmw_operation a_op pv val).
  Proof.
    destruct a_op; cbn [denote_atomic_rmw_operation];
      try apply cfg_local_sim_EOU_sync;
      try apply cfg_local_sim_raise_sync.
    - (* Axchg *)
      apply cfg_local_sim_ret; repeat split; reflexivity.
    - (* Anand *)
      destruct val as [db | |]; try apply cfg_local_sim_raise_sync.
      destruct db as [p | sz i | ip | d | f | | | bsz bv];
        try apply cfg_local_sim_raise_sync.
      apply cfg_local_sim_EOU_sync.
  Qed.

  Lemma cfg_local_sim_denote_atomicrmw_sync
    (env1 env2 : @local_env PaV) (id : raw_id) (armw : atomicrmw dtyp) :
    env_agree_on
      (full_texp_uses (a_ptr armw) ++ full_texp_uses (a_val armw))
      env1 env2 ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         exists v, e1' = Maps.add id v env1 /\ e2' = Maps.add id v env2)
      env1 env2 (denote_atomicrmw id armw) (denote_atomicrmw id armw).
  Proof.
    intros Hagree.
    pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_ptr.
    pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_val.
    unfold denote_atomicrmw.
    destruct (a_ptr armw) as [ptr_ty ptr_val];
      destruct (a_val armw) as [a_ty a_val];
      cbn [full_texp_uses snd] in Hag_ptr, Hag_val; cbv beta iota zeta.
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some ptr_ty) ptr_val Hag_ptr) |].
    intros ? ? ptr_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some a_ty) a_val Hag_val) |].
    intros ? ? a_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? _ _ (-> & -> & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
    intros ? ? loaded_v _ (-> & -> & <- & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_denote_atomic_rmw_op_sync |].
    intros ? ? stored_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
    intros ? ? _ _ (-> & -> & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
    intros ? ? _ _ (-> & -> & _).
    apply cfg_local_sim_ret; exists loaded_v; split; reflexivity.
  Qed.

  (** ** Lockstep Instruction & Intra-Block Backward DCE Simulation *)

  Definition instr_live_before
    (ins : instr_id * instr dtyp * list (metadata dtyp))
    (live_after : list raw_id) : list raw_id :=
    let '(iid, i, _) := ins in
    let live_killed :=
      match instr_must_kill iid i with
      | Some x => remove_raw_id x live_after
      | None => live_after
      end in
    add_raw_ids (full_instr_uses i) live_killed.

  Lemma cfg_local_sim_denote_instr_sync
    (te : ty_env) (live_after : list raw_id)
    (env1 env2 : @local_env PaV)
    (ins : instr_id * instr dtyp * list (metadata dtyp))
    (va : option (@ptr PaV)) :
    tenv_sound te env1 ->
    env_agree_on (instr_live_before ins live_after) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         (env1 = env2 -> e1' = e2') /\
         tenv_sound (step_tenv_instr te ins) e1' /\
         env_agree_on live_after e1' e2')
      env1 env2 (denote_instr ins va) (denote_instr ins va).
  Proof.
    intros Hte Hagree.
    destruct ins as [[iid i] md].
    unfold instr_live_before in Hagree.
    apply env_agree_on_add_raw_ids_split in Hagree as [Huses Hkill].
    destruct i as
      [ msg
      | op
      | [dt f] args anns obs
      | dt anns
      | dt [du ptr] anns
      | [dt val] [du ptr] anns
      | syncscope o
      | cpx
      | armw
      | [t ptr_exp] argty
      | resultty cleanup cs ].
    - (* INSTR_Comment *)
      destruct iid as [id | vid]; unfold denote_instr; cbv beta iota zeta.
      + apply cfg_local_sim_raise_sync.
      + cbn [step_tenv_instr instr_must_kill] in Hkill |- *.
        apply cfg_local_sim_ret; split; [intros Heq; exact Heq | exact (conj Hte Hkill)].
    - (* INSTR_Op *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_op_sync te env1 env2 op Hte Huses) |].
      intros ? ? uv _ (-> & -> & <- & Huv).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
      intros ? ? _ _ (-> & -> & _).
      apply cfg_local_sim_ret; split; [intros ->; reflexivity |].
      split;
        [ apply (tenv_sound_set_ty id (infer_op_oty te op) uv te env1 Huv Hte)
        | apply (env_agree_on_add_both live_after id uv env1 env2 Hkill) ].
    - (* INSTR_Call *)
      cbn [full_instr_uses] in Huses.
      pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_f.
      pose proof (env_agree_on_app_r _ _ _ _ Huses) as Hag_rest1.
      pose proof (env_agree_on_app_l _ _ _ _ Hag_rest1) as Hag_args.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_rest1) as Hag_rest2.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_rest2) as Hag_obs.
      cbn [full_texp_uses snd] in Hag_f.
      destruct iid as [id | vid];
        cbn [step_tenv_instr instr_must_kill] in Hkill |- *;
        unfold denote_instr; cbv beta iota zeta.
      + eapply cfg_local_sim_bind;
          [apply (cfg_local_sim_denote_call_args_sync env1 env2 args _ Hag_args) |].
        intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_bind;
          [apply (cfg_local_sim_denote_operand_bundles_sync env1 env2 _ f obs Hag_obs) |].
        intros ? ? _ _ (-> & -> & _).
        eapply cfg_local_sim_bind.
        * destruct (intrinsic_exp f) as [s |].
          -- apply cfg_local_sim_intrinsic_sync.
          -- eapply cfg_local_sim_bind;
               [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 None f Hag_f) |].
             intros ? ? fv _ (-> & -> & <-); apply cfg_local_sim_call_sync.
        * intros ? ? res _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [apply cfg_local_sim_check_call_return_sync |].
          intros ? ? res' _ (-> & -> & <-).
          eapply cfg_local_sim_bind.
          -- destruct res' as [ex | dv];
               [apply cfg_local_sim_raiseLLVM_sync
               | apply cfg_local_sim_ret; repeat split; reflexivity].
          -- intros ? ? rv _ (-> & -> & <-).
             eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
             intros ? ? _ _ (-> & -> & _); split; [intros ->; reflexivity |].
             split;
               [ apply (tenv_sound_set_ty id None rv te env1 I Hte)
               | apply (env_agree_on_add_both live_after id rv env1 env2 Hkill) ].
      + eapply cfg_local_sim_bind;
          [apply (cfg_local_sim_denote_call_args_sync env1 env2 args _ Hag_args) |].
        intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_bind;
          [apply (cfg_local_sim_denote_operand_bundles_sync env1 env2 _ f obs Hag_obs) |].
        intros ? ? _ _ (-> & -> & _).
        eapply cfg_local_sim_bind.
        * destruct (intrinsic_exp f) as [s |].
          -- apply cfg_local_sim_intrinsic_sync.
          -- eapply cfg_local_sim_bind;
               [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 None f Hag_f) |].
             intros ? ? fv _ (-> & -> & <-); apply cfg_local_sim_call_sync.
        * intros ? ? res _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [apply cfg_local_sim_check_call_return_sync |].
          intros ? ? res' _ (-> & -> & <-).
          eapply cfg_local_sim_bind.
          -- destruct res' as [ex | dv];
               [apply cfg_local_sim_raiseLLVM_sync
               | apply cfg_local_sim_ret; repeat split; reflexivity].
          -- intros ? ? _ _ (-> & -> & _).
             apply cfg_local_sim_ret; split; [intros Heq; exact Heq | exact (conj Hte Hkill)].
    - (* INSTR_Alloca *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' _ _ =>
                 exists v,
                   e1' = Maps.add id v env1 /\
                   e2' = Maps.add id v env2 /\
                   dvalue_has_dtyp v (DTYPE_Base DTYPE_Pointer)).
      + destruct (find_option ann_num_elements anns) as [[t num_exp] |] eqn:Efind.
        * assert (Hag_num : env_agree_on (full_exp_uses num_exp) env1 env2).
          { intros x Hx; apply Huses, in_raw_ids_spec.
            apply in_raw_ids_spec in Hx.
            exact (find_option_ann_num_elements_uses anns (t, num_exp) x Efind Hx). }
          eapply cfg_local_sim_bind;
            [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some t) num_exp Hag_num) |].
          intros ? ? n _ (-> & -> & <-).
          destruct (dvalue_is_poison n); [apply cfg_local_sim_raiseUB_cut |].
          eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
          intros ? ? n' _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [apply cfg_local_sim_alloca_sync |].
          intros ? ? v _ (-> & -> & <- & Hv).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); exists v; split; [reflexivity | split; [reflexivity | exact Hv]].
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_alloca_sync |].
          intros ? ? v _ (-> & -> & <- & Hv).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); exists v; split; [reflexivity | split; [reflexivity | exact Hv]].
      + intros ? ? _ _ (v & -> & -> & Hv).
        apply cfg_local_sim_ret; split; [intros ->; reflexivity |].
        split.
        * apply (tenv_sound_set_ty id (Some (DTYPE_Base DTYPE_Pointer)) v te env1);
            [apply val_matches_normalize_oty; intros _; exact Hv | exact Hte].
        * apply (env_agree_on_add_both live_after id v env1 env2 Hkill).
    - (* INSTR_Load *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_ptr.
      cbn [full_texp_uses snd] in Hag_ptr.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some du) ptr Hag_ptr) |].
      intros ? ? a _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
      intros ? ? v _ (-> & -> & <- & Hv).
      eapply cfg_local_sim_bind.
      + apply (cfg_local_sim_EOU_ret_sync
                 (fun v' => is_scalar_dtyp dt = true -> dvalue_has_dtyp v' dt)).
        eapply eou_ret_imp_weaken;
          [| apply (apply_value_attrs_scalar_typ
                      (load_metadata_attrs md) _ dt
                      (value_metadata_range (metadata_range md) v))].
        intros v' Hattr Hsc.
        apply (Hattr Hsc), (value_metadata_range_scalar_typ (metadata_range md) dt v Hsc (Hv Hsc)).
      + intros ? ? v' _ (-> & -> & <- & Hv').
        eapply cfg_local_sim_bind.
        * unfold assert_load_dereferenceable.
          destruct (load_metadata_dereferenceable md) as [[or_null n] |];
            [ apply cfg_local_sim_assert_dereferenceable_sync
            | apply cfg_local_sim_ret; repeat split; reflexivity ].
        * intros ? ? _ _ (-> & -> & _).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); split; [intros ->; reflexivity |].
          split.
          -- apply (tenv_sound_set_ty id (Some dt) v' te env1);
               [apply val_matches_normalize_oty, Hv' | exact Hte].
          -- apply (env_agree_on_add_both live_after id v' env1 env2 Hkill).
    - (* INSTR_Store *)
      destruct iid as [id | vid];
        [unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync |].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_val.
      pose proof (env_agree_on_app_r _ _ _ _ Huses) as Hag_pa.
      pose proof (env_agree_on_app_l _ _ _ _ Hag_pa) as Hag_ptr.
      cbn [full_texp_uses snd] in Hag_val, Hag_ptr.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some dt) val Hag_val) |].
      intros ? ? v _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some du) ptr Hag_ptr) |].
      intros ? ? a _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind.
      + destruct a as [db | |];
          [destruct db as [p | sz k | ip | d | f | | | bsz bv] | |];
          try apply cfg_local_sim_store_sync;
          apply cfg_local_sim_raiseUB_cut.
      + intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret; split; [intros Heq; exact Heq | exact (conj Hte Hkill)].
    - (* INSTR_Fence *)
      destruct iid as [id | vid];
        cbn [step_tenv_instr instr_must_kill] in Hkill |- *;
        unfold denote_instr; cbv beta iota zeta;
        apply cfg_local_sim_ret; (split; [intros Heq; exact Heq | exact (conj Hte Hkill)]).
    - (* INSTR_AtomicCmpXchg *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_weaken;
        [| exact (cfg_local_sim_denote_cmpxchg_sync env1 env2 id cpx Huses)].
      intros ? ? _ _ (v & -> & ->); split; [intros ->; reflexivity |].
      split;
        [ apply (tenv_sound_set_ty id None v te env1 I Hte)
        | apply (env_agree_on_add_both live_after id v env1 env2 Hkill) ].
    - (* INSTR_AtomicRMW *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_weaken;
        [| exact (cfg_local_sim_denote_atomicrmw_sync env1 env2 id armw Huses)].
      intros ? ? _ _ (v & -> & ->); split; [intros ->; reflexivity |].
      split;
        [ apply (tenv_sound_set_ty id None v te env1 I Hte)
        | apply (env_agree_on_add_both live_after id v env1 env2 Hkill) ].
    - (* INSTR_VAArg *)
      cbn [full_instr_uses full_texp_uses snd] in Huses.
      destruct iid as [id | vid];
        cbn [step_tenv_instr instr_must_kill] in Hkill |- *;
        unfold denote_instr; cbv beta iota zeta.
      + eapply cfg_local_sim_bind;
          [exact (cfg_local_sim_denote_exp_plain_sync
                    env1 env2 (Some (DTYPE_Base DTYPE_Pointer)) ptr_exp Huses) |].
        intros ? ? ptr_to_args _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? args_p _ (-> & -> & <- & _).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? retv _ (-> & -> & <- & _).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? ix _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? args' _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _).
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
        intros ? ? _ _ (-> & -> & _); split; [intros ->; reflexivity |].
        split;
          [ apply (tenv_sound_set_ty id None retv te env1 I Hte)
          | apply (env_agree_on_add_both live_after id retv env1 env2 Hkill) ].
      + eapply cfg_local_sim_bind;
          [exact (cfg_local_sim_denote_exp_plain_sync
                    env1 env2 (Some (DTYPE_Base DTYPE_Pointer)) ptr_exp Huses) |].
        intros ? ? ptr_to_args _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? args_p _ (-> & -> & <- & _).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? _ _ (-> & -> & _ & _).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? ix _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? args' _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret; split; [intros Heq; exact Heq | exact (conj Hte Hkill)].
    - (* INSTR_LandingPad *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [step_tenv_instr instr_must_kill] in Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind; [apply cfg_local_sim_stack_get_exc_sync |].
      intros ? ? oe _ (-> & -> & <-).
      destruct oe as [ex |]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
      intros ? ? _ _ (-> & -> & _); split; [intros ->; reflexivity |].
      split;
        [ apply (tenv_sound_set_ty id None ex te env1 I Hte)
        | apply (env_agree_on_add_both live_after id ex env1 env2 Hkill) ].
  Qed.

  Lemma dce_code_cons_cases
    (te : ty_env) (ins : instr_id * instr dtyp * list (metadata dtyp))
    (rest : code dtyp) (live_after : list raw_id) :
    let '(live_mid, rest') := dce_code (step_tenv_instr te ins) rest live_after in
    (exists x op md,
       ins = (IId x, INSTR_Op op, md) /\
       in_raw_ids x live_mid = false /\
       check_safe_op te op = true /\
       dce_code te (ins :: rest) live_after = (live_mid, rest'))
    \/
    (dce_code te (ins :: rest) live_after =
       (instr_live_before ins live_mid, ins :: rest')).
  Proof.
    cbn [dce_code].
    destruct (dce_code (step_tenv_instr te ins) rest live_after) as [live_mid rest'].
    destruct ins as [[iid i] md].
    destruct iid as [x | vid], i;
      try (right; reflexivity).
    destruct (negb (in_raw_ids x live_mid) && check_safe_op te e) eqn:Edel.
    - apply andb_true_iff in Edel as [Hnx Hsafe].
      apply negb_true_iff in Hnx.
      left; exists x, e, md; repeat split; [exact Hnx | exact Hsafe].
    - right; reflexivity.
  Qed.

  Lemma left_deleted_op_sim
    (te : ty_env) (x : local_id) (op : exp dtyp) (md : list (metadata dtyp))
    (va : option (@ptr PaV))
    (RR : @local_env PaV -> @local_env PaV -> unit -> unit -> Prop)
    (env1 env2 : @local_env PaV)
    (k1 : @CFGtop PaV unit) (t2 : @CFGtop PaV unit) :
    check_safe_op te op = true ->
    tenv_sound te env1 ->
    (forall uv : @dvalue PaV,
       val_matches_oty (normalize_oty (infer_op_oty te op)) uv ->
       cfg_local_sim RR (Maps.add x uv env1) env2 k1 t2) ->
    cfg_local_sim RR env1 env2
      (ITree.bind (denote_instr (IId x, INSTR_Op op, md) va) (fun _ => k1))
      t2.
  Proof.
    intros Hsafe Hte Hk.
    unfold denote_instr; cbv beta iota zeta.
    eapply cfg_local_sim_obs_eq; [symmetry; apply Eqit.bind_bind | reflexivity |].
    eapply left_evals_to_bind_sim;
      [exact (check_safe_op_sound te op env1 Hsafe Hte) |].
    intros uv Huv.
    specialize (Hk uv Huv).
    pstep; eapply CLS_WriteL.
    - unfold lwrite; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [] _ _; apply Eqit.bind_ret_l.
    - punfold Hk; eapply cfg_local_sim__mon;
        [exact Hk | intros ? ? ? ? [Hl | []]; left; eapply paco4_mon; [exact Hl | intros ? ? ? ? []]].
  Qed.

  Lemma dce_code_sim
    (cs : code dtyp) (va : option (@ptr PaV)) :
    forall (te : ty_env) (live_after : list raw_id)
           (env1 env2 : @local_env PaV),
      let '(live_in, cs') := dce_code te cs live_after in
      tenv_sound te env1 ->
      env_agree_on live_in env1 env2 ->
      cfg_local_sim
        (fun e1' e2' _ _ =>
           tenv_sound (step_tenv_code te cs) e1' /\
           env_agree_on live_after e1' e2')
        env1 env2 (denote_code cs va) (denote_code cs' va).
  Proof.
    induction cs as [| ins rest IH]; intros te live_after env1 env2.
    - cbn [dce_code step_tenv_code]; intros Hte Hagree.
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_nil | symmetry; apply denote_code_nil |].
      apply cfg_local_sim_ret; exact (conj Hte Hagree).
    - pose proof (dce_code_cons_cases te ins rest live_after) as Hcases.
      specialize (IH (step_tenv_instr te ins) live_after).
      destruct (dce_code (step_tenv_instr te ins) rest live_after) as [live_mid rest'].
      cbn [step_tenv_code].
      destruct Hcases as [(x & op & md & -> & Hnx & Hsafe & ->) | ->].
      + (* Deleted dead INSTR_Op *)
        intros Hte Hagree.
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply denote_code_cons | reflexivity |].
        eapply left_deleted_op_sim; [exact Hsafe | exact Hte |].
        intros uv Huv; apply IH.
        * cbn [step_tenv_instr].
          apply (tenv_sound_set_ty x (infer_op_oty te op) uv te env1 Huv Hte).
        * apply (env_agree_on_add_dead_l live_mid x uv env1 env2 Hnx Hagree).
      + (* Kept instruction *)
        intros Hte Hagree.
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply denote_code_cons | symmetry; apply denote_code_cons |].
        eapply cfg_local_sim_bind;
          [exact (cfg_local_sim_denote_instr_sync te live_mid env1 env2 ins va Hte Hagree) |].
        intros e1' e2' _ _ (_ & Hte' & Hagree').
        exact (IH e1' e2' Hte' Hagree').
  Qed.

  Lemma denote_code_refl_sim
    (cs : code dtyp) (va : option (@ptr PaV)) (env : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2)
      env env (denote_code cs va) (denote_code cs va).
  Proof.
    revert env; induction cs as [| ins rest IH]; intros env.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_nil | symmetry; apply denote_code_nil |].
      apply cfg_local_sim_ret; split; reflexivity.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_cons | symmetry; apply denote_code_cons |].
      eapply cfg_local_sim_bind.
      + apply (cfg_local_sim_denote_instr_sync [] [] env env ins va
                 (tenv_sound_nil env) (env_agree_on_refl _ env)).
      + intros e1' e2' _ _ (Heq & _ & _).
        rewrite (Heq Logic.eq_refl); apply IH.
  Qed.

  (** ** Two-Phase [denote_phis] Dead-Phi Simulation *)

  Inductive phi_vals_rel (live_after : list raw_id)
    : list (local_id * ty_info) ->
      list local_id ->
      list (local_id * @dvalue PaV) ->
      list (local_id * @dvalue PaV) -> Prop :=
  | PVR_nil :
      phi_vals_rel live_after [] [] [] []
  | PVR_keep (id : local_id) (oty : ty_info) (v : @dvalue PaV)
      (ws : list (local_id * ty_info)) (kds : list local_id)
      (dvs1 dvs2 : list (local_id * @dvalue PaV)) :
      val_matches_oty (normalize_oty oty) v ->
      phi_vals_rel live_after ws kds dvs1 dvs2 ->
      phi_vals_rel live_after ((id, oty) :: ws) (id :: kds)
        ((id, v) :: dvs1) ((id, v) :: dvs2)
  | PVR_drop (id : local_id) (oty : ty_info) (v : @dvalue PaV)
      (ws : list (local_id * ty_info)) (kds : list local_id)
      (dvs1 dvs2 : list (local_id * @dvalue PaV)) :
      in_raw_ids id live_after = false ->
      val_matches_oty (normalize_oty oty) v ->
      phi_vals_rel live_after ws kds dvs1 dvs2 ->
      phi_vals_rel live_after ((id, oty) :: ws) kds
        ((id, v) :: dvs1) dvs2.

  Lemma phi_writes_sim
    (live_after : list raw_id)
    (ws : list (local_id * ty_info))
    (kds : list local_id)
    (dvs1 dvs2 : list (local_id * @dvalue PaV))
    (Hpvr : phi_vals_rel live_after ws kds dvs1 dvs2) :
    forall (te : ty_env) (env1 env2 : @local_env PaV),
      tenv_sound te env1 ->
      env_agree_on (remove_raw_ids kds live_after) env1 env2 ->
      cfg_local_sim
        (fun e1' e2' _ _ =>
           tenv_sound (apply_phi_writes ws te) e1' /\
           env_agree_on live_after e1' e2')
        env1 env2
        (map_monad (fun '(id, dv) => lwrite id dv) dvs1)
        (map_monad (fun '(id, dv) => lwrite id dv) dvs2).
  Proof.
    induction Hpvr as
      [ | id oty v ws kds dvs1 dvs2 Hv _ IH
        | id oty v ws kds dvs1 dvs2 Hdead Hv _ IH ];
      intros te env1 env2 Hte Hpass;
      cbn [apply_phi_writes map_monad].
    - cbn [remove_raw_ids fold_right] in Hpass.
      apply cfg_local_sim_ret; exact (conj Hte Hpass).
    - cbn [remove_raw_ids fold_right] in Hpass.
      eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind.
      + apply IH.
        * apply (tenv_sound_set_ty id oty v te env1 Hv Hte).
        * apply (env_agree_on_add_both _ id v env1 env2 Hpass).
      + intros e1' e2' _ _ Hpost; apply cfg_local_sim_ret, Hpost.
    - assert (Hsim_next :
        cfg_local_sim
          (fun e1' e2' _ _ =>
             tenv_sound (apply_phi_writes ws (set_ty id oty te)) e1' /\
             env_agree_on live_after e1' e2')
          (Maps.add id v env1) env2
          (ITree.bind
             (map_monad (fun '(id0, dv) => lwrite id0 dv) dvs1)
             (fun us => Ret (tt :: us)))
          (map_monad (fun '(id0, dv) => lwrite id0 dv) dvs2)).
      { eapply cfg_local_sim_obs_eq;
          [reflexivity | symmetry; apply Eqit.bind_ret_r |].
        eapply cfg_local_sim_bind.
        - apply IH.
          + apply (tenv_sound_set_ty id oty v te env1 Hv Hte).
          + apply env_agree_on_add_dead_l; [| exact Hpass].
            destruct (in_raw_ids id (remove_raw_ids kds live_after)) eqn:Ein;
              [| reflexivity].
            apply in_remove_raw_ids in Ein as [_ Hin]; congruence.
        - intros e1' e2' _ _ Hpost; apply cfg_local_sim_ret, Hpost. }
      pstep; eapply CLS_WriteL; [reflexivity |].
      punfold Hsim_next; eapply cfg_local_sim__mon;
        [exact Hsim_next | intros ? ? ? ? [Hl | []]; left; eapply paco4_mon; [exact Hl | intros ? ? ? ? []]].
  Qed.

  Lemma dce_phis_eval_sim
    (edges : list (block_id * ty_env))
    (bid_from : block_id) (te_edge : ty_env)
    (live_after : list raw_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (env1 env2 : @local_env PaV) :
    In (bid_from, te_edge) edges ->
    tenv_sound te_edge env1 ->
    env_agree_on
      (kept_phis_uses_from bid_from (dce_phis edges live_after phis))
      env1 env2 ->
    cfg_local_sim
      (fun e1' e2' dvs1 dvs2 =>
         e1' = env1 /\ e2' = env2 /\
         phi_vals_rel live_after
           (List.map (fun '(id, p, _) => (id, phi_res_oty bid_from te_edge p)) phis)
           (kept_phi_defs (dce_phis edges live_after phis))
           dvs1 dvs2)
      env1 env2
      (map_monad (denote_phi bid_from) phis)
      (map_monad (denote_phi bid_from) (dce_phis edges live_after phis)).
  Proof.
    intros Hin Hte.
    induction phis as [| [[id [pfm dt args]] md] rest IH]; intros Huses.
    - cbn [dce_phis kept_phi_defs List.map map_monad].
      apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | constructor]].
    - cbn [dce_phis List.map] in Huses |- *.
      destruct (negb (in_raw_ids id live_after) &&
                forallb (fun '(pred, te_e) =>
                           is_safe_phi_on_edge pred te_e (Phi pfm dt args))
                        edges) eqn:Edel.
      + (* Deleted dead phi *)
        apply andb_true_iff in Edel as [Hnid Hall].
        apply negb_true_iff in Hnid.
        rewrite forallb_forall in Hall.
        specialize (Hall (bid_from, te_edge) Hin);
          unfold is_safe_phi_on_edge in Hall; cbv beta iota in Hall.
        destruct (assoc bid_from args) as [op |] eqn:Eassoc; [| discriminate Hall].
        assert (Hphi_eval :
          left_evals_to
            (fun y =>
               exists uv,
                 y = (id, uv) /\
                 val_matches_oty
                   (normalize_oty (phi_res_oty bid_from te_edge (Phi pfm dt args)))
                   uv)
            env1
            (denote_phi bid_from (id, Phi pfm dt args, md))).
        { unfold denote_phi; cbv beta iota zeta; rewrite Eassoc.
          eapply left_evals_to_bind;
            [exact (check_any_texp_sound te_edge op dt env1 Hall Hte) |].
          intros uv Huv; apply left_evals_to_ret.
          exists uv; split; [reflexivity |].
          unfold phi_res_oty; rewrite Eassoc.
          destruct (guarantees_scalar_dtyp te_edge dt op) eqn:Eguar.
          - apply val_matches_normalize_oty; intros _; apply Huv, Logic.eq_refl.
          - exact I. }
        cbn [map_monad].
        eapply left_evals_to_bind_sim; [exact Hphi_eval |].
        intros _ (uv & -> & Huv).
        eapply cfg_local_sim_obs_eq;
          [reflexivity | symmetry; apply Eqit.bind_ret_r |].
        eapply cfg_local_sim_bind; [exact (IH Huses) |].
        intros ? ? dvs1 dvs2 (-> & -> & Hpvr).
        apply cfg_local_sim_ret; split;
          [reflexivity | split; [reflexivity | apply PVR_drop; assumption]].
      + (* Kept phi *)
        cbn [kept_phis_uses_from flat_map] in Huses.
        pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_hd.
        pose proof (env_agree_on_app_r _ _ _ _ Huses) as Hag_tl.
        cbn [kept_phi_defs List.map map_monad].
        eapply cfg_local_sim_bind.
        * unfold denote_phi; cbv beta iota zeta.
          destruct (assoc bid_from args) as [op |] eqn:Eassoc;
            [| apply cfg_local_sim_raise_sync].
          eapply cfg_local_sim_bind;
            [exact (cfg_local_sim_denote_exp_sync te_edge env1 env2 op Hte Hag_hd (Some dt)) |].
          intros ? ? uv _ (-> & -> & <- & Huv).
          apply cfg_local_sim_ret.
          instantiate (1 := fun e1' e2' y1 y2 =>
                              e1' = env1 /\ e2' = env2 /\ y1 = y2 /\
                              exists uv0,
                                y1 = (id, uv0) /\
                                val_matches_oty
                                  (normalize_oty (phi_res_oty bid_from te_edge (Phi pfm dt args)))
                                  uv0).
          repeat split; try reflexivity.
          exists uv; split; [reflexivity |].
          unfold phi_res_oty; rewrite Eassoc.
          destruct (guarantees_scalar_dtyp te_edge dt op) eqn:Eguar.
          -- apply val_matches_normalize_oty; intros _; apply Huv, Logic.eq_refl.
          -- exact I.
        * intros ? ? _ _ (-> & -> & <- & uv & -> & Huv).
          eapply cfg_local_sim_bind; [exact (IH Hag_tl) |].
          intros ? ? dvs1 dvs2 (-> & -> & Hpvr).
          apply cfg_local_sim_ret; split;
            [reflexivity | split; [reflexivity | apply PVR_keep; assumption]].
  Qed.

  Lemma dce_phis_sim
    (edges : list (block_id * ty_env))
    (bid_from : block_id) (te_edge : ty_env)
    (live_after : list raw_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (env1 env2 : @local_env PaV) :
    In (bid_from, te_edge) edges ->
    tenv_sound te_edge env1 ->
    env_agree_on
      (edge_live_req bid_from (dce_phis edges live_after phis) live_after)
      env1 env2 ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         tenv_sound (step_tenv_phis_from bid_from phis te_edge) e1' /\
         env_agree_on live_after e1' e2')
      env1 env2
      (denote_phis bid_from phis)
      (denote_phis bid_from (dce_phis edges live_after phis)).
  Proof.
    intros Hin Hte Hagree.
    unfold edge_live_req in Hagree.
    apply env_agree_on_add_raw_ids_split in Hagree as [Huses Hpass].
    unfold denote_phis, step_tenv_phis_from.
    eapply cfg_local_sim_bind;
      [exact (dce_phis_eval_sim edges bid_from te_edge live_after phis
                env1 env2 Hin Hte Huses) |].
    intros ? ? dvs1 dvs2 (-> & -> & Hpvr).
    eapply cfg_local_sim_bind;
      [exact (phi_writes_sim live_after _ _ dvs1 dvs2 Hpvr te_edge env1 env2 Hte Hpass) |].
    intros e1' e2' _ _ Hpost; apply cfg_local_sim_ret, Hpost.
  Qed.

  Lemma denote_phis_refl_sim
    (bid_from : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (env : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2)
      env env (denote_phis bid_from phis) (denote_phis bid_from phis).
  Proof.
    unfold denote_phis.
    eapply cfg_local_sim_bind.
    - apply cfg_local_sim_map_monad_sync; intros [[id [pfm dt args]] md] _.
      unfold denote_phi; cbv beta iota zeta.
      destruct (assoc bid_from args) as [op |]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_bind;
        [apply cfg_local_sim_denote_exp_plain_sync, env_agree_on_refl |].
      intros ? ? uv _ (-> & -> & <-).
      apply cfg_local_sim_ret; repeat split; reflexivity.
    - intros ? ? dvs _ (-> & -> & <-).
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' _ _ => e1' = e2').
      + revert env; induction dvs as [| [id dv] rest IH]; intros env; cbn [map_monad].
        * apply cfg_local_sim_ret; reflexivity.
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
          intros ? ? _ _ (-> & -> & _).
          eapply cfg_local_sim_bind; [apply IH |].
          intros e1' e2' _ _ ->; apply cfg_local_sim_ret; reflexivity.
      + intros e1' e2' _ _ ->; apply cfg_local_sim_ret; split; reflexivity.
  Qed.

  (** ** Terminator Simulation *)

  Lemma select_switch_in
    (selector : @dvalue PaV) (default_br : block_id)
    (switches : list (@dvalue PaV * block_id)) :
    eou_ret_imp
      (fun bid => bid = default_br \/ In bid (List.map snd switches))
      (@select_switch PaV selector default_br switches).
  Proof.
    induction switches as [| [v id] rest IH]; cbn [select_switch].
    - cbn; left; reflexivity.
    - destruct selector as [db1 | |]; try exact I.
      destruct db1 as [p1 | sz1 i1 | ip1 | d1 | f1 | | | bsz1 bv1]; try exact I.
      destruct v as [db2 | |]; try exact I.
      destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2]; try exact I.
      destruct (Pos.eq_dec sz1 sz2) as [Heq | _]; [| exact I].
      subst sz2; cbn [eq_rect eq_rect_r eq_sym].
      match goal with |- context [if ?b then _ else _] => destruct b end.
      + cbn; right; left; reflexivity.
      + eapply eou_ret_imp_weaken; [| exact IH].
        intros b [-> | Hin]; [left; reflexivity | right; right; exact Hin].
  Qed.

  Lemma map_monad_switch_dests_snd
    (dests : list (tint_literal * block_id)) :
    eou_ret_imp
      (fun switches : list (@dvalue PaV * block_id) =>
         List.map snd switches = List.map snd dests)
      (map_monad
         (fun '((TInt_Literal sz x), id) =>
            s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
            ret (DVALUE_Base s, id))
         dests).
  Proof.
    set (f := fun '((TInt_Literal sz x), id) =>
                s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
                (ret (DVALUE_Base s, id) : EOU (@dvalue PaV * block_id))).
    change (eou_ret_imp
              (fun switches : list (@dvalue PaV * block_id) =>
                 List.map snd switches = List.map snd dests)
              (map_monad f dests)).
    induction dests as [| [[sz x] id] rest IH]; cbn [map_monad List.map snd].
    - reflexivity.
    - unfold f at 1.
      destruct (@coerce_integer_to_int PaV (Some sz) (denote_int_syntax x))
        as [| | | s]; cbn; try exact I.
      destruct (map_monad f rest) as [| | | sws]; cbn in IH |- *; try exact I.
      f_equal; exact IH.
  Qed.

  Lemma switch_target_eou_in
    (selector : @dvalue PaV) (default_br : block_id)
    (dests : list (tint_literal * block_id)) :
    eou_ret_imp
      (fun bid => In bid (default_br :: List.map snd dests))
      (switches <- map_monad
                     (fun '((TInt_Literal sz x), id) =>
                        s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
                        ret (DVALUE_Base s, id))
                     dests ;;
       @select_switch PaV selector default_br switches).
  Proof.
    pose proof (map_monad_switch_dests_snd dests) as Hsw.
    destruct
      (map_monad
         (fun '((TInt_Literal sz x), id) =>
            s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
            (ret (DVALUE_Base s, id) : EOU (@dvalue PaV * block_id)))
         dests) as [| | | switches];
      cbn in Hsw |- *; try exact I.
    rewrite <- Hsw; apply select_switch_in.
  Qed.

  Lemma step_tenv_term_non_invoke
    (iid : instr_id) (tm : terminator dtyp) (md : list (metadata dtyp))
    (succ : block_id) (te : ty_env) :
    (match tm with TERM_Invoke _ _ _ _ _ _ => False | _ => True end) ->
    step_tenv_term (iid, tm, md) succ te = te.
  Proof.
    destruct iid, tm; intros H; try contradiction; reflexivity.
  Qed.

  Lemma cfg_local_sim_denote_terminator_sync
    (te : ty_env) (live_out : list raw_id)
    (env1 env2 : @local_env PaV)
    (trm : instr_id * terminator dtyp * list (metadata dtyp)) :
    let '(_, tm, _) := trm in
    tenv_sound te env1 ->
    env_agree_on (add_raw_ids (full_term_uses tm) live_out) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         (env1 = env2 -> e1' = e2') /\
         r1 = r2 /\
         match r1 with
         | inl succ =>
             In succ (term_successors tm) /\
             tenv_sound (step_tenv_term trm succ te) e1' /\
             env_agree_on live_out e1' e2'
         | inr _ => True
         end)
      env1 env2 (denote_terminator trm) (denote_terminator trm).
  Proof.
    destruct trm as [[iid tm] md].
    intros Hte Hagree.
    apply env_agree_on_add_raw_ids_split in Hagree as [Huses Hlive].
    destruct tm as
      [ [dt op]
      |
      | [dt op] br1 br2
      | br
      | [dt e] default_br dests
      | [t addr] brs fn
      | [t expr]
      | [dt fnptrval] args to_label unwind_label anns obs
      | ];
      unfold denote_terminator; cbv beta iota zeta.
    - (* TERM_Ret *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some dt) op Huses) |].
      intros ? ? dv _ (-> & -> & <-).
      apply cfg_local_sim_ret;
        split; [intros Heq; exact Heq | split; [reflexivity | exact I]].
    - (* TERM_Ret_void *)
      apply cfg_local_sim_ret;
        split; [intros Heq; exact Heq | split; [reflexivity | exact I]].
    - (* TERM_Br *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some dt) op Huses) |].
      intros ? ? v _ (-> & -> & <-).
      destruct v as [db | |]; try apply cfg_local_sim_raise_sync.
      destruct db as [p | sz cb | ip | d | f | | | bsz bv];
        try apply cfg_local_sim_raise_sync.
      + destruct sz as [p | p |]; try apply cfg_local_sim_raise_sync.
        match goal with |- context [if ?b then _ else _] => destruct b end;
          apply cfg_local_sim_ret;
          (split; [intros Heq; exact Heq | split; [reflexivity |]]);
          rewrite (step_tenv_term_non_invoke iid _ md _ te I);
          (split; [cbn; auto | exact (conj Hte Hlive)]).
      + apply cfg_local_sim_raiseUB_cut.
    - (* TERM_Br_1 *)
      apply cfg_local_sim_ret;
        split; [intros Heq; exact Heq | split; [reflexivity |]].
      rewrite (step_tenv_term_non_invoke iid _ md _ te I).
      split; [cbn; left; reflexivity | exact (conj Hte Hlive)].
    - (* TERM_Switch *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some dt) e Huses) |].
      intros ? ? selector _ (-> & -> & <-).
      destruct (dvalue_is_poison selector); [apply cfg_local_sim_raiseUB_cut |].
      eapply cfg_local_sim_bind;
        [apply (cfg_local_sim_EOU_ret_sync _ env1 env2 _
                  (switch_target_eou_in selector default_br dests)) |].
      intros ? ? bid _ (-> & -> & <- & Hbid).
      apply cfg_local_sim_ret;
        split; [intros Heq; exact Heq | split; [reflexivity |]].
      rewrite (step_tenv_term_non_invoke iid _ md _ te I).
      split; [exact Hbid | exact (conj Hte Hlive)].
    - (* TERM_IndirectBr *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some t) addr Huses) |].
      intros ? ? a _ (-> & -> & <-).
      destruct (dvalue_is_poison a); [apply cfg_local_sim_raiseUB_cut |].
      destruct fn as [f |]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_bind.
      + apply cfg_local_sim_map_monad_sync; intros b _.
        eapply cfg_local_sim_bind; [apply cfg_local_sim_gread_sync |].
        intros ? ? ba _ (-> & -> & <-); apply cfg_local_sim_ret; repeat split; reflexivity.
      + intros ? ? addrs _ (-> & -> & <-).
        destruct (dvalue_ptr_address a) as [z |]; [| apply cfg_local_sim_raise_sync].
        destruct (indirectbr_target z (combine brs addrs)) as [b |] eqn:Etgt;
          [| apply cfg_local_sim_raiseUB_cut].
        apply cfg_local_sim_ret;
          split; [intros Heq; exact Heq | split; [reflexivity |]].
        rewrite (step_tenv_term_non_invoke iid _ md _ te I).
        split; [exact (indirectbr_target_In z brs addrs b Etgt) | exact (conj Hte Hlive)].
    - (* TERM_Resume *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some t) expr Huses) |].
      intros ? ? exn _ (-> & -> & <-).
      apply cfg_local_sim_raiseLLVM_sync.
    - (* TERM_Invoke *)
      cbn [full_term_uses] in Huses.
      pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_f.
      pose proof (env_agree_on_app_r _ _ _ _ Huses) as Hag_rest1.
      pose proof (env_agree_on_app_l _ _ _ _ Hag_rest1) as Hag_args.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_rest1) as Hag_rest2.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_rest2) as Hag_obs.
      cbn [full_texp_uses snd] in Hag_f.
      eapply cfg_local_sim_bind;
        [apply (cfg_local_sim_denote_call_args_sync env1 env2 args _ Hag_args) |].
      intros ? ? uvs _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply (cfg_local_sim_denote_operand_bundles_sync env1 env2 _ fnptrval obs Hag_obs) |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 None fnptrval Hag_f) |].
      intros ? ? fv _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_call_sync |].
      intros ? ? rv _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_check_call_return_sync |].
      intros ? ? rv' _ (-> & -> & <-).
      destruct rv' as [exn | returned_value].
      + (* Unwind branch -> unwind_label *)
        eapply cfg_local_sim_bind; [apply cfg_local_sim_stack_raise_sync |].
        intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret;
          split; [intros Heq; exact Heq | split; [reflexivity |]].
        split; [cbn; right; left; reflexivity | split; [| exact Hlive]].
        destruct iid as [x | vid]; cbn [step_tenv_term]; [| exact Hte].
        rewrite raw_id_eqb_refl; cbn [negb]; rewrite andb_false_r.
        destruct (raw_id_eqb unwind_label to_label); cbn [negb];
          [apply tenv_sound_remove_ty_same, Hte | exact Hte].
      + (* Normal branch -> to_label *)
        destruct iid as [x | vid].
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
          intros ? ? _ _ (-> & -> & _).
          apply cfg_local_sim_ret; split; [intros ->; reflexivity | split; [reflexivity |]].
          split; [cbn; left; reflexivity |].
          split; [| apply env_agree_on_add_both_same, Hlive].
          cbn [step_tenv_term]; rewrite raw_id_eqb_refl; cbn [andb negb].
          destruct (raw_id_eqb to_label unwind_label); cbn [negb];
            [ apply tenv_sound_remove_ty_add, Hte
            | apply (tenv_sound_set_ty x None returned_value te env1 I Hte) ].
        * eapply cfg_local_sim_bind;
            [apply cfg_local_sim_ret; instantiate (1 := fun e1' e2' _ _ => e1' = env1 /\ e2' = env2); split; reflexivity |].
          intros ? ? _ _ (-> & ->).
          apply cfg_local_sim_ret;
            split; [intros Heq; exact Heq | split; [reflexivity |]].
          cbn [step_tenv_term]; split; [cbn; left; reflexivity | exact (conj Hte Hlive)].
    - (* TERM_Unreachable *)
      apply cfg_local_sim_raiseUB_cut.
  Qed.

  (** ** Validator Soundness & Whole-CFG Iteration Simulation *)

  Lemma denote_cfg_refl_sim
    (c : CFG.cfg dtyp) (va : option (@ptr PaV)) (env : @local_env PaV) :
    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
      env env (denote_cfg c va) (denote_cfg c va).
  Proof.
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
          eapply cfg_local_sim_weaken;
            [| apply (cfg_local_sim_denote_terminator_sync
                        [] [] e1'' e1'' (blk_term bk_src)
                        (tenv_sound_nil e1'') (env_agree_on_refl _ e1''))].
          intros ? ? ? ? (Heq & <- & _); split; [exact (Heq Logic.eq_refl) | reflexivity].
        * intros e1' e2' [bid_tgt | dv] _ [<- <-];
            apply cfg_local_sim_ret; cbn; auto.
      + apply cfg_local_sim_ret; cbn; reflexivity.
    - intros ? ? [bid | uv] _ <-;
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_ret; reflexivity].
  Qed.

  Lemma check_fwd_cfg_init
    (fargs : list local_id) (reach : list block_id)
    (fm : fwd_map) (c : CFG.cfg dtyp) :
    check_fwd_cfg fargs reach fm c = true ->
    in_raw_ids (init c) reach = true /\
    (forall bk_init,
       find_block (blks c) (init c) = Some bk_init ->
       tenv_subsumes
         (lookup_fwd (init c) fm)
         (step_tenv_phis_from (init c) (blk_phis bk_init) (init_tenv fargs)) = true).
  Proof.
    unfold check_fwd_cfg; intros Hchk.
    apply andb_true_iff in Hchk as [Hchk _].
    apply andb_true_iff in Hchk as [Hreach Hinit].
    split; [exact Hreach |].
    intros bk_init Efind; rewrite Efind in Hinit; exact Hinit.
  Qed.

  Lemma check_fwd_cfg_edge
    (fargs : list local_id) (reach : list block_id)
    (fm : fwd_map) (c : CFG.cfg dtyp)
    (bk : block dtyp) (succ : block_id) :
    check_fwd_cfg fargs reach fm c = true ->
    In bk (blks c) ->
    in_raw_ids (blk_id bk) reach = true ->
    In succ (block_successors bk) ->
    in_raw_ids succ reach = true /\
    (forall bk_succ,
       find_block (blks c) succ = Some bk_succ ->
       let te_end := step_tenv_code (lookup_fwd (blk_id bk) fm) (blk_code bk) in
       let te_edge := step_tenv_term (blk_term bk) succ te_end in
       tenv_subsumes
         (lookup_fwd succ fm)
         (step_tenv_phis_from (blk_id bk) (blk_phis bk_succ) te_edge) = true).
  Proof.
    unfold check_fwd_cfg; intros Hchk Hin_bk Hreach Hsucc.
    apply andb_true_iff in Hchk as [_ Hall].
    rewrite forallb_forall in Hall.
    specialize (Hall bk Hin_bk); rewrite Hreach in Hall.
    cbv zeta in Hall; rewrite forallb_forall in Hall.
    specialize (Hall succ Hsucc).
    apply andb_true_iff in Hall as [Hr_succ Hsub].
    split; [exact Hr_succ |].
    intros bk_succ Efind; rewrite Efind in Hsub; exact Hsub.
  Qed.

  Lemma check_live_cfg_edge
    (fargs : list local_id) (reach : list block_id)
    (fm : fwd_map) (lm : live_map) (c : CFG.cfg dtyp)
    (bk bk_succ : block dtyp) (succ : block_id) :
    check_live_cfg fargs reach fm lm c = true ->
    In bk (blks c) ->
    in_raw_ids (blk_id bk) reach = true ->
    In succ (block_successors bk) ->
    find_block (blks c) succ = Some bk_succ ->
    let '(live_code_s, bk_dce_s) := dce_block_info fargs reach fm lm c bk_succ in
    raw_ids_subset
      (edge_live_req (blk_id bk) (blk_phis bk_dce_s) live_code_s)
      (lookup_live (blk_id bk) lm) = true.
  Proof.
    unfold check_live_cfg; intros Hchk Hin_bk Hreach Hsucc Efind.
    rewrite forallb_forall in Hchk.
    specialize (Hchk bk Hin_bk); rewrite Hreach in Hchk.
    rewrite forallb_forall in Hchk.
    specialize (Hchk succ Hsucc); rewrite Efind in Hchk; exact Hchk.
  Qed.

  Definition dce_iter_inv
    (fargs : list local_id) (reach : list block_id)
    (fm : fwd_map) (lm : live_map) (c : CFG.cfg dtyp)
    (env1 env2 : @local_env PaV)
    (s1 s2 : block_id * block_id) : Prop :=
    s1 = s2 /\
    let '(bid_from, bid_src) := s1 in
    in_raw_ids bid_src reach = true /\
    exists te_edge : ty_env,
      In (bid_from, te_edge) (incoming_edges_for fargs reach fm c bid_src) /\
      tenv_sound te_edge env1 /\
      (forall bk_src : block dtyp,
         find_block (blks c) bid_src = Some bk_src ->
         tenv_subsumes
           (lookup_fwd bid_src fm)
           (step_tenv_phis_from bid_from (blk_phis bk_src) te_edge) = true /\
         let '(live_code_s, bk_dce_s) :=
           dce_block_info fargs reach fm lm c bk_src in
         env_agree_on
           (edge_live_req bid_from (blk_phis bk_dce_s) live_code_s)
           env1 env2).

  Lemma dce_cfg_once_sim
    (fargs : list local_id) (c : CFG.cfg dtyp)
    (env : @local_env PaV) (va : option (@ptr PaV)) :
    (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
      env env (denote_cfg c va) (denote_cfg (dce_cfg_once fargs c) va).
  Proof.
    intros Henv; unfold dce_cfg_once; cbn zeta.
    destruct (cfg_no_block_addresses c && nodup_raw_ids (List.map blk_id (blks c)));
      [| apply denote_cfg_refl_sim].
    set (reach := compute_reach c).
    set (fm := compute_fwd_tenv fargs reach c).
    set (lm := compute_live_out fargs reach fm c).
    destruct (check_fwd_cfg fargs reach fm c) eqn:Efwd; cbn [andb];
      [| apply denote_cfg_refl_sim].
    destruct (check_live_cfg fargs reach fm lm c) eqn:Elive;
      [| apply denote_cfg_refl_sim].
    unfold denote_cfg, denote_cfg_map, denote_ocfg_map; cbn [init blks].
    eapply cfg_local_sim_bind.
    - eapply (cfg_local_sim_iter
                (dce_iter_inv fargs reach fm lm c)
                (fun _ _ r1 r2 => r1 = r2)).
      + (* Loop body simulation *)
        intros env1 env2 [bid_from bid_src] s2
          (<- & Hreach & te_edge & Hin_edge & Hte_edge & Hbk_inv).
        rewrite !(@ocfg_map_find_block dtyp).
        rewrite (@find_block_map dtyp (dce_block fargs reach fm lm c)
                   (blks c) bid_src (dce_block_id fargs reach fm lm c)).
        destruct (find_block (blks c) bid_src) as [bk_src |] eqn:Efind;
          cbn [option_map].
        * pose proof (@find_block_has_id dtyp (blks c) bid_src bk_src Efind) as Hbid.
          pose proof (@find_block_In' dtyp (blks c) bid_src bk_src Efind) as Hin_bk.
          specialize (Hbk_inv bk_src Efind) as [Hsub_in Hag_in].
          subst bid_src.
          unfold dce_block; unfold dce_block_info in Hag_in |- *; cbn zeta in Hag_in |- *.
          rewrite Hreach in Hag_in |- *.
          set (te_in := lookup_fwd (blk_id bk_src) fm) in *.
          set (live_end := block_live_before_term bk_src lm) in *.
          set (edges := incoming_edges_for fargs reach fm c (blk_id bk_src)) in *.
          pose proof (dce_code_sim (blk_code bk_src) va te_in live_end) as Hcode_sim.
          destruct (dce_code te_in (blk_code bk_src) live_end) as [live_code code'].
          cbn [snd blk_phis] in Hag_in |- *.
          eapply cfg_local_sim_bind with
            (RR := fun e1_t e2_t bd1 bd2 =>
                     bd1 = bd2 /\
                     match bd1 with
                     | inl bid_tgt =>
                         In bid_tgt (block_successors bk_src) /\
                         tenv_sound
                           (step_tenv_term (blk_term bk_src) bid_tgt
                              (step_tenv_code te_in (blk_code bk_src)))
                           e1_t /\
                         env_agree_on (lookup_live (blk_id bk_src) lm) e1_t e2_t
                     | inr _ => True
                     end).
          -- (* Block body: phis ;; code ;; term *)
             unfold denote_block; cbn [blk_phis blk_code blk_term].
             eapply cfg_local_sim_bind;
               [exact (dce_phis_sim edges bid_from te_edge live_code
                         (blk_phis bk_src) env1 env2 Hin_edge Hte_edge Hag_in) |].
             intros e1_p e2_p _ _ [Hte_p Hag_p].
             assert (Hte_in : tenv_sound te_in e1_p)
               by exact (tenv_sound_subsumes _ _ e1_p Hsub_in Hte_p).
             eapply cfg_local_sim_bind;
               [exact (Hcode_sim e1_p e2_p Hte_in Hag_p) |].
             intros e1_c e2_c _ _ [Hte_c Hag_c].
             unfold live_end, block_live_before_term in Hag_c.
             unfold block_successors.
             pose proof (cfg_local_sim_denote_terminator_sync
                           (step_tenv_code te_in (blk_code bk_src))
                           (lookup_live (blk_id bk_src) lm)
                           e1_c e2_c (blk_term bk_src)) as Hterm_sim.
             destruct (blk_term bk_src) as [[tiid tm] tmd].
             eapply cfg_local_sim_weaken;
               [| exact (Hterm_sim Hte_c Hag_c)].
             intros e1_t e2_t bd1 bd2 (_ & <- & Hbd); exact (conj Logic.eq_refl Hbd).
          -- (* Transition to next block or return *)
             intros e1_t e2_t [bid_tgt | dv] _ [<- Hbd].
             ++ destruct Hbd as (Hsucc & Hte_next & Hag_out).
                apply cfg_local_sim_ret; cbn [iter_step_rel].
                destruct (check_fwd_cfg_edge fargs reach fm c bk_src bid_tgt
                            Efwd Hin_bk Hreach Hsucc) as [Hreach_tgt Hfwd_tgt].
                split; [reflexivity | split; [exact Hreach_tgt |]].
                exists (step_tenv_term (blk_term bk_src) bid_tgt
                          (step_tenv_code te_in (blk_code bk_src))).
                split.
                ** unfold incoming_edges_for; apply in_or_app; right.
                   apply in_flat_map; exists bk_src; split; [exact Hin_bk |].
                   rewrite Hreach, (proj2 (in_raw_ids_spec bid_tgt _) Hsucc); cbn [andb].
                   left; reflexivity.
                ** split; [exact Hte_next |].
                   intros bk_tgt Efind_tgt.
                   split; [exact (Hfwd_tgt bk_tgt Efind_tgt) |].
                   pose proof (check_live_cfg_edge fargs reach fm lm c
                                 bk_src bk_tgt bid_tgt
                                 Elive Hin_bk Hreach Hsucc Efind_tgt) as Hsub_live.
                   destruct (dce_block_info fargs reach fm lm c bk_tgt)
                     as [live_code_t bk_dce_t].
                   exact (env_agree_on_subset _ _ e1_t e2_t
                            (raw_ids_subset_spec _ _ Hsub_live) Hag_out).
             ++ apply cfg_local_sim_ret; cbn [iter_step_rel]; reflexivity.
        * apply cfg_local_sim_ret; cbn [iter_step_rel]; reflexivity.
      + (* Initial state invariant *)
        destruct (check_fwd_cfg_init fargs reach fm c Efwd) as [Hreach_init Hfwd_init].
        split; [reflexivity | split; [exact Hreach_init |]].
        exists (init_tenv fargs).
        split.
        * unfold incoming_edges_for; rewrite raw_id_eqb_refl; left; reflexivity.
        * split; [exact (init_tenv_sound fargs env Henv) |].
          intros bk_init Efind_init.
          split; [exact (Hfwd_init bk_init Efind_init) |].
          destruct (dce_block_info fargs reach fm lm c bk_init).
          apply env_agree_on_refl.
    - intros ? ? [bid | uv] _ <-;
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_ret; reflexivity].
  Qed.

End DCESoundness.

(** * 9. Module-Level Dead Code Elimination Pass & Soundness Theorem *)

Definition dce_mcfg_once (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  map_mcfg_with_args dce_cfg_once M.

Lemma dce_mcfg_once_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (dce_mcfg_once M).
Proof.
  intros IP IPT M.
  exact (@lift_cfg_with_args_local_pass IP IPT
           dce_cfg_once
           dce_cfg_once_block_addresses
           (@dce_cfg_once_sim IP IPT)
           M).
Qed.

(** Three rounds of whole-CFG backward/forward DCE eliminate multi-block and
    cyclic dead [Phi]/[INSTR_Op] chains in a single pass invocation. *)
Definition dce_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  dce_mcfg_once (dce_mcfg_once (dce_mcfg_once M)).

Definition dce_mcfg_typ (M : CFG.mcfg typ) : CFG.mcfg dtyp :=
  dce_mcfg (convert_types M).

Theorem dce_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (dce_mcfg M).
Proof.
  intros IP IPT M; unfold dce_mcfg.
  eapply (@prog_refines_trans IP IPT); [apply dce_mcfg_once_refines |].
  eapply (@prog_refines_trans IP IPT); [apply dce_mcfg_once_refines |].
  apply dce_mcfg_once_refines.
Qed.
