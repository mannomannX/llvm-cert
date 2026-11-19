(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Control-Flow Graph Simplification ([CertPasses.SimplifyCFG])

    Implements and proves whole-program refinement ([prog_refines]) for three
    composable control-flow optimizations over [CFG.mcfg dtyp]:
    1. Constant Terminator Folding ([fold_const_term_mcfg]): folds constant
       boolean/integer [TERM_Br] and constant integer [TERM_Switch] terminators
       to unconditional [TERM_Br_1] branches.
    2. Unreachable Block & Phi-Edge Elimination ([elim_unreachable_mcfg]):
       computes reachable blocks from [init c], validates reachability closure,
       removes unreachable blocks, and prunes dead incoming phi edges.
    3. Iterated Single-Predecessor Block Coalescing ([coalesce_mcfg]):
       boundedly merges linear block pairs [(b1, b2)] where [b1] branches
       unconditionally to non-entry, phi-free [b2] as its unique predecessor,
       updating downstream phi predecessors without shadowing. *)

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
  Eq.Eqit
  Basics.HeterogeneousRelations.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads
  Core.RelDec
  Programming.Eqv.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  ScopeTheory
  Utils.rutt_cutoff
  Theory.Equational
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Implementations.ParamsV.

From CertPasses Require Import PassCommon.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.

(** * 1. Combinatorial, Lookup, Block-Address, & [refine_cfg] Helpers *)

Fixpoint nodup_raw_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (in_raw_ids x rest) && nodup_raw_ids rest
  end.

Lemma nodup_raw_ids_spec (xs : list raw_id) :
  nodup_raw_ids xs = true <-> NoDup xs.
Proof.
  induction xs as [| x rest IH]; cbn [nodup_raw_ids].
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite Bool.andb_true_iff, Bool.negb_true_iff, in_raw_ids_false, IH.
    split.
    + intros [Hnin Hnd]; constructor; assumption.
    + intros Hnd; inversion Hnd; subst; split; assumption.
Qed.

(** Vanilla-CIC UIP on [positive] via Hedberg's construction over [Pos.eq_dec]. *)
Definition pos_eq_canon {x y : positive} (H : x = y) : x = y :=
  match Pos.eq_dec x y with
  | left Heq => Heq
  | right Hneq => False_rect _ (Hneq H)
  end.

Lemma pos_eq_canon_irrel {x y : positive} (H1 H2 : x = y) :
  pos_eq_canon H1 = pos_eq_canon H2.
Proof.
  unfold pos_eq_canon.
  destruct (Pos.eq_dec x y) as [Heq | Hneq].
  - reflexivity.
  - exfalso; exact (Hneq H1).
Qed.

Lemma eq_trans_sym_l {A : Type} {a b : A} (p : a = b) :
  eq_trans (eq_sym p) p = eq_refl.
Proof.
  destruct p; reflexivity.
Qed.

Lemma pos_eq_trans_canon {x y : positive} (H : x = y) :
  eq_trans (eq_sym (pos_eq_canon (@eq_refl positive x))) (pos_eq_canon H) = H.
Proof.
  destruct H; apply eq_trans_sym_l.
Qed.

Lemma pos_uip {x : positive} (H : x = x) :
  H = eq_refl.
Proof.
  rewrite <- (pos_eq_trans_canon H).
  rewrite (pos_eq_canon_irrel H (@eq_refl positive x)).
  apply eq_trans_sym_l.
Qed.

(** [assoc] characterization over [raw_id] (independent of [simpl never]). *)
Lemma assoc_raw_id_nil {B : Type} (x : raw_id) :
  @assoc raw_id B eq_dec_raw_id x [] = None.
Proof.
  reflexivity.
Qed.

Lemma assoc_raw_id_cons {B : Type} (x k : raw_id) (v : B) (rest : list (raw_id * B)) :
  @assoc raw_id B eq_dec_raw_id x ((k, v) :: rest) =
    if raw_id_eqb x k then Some v else @assoc raw_id B eq_dec_raw_id x rest.
Proof.
  unfold assoc at 1; cbv beta iota.
  fold (@assoc raw_id B eq_dec_raw_id).
  unfold rel_dec, eq_dec_raw_id, RelDec_from_dec, raw_id_eqb.
  destruct (RawIDOrd.eq_dec x k); reflexivity.
Qed.

Lemma assoc_block_id_cons {B : Type} (x k : block_id) (v : B) (rest : list (block_id * B)) :
  @assoc block_id B eq_dec_raw_id x ((k, v) :: rest) =
    if raw_id_eqb x k then Some v else @assoc block_id B eq_dec_raw_id x rest.
Proof.
  exact (@assoc_raw_id_cons B x k v rest).
Qed.

(** [find_block] lookup lemmas over filtered and duplicate-free block lists. *)
Lemma find_block_filter_id (p : raw_id -> bool) (bks : ocfg dtyp) (x : block_id)
  (Hx : p x = true) :
  find_block (List.filter (fun b => p (blk_id b)) bks) x = find_block bks x.
Proof.
  induction bks as [| b rest IH]; [reflexivity |].
  cbn [List.filter].
  destruct (RawIDOrd.eq_dec (blk_id b) x) as [Heq | Hneq].
  - rewrite Heq, Hx; cbv iota.
    rewrite !find_block_eq by exact Heq.
    reflexivity.
  - rewrite find_block_ineq by exact Hneq.
    destruct (p (blk_id b)); cbv iota.
    + rewrite find_block_ineq by exact Hneq; exact IH.
    + exact IH.
Qed.

Lemma find_block_nodup_in (bks : ocfg dtyp) (b : block dtyp)
  (Hnd : NoDup (List.map blk_id bks))
  (Hin : In b bks) :
  find_block bks (blk_id b) = Some b.
Proof.
  induction bks as [| hd rest IH]; [contradiction |].
  cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
  destruct Hin as [<- | Hin].
  - apply find_block_eq; reflexivity.
  - assert (Hneq : blk_id hd <> blk_id b).
    { intros Heq; apply Hnin; rewrite Heq; apply in_map, Hin. }
    rewrite find_block_ineq by exact Hneq.
    apply IH; assumption.
Qed.

(** List and [block_block_addresses] emptiness lemmas. *)
Lemma list_app_nil_iff {A : Type} (l1 l2 : list A) :
  (l1 ++ l2)%list = [] <-> l1 = [] /\ l2 = [].
Proof.
  destruct l1 as [| a l1']; cbn [app].
  - split; [intros ->; split; reflexivity | intros [_ ->]; reflexivity].
  - split; [intros H; discriminate H | intros [H _]; discriminate H].
Qed.

Lemma flat_map_eq_nil_iff {A B : Type} (f : A -> list B) (xs : list A) :
  flat_map f xs = [] <-> (forall x, In x xs -> f x = []).
Proof.
  induction xs as [| x rest IH]; cbn [flat_map In].
  - split; [intros _ ? [] | intros _; reflexivity].
  - rewrite list_app_nil_iff, IH.
    split.
    + intros [Hx Hrest] y [<- | Hy]; [exact Hx | apply Hrest, Hy].
    + intros Hall; split;
        [apply Hall; left; reflexivity | intros y Hy; apply Hall; right; exact Hy].
Qed.

Lemma block_block_addresses_nil_iff (b : block dtyp) :
  block_block_addresses b = [] <->
  flat_map (fun '(_, Phi _ _ pargs, _) =>
              flat_map (fun x => exp_block_addresses (snd x)) pargs) (blk_phis b) = [] /\
  flat_map (fun '(_, i, _) => instr_block_addresses i) (blk_code b) = [] /\
  (let '(_, tm, _) := blk_term b in term_block_addresses tm) = [].
Proof.
  unfold block_block_addresses.
  rewrite !list_app_nil_iff; tauto.
Qed.

(** [refine_cfg] rewriting & effect helpers. *)
Lemma refine_cfg_eq_itree_l {Pa : Params} {R1 R2} (RR : R1 -> R2 -> Prop)
  (t1 t1' : CFGtop R1) (t2 : CFGtop R2) :
  t1 ≅ t1' ->
  refine_cfg RR t1' t2 ->
  refine_cfg RR t1 t2.
Proof.
  unfold refine_cfg; intros Heq Href; rewrite Heq; exact Href.
Qed.

Lemma refine_cfg_eq_itree_r {Pa : Params} {R1 R2} (RR : R1 -> R2 -> Prop)
  (t1 : CFGtop R1) (t2 t2' : CFGtop R2) :
  t2 ≅ t2' ->
  refine_cfg RR t1 t2' ->
  refine_cfg RR t1 t2.
Proof.
  unfold refine_cfg; intros Heq Href; rewrite Heq; exact Href.
Qed.

Lemma refine_cfg_raise {Pa : Params} {R1 R2} (RR : R1 -> R2 -> Prop) (s1 s2 : string) :
  refine_cfg RR (raise s1) (raise s2).
Proof.
  unfold refine_cfg, raise, trigger_cast.
  eapply ruttc_trigger';
    [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
Qed.

Lemma refine_cfg_raiseUB {Pa : Params} {R1 R2} (RR : R1 -> R2 -> Prop)
  (s : string) (t2 : CFGtop R2) :
  refine_cfg RR (raiseUB s) t2.
Proof.
  unfold refine_cfg, raiseUB, trigger_cast.
  apply ruttc_trigger_cutl; exact (CutUB_rel (print_msg s)).
Qed.

Lemma refine_cfg_raiseLLVM {Pa : Params} {R1 R2} (RR : R1 -> R2 -> Prop)
  (exn : @dvalue Pa) :
  refine_cfg RR (raiseLLVM exn) (raiseLLVM exn).
Proof.
  unfold refine_cfg, raiseLLVM, trigger_cast.
  eapply ruttc_trigger'; [apply EqE_CFG_refl | intros [] [] _].
Qed.

Lemma denote_phis_nil {Pa : Params} (from : block_id) :
  @denote_phis Pa from [] ≅ Ret tt.
Proof.
  unfold denote_phis; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
  rewrite Eqit.bind_ret_l; cbn [map_monad ExtLib.Structures.Monad.ret Monad_itree].
  rewrite Eqit.bind_ret_l; reflexivity.
Qed.

(** Switch-table evaluation & terminator output postcondition under [refine_cfg]. *)
Definition eval_one_switch_dest {Pa : Params}
  (d : tint_literal * block_id) : @dvalue Pa * block_id :=
  let '(TInt_Literal sz x, id) := d in
  (DVALUE_Base (@DVALUE_I Pa sz (@Integers.repr sz (denote_int_syntax x))), id).

Lemma eval_switch_dests {Pa : Params} (dests : list (tint_literal * block_id)) :
  map_monad (m := EOU)
    (fun '((TInt_Literal sz x), id) =>
       ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                   (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
    dests
  = raise_ret (List.map (@eval_one_switch_dest Pa) dests).
Proof.
  induction dests as [| [[sz x] id] rest IH]; [reflexivity |].
  cbn [map_monad List.map eval_one_switch_dest coerce_integer_to_int ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad] in IH |- *.
  rewrite IH; reflexivity.
Qed.

Lemma switch_dests_snd {Pa : Params} (dests : list (tint_literal * block_id)) :
  List.map snd (List.map (@eval_one_switch_dest Pa) dests) = List.map snd dests.
Proof.
  induction dests as [| [[sz x] id] rest IH]; [reflexivity |].
  cbn [List.map eval_one_switch_dest snd]; f_equal; exact IH.
Qed.

Lemma select_switch_in {Pa : Params} (sel : @dvalue Pa) (def : block_id)
  (sws : list (@dvalue Pa * block_id)) (bid : block_id) :
  select_switch sel def sws = raise_ret bid ->
  bid = def \/ In bid (List.map snd sws).
Proof.
  induction sws as [| [v id] rest IH]; cbn [select_switch List.map snd].
  - intros H; inversion H; left; reflexivity.
  - destruct sel as [[p1 | sz1 i1 | ip1 | d1 | f1 | | | bsz1 bv1] | ? ? | ? ?];
      try (intros H; discriminate H).
    destruct v as [[p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2] | ? ? | ? ?];
      try (intros H; discriminate H).
    cbn [select_switch].
    destruct (Pos.eq_dec sz1 sz2) as [Heq | Hneq]; [subst sz2 | intros H; discriminate H].
    cbn [eq_rec_r eq_rec eq_rect_r eq_rect eq_ind eq_ind_r eq_sym ExtLib.Structures.Monad.ret EOU_monad].
    destruct (VellvmIntegers.cmp Ceq i1 i2).
    + intros H; inversion H; right; left; reflexivity.
    + intros H; destruct (IH H) as [Heq | Hin];
        [left; exact Heq | right; right; exact Hin].
Qed.

Lemma refine_cfg_terminator_outputs {Pa : Params}
  (trm : instr_id * terminator dtyp * list (metadata dtyp)) :
  refine_cfg
    (sum_rel
       (fun id1 id2 => id1 = id2 /\ In id1 (let '(_, tm, _) := trm in terminator_outputs tm))
       Logic.eq)
    (denote_terminator trm)
    (denote_terminator trm).
Proof.
  destruct trm as [[iid tm] md].
  unfold denote_terminator.
  destruct tm as
    [ [dt op]
    |
    | [dt op] br1 br2
    | br
    | [dt e] default_br dests
    | [dt addr] brs fn
    | [dt expr]
    | [dt fnptrval] cargs to_lbl unwind_lbl anns obs
    | ].
  - (* TERM_Ret *)
    eapply ruttc_bind; [apply refine_cfg_refl | intros dv _ <-].
    apply ruttc_ret; constructor; reflexivity.
  - (* TERM_Ret_void *)
    apply ruttc_ret; constructor; reflexivity.
  - (* TERM_Br *)
    eapply ruttc_bind; [apply refine_cfg_refl | intros v _ <-].
    destruct v as [[p | sz bit | ip | d | f | | | bsz bv] | ? ? | ? ?];
      lazymatch goal with
      | |- ruttc _ _ _ _ _ (raise _) (raise _) => apply refine_cfg_raise
      | _ => idtac
      end.
    + destruct sz as [? | ? | ];
        lazymatch goal with
        | |- ruttc _ _ _ _ _ (raise _) (raise _) => apply refine_cfg_raise
        | _ => idtac
        end.
      destruct (VellvmIntegers.equ bit VellvmIntegers.one).
      * apply ruttc_ret; constructor; split; [reflexivity | cbn; left; reflexivity].
      * apply ruttc_ret; constructor; split; [reflexivity | cbn; right; left; reflexivity].
    + apply refine_cfg_raiseUB.
  - (* TERM_Br_1 *)
    apply ruttc_ret; constructor; split; [reflexivity | cbn; left; reflexivity].
  - (* TERM_Switch *)
    eapply ruttc_bind; [apply refine_cfg_refl | intros sel _ <-].
    destruct (dvalue_is_poison sel); [apply refine_cfg_raiseUB |].
    eapply ruttc_bind.
    + apply refine_EOU_to_cfg with
        (RR := fun b1 b2 => b1 = b2 /\ (b1 = default_br \/ In b1 (List.map snd dests))).
      rewrite eval_switch_dests; cbn [ExtLib.Structures.Monad.bind EOU_monad].
      destruct (select_switch sel default_br (List.map (@eval_one_switch_dest Pa) dests))
        as [err | oom | ub | bid] eqn:Esel; constructor.
      split; [reflexivity |].
      apply select_switch_in in Esel.
      rewrite switch_dests_snd in Esel; exact Esel.
    + intros bid1 bid2 [<- Hin].
      cbn [ExtLib.Structures.Monad.ret Monad_itree].
      apply ruttc_ret; constructor 1; split;
        [reflexivity | cbn; destruct Hin as [-> | Hin]; [left; reflexivity | right; exact Hin]].
  - (* TERM_IndirectBr *)
    eapply ruttc_bind; [apply refine_cfg_refl | intros a _ <-].
    destruct (dvalue_is_poison a); [apply refine_cfg_raiseUB |].
    destruct fn as [f |]; [| apply refine_cfg_raise].
    eapply ruttc_bind; [apply refine_cfg_refl | intros addrs _ <-].
    destruct (dvalue_ptr_address a) as [z |]; [| apply refine_cfg_raise].
    destruct (indirectbr_target z (combine brs addrs)) as [b |] eqn:Eib;
      [| apply refine_cfg_raiseUB].
    apply ruttc_ret; constructor; split;
      [reflexivity | cbn; eapply indirectbr_target_In; exact Eib].
  - (* TERM_Resume *)
    eapply ruttc_bind; [apply refine_cfg_refl | intros exn _ <-].
    apply refine_cfg_raiseLLVM.
  - (* TERM_Invoke *)
    eapply ruttc_bind; [apply refine_cfg_refl | intros uvs _ <-].
    eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
    eapply ruttc_bind; [apply refine_cfg_refl | intros fv _ <-].
    eapply ruttc_bind; [apply refine_cfg_refl | intros rv0 _ <-].
    eapply ruttc_bind; [apply refine_cfg_refl | intros rv _ <-].
    destruct rv as [exn | retv].
    + eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
      apply ruttc_ret; constructor; split;
        [reflexivity | cbn; right; left; reflexivity].
    + eapply ruttc_bind; [destruct iid; apply refine_cfg_refl | intros [] _ <-].
      apply ruttc_ret; constructor; split;
        [reflexivity | cbn; left; reflexivity].
  - (* TERM_Unreachable *)
    apply refine_cfg_raiseUB.
Qed.

(** * 2. Sub-Pass A: Constant Terminator Folding ([fold_const_term_cfg]) *)

Fixpoint find_switch_dest (sz : positive) (val : @Integers.bit_int sz)
  (default_br : block_id) (dests : list (tint_literal * block_id)) : option block_id :=
  match dests with
  | [] => Some default_br
  | (TInt_Literal sz' x', target) :: rest =>
      if Pos.eqb sz sz' then
        if @Integers.cmp sz Ceq val (@Integers.repr sz (denote_int_syntax x'))
        then Some target
        else find_switch_dest sz val default_br rest
      else None
  end.

Definition fold_const_term_tm (tm : terminator dtyp) : terminator dtyp :=
  match tm with
  | TERM_Br (DTYPE_Base (DTYPE_I 1%positive), EXP_Bool true) br1 _ =>
      TERM_Br_1 br1
  | TERM_Br (DTYPE_Base (DTYPE_I 1%positive), EXP_Bool false) _ br2 =>
      TERM_Br_1 br2
  | TERM_Br (DTYPE_Base (DTYPE_I 1%positive), EXP_Integer x) br1 br2 =>
      if @Integers.eq 1%positive
           (@Integers.repr 1%positive (denote_int_syntax x))
           (@Integers.one 1%positive)
      then TERM_Br_1 br1
      else TERM_Br_1 br2
  | TERM_Switch (DTYPE_Base (DTYPE_I sz), EXP_Integer x) default_br dests =>
      match find_switch_dest sz (@Integers.repr sz (denote_int_syntax x)) default_br dests with
      | Some target => TERM_Br_1 target
      | None => tm
      end
  | _ => tm
  end.

Definition fold_const_term_trm
  (trm : instr_id * terminator dtyp * list (metadata dtyp))
  : instr_id * terminator dtyp * list (metadata dtyp) :=
  let '(iid, tm, md) := trm in
  (iid, fold_const_term_tm tm, md).

Definition fold_const_term_block (b : block dtyp) : block dtyp :=
  {| blk_id       := blk_id b;
     blk_phis     := blk_phis b;
     blk_code     := blk_code b;
     blk_term     := fold_const_term_trm (blk_term b);
     blk_comments := blk_comments b |}.

Definition fold_const_term_cfg (c : CFG.cfg dtyp) : CFG.cfg dtyp :=
  if cfg_no_block_addresses c then
    {| init := init c;
       blks := List.map fold_const_term_block (blks c);
       args := args c |}
  else c.

Definition fold_const_term_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  map_mcfg_cfg fold_const_term_cfg M.

Lemma find_switch_dest_sound {Pa : Params} (sz : positive) (val : @Integers.bit_int sz)
  (default_br : block_id) (dests : list (tint_literal * block_id)) (target : block_id) :
  find_switch_dest sz val default_br dests = Some target ->
  select_switch (DVALUE_Base (@DVALUE_I Pa sz val)) default_br
    (List.map (@eval_one_switch_dest Pa) dests) = raise_ret target.
Proof.
  induction dests as [| [[sz' x'] id] rest IH];
    cbn [find_switch_dest List.map eval_one_switch_dest select_switch].
  - intros H; inversion H; reflexivity.
  - destruct (Pos.eqb sz sz') eqn:Esz; [| intros H; discriminate H].
    apply Pos.eqb_eq in Esz; subst sz'.
    destruct (Pos.eq_dec sz sz) as [Heq | Hneq]; [| exfalso; exact (Hneq eq_refl)].
    rewrite (pos_uip Heq); cbn [eq_rec_r eq_rec eq_rect_r eq_rect eq_ind eq_ind_r eq_sym VellvmIntegers.cmp VellvmIntegers.VInt_Bounded].
    destruct (@Integers.cmp sz Ceq val (@Integers.repr sz (denote_int_syntax x'))).
    + intros H; inversion H; reflexivity.
    + exact IH.
Qed.

Lemma denote_terminator_fold_const {Pa : Params}
  (trm : instr_id * terminator dtyp * list (metadata dtyp)) :
  @denote_terminator Pa trm ≅ @denote_terminator Pa (fold_const_term_trm trm).
Proof.
  destruct trm as [[iid tm] md]; cbn [fold_const_term_trm].
  destruct tm as
    [ [dt op]
    |
    | [dt op] br1 br2
    | br
    | [dt e] default_br dests
    | [dt addr] brs fn
    | [dt expr]
    | [dt fnptrval] cargs to_lbl unwind_lbl anns obs
    | ]; try reflexivity.
  - (* TERM_Br *)
    destruct dt as [[sz | | | | | | | | | | ] | ? ? | ? ? ?]; try reflexivity.
    destruct sz as [? | ? | ]; try reflexivity.
    destruct op; try reflexivity.
    + (* EXP_Integer *)
      cbn [fold_const_term_tm].
      unfold denote_terminator, denote_exp', withCall.
      cbn [denote_exp denote_int_syntax_as_int coerce_integer_to_int
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad EOU_to_itree Monad_itree].
      rewrite translate_ret, Eqit.bind_ret_l.
      cbv iota; cbn [VellvmIntegers.equ VellvmIntegers.repr VellvmIntegers.one VellvmIntegers.VInt_Bounded].
      destruct (@Integers.eq 1%positive
                  (@Integers.repr 1%positive (denote_int_syntax x))
                  (@Integers.one 1%positive)); reflexivity.
    + (* EXP_Bool *)
      destruct b; cbn [fold_const_term_tm];
        unfold denote_terminator, denote_exp', withCall;
        cbn [denote_exp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite translate_ret, Eqit.bind_ret_l;
        reflexivity.
  - (* TERM_Switch *)
    destruct dt as [[sz | | | | | | | | | | ] | ? ? | ? ? ?]; try reflexivity.
    destruct e; try reflexivity.
    cbn [fold_const_term_tm].
    destruct (find_switch_dest sz (@Integers.repr sz (denote_int_syntax x)) default_br dests)
      as [target |] eqn:Efind; [| reflexivity].
    unfold denote_terminator, denote_exp', withCall.
    rewrite eval_switch_dests.
    cbn [denote_exp denote_int_syntax_as_int
         ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad EOU_to_itree Monad_itree].
    unfold coerce_integer_to_int at 1.
    cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad EOU_to_itree Monad_itree].
    rewrite translate_ret, Eqit.bind_ret_l.
    cbn [dvalue_is_poison VellvmIntegers.repr VellvmIntegers.VInt_Bounded].
    rewrite (find_switch_dest_sound sz _ default_br dests target Efind).
    cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l; reflexivity.
Qed.

Lemma denote_block_fold_const {Pa : Params}
  (b : block dtyp) (from : block_id) (va : option (@ptr (@PROV Pa) (@PTR Pa))) :
  denote_block b from va ≅ denote_block (fold_const_term_block b) from va.
Proof.
  unfold denote_block, fold_const_term_block; cbn [blk_phis blk_code blk_term].
  eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ <-].
  eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ <-].
  apply denote_terminator_fold_const.
Qed.

Lemma term_block_addresses_fold_const (tm : terminator dtyp) :
  term_block_addresses (fold_const_term_tm tm) = term_block_addresses tm.
Proof.
  destruct tm as
    [ [dt op]
    |
    | [dt op] br1 br2
    | br
    | [dt e] default_br dests
    | [dt addr] brs fn
    | [dt expr]
    | [dt fnptrval] cargs to_lbl unwind_lbl anns obs
    | ]; try reflexivity.
  - destruct dt as [[sz | | | | | | | | | | ] | ? ? | ? ? ?]; try reflexivity.
    destruct sz as [? | ? | ]; try reflexivity.
    destruct op; try reflexivity.
    + cbn [fold_const_term_tm].
      destruct (@Integers.eq 1%positive
                  (@Integers.repr 1%positive (denote_int_syntax x))
                  (@Integers.one 1%positive)); reflexivity.
    + destruct b; reflexivity.
  - destruct dt as [[sz | | | | | | | | | | ] | ? ? | ? ? ?]; try reflexivity.
    destruct e; try reflexivity.
    cbn [fold_const_term_tm].
    destruct (find_switch_dest sz (@Integers.repr sz (denote_int_syntax x)) default_br dests);
      reflexivity.
Qed.

Lemma fold_const_term_cfg_block_addresses (c : CFG.cfg dtyp) :
  flat_map block_block_addresses (blks (fold_const_term_cfg c)) =
  flat_map block_block_addresses (blks c).
Proof.
  unfold fold_const_term_cfg.
  destruct (cfg_no_block_addresses c); [| reflexivity].
  cbn [blks].
  induction (blks c) as [| b rest IH]; [reflexivity |].
  cbn [List.map flat_map].
  rewrite IH; f_equal.
  unfold block_block_addresses, fold_const_term_block; cbn [blk_phis blk_code blk_term].
  destruct (blk_term b) as [[iid tm] md]; cbn [fold_const_term_trm].
  rewrite term_block_addresses_fold_const; reflexivity.
Qed.

Lemma denote_cfg_fold_const {Pa : Params}
  (c : CFG.cfg dtyp) (va : option (@ptr (@PROV Pa) (@PTR Pa))) :
  refine_cfg Logic.eq (denote_cfg c va) (denote_cfg (fold_const_term_cfg c) va).
Proof.
  unfold fold_const_term_cfg.
  destruct (cfg_no_block_addresses c); [cbv iota | apply refine_cfg_refl].
  unfold denote_cfg, denote_cfg_map; cbn [init blks].
  eapply ruttc_bind with (RR := Logic.eq).
  - unfold denote_ocfg_map, refine_cfg.
    eapply ruttc_iter with (II := Logic.eq); [| reflexivity].
    intros [from src] _ <-; cbv beta iota.
    rewrite !ocfg_map_find_block, find_block_map by (intros ?; reflexivity).
    destruct (find_block (blks c) src) as [bk |]; cbn [option_map]; cbv iota.
    + eapply ruttc_bind.
      * eapply (refine_cfg_eq_itree_r Logic.eq);
          [symmetry; apply denote_block_fold_const | apply refine_cfg_refl].
      * intros [tgt | dv] _ <-; cbv beta iota; apply ruttc_ret; constructor; reflexivity.
    + apply ruttc_ret; constructor; reflexivity.
  - intros [bid | uv] _ <-; cbv beta iota;
      [apply refine_cfg_raise | apply ruttc_ret; reflexivity].
Qed.

Theorem fold_const_term_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (fold_const_term_mcfg M).
Proof.
  intros IP IPT M.
  apply lift_cfg_pass.
  - exact fold_const_term_cfg_block_addresses.
  - intros c va; apply denote_cfg_fold_const.
Qed.

(** * 3. Sub-Pass B: Unreachable Block & Phi-Edge Elimination ([elim_unreachable_cfg]) *)

Definition add_unique_ids (xs acc : list raw_id) : list raw_id :=
  List.fold_left (fun a x => if in_raw_ids x a then a else x :: a) xs acc.

Fixpoint reach_loop (bks : ocfg dtyp) (fuel : nat) (vis : list raw_id) : list raw_id :=
  match fuel with
  | O => vis
  | S fuel' =>
      let next :=
        List.fold_left
          (fun acc b =>
             if in_raw_ids (blk_id b) acc
             then add_unique_ids (successors b) acc
             else acc)
          bks vis
      in
      if Nat.eqb (List.length next) (List.length vis)
      then next
      else reach_loop bks fuel' next
  end.

Definition compute_reachable (c : CFG.cfg dtyp) : list raw_id :=
  reach_loop (blks c) (S (List.length (blks c))) [init c].

(** Boolean reachability-closure validator ([PS-10]): soundness relies solely
    on [check_reach_closed c reach = true], decoupling verification from the
    fixed-point traversal heuristic. *)
Definition check_reach_closed (c : CFG.cfg dtyp) (reach : list raw_id) : bool :=
  in_raw_ids (init c) reach &&
  List.forallb
    (fun b =>
       if in_raw_ids (blk_id b) reach
       then List.forallb (fun s => in_raw_ids s reach) (successors b)
       else true)
    (blks c).

Definition prune_phi_entry (reach : list raw_id)
  (entry : local_id * phi dtyp * list (metadata dtyp))
  : local_id * phi dtyp * list (metadata dtyp) :=
  let '(lid, Phi fm dt pargs, mds) := entry in
  (lid, Phi fm dt (List.filter (fun '(pred, _) => in_raw_ids pred reach) pargs), mds).

Definition prune_block_phis (reach : list raw_id) (b : block dtyp) : block dtyp :=
  {| blk_id       := blk_id b;
     blk_phis     := List.map (prune_phi_entry reach) (blk_phis b);
     blk_code     := blk_code b;
     blk_term     := blk_term b;
     blk_comments := blk_comments b |}.

Definition elim_unreachable_cfg (c : CFG.cfg dtyp) : CFG.cfg dtyp :=
  if cfg_no_block_addresses c then
    let reach := compute_reachable c in
    if check_reach_closed c reach then
      {| init := init c;
         blks := List.map (prune_block_phis reach)
                   (List.filter (fun b => in_raw_ids (blk_id b) reach) (blks c));
         args := args c |}
    else c
  else c.

Definition elim_unreachable_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  map_mcfg_cfg elim_unreachable_cfg M.

Lemma assoc_filter_reach {B : Type} (reach : list raw_id) (from : block_id)
  (pargs : list (block_id * B))
  (Hfrom : in_raw_ids from reach = true) :
  assoc from (List.filter (fun '(pred, _) => in_raw_ids pred reach) pargs) =
  assoc from pargs.
Proof.
  induction pargs as [| [pred e] rest IH]; [reflexivity |].
  cbn [List.filter].
  rewrite (assoc_block_id_cons from pred e rest).
  destruct (raw_id_eqb from pred) eqn:Efp.
  - apply raw_id_eqb_spec in Efp; subst pred.
    rewrite Hfrom; cbv iota; rewrite assoc_block_id_cons, raw_id_eqb_refl; reflexivity.
  - destruct (in_raw_ids pred reach); cbv iota.
    + rewrite assoc_block_id_cons, Efp; exact IH.
    + exact IH.
Qed.

Lemma map_monad_denote_phi_prune {Pa : Params} (reach : list raw_id) (from : block_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  (Hfrom : in_raw_ids from reach = true) :
  map_monad (@denote_phi Pa from) (List.map (prune_phi_entry reach) phis) =
  map_monad (@denote_phi Pa from) phis.
Proof.
  induction phis as [| [[lid [fm dt pargs]] mds] rest IH]; [reflexivity |].
  cbn [List.map prune_phi_entry map_monad].
  assert (Hhd : @denote_phi Pa from
                  (lid, Phi fm dt (List.filter (fun '(pred, _) => in_raw_ids pred reach) pargs), mds)
                = @denote_phi Pa from (lid, Phi fm dt pargs, mds)).
  { unfold denote_phi; cbv beta iota zeta; rewrite (assoc_filter_reach reach from pargs Hfrom); reflexivity. }
  rewrite Hhd, IH; reflexivity.
Qed.

Lemma denote_phis_prune {Pa : Params} (reach : list raw_id) (from : block_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  (Hfrom : in_raw_ids from reach = true) :
  @denote_phis Pa from (List.map (prune_phi_entry reach) phis) =
  @denote_phis Pa from phis.
Proof.
  unfold denote_phis; rewrite (map_monad_denote_phi_prune reach from phis Hfrom); reflexivity.
Qed.

Lemma check_reach_closed_spec (c : CFG.cfg dtyp) (reach : list raw_id)
  (Hchk : check_reach_closed c reach = true) :
  in_raw_ids (init c) reach = true /\
  (forall b s,
     In b (blks c) ->
     in_raw_ids (blk_id b) reach = true ->
     In s (successors b) ->
     in_raw_ids s reach = true).
Proof.
  unfold check_reach_closed in Hchk.
  apply Bool.andb_true_iff in Hchk as [Hinit Hall].
  split; [exact Hinit |].
  intros b s Hb Hbr Hs.
  rewrite List.forallb_forall in Hall.
  specialize (Hall b Hb).
  rewrite Hbr in Hall; cbv iota in Hall; rewrite List.forallb_forall in Hall.
  apply Hall, Hs.
Qed.

Lemma prune_block_phis_block_addresses (reach : list raw_id) (b : block dtyp)
  (Hb : block_block_addresses b = []) :
  block_block_addresses (prune_block_phis reach b) = [].
Proof.
  apply block_block_addresses_nil_iff in Hb as (Hphis & Hcode & Hterm).
  apply block_block_addresses_nil_iff.
  cbn [prune_block_phis blk_phis blk_code blk_term].
  refine (conj _ (conj Hcode Hterm)).
  rewrite flat_map_eq_nil_iff in Hphis |- *.
  intros [[lid [fm dt pargs]] mds] Hin.
  apply in_map_iff in Hin as ([[lid0 [fm0 dt0 pargs0]] mds0] & Heq & Hin0).
  cbn [prune_phi_entry] in Heq; inversion Heq; subst.
  specialize (Hphis _ Hin0); cbv beta iota in Hphis |- *.
  rewrite flat_map_eq_nil_iff in Hphis |- *.
  intros [pred ex] Hfilt.
  apply filter_In in Hfilt as [Hin_arg _].
  exact (Hphis (pred, ex) Hin_arg).
Qed.

Lemma elim_unreachable_cfg_block_addresses (c : CFG.cfg dtyp) :
  flat_map block_block_addresses (blks (elim_unreachable_cfg c)) =
  flat_map block_block_addresses (blks c).
Proof.
  unfold elim_unreachable_cfg.
  destruct (cfg_no_block_addresses c) eqn:Eba; [cbv beta iota zeta | reflexivity].
  destruct (check_reach_closed c (compute_reachable c)); [cbv iota | reflexivity].
  apply cfg_no_block_addresses_nil in Eba.
  rewrite Eba; cbn [blks].
  rewrite flat_map_eq_nil_iff in Eba |- *.
  intros b' Hin.
  apply in_map_iff in Hin as (b & <- & Hfilt).
  apply filter_In in Hfilt as [Hb _].
  apply prune_block_phis_block_addresses, Eba, Hb.
Qed.

Lemma denote_cfg_elim_unreachable {Pa : Params}
  (c : CFG.cfg dtyp) (va : option (@ptr (@PROV Pa) (@PTR Pa))) :
  refine_cfg Logic.eq (denote_cfg c va) (denote_cfg (elim_unreachable_cfg c) va).
Proof.
  unfold elim_unreachable_cfg.
  destruct (cfg_no_block_addresses c); [cbv beta iota zeta | apply refine_cfg_refl].
  set (reach := compute_reachable c).
  destruct (check_reach_closed c reach) eqn:Echk; [cbv iota | apply refine_cfg_refl].
  destruct (check_reach_closed_spec c reach Echk) as [Hinit Hclosed].
  unfold denote_cfg, denote_cfg_map; cbn [init blks].
  eapply ruttc_bind with (RR := Logic.eq).
  - unfold denote_ocfg_map, refine_cfg.
    eapply ruttc_iter with
      (II := fun '(from1, src1) '(from2, src2) =>
               from1 = from2 /\ src1 = src2 /\
               in_raw_ids from1 reach = true /\
               in_raw_ids src1 reach = true).
    + intros [from1 src1] [from2 src2] (<- & <- & Hfrom & Hsrc); cbv beta iota.
      rewrite !ocfg_map_find_block.
      rewrite find_block_map by (intros ?; reflexivity).
      rewrite (find_block_filter_id (fun id => in_raw_ids id reach) (blks c) src1 Hsrc).
      destruct (find_block (blks c) src1) as [bk |] eqn:Efind; cbn [option_map]; cbv iota.
      * assert (Hin_bk : In bk (blks c)) by (eapply find_block_In'; exact Efind).
        assert (Hid_bk : src1 = blk_id bk) by (eapply find_block_has_id; exact Efind).
        eapply ruttc_bind.
        -- unfold denote_block; cbn [prune_block_phis blk_phis blk_code blk_term].
           rewrite (denote_phis_prune reach from1 (blk_phis bk) Hfrom).
           eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
           eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
           apply refine_cfg_terminator_outputs.
        -- intros bd1 bd2 Htrm;
             destruct Htrm as [t1 t2 [<- Hout] | v1 v2 <-]; cbv beta iota.
           ++ apply ruttc_ret; constructor.
              refine (conj eq_refl (conj eq_refl (conj Hsrc _))).
              eapply (Hclosed bk t1 Hin_bk);
                [rewrite <- Hid_bk; exact Hsrc | unfold successors; exact Hout].
           ++ apply ruttc_ret; constructor; reflexivity.
      * apply ruttc_ret; constructor; reflexivity.
    + exact (conj eq_refl (conj eq_refl (conj Hinit Hinit))).
  - intros [bid | uv] _ <-; cbv beta iota;
      [apply refine_cfg_raise | apply ruttc_ret; reflexivity].
Qed.

Theorem elim_unreachable_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (elim_unreachable_mcfg M).
Proof.
  intros IP IPT M.
  apply lift_cfg_pass.
  - exact elim_unreachable_cfg_block_addresses.
  - intros c va; apply denote_cfg_elim_unreachable.
Qed.

(** * 4. Sub-Pass C: Iterated Single-Predecessor Block Coalescing ([coalesce_mcfg]) *)

Definition is_nil_phis (ps : list (local_id * phi dtyp * list (metadata dtyp))) : bool :=
  match ps with
  | [] => true
  | _ => false
  end.

Definition term_br1_target (trm : instr_id * terminator dtyp * list (metadata dtyp))
  : option block_id :=
  let '(_, tm, _) := trm in
  match tm with
  | TERM_Br_1 target => Some target
  | _ => None
  end.

Definition is_unique_pred (bks : ocfg dtyp) (id1 id2 : block_id) : bool :=
  List.forallb
    (fun b =>
       if raw_id_eqb (blk_id b) id1
       then true
       else negb (in_raw_ids id2 (successors b)))
    bks.

Definition can_coalesce_pair (init_id : block_id) (bks : ocfg dtyp)
  (b1 b2 : block dtyp) : bool :=
  let id1 := blk_id b1 in
  let id2 := blk_id b2 in
  negb (raw_id_eqb id2 init_id) &&
  negb (raw_id_eqb id1 id2) &&
  (negb (raw_id_eqb id1 init_id) || is_nil_phis (blk_phis b1)) &&
  is_nil_phis (blk_phis b2) &&
  match term_br1_target (blk_term b1) with
  | Some target => raw_id_eqb target id2
  | None => false
  end &&
  is_unique_pred bks id1 id2.

Fixpoint find_coalesce_pair (init_id : block_id) (all_bks rem : ocfg dtyp)
  : option (block dtyp * block dtyp) :=
  match rem with
  | [] => None
  | b1 :: rest =>
      match term_br1_target (blk_term b1) with
      | Some target =>
          match find_block all_bks target with
          | Some b2 =>
              if can_coalesce_pair init_id all_bks b1 b2
              then Some (b1, b2)
              else find_coalesce_pair init_id all_bks rest
          | None => find_coalesce_pair init_id all_bks rest
          end
      | None => find_coalesce_pair init_id all_bks rest
      end
  end.

Fixpoint coalesce_phi_args (id1 id2 : block_id) (pargs : list (block_id * exp dtyp))
  : list (block_id * exp dtyp) :=
  match pargs with
  | [] => []
  | (pred, e) :: rest =>
      if raw_id_eqb pred id1 then
        coalesce_phi_args id1 id2 rest
      else if raw_id_eqb pred id2 then
        (id1, e) :: coalesce_phi_args id1 id2 rest
      else
        (pred, e) :: coalesce_phi_args id1 id2 rest
  end.

Definition coalesce_phi_entry (id1 id2 : raw_id)
  (entry : local_id * phi dtyp * list (metadata dtyp))
  : local_id * phi dtyp * list (metadata dtyp) :=
  let '(lid, Phi fm dt pargs, mds) := entry in
  (lid, Phi fm dt (coalesce_phi_args id1 id2 pargs), mds).

Definition rewrite_block_phis (id1 id2 : raw_id) (b : block dtyp) : block dtyp :=
  {| blk_id       := blk_id b;
     blk_phis     := List.map (coalesce_phi_entry id1 id2) (blk_phis b);
     blk_code     := blk_code b;
     blk_term     := blk_term b;
     blk_comments := blk_comments b |}.

Definition merge_blocks (b1 b2 : block dtyp) : block dtyp :=
  {| blk_id       := blk_id b1;
     blk_phis     := blk_phis b1;
     blk_code     := (blk_code b1 ++ blk_code b2)%list;
     blk_term     := blk_term b2;
     blk_comments := blk_comments b1 |}.

Definition coalesce_step_block (b1 b2 b : block dtyp) : block dtyp :=
  rewrite_block_phis (blk_id b1) (blk_id b2)
    (if raw_id_eqb (blk_id b) (blk_id b1) then merge_blocks b1 b2 else b).

Definition coalesce_blocks (b1 b2 : block dtyp) (bks : ocfg dtyp) : ocfg dtyp :=
  List.map (coalesce_step_block b1 b2)
    (List.filter (fun b => negb (raw_id_eqb (blk_id b) (blk_id b2))) bks).

Definition coalesce_one_cfg (c : CFG.cfg dtyp) : CFG.cfg dtyp :=
  if cfg_no_block_addresses c && nodup_raw_ids (List.map blk_id (blks c)) then
    match find_coalesce_pair (init c) (blks c) (blks c) with
    | Some (b1, b2) =>
        {| init := init c;
           blks := coalesce_blocks b1 b2 (blks c);
           args := args c |}
    | None => c
    end
  else c.

Definition coalesce_one_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  map_mcfg_cfg coalesce_one_cfg M.

Definition coalesce_default_fuel : nat := 32%nat.

Fixpoint coalesce_mcfg_iter (fuel : nat) (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  match fuel with
  | O => M
  | S fuel' => coalesce_mcfg_iter fuel' (coalesce_one_mcfg M)
  end.

Definition coalesce_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  coalesce_mcfg_iter coalesce_default_fuel M.

(** Guard extraction & lookup properties for [coalesce_one_cfg]. *)
Lemma find_coalesce_pair_spec (init_id : block_id) (all_bks rem : ocfg dtyp)
  (b1 b2 : block dtyp)
  (Hsub : forall x, In x rem -> In x all_bks)
  (Hfind : find_coalesce_pair init_id all_bks rem = Some (b1, b2)) :
  In b1 all_bks /\ In b2 all_bks /\ can_coalesce_pair init_id all_bks b1 b2 = true.
Proof.
  induction rem as [| hd rest IH]; cbn [find_coalesce_pair] in Hfind; [discriminate Hfind |].
  assert (Hsub_rest : forall x, In x rest -> In x all_bks).
  { intros x Hx; apply Hsub; right; exact Hx. }
  destruct (term_br1_target (blk_term hd)) as [target |];
    [| apply (IH Hsub_rest Hfind)].
  destruct (find_block all_bks target) as [cand |] eqn:Ecand;
    [| apply (IH Hsub_rest Hfind)].
  destruct (can_coalesce_pair init_id all_bks hd cand) eqn:Ecan;
    [| apply (IH Hsub_rest Hfind)].
  inversion Hfind; subst hd cand.
  split; [apply Hsub; left; reflexivity |].
  split; [eapply find_block_In'; exact Ecand | exact Ecan].
Qed.

Lemma can_coalesce_pair_props (init_id : block_id) (bks : ocfg dtyp) (b1 b2 : block dtyp)
  (Hcan : can_coalesce_pair init_id bks b1 b2 = true) :
  blk_id b2 <> init_id /\
  raw_id_eqb (blk_id b1) (blk_id b2) = false /\
  blk_id b1 <> blk_id b2 /\
  (blk_id b1 = init_id -> blk_phis b1 = []) /\
  blk_phis b2 = [] /\
  (exists iid1 md1, blk_term b1 = (iid1, TERM_Br_1 (blk_id b2), md1)) /\
  (forall b, In b bks -> blk_id b <> blk_id b1 -> ~ In (blk_id b2) (successors b)).
Proof.
  unfold can_coalesce_pair in Hcan; cbv zeta in Hcan.
  rewrite !Bool.andb_true_iff in Hcan.
  destruct Hcan as (((((Hc1 & Hc2) & Hc3) & Hc4) & Hc5) & Hc6).
  apply Bool.negb_true_iff in Hc1.
  apply raw_id_eqb_neq in Hc1.
  apply Bool.negb_true_iff in Hc2.
  pose proof (proj1 (raw_id_eqb_neq _ _) Hc2) as Hneq12.
  assert (Hentry : blk_id b1 = init_id -> blk_phis b1 = []).
  { intros Heq; rewrite Heq, raw_id_eqb_refl in Hc3; cbn [negb orb] in Hc3.
    destruct (blk_phis b1); [reflexivity | discriminate Hc3]. }
  assert (Hphis2 : blk_phis b2 = []).
  { destruct (blk_phis b2); [reflexivity | discriminate Hc4]. }
  assert (Hterm1 : exists iid1 md1, blk_term b1 = (iid1, TERM_Br_1 (blk_id b2), md1)).
  { destruct (blk_term b1) as [[iid1 tm1] md1]; cbn [term_br1_target] in Hc5.
    destruct tm1 as [ | | | br | | | | | ]; try discriminate Hc5; cbv iota in Hc5.
    apply raw_id_eqb_spec in Hc5; subst br.
    exists iid1, md1; reflexivity. }
  assert (Huniq : forall b, In b bks -> blk_id b <> blk_id b1 -> ~ In (blk_id b2) (successors b)).
  { unfold is_unique_pred in Hc6; rewrite List.forallb_forall in Hc6.
    intros b Hb Hbid.
    specialize (Hc6 b Hb).
    apply raw_id_eqb_neq in Hbid; rewrite Hbid in Hc6; cbv iota in Hc6.
    apply Bool.negb_true_iff in Hc6.
    apply in_raw_ids_false, Hc6. }
  exact (conj Hc1 (conj Hc2 (conj Hneq12 (conj Hentry (conj Hphis2 (conj Hterm1 Huniq)))))).
Qed.

Lemma coalesce_step_block_id (b1 b2 b : block dtyp) :
  blk_id (coalesce_step_block b1 b2 b) = blk_id b.
Proof.
  unfold coalesce_step_block, rewrite_block_phis; cbn [blk_id].
  destruct (raw_id_eqb (blk_id b) (blk_id b1)) eqn:E.
  - apply raw_id_eqb_spec in E; cbn [merge_blocks blk_id]; symmetry; exact E.
  - reflexivity.
Qed.

Lemma find_block_coalesce_non_id2 (bks : ocfg dtyp) (b1 b2 : block dtyp) (src : block_id)
  (Hnid2 : src <> blk_id b2) :
  find_block (coalesce_blocks b1 b2 bks) src =
  option_map (coalesce_step_block b1 b2) (find_block bks src).
Proof.
  unfold coalesce_blocks.
  rewrite find_block_map by apply coalesce_step_block_id.
  assert (Hpred : negb (raw_id_eqb src (blk_id b2)) = true).
  { apply Bool.negb_true_iff, raw_id_eqb_neq, Hnid2. }
  rewrite (find_block_filter_id (fun id => negb (raw_id_eqb id (blk_id b2))) bks src Hpred).
  reflexivity.
Qed.

Lemma find_block_coalesce_merged (bks : ocfg dtyp) (b1 b2 : block dtyp)
  (Hnd : NoDup (List.map blk_id bks))
  (Hin1 : In b1 bks)
  (Hid12 : blk_id b1 <> blk_id b2) :
  find_block (coalesce_blocks b1 b2 bks) (blk_id b1) =
  Some (rewrite_block_phis (blk_id b1) (blk_id b2) (merge_blocks b1 b2)).
Proof.
  rewrite (find_block_coalesce_non_id2 bks b1 b2 (blk_id b1) Hid12).
  rewrite (find_block_nodup_in bks b1 Hnd Hin1); cbn [option_map].
  unfold coalesce_step_block; rewrite raw_id_eqb_refl; reflexivity.
Qed.

Lemma find_block_coalesce_other (bks : ocfg dtyp) (b1 b2 : block dtyp)
  (src : block_id) (bk : block dtyp)
  (Hnid1 : src <> blk_id b1)
  (Hnid2 : src <> blk_id b2)
  (Hfind : find_block bks src = Some bk) :
  find_block (coalesce_blocks b1 b2 bks) src =
  Some (rewrite_block_phis (blk_id b1) (blk_id b2) bk).
Proof.
  rewrite (find_block_coalesce_non_id2 bks b1 b2 src Hnid2), Hfind; cbn [option_map].
  assert (Hid_bk : blk_id bk = src) by (symmetry; eapply find_block_has_id; exact Hfind).
  unfold coalesce_step_block; rewrite Hid_bk.
  apply raw_id_eqb_neq in Hnid1; rewrite Hnid1; reflexivity.
Qed.

Lemma find_block_coalesce_none (bks : ocfg dtyp) (b1 b2 : block dtyp)
  (src : block_id)
  (Hnid2 : src <> blk_id b2)
  (Hfind : find_block bks src = None) :
  find_block (coalesce_blocks b1 b2 bks) src = None.
Proof.
  rewrite (find_block_coalesce_non_id2 bks b1 b2 src Hnid2), Hfind; reflexivity.
Qed.

(** Phi-edge coalescing [assoc] & [denote_phis] lemmas. *)
Lemma assoc_coalesce_from_merged (id1 id2 : block_id)
  (pargs : list (block_id * exp dtyp))
  (Hneq : raw_id_eqb id1 id2 = false) :
  assoc id1 (coalesce_phi_args id1 id2 pargs) = assoc id2 pargs.
Proof.
  induction pargs as [| [pred e] rest IH]; [reflexivity |].
  cbn [coalesce_phi_args].
  rewrite (assoc_block_id_cons id2 pred e rest).
  destruct (raw_id_eqb pred id1) eqn:Ep1; cbv iota.
  - apply raw_id_eqb_spec in Ep1; subst pred.
    replace (raw_id_eqb id2 id1) with (raw_id_eqb id1 id2) by apply raw_id_eqb_sym.
    rewrite Hneq; exact IH.
  - destruct (raw_id_eqb pred id2) eqn:Ep2; cbv iota.
    + apply raw_id_eqb_spec in Ep2; subst pred.
      rewrite assoc_block_id_cons, !raw_id_eqb_refl; reflexivity.
    + rewrite assoc_block_id_cons.
      replace (raw_id_eqb id1 pred) with (raw_id_eqb pred id1) by apply raw_id_eqb_sym.
      replace (raw_id_eqb id2 pred) with (raw_id_eqb pred id2) by apply raw_id_eqb_sym.
      rewrite Ep1, Ep2; exact IH.
Qed.

Lemma assoc_coalesce_from_other (id1 id2 from : block_id)
  (pargs : list (block_id * exp dtyp))
  (Hf1 : raw_id_eqb from id1 = false)
  (Hf2 : raw_id_eqb from id2 = false) :
  assoc from (coalesce_phi_args id1 id2 pargs) = assoc from pargs.
Proof.
  induction pargs as [| [pred e] rest IH]; [reflexivity |].
  cbn [coalesce_phi_args].
  rewrite (assoc_block_id_cons from pred e rest).
  destruct (raw_id_eqb pred id1) eqn:Ep1; cbv iota.
  - apply raw_id_eqb_spec in Ep1; subst pred.
    rewrite Hf1; exact IH.
  - destruct (raw_id_eqb pred id2) eqn:Ep2; cbv iota.
    + apply raw_id_eqb_spec in Ep2; subst pred.
      rewrite assoc_block_id_cons, Hf1, Hf2; exact IH.
    + rewrite assoc_block_id_cons.
      destruct (raw_id_eqb from pred); [reflexivity | exact IH].
Qed.

Lemma map_monad_denote_phi_coalesce {Pa : Params}
  (id1 id2 from1 from2 : block_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  (Hid12 : raw_id_eqb id1 id2 = false)
  (Hfrom : (from1 = from2 /\ from1 <> id1 /\ from1 <> id2) \/
           (from1 = id2 /\ from2 = id1)) :
  map_monad (@denote_phi Pa from2) (List.map (coalesce_phi_entry id1 id2) phis) =
  map_monad (@denote_phi Pa from1) phis.
Proof.
  induction phis as [| [[lid [fm dt pargs]] mds] rest IH]; [reflexivity |].
  cbn [List.map coalesce_phi_entry map_monad].
  assert (Hhd : @denote_phi Pa from2 (lid, Phi fm dt (coalesce_phi_args id1 id2 pargs), mds) =
                @denote_phi Pa from1 (lid, Phi fm dt pargs, mds)).
  { unfold denote_phi; cbv beta iota zeta.
    destruct Hfrom as [(<- & Hf1 & Hf2) | [-> ->]].
    - apply raw_id_eqb_neq in Hf1; apply raw_id_eqb_neq in Hf2.
      rewrite (assoc_coalesce_from_other id1 id2 from1 pargs Hf1 Hf2); reflexivity.
    - rewrite (assoc_coalesce_from_merged id1 id2 pargs Hid12); reflexivity. }
  rewrite Hhd, IH; reflexivity.
Qed.

Lemma denote_phis_coalesce {Pa : Params}
  (id1 id2 from1 from2 : block_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  (Hid12 : raw_id_eqb id1 id2 = false)
  (Hfrom : (from1 = from2 /\ from1 <> id1 /\ from1 <> id2) \/
           (from1 = id2 /\ from2 = id1)) :
  @denote_phis Pa from2 (List.map (coalesce_phi_entry id1 id2) phis) =
  @denote_phis Pa from1 phis.
Proof.
  unfold denote_phis.
  rewrite (map_monad_denote_phi_coalesce id1 id2 from1 from2 phis Hid12 Hfrom).
  reflexivity.
Qed.

(** Block-address preservation for [coalesce_one_cfg]. *)
Lemma coalesce_phi_args_in_exp (id1 id2 : raw_id)
  (pargs : list (block_id * exp dtyp)) (p' : block_id) (e : exp dtyp) :
  In (p', e) (coalesce_phi_args id1 id2 pargs) ->
  exists p, In (p, e) pargs.
Proof.
  induction pargs as [| [pred ex] rest IH]; cbn [coalesce_phi_args In]; [contradiction |].
  destruct (raw_id_eqb pred id1); cbv iota.
  - intros Hin; destruct (IH Hin) as [p Hp]; exists p; right; exact Hp.
  - destruct (raw_id_eqb pred id2); cbv iota; cbn [In].
    + intros [Heq | Hin].
      * injection Heq as _ <-; exists pred; left; reflexivity.
      * destruct (IH Hin) as [p Hp]; exists p; right; exact Hp.
    + intros [Heq | Hin].
      * injection Heq as _ <-; exists pred; left; reflexivity.
      * destruct (IH Hin) as [p Hp]; exists p; right; exact Hp.
Qed.

Lemma rewrite_block_phis_block_addresses (id1 id2 : raw_id) (b : block dtyp)
  (Hb : block_block_addresses b = []) :
  block_block_addresses (rewrite_block_phis id1 id2 b) = [].
Proof.
  apply block_block_addresses_nil_iff in Hb as (Hphis & Hcode & Hterm).
  apply block_block_addresses_nil_iff.
  cbn [rewrite_block_phis blk_phis blk_code blk_term].
  refine (conj _ (conj Hcode Hterm)).
  rewrite flat_map_eq_nil_iff in Hphis |- *.
  intros [[lid [fm dt pargs]] mds] Hin.
  apply in_map_iff in Hin as ([[lid0 [fm0 dt0 pargs0]] mds0] & Heq & Hin0).
  cbn [coalesce_phi_entry] in Heq; inversion Heq; subst.
  specialize (Hphis _ Hin0); cbv beta iota in Hphis |- *.
  rewrite flat_map_eq_nil_iff in Hphis |- *.
  intros [p' ex] Hin_c.
  destruct (coalesce_phi_args_in_exp id1 id2 pargs0 p' ex Hin_c) as [p Hp].
  exact (Hphis (p, ex) Hp).
Qed.

Lemma merge_blocks_block_addresses (b1 b2 : block dtyp)
  (Hb1 : block_block_addresses b1 = [])
  (Hb2 : block_block_addresses b2 = []) :
  block_block_addresses (merge_blocks b1 b2) = [].
Proof.
  apply block_block_addresses_nil_iff in Hb1 as (Hphis1 & Hcode1 & _).
  apply block_block_addresses_nil_iff in Hb2 as (_ & Hcode2 & Hterm2).
  apply block_block_addresses_nil_iff.
  cbn [merge_blocks blk_phis blk_code blk_term].
  rewrite flat_map_app, Hcode1, Hcode2; cbn [app].
  exact (conj Hphis1 (conj eq_refl Hterm2)).
Qed.

Lemma coalesce_one_cfg_block_addresses (c : CFG.cfg dtyp) :
  flat_map block_block_addresses (blks (coalesce_one_cfg c)) =
  flat_map block_block_addresses (blks c).
Proof.
  unfold coalesce_one_cfg.
  destruct (cfg_no_block_addresses c) eqn:Eba; [| reflexivity].
  cbn [andb].
  destruct (nodup_raw_ids (List.map blk_id (blks c))); [cbv iota | reflexivity].
  destruct (find_coalesce_pair (init c) (blks c) (blks c)) as [[b1 b2] |] eqn:Efcp;
    [cbv iota | reflexivity].
  destruct (find_coalesce_pair_spec (init c) (blks c) (blks c) b1 b2 (fun _ H => H) Efcp)
    as (Hin1 & Hin2 & _).
  apply cfg_no_block_addresses_nil in Eba.
  rewrite Eba; cbn [blks].
  rewrite flat_map_eq_nil_iff in Eba |- *.
  intros b' Hin.
  unfold coalesce_blocks in Hin.
  apply in_map_iff in Hin as (b & <- & Hfilt).
  apply filter_In in Hfilt as [Hb _].
  unfold coalesce_step_block.
  apply rewrite_block_phis_block_addresses.
  destruct (raw_id_eqb (blk_id b) (blk_id b1)); cbv iota.
  - apply merge_blocks_block_addresses; [apply Eba, Hin1 | apply Eba, Hin2].
  - apply Eba, Hb.
Qed.

(** Block-level & OCFG-level simulation lemmas for [coalesce_one_cfg]. *)
Lemma denote_ocfg_coalesce_lhs_euttge {Pa : Params}
  (va : option (@ptr (@PROV Pa) (@PTR Pa))) (bks : ocfg dtyp)
  (from1 id1 id2 : block_id) (b1 b2 : block dtyp)
  (iid1 : instr_id) (md1 : list (metadata dtyp))
  (Hfind1 : find_block bks id1 = Some b1)
  (Hterm1 : blk_term b1 = (iid1, TERM_Br_1 id2, md1))
  (Hfind2 : find_block bks id2 = Some b2) :
  denote_ocfg bks va (from1, id1) ≳
    ITree.bind
      (ITree.bind (denote_phis from1 (blk_phis b1))
         (fun _ => ITree.bind (denote_code (blk_code b1) va)
                     (fun _ => denote_block b2 id1 va)))
      (fun vob2 =>
         match vob2 with
         | inr v => Ret (inr v)
         | inl tgt => Tau (denote_ocfg bks va (id2, tgt))
         end).
Proof.
  etransitivity; [apply (denote_ocfg_unfold_in_euttge va bks from1 id1 Hfind1) |].
  assert (Hrhs :
    ITree.bind
      (ITree.bind (denote_phis from1 (blk_phis b1))
         (fun _ => ITree.bind (denote_code (blk_code b1) va)
                     (fun _ => denote_block b2 id1 va)))
      (fun vob2 =>
         match vob2 with
         | inr v => Ret (inr v)
         | inl tgt => Tau (denote_ocfg bks va (id2, tgt))
         end)
    ≅
    ITree.bind (denote_phis from1 (blk_phis b1))
      (fun _ =>
         ITree.bind (denote_code (blk_code b1) va)
           (fun _ =>
              ITree.bind (denote_block b2 id1 va)
                (fun vob2 =>
                   match vob2 with
                   | inr v => Ret (inr v)
                   | inl tgt => Tau (denote_ocfg bks va (id2, tgt))
                   end)))).
  { rewrite Eqit.bind_bind.
    apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    rewrite Eqit.bind_bind; reflexivity. }
  etransitivity;
    [| apply (@Eqit.eqit_mon _ _ _ eq eq false false true false
                (fun H => ltac:(discriminate H))
                (fun H => H)
                (fun _ _ H => H));
       symmetry; exact Hrhs].
  unfold denote_block at 1; rewrite Hterm1.
  cbn [denote_terminator ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
  rewrite !Eqit.bind_bind.
  eapply (Eqit.eqit_bind' eq); [reflexivity | intros [] [] _].
  rewrite ?Eqit.bind_bind.
  eapply (Eqit.eqit_bind' eq); [reflexivity | intros [] [] _].
  rewrite Eqit.bind_ret_l; cbv iota.
  rewrite (denote_ocfg_unfold_in_eq_itree va bks id1 id2 Hfind2).
  reflexivity.
Qed.

Lemma denote_block_coalesce_merged {Pa : Params}
  (va : option (@ptr (@PROV Pa) (@PTR Pa))) (init_id id1 id2 from1 from2 : block_id)
  (b1 b2 : block dtyp)
  (Hid12 : raw_id_eqb id1 id2 = false)
  (Hentry : id1 = init_id -> blk_phis b1 = [])
  (Hphis2 : blk_phis b2 = [])
  (Hfrom : (from1 = from2 /\ from1 <> id1 /\ from1 <> id2) \/
           (from1 = id2 /\ from2 = id1) \/
           (id1 = init_id /\ from1 = id1 /\ from2 = id1)) :
  refine_cfg
    (sum_rel (fun t1 t2 => t1 = t2 /\ In t1 (successors b2)) Logic.eq)
    (ITree.bind (denote_phis from1 (blk_phis b1))
       (fun _ => ITree.bind (denote_code (blk_code b1) va)
                   (fun _ => denote_block b2 id1 va)))
    (denote_block (rewrite_block_phis id1 id2 (merge_blocks b1 b2)) from2 va).
Proof.
  unfold denote_block.
  cbn [rewrite_block_phis merge_blocks blk_phis blk_code blk_term ExtLib.Structures.Monad.bind Monad_itree].
  assert (Hphis_ref :
            refine_cfg Logic.eq
              (denote_phis from1 (blk_phis b1))
              (denote_phis from2 (List.map (coalesce_phi_entry id1 id2) (blk_phis b1)))).
  { destruct Hfrom as [H1 | [H2 | (Hid_init & -> & ->)]].
    - rewrite (denote_phis_coalesce id1 id2 from1 from2 (blk_phis b1) Hid12 (or_introl H1)).
      apply refine_cfg_refl.
    - rewrite (denote_phis_coalesce id1 id2 from1 from2 (blk_phis b1) Hid12 (or_intror H2)).
      apply refine_cfg_refl.
    - rewrite (Hentry Hid_init); cbn [List.map]; apply refine_cfg_refl. }
  eapply ruttc_bind; [exact Hphis_ref | intros [] _ <-].
  eapply refine_cfg_eq_itree_r;
    [rewrite (denote_code_app va (blk_code b1) (blk_code b2)), Eqit.bind_bind; reflexivity |].
  eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
  rewrite Hphis2.
  eapply refine_cfg_eq_itree_l;
    [rewrite denote_phis_nil, Eqit.bind_ret_l; reflexivity |].
  eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
  apply refine_cfg_terminator_outputs.
Qed.

Lemma denote_block_coalesce_other {Pa : Params}
  (va : option (@ptr (@PROV Pa) (@PTR Pa))) (id1 id2 from1 from2 : block_id)
  (bk : block dtyp)
  (Hid12 : raw_id_eqb id1 id2 = false)
  (Hfrom : (from1 = from2 /\ from1 <> id1 /\ from1 <> id2) \/
           (from1 = id2 /\ from2 = id1)) :
  refine_cfg
    (sum_rel (fun t1 t2 => t1 = t2 /\ In t1 (successors bk)) Logic.eq)
    (denote_block bk from1 va)
    (denote_block (rewrite_block_phis id1 id2 bk) from2 va).
Proof.
  unfold denote_block; cbn [rewrite_block_phis blk_phis blk_code blk_term].
  rewrite (denote_phis_coalesce id1 id2 from1 from2 (blk_phis bk) Hid12 Hfrom).
  eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
  eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
  apply refine_cfg_terminator_outputs.
Qed.

Definition coalesce_rel (init_id id1 id2 : block_id)
  (s1 s2 : block_id * block_id) : Prop :=
  let '(from1, src1) := s1 in
  let '(from2, src2) := s2 in
  src1 = src2 /\
  src1 <> id2 /\
  ((from1 = from2 /\ from1 <> id1 /\ from1 <> id2) \/
   (from1 = id2 /\ from2 = id1) \/
   (src1 = id1 /\ id1 = init_id /\ from1 = id1 /\ from2 = id1)).

Lemma denote_ocfg_coalesce {Pa : Params}
  (va : option (@ptr (@PROV Pa) (@PTR Pa)))
  (init_id : block_id) (bks : ocfg dtyp) (b1 b2 : block dtyp)
  (Hnd : NoDup (List.map blk_id bks))
  (Hin1 : In b1 bks)
  (Hin2 : In b2 bks)
  (Hcan : can_coalesce_pair init_id bks b1 b2 = true) :
  forall s1 s2,
    coalesce_rel init_id (blk_id b1) (blk_id b2) s1 s2 ->
    refine_cfg
      (sum_rel (fun p1 p2 => snd p1 = snd p2) Logic.eq)
      (denote_ocfg bks va s1)
      (denote_ocfg (coalesce_blocks b1 b2 bks) va s2).
Proof.
  destruct (can_coalesce_pair_props init_id bks b1 b2 Hcan)
    as (_ & Hid12_eqb & Hid12 & Hentry & Hphis2 & (iid1 & md1 & Hterm1) & Huniq).
  pose proof (find_block_nodup_in bks b1 Hnd Hin1) as Hfind1.
  pose proof (find_block_nodup_in bks b2 Hnd Hin2) as Hfind2.
  unfold refine_cfg.
  ginit; gcofix CIH; intros [from1 src1] [from2 src2] Hrel.
  destruct Hrel as (Hsrc_eq & Hsrc_nid2 & Hfrom_cases); subst src2.
  destruct (RawIDOrd.eq_dec src1 (blk_id b1)) as [Hsrc_id1 | Hsrc_nid1].
  - (* Coalesced two-block step: [b1] followed immediately by [b2]. *)
    subst src1.
    assert (Hfrom_m :
              (from1 = from2 /\ from1 <> blk_id b1 /\ from1 <> blk_id b2) \/
              (from1 = blk_id b2 /\ from2 = blk_id b1) \/
              (blk_id b1 = init_id /\ from1 = blk_id b1 /\ from2 = blk_id b1)).
    { destruct Hfrom_cases as [H1 | [H2 | [_ H3]]];
        [left; exact H1 | right; left; exact H2 | right; right; exact H3]. }
    pose proof (find_block_coalesce_merged bks b1 b2 Hnd Hin1 Hid12) as Hfind1'.
    rewrite (denote_ocfg_coalesce_lhs_euttge va bks from1 (blk_id b1) (blk_id b2)
               b1 b2 iid1 md1 Hfind1 Hterm1 Hfind2).
    rewrite (denote_ocfg_unfold_in_eq_itree va (coalesce_blocks b1 b2 bks)
               from2 (blk_id b1) Hfind1').
    eapply gpaco2_uclo; [| eapply ruttc_clo_bind |]; eauto with paco.
    econstructor.
    + apply (denote_block_coalesce_merged va init_id (blk_id b1) (blk_id b2)
               from1 from2 b1 b2 Hid12_eqb Hentry Hphis2 Hfrom_m).
    + intros bd1 bd2 Hbd;
        destruct Hbd as [t1 t2 [<- Hout] | v1 v2 <-]; cbv beta iota.
      * assert (Ht_nid2 : t1 <> blk_id b2).
        { intros Heq; subst t1; eapply (Huniq b2 Hin2); [congruence | exact Hout]. }
        assert (Hnext : coalesce_rel init_id (blk_id b1) (blk_id b2)
                          (blk_id b2, t1) (blk_id b1, t1)).
        { split; [reflexivity | split; [exact Ht_nid2 | right; left; split; reflexivity]]. }
        gstep; constructor; gfinal; left; exact (CIH _ _ Hnext).
      * gstep; constructor; constructor; reflexivity.
  - (* Lockstep single-block step for [src1 <> blk_id b1] and [src1 <> blk_id b2]. *)
    assert (Hfrom_o :
              (from1 = from2 /\ from1 <> blk_id b1 /\ from1 <> blk_id b2) \/
              (from1 = blk_id b2 /\ from2 = blk_id b1)).
    { destruct Hfrom_cases as [H1 | [H2 | [Habs _]]];
        [left; exact H1 | right; exact H2 | contradiction]. }
    destruct (find_block bks src1) as [bk |] eqn:Efind.
    + pose proof (find_block_coalesce_other bks b1 b2 src1 bk Hsrc_nid1 Hsrc_nid2 Efind)
        as Hfind'.
      assert (Hin_bk : In bk bks) by (eapply find_block_In'; exact Efind).
      assert (Hid_bk : blk_id bk = src1) by (symmetry; eapply find_block_has_id; exact Efind).
      rewrite (denote_ocfg_unfold_in_eq_itree va bks from1 src1 Efind).
      rewrite (denote_ocfg_unfold_in_eq_itree va (coalesce_blocks b1 b2 bks)
                 from2 src1 Hfind').
      eapply gpaco2_uclo; [| eapply ruttc_clo_bind |]; eauto with paco.
      econstructor.
      * apply (denote_block_coalesce_other va (blk_id b1) (blk_id b2)
                 from1 from2 bk Hid12_eqb Hfrom_o).
      * intros bd1 bd2 Hbd;
          destruct Hbd as [t1 t2 [<- Hout] | v1 v2 <-]; cbv beta iota.
        -- assert (Ht_nid2 : t1 <> blk_id b2).
           { intros Heq; subst t1; eapply (Huniq bk Hin_bk);
               [rewrite Hid_bk; exact Hsrc_nid1 | exact Hout]. }
           assert (Hnext : coalesce_rel init_id (blk_id b1) (blk_id b2)
                             (src1, t1) (src1, t1)).
           { split; [reflexivity | split; [exact Ht_nid2 |]].
             left; exact (conj eq_refl (conj Hsrc_nid1 Hsrc_nid2)). }
           gstep; constructor; gfinal; left; exact (CIH _ _ Hnext).
        -- gstep; constructor; constructor; reflexivity.
    + pose proof (find_block_coalesce_none bks b1 b2 src1 Hsrc_nid2 Efind) as Hfind'.
      rewrite (denote_ocfg_unfold_not_in_eq_itree va bks from1 src1 Efind).
      rewrite (denote_ocfg_unfold_not_in_eq_itree va (coalesce_blocks b1 b2 bks)
                 from2 src1 Hfind').
      gstep; constructor; constructor; cbn; reflexivity.
Qed.

Lemma denote_cfg_coalesce_one {Pa : Params}
  (c : CFG.cfg dtyp) (va : option (@ptr (@PROV Pa) (@PTR Pa))) :
  refine_cfg Logic.eq (denote_cfg c va) (denote_cfg (coalesce_one_cfg c) va).
Proof.
  unfold coalesce_one_cfg.
  destruct (cfg_no_block_addresses c); cbn [andb]; [| apply refine_cfg_refl].
  destruct (nodup_raw_ids (List.map blk_id (blks c))) eqn:End; [cbv iota | apply refine_cfg_refl].
  destruct (find_coalesce_pair (init c) (blks c) (blks c)) as [[b1 b2] |] eqn:Efcp;
    [cbv iota | apply refine_cfg_refl].
  apply nodup_raw_ids_spec in End.
  destruct (find_coalesce_pair_spec (init c) (blks c) (blks c) b1 b2 (fun _ H => H) Efcp)
    as (Hin1 & Hin2 & Hcan).
  destruct (can_coalesce_pair_props (init c) (blks c) b1 b2 Hcan) as (Hid2_init & _).
  assert (Hinit_nid2 : init c <> blk_id b2) by congruence.
  assert (Hinit_rel : coalesce_rel (init c) (blk_id b1) (blk_id b2)
                        (init c, init c) (init c, init c)).
  { split; [reflexivity | split; [exact Hinit_nid2 |]].
    destruct (RawIDOrd.eq_dec (init c) (blk_id b1)) as [Heq | Hneq].
    - right; right; rewrite <- Heq; repeat split; reflexivity.
    - left; exact (conj eq_refl (conj Hneq Hinit_nid2)). }
  unfold denote_cfg, denote_cfg_map; cbn [init blks].
  fold (denote_ocfg (blks c)) (denote_ocfg (coalesce_blocks b1 b2 (blks c))).
  eapply ruttc_bind.
  - apply (denote_ocfg_coalesce va (init c) (blks c) b1 b2 End Hin1 Hin2 Hcan
             (init c, init c) (init c, init c) Hinit_rel).
  - intros r1 r2 Hr; destruct Hr as [p1 p2 _ | uv1 uv2 <-]; cbv beta iota;
      [apply refine_cfg_raise | apply ruttc_ret; reflexivity].
Qed.

Theorem coalesce_one_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (coalesce_one_mcfg M).
Proof.
  intros IP IPT M.
  apply lift_cfg_pass.
  - exact coalesce_one_cfg_block_addresses.
  - intros c va; apply denote_cfg_coalesce_one.
Qed.

Theorem coalesce_mcfg_iter_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (fuel : nat) (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (coalesce_mcfg_iter fuel M).
Proof.
  intros IP IPT fuel.
  induction fuel as [| fuel' IH]; intros M; cbn [coalesce_mcfg_iter].
  - apply prog_refines_refl.
  - eapply prog_refines_trans.
    + apply coalesce_one_mcfg_refines.
    + apply IH.
Qed.

Theorem coalesce_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (coalesce_mcfg M).
Proof.
  intros IP IPT M.
  apply coalesce_mcfg_iter_refines.
Qed.

(** * 5. Composed SimplifyCFG Pass & Whole-Module Soundness *)

Definition simplifycfg_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  coalesce_mcfg
    (elim_unreachable_mcfg
      (fold_const_term_mcfg M)).

Definition simplifycfg_mcfg_typ (M : CFG.mcfg typ) : CFG.mcfg dtyp :=
  simplifycfg_mcfg (convert_types M).

Theorem simplifycfg_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (simplifycfg_mcfg M).
Proof.
  intros IP IPT M.
  unfold simplifycfg_mcfg.
  eapply prog_refines_trans; [apply fold_const_term_mcfg_refines |].
  eapply prog_refines_trans; [apply elim_unreachable_mcfg_refines |].
  apply coalesce_mcfg_refines.
Qed.
