(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Stack-Slot to SSA Register Promotion ([CertPasses.Mem2Reg])

    Promotes non-escaping scalar [alloca] stack slots in function entry blocks
    to SSA registers and block-entry [Phi] nodes (Stage 1), followed by
    reverse-order dead scalar [alloca] elimination in leaf functions (Stage 2)
    so inlinable callees become [alloca]-free before [CertPasses.Inline].
    Composed across bounded rounds via [prog_refines_trans]. *)

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
  Structures.Functor
  Data.Monads.EitherMonad.

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
  Semantics.Implementations.Sizeof
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.

From CertPasses Require Import PassCommon.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.

From CertPasses Require Import Mem2RegSpec Mem2RegModel Mem2RegMemBase Mem2RegGhostInv.

#[local] Notation refine_prov_bind := m2r_refine_prov_bind (only parsing).

Section MemoryAndSerialization.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.
  #[local] Existing Instance PointerV.
  #[local] Existing Instance PIV.
  #[local] Existing Instance PITheoryV.
  #[local] Hint Resolve refine_prov__mon : paco.
  Arguments memM_interp_prov {_ _} [T] _ _.
  Arguments interp_vellvm_prov_h {_ _} [T] _ _.

  (** ** 3F. Syntactic Uniqueness, Environment & Interpreter Lifting Helpers *)

  Lemma m2r_flat_map_app {A B} (f : A -> list B) (l1 l2 : list A) :
    flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof using.
    induction l1 as [| a l1' IH]; cbn; [reflexivity | rewrite IH, app_assoc; reflexivity].
  Qed.

  Lemma m2r_in_raw_ids_dec (x : raw_id) (xs : list raw_id) :
    {In x xs} + {~ In x xs}.
  Proof using.
    induction xs as [| y ys IH].
    - right; intros [].
    - destruct (raw_id_eqb x y) eqn:Exy; [apply raw_id_eqb_spec in Exy; subst x | apply raw_id_eqb_neq in Exy; rename Exy into Hne].
      + left; left; reflexivity.
      + destruct IH as [Hin | Hnin].
        * left; right; exact Hin.
        * right; intros [Heq | Hin]; [exact (Hne (eq_sym Heq)) | exact (Hnin Hin)].
  Qed.

  Lemma m2r_in_raw_ids_true (x : raw_id) (xs : list raw_id) :
    in_raw_ids x xs = true <-> In x xs.
  Proof using.
    destruct (in_raw_ids x xs) eqn:E.
    - destruct (m2r_in_raw_ids_dec x xs) as [Hin | Hnin];
        [tauto | apply in_raw_ids_false in Hnin; congruence].
    - apply in_raw_ids_false in E; split; [discriminate | intros H; contradiction (E H)].
  Qed.

  Lemma m2r_count_id_in_pos (x : raw_id) (xs : list raw_id) :
    In x xs ->
    (1 <= m2r_count_id x xs)%nat.
  Proof using.
    induction xs as [| y ys IH]; cbn [In m2r_count_id]; [intros [] |].
    intros [-> | Hin].
    - rewrite raw_id_eqb_refl; lia.
    - specialize (IH Hin); destruct (raw_id_eqb x y); lia.
  Qed.

  Lemma m2r_in_filter_no_p (p q : raw_id) (xs : list raw_id) :
    In q (List.filter (fun r => negb (raw_id_eqb r p)) xs) <->
    In q xs /\ q <> p.
  Proof using.
    rewrite filter_In, negb_true_iff.
    destruct (raw_id_eqb q p) eqn:Eqp; [apply raw_id_eqb_spec in Eqp; subst q | apply raw_id_eqb_neq in Eqp; rename Eqp into Hne].
    - split; [intros [_ H]; discriminate H | intros [_ H]; contradiction (H Logic.eq_refl)].
    - split; [intros [Hq _]; split; [exact Hq | exact Hne] | intros [Hq _]; split; [exact Hq | reflexivity]].
  Qed.

  Lemma m2r_collect_unique_allocas_inv
    (all_defs : list raw_id) (bks : ocfg dtyp) (q : local_id) :
    In q (m2r_collect_unique_allocas all_defs bks) ->
    m2r_count_id q all_defs = 1%nat /\
    exists bk dt_q anns_q md_q,
      In bk bks /\
      In (IId q, INSTR_Alloca dt_q anns_q, md_q) (blk_code bk).
  Proof using.
    unfold m2r_collect_unique_allocas; rewrite in_flat_map.
    intros (bk & Hbk & Hin1).
    rewrite in_flat_map in Hin1.
    destruct Hin1 as ([[iid ins] md] & Him & Hin2).
    destruct iid as [id0 |]; [| contradiction Hin2].
    destruct ins; try contradiction Hin2.
    destruct (Nat.eqb_spec (m2r_count_id id0 all_defs) 1%nat) as [Hcnt | _];
      [| contradiction Hin2].
    destruct Hin2 as [<- | []].
    split; [exact Hcnt | eexists bk, _, _, md; split; eassumption].
  Qed.

  Lemma m2r_safe_ptr_exp_mono (s1 s2 : list local_id) (e : exp dtyp) :
    (forall q, In q s1 -> In q s2) ->
    m2r_safe_ptr_exp s1 e = true ->
    m2r_safe_ptr_exp s2 e = true.
  Proof using.
    intros Hsub; revert e; fix IH 1; intros e.
    destruct e;
      repeat match goal with p : dtyp * exp dtyp |- _ => destruct p end;
      cbn [m2r_safe_ptr_exp]; try exact (fun x => x).
    - destruct id as [| q]; [exact (fun x => x) |].
      rewrite !m2r_in_raw_ids_true; apply Hsub.
    - apply IH.
    - rewrite !andb_true_iff; intros [H1 H2]; split; [exact (IH _ H1) | exact (IH _ H2)].
  Qed.

  Lemma m2r_nodup_map_inv {A B} (f : A -> B) (xs : list A) :
    NoDup (List.map f xs) ->
    NoDup xs.
  Proof using.
    induction xs as [| x xs' IH]; cbn [List.map]; intros Hnd; [constructor |].
    inversion Hnd as [| ? ? Hnin Hnd']; subst.
    constructor; [intros Hx; exact (Hnin (in_map f xs' x Hx)) | apply IH, Hnd'].
  Qed.

  Lemma m2r_count_id_in_two_elems {A} (g : A -> list raw_id) (xs : list A)
    (a1 a2 : A) (q : raw_id) :
    NoDup xs ->
    In a1 xs ->
    In a2 xs ->
    a1 <> a2 ->
    In q (g a1) ->
    In q (g a2) ->
    (2 <= m2r_count_id q (flat_map g xs))%nat.
  Proof using.
    intros Hnd; induction Hnd as [| x xs' Hnin Hnd' IH]; cbn [In flat_map]; [intros [] |].
    intros [<- | Ha1] [<- | Ha2] Hne Hq1 Hq2; try contradiction.
    - rewrite m2r_count_id_app.
      pose proof (m2r_count_id_in_pos q (g x) Hq1).
      assert (Hin2 : In q (flat_map g xs')) by (apply in_flat_map; exists a2; split; assumption).
      pose proof (m2r_count_id_in_pos q (flat_map g xs') Hin2); lia.
    - rewrite m2r_count_id_app.
      pose proof (m2r_count_id_in_pos q (g x) Hq2).
      assert (Hin1 : In q (flat_map g xs')) by (apply in_flat_map; exists a1; split; assumption).
      pose proof (m2r_count_id_in_pos q (flat_map g xs') Hin1); lia.
    - rewrite m2r_count_id_app.
      pose proof (IH Ha1 Ha2 Hne Hq1 Hq2); lia.
  Qed.

  Lemma unique_alloca_not_in_fargs
    (fargs : list local_id) (bks : ocfg dtyp) (q : local_id) :
    In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks) ->
    ~ In q fargs.
  Proof using.
    intros Hq Hin_arg.
    apply m2r_collect_unique_allocas_inv in Hq as (Hcnt & bk0 & dt0 & anns0 & md0 & Hbk0 & Him0).
    rewrite m2r_count_id_app in Hcnt.
    pose proof (m2r_count_id_in_pos q fargs Hin_arg) as H1.
    assert (Hin_bks : In q (flat_map full_block_defs bks)).
    { apply in_flat_map; exists bk0; split; [exact Hbk0 |].
      unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
      apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0); split; [exact Him0 | left; reflexivity]. }
    pose proof (m2r_count_id_in_pos q _ Hin_bks) as H2; lia.
  Qed.

  Lemma unique_alloca_not_phi_def
    (fargs : list local_id) (bks : ocfg dtyp) (q : local_id) :
    NoDup (List.map blk_id bks) ->
    In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks) ->
    forall bk x ph md,
      In bk bks ->
      In (x, ph, md) (blk_phis bk) ->
      x <> q.
  Proof using.
    intros Hnd_ids Hq bk x ph md Hbk Hphi ->.
    pose proof (m2r_nodup_map_inv _ _ Hnd_ids) as Hnd_bks.
    apply m2r_collect_unique_allocas_inv in Hq as (Hcnt & bk0 & dt0 & anns0 & md0 & Hbk0 & Him0).
    rewrite m2r_count_id_app in Hcnt.
    assert (Hin_phi : In q (List.map (fun '(y, _, _) => y) (blk_phis bk))).
    { apply in_map_iff; exists (q, ph, md); split; [reflexivity | exact Hphi]. }
    assert (Hin_al : In q (flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk0))).
    { apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0); split; [exact Him0 | left; reflexivity]. }
    destruct (raw_id_eqb (blk_id bk) (blk_id bk0)) eqn:Eeq_id; [apply raw_id_eqb_spec in Eeq_id; rename Eeq_id into Heq_id | apply raw_id_eqb_neq in Eeq_id; rename Eeq_id into Hne_id].
    - assert (bk = bk0).
      { clear -Hnd_ids Hbk Hbk0 Heq_id; revert bk bk0 Hbk Hbk0 Heq_id.
        induction bks as [| b bs IH]; intros bk bk0 Hbk Hbk0 Heq_id;
          cbn [List.map In] in *; [contradiction |].
        inversion Hnd_ids as [| ? ? Hnin Hnd']; subst.
        destruct Hbk as [<- | Hbk], Hbk0 as [<- | Hbk0].
        - reflexivity.
        - exfalso; apply Hnin; rewrite Heq_id; apply in_map, Hbk0.
        - exfalso; apply Hnin; rewrite <- Heq_id; apply in_map, Hbk.
        - exact (IH Hnd' bk bk0 Hbk Hbk0 Heq_id). }
      subst bk0.
      assert (H2 : (2 <= m2r_count_id q (full_block_defs bk))%nat).
      { unfold full_block_defs; rewrite !m2r_count_id_app.
        pose proof (m2r_count_id_in_pos q _ Hin_phi).
        pose proof (m2r_count_id_in_pos q _ Hin_al); lia. }
      assert (Hge : (m2r_count_id q (full_block_defs bk) <= m2r_count_id q (flat_map full_block_defs bks))%nat).
      { clear -Hbk; induction bks as [| b bs IH]; cbn [In flat_map] in *; [contradiction |].
        rewrite m2r_count_id_app; destruct Hbk as [<- | Hbk]; [lia | specialize (IH Hbk); lia]. }
      lia.
    - assert (Hne_bk : bk <> bk0) by (intros ->; exact (Hne_id Logic.eq_refl)).
      assert (Hdef1 : In q (full_block_defs bk)) by (unfold full_block_defs; apply in_app_iff; left; exact Hin_phi).
      assert (Hdef2 : In q (full_block_defs bk0))
        by (unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left; exact Hin_al).
      pose proof (m2r_count_id_in_two_elems full_block_defs bks bk bk0 q Hnd_bks Hbk Hbk0 Hne_bk Hdef1 Hdef2).
      lia.
  Qed.

  Lemma unique_alloca_code_def_is_alloca
    (fargs : list local_id) (bks : ocfg dtyp) (q : local_id) :
    NoDup (List.map blk_id bks) ->
    In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks) ->
    forall bk pre ins md post,
      In bk bks ->
      blk_code bk = pre ++ (IId q, ins, md) :: post ->
      exists dt0 anns0, ins = INSTR_Alloca dt0 anns0.
  Proof using.
    intros Hnd_ids Hq bk pre ins md post Hbk Hsplit.
    pose proof (m2r_nodup_map_inv _ _ Hnd_ids) as Hnd_bks.
    apply m2r_collect_unique_allocas_inv in Hq as (Hcnt & bk0 & dt0 & anns0 & md0 & Hbk0 & Him0).
    rewrite m2r_count_id_app in Hcnt.
    destruct (raw_id_eqb (blk_id bk) (blk_id bk0)) eqn:Eeq_id; [apply raw_id_eqb_spec in Eeq_id; rename Eeq_id into Heq_id | apply raw_id_eqb_neq in Eeq_id; rename Eeq_id into Hne_id].
    - assert (bk = bk0).
      { clear -Hnd_ids Hbk Hbk0 Heq_id; revert bk bk0 Hbk Hbk0 Heq_id.
        induction bks as [| b bs IH]; intros bk bk0 Hbk Hbk0 Heq_id;
          cbn [List.map In] in *; [contradiction |].
        inversion Hnd_ids as [| ? ? Hnin Hnd']; subst.
        destruct Hbk as [<- | Hbk], Hbk0 as [<- | Hbk0].
        - reflexivity.
        - exfalso; apply Hnin; rewrite Heq_id; apply in_map, Hbk0.
        - exfalso; apply Hnin; rewrite <- Heq_id; apply in_map, Hbk.
        - exact (IH Hnd' bk bk0 Hbk Hbk0 Heq_id). }
      subst bk0.
      rewrite Hsplit in Him0; apply in_app_iff in Him0 as [Hin | [Heq_im | Hin]].
      + exfalso.
        assert (Hge : (m2r_count_id q (full_block_defs bk) <= m2r_count_id q (flat_map full_block_defs bks))%nat).
        { clear -Hbk; induction bks as [| b bs IH]; cbn [In flat_map] in *; [contradiction |].
          rewrite m2r_count_id_app; destruct Hbk as [<- | Hbk]; [lia | specialize (IH Hbk); lia]. }
        assert (H2 : (2 <= m2r_count_id q (full_block_defs bk))%nat).
        { unfold full_block_defs; rewrite Hsplit, m2r_flat_map_app.
          replace (flat_map (fun '(iid, _, _) => instr_id_defs iid) ((IId q, ins, md) :: post))
            with ([q] ++ flat_map (fun '(iid, _, _) => instr_id_defs iid) post) by reflexivity.
          rewrite !m2r_count_id_app.
          replace (m2r_count_id q [q]) with 1%nat
            by (cbn [m2r_count_id]; rewrite raw_id_eqb_refl; reflexivity).
          assert (Hp : In q (flat_map (fun '(iid, _, _) => instr_id_defs iid) pre)).
          { apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0);
              split; [exact Hin | left; reflexivity]. }
          pose proof (m2r_count_id_in_pos q _ Hp); lia. }
        lia.
      + inversion Heq_im; exists dt0, anns0; reflexivity.
      + exfalso.
        assert (Hge : (m2r_count_id q (full_block_defs bk) <= m2r_count_id q (flat_map full_block_defs bks))%nat).
        { clear -Hbk; induction bks as [| b bs IH]; cbn [In flat_map] in *; [contradiction |].
          rewrite m2r_count_id_app; destruct Hbk as [<- | Hbk]; [lia | specialize (IH Hbk); lia]. }
        assert (H2 : (2 <= m2r_count_id q (full_block_defs bk))%nat).
        { unfold full_block_defs; rewrite Hsplit, m2r_flat_map_app.
          replace (flat_map (fun '(iid, _, _) => instr_id_defs iid) ((IId q, ins, md) :: post))
            with ([q] ++ flat_map (fun '(iid, _, _) => instr_id_defs iid) post) by reflexivity.
          rewrite !m2r_count_id_app.
          replace (m2r_count_id q [q]) with 1%nat
            by (cbn [m2r_count_id]; rewrite raw_id_eqb_refl; reflexivity).
          assert (Hp : In q (flat_map (fun '(iid, _, _) => instr_id_defs iid) post)).
          { apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0);
              split; [exact Hin | left; reflexivity]. }
          pose proof (m2r_count_id_in_pos q _ Hp); lia. }
        lia.
    - exfalso.
      assert (Hne_bk : bk <> bk0) by (intros ->; exact (Hne_id Logic.eq_refl)).
      assert (Hdef1 : In q (full_block_defs bk)).
      { unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
        rewrite Hsplit; apply in_flat_map; exists (IId q, ins, md);
          split; [apply in_app_iff; right; left; reflexivity | left; reflexivity]. }
      assert (Hdef2 : In q (full_block_defs bk0)).
      { unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
        apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0); split; [exact Him0 | left; reflexivity]. }
      pose proof (m2r_count_id_in_two_elems full_block_defs bks bk bk0 q Hnd_bks Hbk Hbk0 Hne_bk Hdef1 Hdef2).
      lia.
  Qed.

  Definition safe_locals_env
    (P_unprom : list N) (safe_locals : list local_id)
    (env : @local_env (@ParamsV IP IPT)) : Prop :=
    forall q v,
      In q safe_locals ->
      Maps.lookup q env = Some v ->
      is_safe_ptr_dvalue P_unprom v.

  Lemma safe_locals_env_incl (P1 P2 : list N) (safe_locals : list local_id)
    (env : @local_env (@ParamsV IP IPT)) :
    incl P1 P2 ->
    safe_locals_env P1 safe_locals env ->
    safe_locals_env P2 safe_locals env.
  Proof using.
    intros Hinc Henv q v Hq Hlk.
    eapply is_safe_ptr_dvalue_incl; [exact Hinc | exact (Henv q v Hq Hlk)].
  Qed.

  Lemma select_switch_in
    (value : @dvalue (@ParamsV IP IPT)) (default_dest : block_id)
    (switches : list (@dvalue (@ParamsV IP IPT) * block_id)) (bid : block_id) :
    select_switch value default_dest switches = raise_ret bid ->
    bid = default_dest \/ In bid (List.map snd switches).
  Proof using.
    induction switches as [| [v id0] sw' IH]; cbn [select_switch List.map].
    - intros H; inversion H; left; reflexivity.
    - destruct value as [db1 | |]; try (intros H; discriminate H).
      destruct db1; try (intros H; discriminate H).
      destruct v as [db2 | |]; try (intros H; discriminate H).
      destruct db2; try (intros H; discriminate H).
      match goal with
      | |- context [Pos.eq_dec ?s1 ?s2] =>
          destruct (Pos.eq_dec s1 s2) as [? | _]; subst; [| intros H; discriminate H]
      end.
      cbn.
      match goal with
      | |- context [if ?c then _ else _] => destruct c
      end.
      + intros H; inversion H; right; left; reflexivity.
      + intros H; destruct (IH H) as [-> | Hin];
          [left; reflexivity | right; right; exact Hin].
  Qed.

  Lemma switch_dests_map_snd
    (dests : list (tint_literal * block_id))
    (switches : list (@dvalue (@ParamsV IP IPT) * block_id)) :
    map_monad
      (fun '((TInt_Literal sz x), id) =>
         ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
           (fun s => ExtLib.Structures.Monad.ret (@DVALUE_Base (@ParamsV IP IPT) s, id)))
      dests = raise_ret switches ->
    List.map snd switches = List.map snd dests.
  Proof using.
    revert switches; induction dests as [| [[sz x] id0] dests' IH]; intros switches H;
      cbn [map_monad] in H.
    - inversion H; reflexivity.
    - apply EOU_bind_ret_inv in H as ([v0 bid0] & Hhd & Htl).
      apply EOU_bind_ret_inv in Hhd as (s & _ & Heq0); inversion Heq0; subst.
      apply EOU_bind_ret_inv in Htl as (sw_tl & Hmap & Heq_sw); inversion Heq_sw; subst.
      cbn [List.map snd]; f_equal; apply IH, Hmap.
  Qed.

  Inductive tau_expand_ {E : Type -> Type} {R : Type}
    (r : itree E R -> itree E R -> Prop) : itree E R -> itree E R -> Prop :=
  | TE_Eq t1 t1' t2 t2' :
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      tau_expand_ r t1' t2' ->
      tau_expand_ r t1 t2
  | TE_Ret x :
      tau_expand_ r (Ret x) (Ret x)
  | TE_Tau m1 m2 :
      r m1 m2 ->
      tau_expand_ r (Tau m1) (Tau m2)
  | TE_Vis X (e : E X) k1 k2 :
      (forall x, r (k1 x) (k2 x)) ->
      tau_expand_ r (Vis e k1) (Vis e k2)
  | TE_TauL m1 t2 :
      tau_expand_ r m1 t2 ->
      tau_expand_ r (Tau m1) t2.

  Lemma tau_expand__mon {E : Type -> Type} {R : Type} :
    monotone2 (@tau_expand_ E R).
  Proof using.
    intros t1 t2 r r' IN LE.
    induction IN as [t1 t1' t2 t2' E1 E2 _ IH
                    | x
                    | m1 m2 Hr
                    | X e k1 k2 Hk
                    | m1 t2 _ IH].
    - eapply TE_Eq; [exact E1 | exact E2 | exact IH].
    - apply TE_Ret.
    - apply TE_Tau; apply LE, Hr.
    - apply TE_Vis; intros x; apply LE, Hk.
    - apply TE_TauL, IH.
  Qed.
  #[local] Hint Resolve tau_expand__mon : paco.

  Definition tau_expand {E : Type -> Type} {R : Type}
    (t1 t2 : itree E R) : Prop :=
    paco2 (@tau_expand_ E R) bot2 t1 t2.

  Lemma tau_expand_obs_eq {E : Type -> Type} {R : Type}
    (t1 t1' t2 t2' : itree E R) :
    t1 ≅ t1' ->
    t2 ≅ t2' ->
    tau_expand t1 t2 ->
    tau_expand t1' t2'.
  Proof using.
    intros E1 E2 H; punfold H; pstep.
    eapply TE_Eq; [symmetry; exact E1 | symmetry; exact E2 |].
    eapply tau_expand__mon; [exact H | intros a b [Hab | []]; left; exact Hab].
  Qed.

  Lemma tau_expand_refl {E : Type -> Type} {R : Type} :
    forall (t : itree E R), tau_expand t t.
  Proof using.
    pcofix CIH; intros t; pstep.
    eapply TE_Eq; [apply itree_eta | apply itree_eta |].
    destruct (observe t) as [x | m | X e k].
    - apply TE_Ret.
    - apply TE_Tau; right; apply CIH.
    - apply TE_Vis; intros x; right; apply CIH.
  Qed.

  Lemma tau_expand_bind {E : Type -> Type} {A B : Type} :
    forall (u1 u2 : itree E A) (k1 k2 : A -> itree E B),
      tau_expand u1 u2 ->
      (forall a, tau_expand (k1 a) (k2 a)) ->
      tau_expand (ITree.bind u1 k1) (ITree.bind u2 k2).
  Proof using.
    pcofix CIH; intros u1 u2 k1 k2 Hu Hk; punfold Hu; pstep.
    induction Hu as [t1 t1' t2 t2' E1 E2 _ IH
                    | x
                    | m1 m2 Hm
                    | X e h1 h2 Hh
                    | m1 t2 _ IH].
    - eapply TE_Eq; [rewrite E1; reflexivity | rewrite E2; reflexivity | exact IH].
    - eapply TE_Eq; [apply Eqit.bind_ret_l | apply Eqit.bind_ret_l |].
      specialize (Hk x); punfold Hk.
      eapply tau_expand__mon;
        [exact Hk | intros a b [Hab | []]; left; eapply paco2_mon; [exact Hab | intros ? ? []]].
    - eapply TE_Eq; [apply Eqit.bind_tau | apply Eqit.bind_tau |].
      apply TE_Tau; pclearbot; right; apply CIH; [exact Hm | exact Hk].
    - eapply TE_Eq; [apply Eqit.bind_vis | apply Eqit.bind_vis |].
      apply TE_Vis; intros x; specialize (Hh x); pclearbot; right; apply CIH; [exact Hh | exact Hk].
    - eapply TE_Eq; [apply Eqit.bind_tau | reflexivity |].
      apply TE_TauL, IH.
  Qed.

  Lemma tau_expand_bind_l {E : Type -> Type} {A B : Type} :
    forall (u1 u2 : itree E A) (k : A -> itree E B),
      tau_expand u1 u2 ->
      tau_expand (ITree.bind u1 k) (ITree.bind u2 k).
  Proof using.
    intros u1 u2 k Hu; apply tau_expand_bind; [exact Hu | intro a; apply tau_expand_refl].
  Qed.

  (** *** Lifting [tau_expand] to [refine_prov] without [Eqdep] *)

  Definition prov_te_vis_match {R : Type}
    (r : itree ProvBotE R -> itree ProvBotE R -> Prop)
    {X1} (e1 : ProvBotE X1) (k1 : X1 -> itree ProvBotE R)
    {X2} (e2 : ProvBotE X2) (k2 : X2 -> itree ProvBotE R) : Prop :=
    match e1 return (X1 -> itree ProvBotE R) -> Prop with
    | inl1 p1 => fun k1' =>
        match e2 return (X2 -> itree ProvBotE R) -> Prop with
        | inl1 p2 => fun k2' =>
            match p1 in ProvE Y1 return (Y1 -> itree ProvBotE R) -> Prop with
            | FreshProv => fun k1'' =>
                match p2 in ProvE Y2 return (Y2 -> itree ProvBotE R) -> Prop with
                | FreshProv => fun k2'' => forall p : N, r (k1'' p) (k2'' p)
                end k2'
            end k1'
        | inr1 _ => fun _ => False
        end k2
    | inr1 b1 => fun k1' =>
        match e2 return (X2 -> itree ProvBotE R) -> Prop with
        | inl1 _ => fun _ => False
        | inr1 b2 => fun k2' =>
            EqE_bot _ _ b1 b2 /\
            EqE_bot _ _ b2 b1 /\
            (forall a1 a2, EqA_bot _ _ b1 a1 b2 a2 -> r (k1' a1) (k2' a2)) /\
            (forall a2 a1, EqA_bot _ _ b2 a2 b1 a1 -> r (k1' a1) (k2' a2))
        end k2
    end k1.

  Definition prov_te_step_body {R : Type}
    (r : itree ProvBotE R -> itree ProvBotE R -> Prop)
    (ot1 ot2 : itree' ProvBotE R) : Prop :=
    match ot1 with
    | RetF r1 =>
        match ot2 with
        | RetF r2 => r1 = r2
        | _ => False
        end
    | TauF m1 =>
        match ot2 with
        | TauF m2 => r m1 m2
        | _ => False
        end
    | VisF _ e1 k1 =>
        match ot2 with
        | VisF _ e2 k2 => prov_te_vis_match r e1 k1 e2 k2
        | _ => False
        end
    end.

  Inductive prov_te_ {R : Type}
    (r : itree ProvBotE R -> itree ProvBotE R -> Prop)
    : itree ProvBotE R -> itree ProvBotE R -> Prop :=
  | PTE_Step t1 t2 :
      prov_te_step_body r (observe t1) (observe t2) ->
      prov_te_ r t1 t2
  | PTE_TauL t1 m1 t2 :
      observe t1 = TauF m1 ->
      prov_te_ r m1 t2 ->
      prov_te_ r t1 t2.

  Lemma prov_te__mon {R : Type} :
    monotone2 (@prov_te_ R).
  Proof using.
    intros t1 t2 r r' IN LE.
    induction IN as [t1 t2 Hstep | t1 m1 t2 Ht1 _ IH].
    - apply PTE_Step; unfold prov_te_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1],
               (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
      + exact Hstep.
      + apply LE, Hstep.
      + destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
        * destruct p1, p2; intros p; apply LE, Hstep.
        * destruct Hstep as (HE1 & HE2 & HA1 & HA2).
          split; [exact HE1 | split; [exact HE2 | split]].
          -- intros a1 a2 Ha; apply LE, HA1, Ha.
          -- intros a2 a1 Ha; apply LE, HA2, Ha.
    - eapply PTE_TauL; [exact Ht1 | exact IH].
  Qed.
  #[local] Hint Resolve prov_te__mon : paco.

  Definition prov_te {R : Type} (t1 t2 : itree ProvBotE R) : Prop :=
    paco2 (@prov_te_ R) bot2 t1 t2.

  Lemma prov_te__obs_eq {R : Type}
    (r r' : itree ProvBotE R -> itree ProvBotE R -> Prop)
    (Hr_eq : forall a1 a1' a2 a2',
               a1 ≅ a1' -> a2 ≅ a2' -> r a1 a2 -> r' a1' a2') :
    forall (t1 t1' t2 t2' : itree ProvBotE R),
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      prov_te_ r t1 t2 ->
      prov_te_ r' t1' t2'.
  Proof using.
    intros t1 t1' t2 t2' E1 E2 Hrel.
    revert t1' t2' E1 E2;
      induction Hrel as [t1 t2 Hstep | t1 m1 t2 Ht1 _ IH];
      intros t1' t2' E1 E2.
    - punfold E1; red in E1; punfold E2; red in E2.
      apply PTE_Step; unfold prov_te_step_body in *.
      destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
        try inversion Hchk; pclearbot.
      + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; exact Hstep.
      + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
      + destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
        * destruct p1, p2; intros p; eapply Hr_eq; [apply Hk1 | apply Hk2 | apply Hstep].
        * destruct Hstep as (HE1 & HE2 & HA1 & HA2).
          split; [exact HE1 | split; [exact HE2 | split]].
          -- intros a1 a2 Ha; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA1 a1 a2 Ha)].
          -- intros a2 a1 Ha; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA2 a2 a1 Ha)].
    - punfold E1; red in E1; rewrite Ht1 in E1;
        apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
      eapply PTE_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
  Qed.

  Lemma tau_expand_step_prov_te {R : Type} (t1 t2 : itree ProvBotE R) :
    tau_expand_ (upaco2 (@tau_expand_ ProvBotE R) bot2) t1 t2 ->
    prov_te_ (@tau_expand ProvBotE R) t1 t2.
  Proof using.
    intros Hte.
    induction Hte as [t1 t1' t2 t2' E1 E2 _ IH
                     | x
                     | m1 m2 Hm
                     | X e k1 k2 Hk
                     | m1 t2 _ IH].
    - eapply prov_te__obs_eq; [exact (@tau_expand_obs_eq ProvBotE R) | | | exact IH];
        symmetry; assumption.
    - apply PTE_Step; cbn; reflexivity.
    - pclearbot; apply PTE_Step; cbn; exact Hm.
    - apply PTE_Step; cbn.
      destruct e as [p | b]; cbn.
      + destruct p; intros q; specialize (Hk q); pclearbot; exact Hk.
      + split; [apply EqE_bot_refl | split; [apply EqE_bot_refl | split]].
        * intros a1 a2 Ha; apply EqA_bot_eq in Ha; subst a2;
            specialize (Hk a1); pclearbot; exact Hk.
        * intros a2 a1 Ha; apply EqA_bot_eq in Ha; subst a1;
            specialize (Hk a2); pclearbot; exact Hk.
    - eapply PTE_TauL; [reflexivity | exact IH].
  Qed.

  Lemma tau_expand_to_prov_te {R : Type} :
    forall (t1 t2 : itree ProvBotE R),
      tau_expand t1 t2 ->
      prov_te t1 t2.
  Proof using.
    pcofix CIH; intros t1 t2 Hte; pstep; punfold Hte.
    apply tau_expand_step_prov_te in Hte.
    eapply prov_te__mon; [exact Hte | intros a1 a2 Ha; right; apply CIH, Ha].
  Qed.

  Definition rel_te_l {R1 R2 : Type} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1' : itree ProvBotE R1) (t2 : itree ProvBotE R2) : Prop :=
    exists t1, prov_te t1' t1 /\ refine_prov RR U t1 t2.

  Lemma refine_prov_prov_te_l_step {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    refine_prov RR U t1 t2 ->
    forall t1',
      prov_te t1' t1 ->
      refine_prov_ RR (upaco3 (refine_prov_ RR) (rel_te_l RR)) U t1' t2.
  Proof using.
    intros Hrp; punfold Hrp.
    induction Hrp as [U t1 t2 Hstep_rp | U t1 m1 t2 Ht1 _ IH_rp | U t1 t2 m2 Ht2 _ IH_rp];
      intros t1' Hte.
    - punfold Hte; revert Hstep_rp.
      induction Hte as [t1' t1_ Hstep_te | t1' n1' t1_ Hot1' _ IH_te]; intros Hstep_rp.
      + apply RP_Step; unfold rp_step_body, prov_te_step_body in *.
        destruct (observe t1') as [x1' | m1' | X1' e1' k1'],
                 (observe t1_) as [x1 | m1 | X1 e1 k1]; try contradiction.
        * subst x1'; exact Hstep_rp.
        * destruct (observe t2) as [| m2 |]; try contradiction; pclearbot.
          right; exists m1; split; assumption.
        * destruct e1' as [p1' | b1'], e1 as [p1 | b1]; cbn in Hstep_te; try contradiction.
          -- destruct p1', p1.
             destruct Hstep_rp as [Hub | [Hleft | Hboth]]; [discriminate Hub | |].
             ++ right; left; intros p Hp.
                specialize (Hstep_te p); specialize (Hleft p Hp); pclearbot.
                right; exists (k1 p); split; assumption.
             ++ right; right.
                destruct (observe t2) as [| | X2 e2 k2]; try contradiction.
                destruct e2 as [p2 | b2]; cbn in *; try contradiction; destruct p2.
                intros p Hp; specialize (Hstep_te p); specialize (Hboth p Hp); pclearbot.
                right; exists (k1 p); split; assumption.
          -- destruct Hstep_te as (HE1' & _ & HA1' & _).
             destruct Hstep_rp as [Hub | [Hleft | Hboth]]; [| cbn in Hleft; contradiction |].
             ++ left; cbn in *; rewrite (EqE_bot_is_ub _ _ HE1'); exact Hub.
             ++ right; right.
                destruct (observe t2) as [| | X2 e2 k2]; try contradiction.
                destruct e2 as [p2 | b2]; cbn in *; try contradiction.
                destruct Hboth as [HE12 HA12].
                split; [eapply EqE_bot_trans; eassumption |].
                intros a1' a2 Ha1'2.
                destruct (EqA_bot_trans b1' b1 b2 a1' a2 HE1' HE12 Ha1'2) as [a1 [Ha1'1 Ha12]].
                specialize (HA1' a1' a1 Ha1'1); specialize (HA12 a1 a2 Ha12); pclearbot.
                rewrite (bot_ans_provs_eq b1' b1 a1' a1 HE1' Ha1'1).
                right; exists (k1 a1); split; assumption.
      + eapply RP_TauL; [exact Hot1' | exact (IH_te Hstep_rp)].
    - punfold Hte; revert Ht1.
      induction Hte as [t1' t1_ Hstep_te | t1' n1' t1_ Hot1' _ IH_te]; intros Ht1.
      + unfold prov_te_step_body in Hstep_te; rewrite Ht1 in Hstep_te.
        destruct (observe t1') as [| m1' |] eqn:Hot1'; try contradiction; pclearbot.
        eapply RP_TauL; [exact Hot1' | apply (IH_rp m1' Hstep_te)].
      + eapply RP_TauL; [exact Hot1' | apply (IH_te Ht1)].
    - eapply RP_TauR; [exact Ht2 | apply (IH_rp t1' Hte)].
  Qed.

  Lemma refine_prov_tau_expand_l {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 t1' : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    tau_expand t1' t1 ->
    refine_prov RR U t1 t2 ->
    refine_prov RR U t1' t2.
  Proof using.
    intros Hte Hrp; apply tau_expand_to_prov_te in Hte.
    assert (Hmain : forall U0 a1' a2, rel_te_l RR U0 a1' a2 -> refine_prov RR U0 a1' a2).
    { pcofix CIH; intros U0 a1' a2 (a1 & Hae & Har); pstep.
      eapply refine_prov__mon; [exact (refine_prov_prov_te_l_step RR U0 a1 a2 Har a1' Hae) |].
      intros U1 b1' b2 [Hb | Hb]; [left; eapply paco3_mon; [exact Hb | intros ? ? ? Hrel; apply CIH, Hrel] | right; apply CIH, Hb]. }
    apply Hmain; exists t1; split; assumption.
  Qed.

  Definition rel_te_r {R1 R2 : Type} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2' : itree ProvBotE R2) : Prop :=
    exists t2, prov_te t2' t2 /\ refine_prov RR U t1 t2.

  Lemma refine_prov_prov_te_r_step {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    refine_prov RR U t1 t2 ->
    forall t2',
      prov_te t2' t2 ->
      refine_prov_ RR (upaco3 (refine_prov_ RR) (rel_te_r RR)) U t1 t2'.
  Proof using.
    intros Hrp; punfold Hrp.
    induction Hrp as [U t1 t2 Hstep_rp | U t1 m1 t2 Ht1 _ IH_rp | U t1 t2 m2 Ht2 _ IH_rp];
      intros t2' Hte.
    - unfold rp_step_body in Hstep_rp.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1] eqn:Hot1.
      + punfold Hte; revert Hstep_rp.
        induction Hte as [t2' t2_ Hstep_te | t2' n2' t2_ Hot2' _ IH_te]; intros Hstep_rp.
        * apply RP_Step; unfold rp_step_body, prov_te_step_body in *; rewrite Hot1.
          destruct (observe t2') as [x2' | |], (observe t2_) as [x2 | |]; try contradiction.
          subst x2'; exact Hstep_rp.
        * eapply RP_TauR; [exact Hot2' | exact (IH_te Hstep_rp)].
      + punfold Hte; revert Hstep_rp.
        induction Hte as [t2' t2_ Hstep_te | t2' n2' t2_ Hot2' _ IH_te]; intros Hstep_rp.
        * apply RP_Step; unfold rp_step_body, prov_te_step_body in *; rewrite Hot1.
          destruct (observe t2') as [| m2' |], (observe t2_) as [| m2 |]; try contradiction.
          pclearbot; right; exists m2; split; assumption.
        * eapply RP_TauR; [exact Hot2' | exact (IH_te Hstep_rp)].
      + destruct Hstep_rp as [Hub | [Hleft | Hboth]].
        * apply RP_Step; unfold rp_step_body; rewrite Hot1; left; exact Hub.
        * apply RP_Step; unfold rp_step_body; rewrite Hot1; right; left.
          destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          right; exists t2; split; [exact Hte | exact Hleft].
        * punfold Hte; revert Hboth.
          induction Hte as [t2' t2_ Hstep_te | t2' n2' t2_ Hot2' _ IH_te]; intros Hboth.
          -- apply RP_Step; unfold rp_step_body, prov_te_step_body in *; rewrite Hot1.
             right; right.
             destruct (observe t2') as [| | X2' e2' k2'],
                      (observe t2_) as [| | X2 e2 k2]; try contradiction.
             destruct e1 as [p1 | b1], e2 as [p2 | b2], e2' as [p2' | b2'];
               cbn in *; try contradiction.
             ++ destruct p1, p2, p2'; intros p Hp.
                specialize (Hboth p Hp); specialize (Hstep_te p); pclearbot.
                right; exists (k2 p); split; assumption.
             ++ destruct Hboth as [HE12 HA12].
                destruct Hstep_te as (_ & HE22' & _ & HA22').
                split; [eapply EqE_bot_trans; eassumption |].
                intros a1 a2' Ha12'.
                destruct (EqA_bot_trans b1 b2 b2' a1 a2' HE12 HE22' Ha12') as [a2 [Ha12 Ha22']].
                specialize (HA12 a1 a2 Ha12); specialize (HA22' a2 a2' Ha22'); pclearbot.
                right; exists (k2 a2); split; assumption.
          -- eapply RP_TauR; [exact Hot2' | exact (IH_te Hboth)].
    - eapply RP_TauL; [exact Ht1 | apply (IH_rp t2' Hte)].
    - punfold Hte; revert Ht2.
      induction Hte as [t2' t2_ Hstep_te | t2' n2' t2_ Hot2' _ IH_te]; intros Ht2.
      + unfold prov_te_step_body in Hstep_te; rewrite Ht2 in Hstep_te.
        destruct (observe t2') as [| m2' |] eqn:Hot2'; try contradiction; pclearbot.
        eapply RP_TauR; [exact Hot2' | apply (IH_rp m2' Hstep_te)].
      + eapply RP_TauR; [exact Hot2' | apply (IH_te Ht2)].
  Qed.

  Lemma refine_prov_tau_expand_r {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2) :
    tau_expand t2' t2 ->
    refine_prov RR U t1 t2 ->
    refine_prov RR U t1 t2'.
  Proof using.
    intros Hte Hrp; apply tau_expand_to_prov_te in Hte.
    assert (Hmain : forall U0 a1 a2', rel_te_r RR U0 a1 a2' -> refine_prov RR U0 a1 a2').
    { pcofix CIH; intros U0 a1 a2' (a2 & Hae & Har); pstep.
      eapply refine_prov__mon; [exact (refine_prov_prov_te_r_step RR U0 a1 a2 Har a2' Hae) |].
      intros U1 b1 b2' [Hb | Hb]; [left; eapply paco3_mon; [exact Hb | intros ? ? ? Hrel; apply CIH, Hrel] | right; apply CIH, Hb]. }
    apply Hmain; exists t2; split; assumption.
  Qed.

  Lemma refine_prov_tau_expand {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 t1' : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2) :
    tau_expand t1' t1 ->
    tau_expand t2' t2 ->
    refine_prov RR U t1 t2 ->
    refine_prov RR U t1' t2'.
  Proof using.
    intros H1 H2 Hrp.
    eapply refine_prov_tau_expand_l; [exact H1 |].
    eapply refine_prov_tau_expand_r; [exact H2 | exact Hrp].
  Qed.

  (** *** Syntactic & CFG Structural Lemmas for Stage 1 and Stage 2 *)

  Lemma in_defs_in_cfg_all_ids {T : Set} (c : CFG.cfg T) (bk : block T) (x : raw_id) :
    In bk (blks c) ->
    In x (full_block_defs bk) ->
    In x (cfg_all_ids c).
  Proof using.
    intros Hbk Hx; unfold cfg_all_ids; right.
    apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
    apply in_flat_map; exists bk; split; assumption.
  Qed.

  Lemma in_uses_in_cfg_all_ids {T : Set} (c : CFG.cfg T) (bk : block T) (x : raw_id) :
    In bk (blks c) ->
    In x (full_block_uses bk) ->
    In x (cfg_all_ids c).
  Proof using.
    intros Hbk Hx; unfold cfg_all_ids; right.
    apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right.
    apply in_flat_map; exists bk; split; assumption.
  Qed.

  Lemma m2r_phi_entry_uses_in_block {T : Set} (bk : block T)
    (pe : local_id * phi T * list (metadata T)) (x : raw_id) :
    In pe (blk_phis bk) ->
    In x (m2r_phi_entry_uses pe) ->
    In x (full_block_uses bk).
  Proof using.
    intros Hpe Hx; unfold full_block_uses; apply in_app_iff; left.
    apply in_flat_map; exists pe; split; [exact Hpe |].
    destruct pe as [[y ph] mds]; exact Hx.
  Qed.

  Lemma m2r_code_entry_uses_in_block {T : Set} (bk : block T)
    (im : instr_id * instr T * list (metadata T)) (x : raw_id) :
    In im (blk_code bk) ->
    In x (m2r_code_entry_uses im) ->
    In x (full_block_uses bk).
  Proof using.
    intros Him Hx; unfold full_block_uses; apply in_app_iff; right; apply in_app_iff; left.
    apply in_flat_map; exists im; split; [exact Him |].
    destruct im as [[iid ins] mds]; exact Hx.
  Qed.

  Lemma m2r_term_entry_uses_in_block {T : Set} (bk : block T) (x : raw_id) :
    In x (m2r_term_entry_uses (blk_term bk)) ->
    In x (full_block_uses bk).
  Proof using.
    intros Hx; unfold full_block_uses; apply in_app_iff; right; apply in_app_iff; right.
    destruct (blk_term bk) as [[iid tm] mds]; exact Hx.
  Qed.

  Lemma find_promotable_in_init_code_inv
    (allow_calls : bool) (all_defs all_uses : list raw_id)
    (safe_locals : list local_id) (init_bid : block_id) (bks : ocfg dtyp)
    (b_init : block dtyp) (acc_pre rem : code dtyp)
    (pre_al : code dtyp) (al_ins : instr_id * instr dtyp * list (metadata dtyp))
    (post_al : code dtyp) (p : local_id) (dt : dtyp) :
    find_promotable_in_init_code allow_calls all_defs all_uses safe_locals
      init_bid bks b_init acc_pre rem = Some (pre_al, al_ins, post_al, p, dt) ->
    let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
    List.rev acc_pre ++ rem = pre_al ++ al_ins :: post_al /\
    (exists anns_al md_al,
       al_ins = (IId p, INSTR_Alloca dt anns_al, md_al) /\
       is_only_align_anns anns_al = true /\
       is_debug_or_file_md md_al = true) /\
    is_scalar_dtyp dt = true /\
    m2r_count_id p all_defs = 1%nat /\
    in_raw_ids p all_uses = true /\
    forallb (check_other_instr_for_slot allow_calls safe_no_p p) pre_al = true /\
    forallb (check_code_entry_for_slot allow_calls safe_no_p p dt) post_al = true /\
    in_raw_ids p (m2r_term_entry_uses (blk_term b_init)) = false /\
    m2r_non_invoke_term (snd (fst (blk_term b_init))) = true /\
    forallb (fun bk => if raw_id_eqb (blk_id bk) init_bid then true
                       else check_block_non_entry_for_slot allow_calls safe_no_p p dt bk) bks = true.
  Proof using.
    revert acc_pre; induction rem as [| im rem' IH]; intros acc_pre H;
      cbn [find_promotable_in_init_code] in H; [discriminate H |].
    match type of H with
    | context [match ?c with Some _ => _ | None => _ end] =>
        destruct c as [res |] eqn:Ecand
    end.
    - inversion H; subst; clear H.
      destruct im as [[iid ins] md_al]; destruct iid as [p0 |]; [| discriminate Ecand].
      destruct ins; try discriminate Ecand.
      match type of Ecand with
      | (if ?g then _ else _) = _ => destruct g eqn:Eg; [| discriminate Ecand]
      end.
      inversion Ecand; subst; clear Ecand.
      rewrite !andb_true_iff, !negb_true_iff, Nat.eqb_eq in Eg.
      destruct Eg as (((((((((Hsc & Hanns) & Hmd) & Hcnt) & Huse) & Hpre) & Hpost) & Hterm_p) & Hterm_ni) & Hbks).
      cbv zeta.
      split; [reflexivity |].
      split; [eexists _, _; split; [reflexivity | split; assumption] |].
      repeat split; assumption.
    - apply IH in H; cbv zeta in *.
      destruct H as (Hsplit & Hal & Hrest).
      split; [| split; [exact Hal | exact Hrest]].
      cbn [List.rev] in Hsplit; rewrite <- app_assoc in Hsplit; exact Hsplit.
  Qed.

  Lemma find_trailing_dead_alloca_in_code_inv
    (all_defs all_uses : list raw_id) (safe_locals : list local_id)
    (acc_pre rem : code dtyp)
    (pre_al : code dtyp) (al_ins : instr_id * instr dtyp * list (metadata dtyp))
    (post_al : code dtyp) (p : local_id) (dt : dtyp) :
    find_trailing_dead_alloca_in_code all_defs all_uses safe_locals acc_pre rem =
      Some (pre_al, al_ins, post_al, p, dt) ->
    let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
    List.rev acc_pre ++ rem = pre_al ++ al_ins :: post_al /\
    (exists anns_al md_al,
       al_ins = (IId p, INSTR_Alloca dt anns_al, md_al) /\
       is_only_align_anns anns_al = true /\
       is_debug_or_file_md md_al = true) /\
    is_scalar_dtyp dt = true /\
    m2r_count_id p all_defs = 1%nat /\
    in_raw_ids p all_uses = false /\
    forallb (check_other_instr_for_slot false safe_no_p p) pre_al = true /\
    forallb (check_no_alloca_or_call_instr safe_no_p) post_al = true.
  Proof using.
    revert acc_pre; induction rem as [| im rem' IH]; intros acc_pre H;
      cbn [find_trailing_dead_alloca_in_code] in H; [discriminate H |].
    destruct (find_trailing_dead_alloca_in_code all_defs all_uses safe_locals (im :: acc_pre) rem')
      as [later |] eqn:Elater.
    - inversion H; subst later; clear H.
      apply IH in Elater; cbv zeta in *.
      destruct Elater as (Hsplit & Hal & Hrest).
      split; [| split; [exact Hal | exact Hrest]].
      cbn [List.rev] in Hsplit; rewrite <- app_assoc in Hsplit; exact Hsplit.
    - destruct im as [[iid ins] md_al]; destruct iid as [p0 |]; [| discriminate H].
      destruct ins; try discriminate H.
      match type of H with
      | (if ?g then _ else _) = _ => destruct g eqn:Eg; [| discriminate H]
      end.
      inversion H; subst; clear H.
      rewrite !andb_true_iff, !negb_true_iff, Nat.eqb_eq in Eg.
      destruct Eg as ((((((Hsc & Hanns) & Hmd) & Hcnt) & Huse) & Hpre) & Hpost).
      cbv zeta.
      split; [reflexivity |].
      split; [eexists _, _; split; [reflexivity | split; assumption] |].
      repeat split; assumption.
  Qed.

  Lemma promote_first_in_defs_inv
    (interproc_safe : bool)
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    promote_first_in_defs interproc_safe defs = Some defs' ->
    exists pre df df' post,
      defs = pre ++ df :: post /\
      defs' = pre ++ df' :: post /\
      try_promote_slot_in_defn interproc_safe df = Some df'.
  Proof using.
    revert defs'; induction defs as [| d rest IH]; intros defs' H;
      cbn [promote_first_in_defs] in H; [discriminate H |].
    destruct (try_promote_slot_in_defn interproc_safe d) as [d' |] eqn:Ed.
    - inversion H; subst defs'; exists [], d, d', rest; repeat split; assumption.
    - destruct (promote_first_in_defs interproc_safe rest) as [rest' |] eqn:Erest;
        cbn in H; [| discriminate H].
      inversion H; subst defs'; clear H.
      destruct (IH rest' Logic.eq_refl) as (pre & df & df' & post & -> & -> & Htry).
      exists (d :: pre), df, df', post; repeat split; exact Htry.
  Qed.

  Lemma elim_first_dead_alloca_in_defs_inv
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    elim_first_dead_alloca_in_defs defs = Some defs' ->
    exists pre df df' post,
      defs = pre ++ df :: post /\
      defs' = pre ++ df' :: post /\
      try_elim_dead_alloca_in_defn df = Some df'.
  Proof using.
    revert defs'; induction defs as [| d rest IH]; intros defs' H;
      cbn [elim_first_dead_alloca_in_defs] in H; [discriminate H |].
    destruct (try_elim_dead_alloca_in_defn d) as [d' |] eqn:Ed.
    - inversion H; subst defs'; exists [], d, d', rest; repeat split; assumption.
    - destruct (elim_first_dead_alloca_in_defs rest) as [rest' |] eqn:Erest;
        cbn in H; [| discriminate H].
      inversion H; subst defs'; clear H.
      destruct (IH rest' Logic.eq_refl) as (pre & df & df' & post & -> & -> & Htry).
      exists (d :: pre), df, df', post; repeat split; exact Htry.
  Qed.

  Lemma rewrite_code_for_slot_fresh_inv
    (avoid0 : list raw_id) (p : local_id) (dt : dtyp)
    (cur_reg : local_id) (avoid : list raw_id) (cd : code dtyp)
    (cd' : code dtyp) (end_reg : local_id) (avoid' : list raw_id) :
    rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_reg, avoid') ->
    incl avoid0 avoid ->
    ~ In cur_reg avoid0 ->
    incl avoid avoid' /\ ~ In end_reg avoid0.
  Proof using.
    revert cur_reg avoid cd' end_reg avoid';
      induction cd as [| im rest IH];
      intros cur_reg avoid cd' end_reg avoid' Hrw Hinc Hcur;
      cbn [rewrite_code_for_slot] in Hrw.
    - inversion Hrw; subst; split; [apply incl_refl | exact Hcur].
    - destruct (is_promotable_load_of p dt im) as [dst |].
      + set (lv_reg := fresh_name "mlv" (p :: cur_reg :: avoid)) in *.
        destruct (rewrite_code_for_slot p dt cur_reg (lv_reg :: avoid) rest) as [[rest' er] av'] eqn:E.
        inversion Hrw; subst.
        assert (Hinc1 : incl avoid0 (lv_reg :: avoid)) by (intros z Hz; right; apply Hinc, Hz).
        destruct (IH cur_reg (lv_reg :: avoid) rest' end_reg avoid' E Hinc1 Hcur) as [Hav Her].
        split; [intros z Hz; apply Hav; right; exact Hz | exact Her].
      + destruct (is_promotable_store_of p dt im) as [val_exp |].
        * set (sv_reg := fresh_name "msv" (p :: avoid)) in *.
          set (st_reg := fresh_name "mst" (p :: sv_reg :: avoid)) in *.
          destruct (rewrite_code_for_slot p dt st_reg (st_reg :: sv_reg :: avoid) rest) as [[rest' er] av'] eqn:E.
          inversion Hrw; subst.
          assert (Hst : ~ In st_reg avoid0).
          { intros Hin0; exact (fresh_name_not_in "mst" (p :: sv_reg :: avoid)
                                   (or_intror (or_intror (Hinc _ Hin0)))). }
          assert (Hinc1 : incl avoid0 (st_reg :: sv_reg :: avoid))
            by (intros z Hz; right; right; apply Hinc, Hz).
          destruct (IH st_reg (st_reg :: sv_reg :: avoid) rest' end_reg avoid' E Hinc1 Hst) as [Hav Her].
          split; [intros z Hz; apply Hav; right; right; exact Hz | exact Her].
        * destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:E.
          inversion Hrw; subst; eapply IH; eassumption.
  Qed.

  Lemma lookup_end_reg_in_nodup
    (end_map : list (block_id * local_id)) (bid : block_id) (r def_r : local_id) :
    NoDup (List.map fst end_map) ->
    In (bid, r) end_map ->
    lookup_end_reg end_map bid def_r = r.
  Proof using.
    induction end_map as [| [b0 r0] rest IH]; cbn [In List.map fst lookup_end_reg];
      [intros _ [] |].
    intros Hnd [Heq | Hin].
    - inversion Heq; subst b0 r0; rewrite raw_id_eqb_refl; reflexivity.
    - inversion Hnd as [| ? ? Hnin Hnd']; subst.
      destruct (raw_id_eqb b0 bid) eqn:Eb0; [apply raw_id_eqb_spec in Eb0; subst b0 | clear Eb0].
      + exfalso; apply Hnin; apply in_map with (f := fst) in Hin; exact Hin.
      + apply IH; assumption.
  Qed.

  (** *** Expression & Dynamic-Value Size Measures and [withCall] Lifters *)

  Fixpoint m2r_exp_size {T : Set} (e : exp T) : nat :=
    let fix list_sz (l : list (T * exp T)) : nat :=
      match l with
      | [] => O
      | (_, ex) :: rest => S (m2r_exp_size ex + list_sz rest)
      end
    in
    match e with
    | EXP_Cstring elts | EXP_Struct elts | EXP_Packed_struct elts
    | EXP_Array elts | EXP_Vector elts => S (list_sz elts)
    | OP_IBinop _ _ e1 e2 | OP_ICmp _ _ _ e1 e2
    | OP_FBinop _ _ _ e1 e2 | OP_FCmp _ _ _ e1 e2 =>
        S (m2r_exp_size e1 + m2r_exp_size e2)
    | OP_Fneg _ (_, e1) | OP_Conversion _ _ e1 _
    | OP_ExtractValue (_, e1) _ | OP_Freeze (_, e1)
    | EXP_Splat (_, e1) => S (m2r_exp_size e1)
    | OP_GetElementPtr _ _ (_, ep) idxs =>
        S (m2r_exp_size ep + list_sz idxs)
    | OP_ExtractElement (_, e1) (_, e2)
    | OP_InsertValue (_, e1) (_, e2) _ =>
        S (m2r_exp_size e1 + m2r_exp_size e2)
    | OP_InsertElement (_, e1) (_, e2) (_, e3)
    | OP_ShuffleVector (_, e1) (_, e2) (_, e3)
    | OP_Select _ (_, e1) (_, e2) (_, e3) =>
        S (m2r_exp_size e1 + m2r_exp_size e2 + m2r_exp_size e3)
    | EXP_Metadata (METADATA_Const (_, ex)) => S (m2r_exp_size ex)
    | _ => 1%nat
    end.

  Lemma m2r_exp_size_pos {T : Set} (e : exp T) :
    (1 <= m2r_exp_size e)%nat.
  Proof using.
    destruct e; try (destruct m as [| | [? ?] | | | |]);
      repeat match goal with p : _ * exp _ |- _ => destruct p end;
      cbn [m2r_exp_size]; lia.
  Qed.

  Fixpoint m2r_dvalue_size (dv : @dvalue (@ParamsV IP IPT)) : nat :=
    let fix list_sz (l : list (@dvalue (@ParamsV IP IPT))) : nat :=
      match l with
      | [] => O
      | v :: rest => S (m2r_dvalue_size v + list_sz rest)
      end
    in
    match dv with
    | DVALUE_Base _ => 1%nat
    | DVALUE_Struct _ fields => S (list_sz fields)
    | DVALUE_Array _ elts => S (list_sz elts)
    end.

  Lemma m2r_dvalue_size_pos (dv : @dvalue (@ParamsV IP IPT)) :
    (1 <= m2r_dvalue_size dv)%nat.
  Proof using.
    destruct dv; cbn; lia.
  Qed.

  Lemma withCall_ret_eq {R} (x : R) :
    @withCall (@ParamsV IP IPT) R (Ret x) ≅ Ret x.
  Proof using.
    unfold withCall; rewrite unfold_translate; reflexivity.
  Qed.

  Lemma withCall_bind_eq {A B}
    (u : @MCFGtop (@ParamsV IP IPT) A)
    (k : A -> @MCFGtop (@ParamsV IP IPT) B) :
    withCall (ITree.bind u k) ≅ ITree.bind (withCall u) (fun x => withCall (k x)).
  Proof using.
    unfold withCall; apply TranslateFacts.translate_bind.
  Qed.

  Lemma withCall_trigger_eq {X} (me : @MCFGEtop (@ParamsV IP IPT) X) :
    withCall (ITree.trigger me) ≅ ITree.trigger (inr1 me).
  Proof using.
    unfold withCall, ITree.trigger; rewrite unfold_translate; cbn.
    apply eqit_Vis; intros x; rewrite unfold_translate; reflexivity.
  Qed.

  Lemma interp_mrec_trigger_inr1 {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) :
    interp_mrec (mrec_ctx ctx) (ITree.trigger (inr1 me)) ≅
    ITree.bind (ITree.trigger me) (fun x => Tau (Ret x)).
  Proof using.
    rewrite bind_trigger; unfold ITree.trigger.
    rewrite unfold_interp_mrec; cbn [_interp_mrec].
    apply eqit_Vis; intros x; rewrite interp_mrec_ret; reflexivity.
  Qed.

  Lemma tau_expand_cfg_withCall_ret {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : R) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (Ret x)) s)
      (interp_mcfg_model (Ret x) s).
  Proof using.
    eapply tau_expand_obs_eq.
    - symmetry; rewrite (interp_cfg_model_obs_eq ctx _ _ s (withCall_ret_eq x)),
        interp_cfg_model_ret; reflexivity.
    - symmetry; apply interp_mcfg_model_ret.
    - apply tau_expand_refl.
  Qed.

  Lemma tau_expand_cfg_withCall_bind {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (u : @MCFGtop (@ParamsV IP IPT) A)
    (k : A -> @MCFGtop (@ParamsV IP IPT) B) (s : FusedS) :
    tau_expand (interp_cfg_model ctx (withCall u) s) (interp_mcfg_model u s) ->
    (forall s' a,
       tau_expand (interp_cfg_model ctx (withCall (k a)) s') (interp_mcfg_model (k a) s')) ->
    tau_expand
      (interp_cfg_model ctx (withCall (ITree.bind u k)) s)
      (interp_mcfg_model (ITree.bind u k) s).
  Proof using.
    intros Hu Hk; eapply tau_expand_obs_eq.
    - symmetry; rewrite (interp_cfg_model_obs_eq ctx _ _ s (withCall_bind_eq u k)),
        interp_cfg_model_bind; reflexivity.
    - symmetry; apply interp_mcfg_model_bind.
    - eapply tau_expand_bind; [exact Hu | intros [s' a]; apply Hk].
  Qed.

  Lemma tau_expand_cfg_withCall_trigger {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (ITree.trigger me)) s)
      (interp_mcfg_model (ITree.trigger me) s).
  Proof using.
    eapply tau_expand_obs_eq.
    - symmetry.
      rewrite (interp_cfg_model_obs_eq ctx _ _ s (withCall_trigger_eq me)).
      unfold interp_cfg_model.
      rewrite (interp_mcfg_model_obs_eq _ _ s (interp_mrec_trigger_inr1 ctx me)).
      apply interp_mcfg_model_bind.
    - rewrite <- (Eqit.bind_ret_r (interp_mcfg_model (ITree.trigger me) s)) at 1; reflexivity.
    - eapply tau_expand_bind; [apply tau_expand_refl |].
      intros [s' x]; eapply tau_expand_obs_eq.
      + symmetry; rewrite interp_mcfg_model_tau, interp_mcfg_model_ret; reflexivity.
      + reflexivity.
      + pstep; apply TE_TauL, TE_Ret.
  Qed.

  Lemma tau_expand_cfg_withCall_EOU {A}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (m : EOU A) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (EOU_to_itree m)) s)
      (interp_mcfg_model (EOU_to_itree m) s).
  Proof using.
    destruct m as [msg | msg | msg | v]; cbn [EOU_to_itree].
    - unfold raise, trigger_cast; eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_trigger | intros ? []].
    - unfold raiseOOM, trigger_cast; eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_trigger | intros ? []].
    - unfold raiseUB, trigger_cast; eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_trigger | intros ? []].
    - apply tau_expand_cfg_withCall_ret.
  Qed.

  Lemma tau_expand_cfg_withCall_map_monad {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (f : A -> @MCFGtop (@ParamsV IP IPT) B) (xs : list A)
    (Hf : forall a s0,
            In a xs ->
            tau_expand (interp_cfg_model ctx (withCall (f a)) s0) (interp_mcfg_model (f a) s0)) :
    forall s,
      tau_expand
        (interp_cfg_model ctx (withCall (map_monad f xs)) s)
        (interp_mcfg_model (map_monad f xs) s).
  Proof using.
    induction xs as [| a xs' IH]; intros s; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - apply tau_expand_cfg_withCall_ret.
    - eapply tau_expand_cfg_withCall_bind; [apply Hf; left; reflexivity |].
      intros s1 b; eapply tau_expand_cfg_withCall_bind.
      + apply IH; intros a' s0 Ha'; apply Hf; right; exact Ha'.
      + intros s2 bs; apply tau_expand_cfg_withCall_ret.
  Qed.

  Lemma tau_expand_cfg_withCall_convert
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (ct : conversion_type) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (convert ct t_from dv t_to)) s)
      (interp_mcfg_model (convert ct t_from dv t_to) s).
  Proof using.
    unfold convert; destruct ct as [| pct | ict].
    - destruct (dtyp_eqb t_from t_to); [apply tau_expand_cfg_withCall_ret |].
      match goal with |- context [(?a =? ?b)%N] => destruct (a =? b)%N end.
      + apply tau_expand_cfg_withCall_EOU.
      + apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
    - apply tau_expand_cfg_withCall_EOU.
    - unfold conv, Subevent.trigger; try unfold trigger_cast; apply tau_expand_cfg_withCall_trigger.
  Qed.

  Lemma tau_expand_cfg_withCall_freeze_base
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (db : @dvalue_base (@ParamsV IP IPT)) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (freeze_base dt db)) s)
      (interp_mcfg_model (freeze_base dt db) s).
  Proof using.
    unfold freeze_base.
    destruct db as [| | | | | | | sz bv].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold draw, Subevent.trigger; try unfold trigger_cast; apply tau_expand_cfg_withCall_trigger.
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - destruct bv as [| | bits].
      + unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
          eapply tau_expand_cfg_withCall_bind;
          [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
          eapply tau_expand_cfg_withCall_bind;
          [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + destruct (existsb is_poison_bit bits); cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        * eapply tau_expand_cfg_withCall_bind.
          -- unfold draw, Subevent.trigger; try unfold trigger_cast; apply tau_expand_cfg_withCall_trigger.
          -- intros s' x; apply tau_expand_cfg_withCall_ret.
        * unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
            eapply tau_expand_cfg_withCall_bind;
            [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
  Qed.

  Lemma tau_expand_cfg_withCall_freeze
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (freeze dt dv)) s)
      (interp_mcfg_model (freeze dt dv) s).
  Proof using.
    remember (m2r_dvalue_size dv) as sz eqn:Esz.
    assert (Hle : (m2r_dvalue_size dv <= sz)%nat) by lia; clear Esz.
    revert dv dt s Hle; induction sz as [| sz IH]; intros dv dt s Hle.
    - pose proof (m2r_dvalue_size_pos dv); lia.
    - destruct dv as [db | p fields | vec elts]; cbn [freeze].
      + apply tau_expand_cfg_withCall_freeze_base.
      + destruct dt as [| p' dts |];
          [apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)
          |
          | apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)].
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply tau_expand_cfg_withCall_bind; [| intros ? ?; apply tau_expand_cfg_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Hfld : ( (fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) fields <= sz)%nat) by lia.
        clear Hle.
        lazymatch goal with
        | |- tau_expand (interp_cfg_model ctx (withCall (?go1 fields dts [])) s)
                        (interp_mcfg_model (?go2 fields dts []) s) =>
            cut (forall acc : list (@dvalue (@ParamsV IP IPT)),
                    tau_expand (interp_cfg_model ctx (withCall (go1 fields dts acc)) s)
                               (interp_mcfg_model (go2 fields dts acc) s));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert dts s Hfld; induction fields as [| v vs IHf]; intros [| t ts] s Hfld acc;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        * apply tau_expand_cfg_withCall_ret.
        * apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
        * apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
        * eapply tau_expand_cfg_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _ t v); apply IH; lia.
          -- intros s1 v'; apply IHf; lia.
      + destruct dt as [| | v' sz_n t];
          [apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)
          | apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)
          |].
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply tau_expand_cfg_withCall_bind; [| intros ? ?; apply tau_expand_cfg_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Helt : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) elts <= sz)%nat) by lia.
        clear Hle.
        lazymatch goal with
        | |- tau_expand (interp_cfg_model ctx (withCall (?go1 elts [])) s)
                        (interp_mcfg_model (?go2 elts []) s) =>
            cut (forall acc : list (@dvalue (@ParamsV IP IPT)),
                    tau_expand (interp_cfg_model ctx (withCall (go1 elts acc)) s)
                               (interp_mcfg_model (go2 elts acc) s));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert s Helt; induction elts as [| v vs IHe]; intros s Helt acc;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        * apply tau_expand_cfg_withCall_ret.
        * eapply tau_expand_cfg_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _ t v); apply IH; lia.
          -- intros s1 v1; apply IHe; lia.
  Qed.

  Lemma tau_expand_cfg_withCall_denote_exp
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (top : option dtyp) (e : exp dtyp) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (denote_exp' top e) s)
      (interp_mcfg_model (denote_exp top e) s).
  Proof using.
    unfold denote_exp'.
    remember (m2r_exp_size e) as sz eqn:Esz.
    assert (Hle : (m2r_exp_size e <= sz)%nat) by lia; clear Esz.
    revert top e s Hle; induction sz as [| sz IH]; intros top e s Hle.
    - pose proof (m2r_exp_size_pos e); lia.
    - assert (Hlist :
        forall (elts : list (dtyp * exp dtyp)) s0,
          (S ((fix list_sz l := match l with [] => O | (_, ex) :: r => S (m2r_exp_size ex + list_sz r) end) elts) <= S sz)%nat ->
          tau_expand
            (interp_cfg_model ctx (withCall (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts)) s0)
            (interp_mcfg_model (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts) s0)).
      { intros elts s0 Helts; apply tau_expand_cfg_withCall_map_monad.
        intros [dt0 ex0] s1 Hin.
        apply IH.
        clear -Hin Helts; induction elts as [| [d1 e1] rest IHr]; [contradiction |].
        destruct Hin as [Heq | Hin]; [inversion Heq; subst; lia | apply IHr; [lia | exact Hin]]. }
      destruct e; cbn [denote_exp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; cbn [m2r_exp_size] in Hle.
      + destruct id as [gid | lid]; cbn [lookup_id];
          unfold gread, lread, Subevent.trigger; try unfold trigger_cast;
          apply tau_expand_cfg_withCall_trigger.
      + destruct top as [t |]; [apply tau_expand_cfg_withCall_EOU | apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)].
      + destruct top as [t |]; [apply tau_expand_cfg_withCall_EOU | apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)].
      + destruct b; apply tau_expand_cfg_withCall_ret.
      + apply tau_expand_cfg_withCall_ret.
      + destruct top as [t |]; [apply tau_expand_cfg_withCall_EOU | apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)].
      + eapply tau_expand_cfg_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + apply tau_expand_cfg_withCall_ret.
      + apply tau_expand_cfg_withCall_ret.
      + eapply tau_expand_cfg_withCall_bind; [apply (Hlist fields s Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + eapply tau_expand_cfg_withCall_bind; [apply tau_expand_cfg_withCall_EOU |].
        intros s1 []; eapply tau_expand_cfg_withCall_bind; [apply (Hlist fields s1 Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + eapply tau_expand_cfg_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + eapply tau_expand_cfg_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + destruct v as [dt1 op1]; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_convert].
      + destruct ptrval as [dt2 ptr_e].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros s1 vptr; eapply tau_expand_cfg_withCall_bind; [apply Hlist; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
      + destruct vec as [dt1 e1], idx as [dt2 e2].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + destruct vec as [dt1 e1], elt as [dt2 e2], idx as [dt3 e3].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros s1 v1; eapply tau_expand_cfg_withCall_bind.
        * eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
        * intros s2 elt_v; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
      + destruct vec1 as [dt1 e1], vec2 as [dt2 e2], idxmask as [dt3 e3].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s2 v2; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]]].
      + destruct vec as [dt1 e1]; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
      + destruct vec as [dt1 e1], elt as [dt2 e2].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + destruct cnd as [dt1 e1], v1 as [dt2 e2], v2 as [dt3 e3].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 vc; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s2 vv1; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]]].
      + destruct v as [dt1 e1]; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_freeze].
      + apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
      + match goal with m0 : metadata _ |- _ => destruct m0 as [| | [dt1 ex1] | | | |] end;
          try apply tau_expand_cfg_withCall_ret.
        apply IH; cbn in Hle; lia.
      + destruct elt as [dt1 e1].
        eapply tau_expand_cfg_withCall_bind; [apply tau_expand_cfg_withCall_EOU |].
        intros s1 [sz_v t_v]; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + unfold gread, Subevent.trigger; try unfold trigger_cast; apply tau_expand_cfg_withCall_trigger.
  Qed.

  Definition mcfg_inr_exc {R : Type}
    (u : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS)
    : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R)) :=
    ITree.bind (interp_mcfg_model u s) (fun '(s', r) => Ret (s', inr r)).

  Lemma tau_expand_exc_withCall_ret {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : R) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (Ret x)) s)
      (mcfg_inr_exc (Ret x) s).
  Proof using.
    unfold mcfg_inr_exc; eapply tau_expand_obs_eq.
    - symmetry; rewrite (interp_cfg_exc_obs_eq ctx _ _ s (withCall_ret_eq x)),
        interp_cfg_exc_ret; reflexivity.
    - symmetry; rewrite interp_mcfg_model_ret, Eqit.bind_ret_l; reflexivity.
    - apply tau_expand_refl.
  Qed.

  Lemma tau_expand_exc_withCall_bind {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (u : @MCFGtop (@ParamsV IP IPT) A)
    (k : A -> @MCFGtop (@ParamsV IP IPT) B) (s : FusedS) :
    tau_expand (interp_cfg_exc ctx (withCall u) s) (mcfg_inr_exc u s) ->
    (forall s' a,
       tau_expand (interp_cfg_exc ctx (withCall (k a)) s') (mcfg_inr_exc (k a) s')) ->
    tau_expand
      (interp_cfg_exc ctx (withCall (ITree.bind u k)) s)
      (mcfg_inr_exc (ITree.bind u k) s).
  Proof using.
    intros Hu Hk; unfold mcfg_inr_exc in *.
    eapply tau_expand_obs_eq with
      (t2 := ITree.bind
               (ITree.bind (interp_mcfg_model u s) (fun '(s', a) => Ret (s', inr a)))
               (fun '(s', res) =>
                  match res with
                  | inl ex => Ret (s', @inl (@exc (@ParamsV IP IPT)) B ex)
                  | inr a =>
                      ITree.bind (interp_mcfg_model (k a) s') (fun '(s'', r) => Ret (s'', inr r))
                  end)).
    - symmetry; rewrite (interp_cfg_exc_obs_eq ctx _ _ s (withCall_bind_eq u k)),
        interp_cfg_exc_bind; reflexivity.
    - rewrite interp_mcfg_model_bind, !Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' a] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
    - eapply tau_expand_bind; [exact Hu |].
      intros [s' [ex | a]].
      + apply tau_expand_refl.
      + apply Hk.
  Qed.

  Lemma tau_expand_exc_withCall_trigger {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS)
    (Hne : exc_of_event (inr1 me) = None) :
    tau_expand
      (interp_cfg_exc ctx (withCall (ITree.trigger me)) s)
      (mcfg_inr_exc (ITree.trigger me) s).
  Proof using.
    unfold mcfg_inr_exc; eapply tau_expand_obs_eq.
    - symmetry.
      rewrite (interp_cfg_exc_obs_eq ctx _ _ s (withCall_trigger_eq me)).
      exact (interp_cfg_exc_trigger_non_exc ctx (inr1 me) s Hne).
    - reflexivity.
    - eapply tau_expand_bind.
      + eapply tau_expand_obs_eq;
          [apply (interp_cfg_model_obs_eq ctx _ _ s (withCall_trigger_eq me))
          | reflexivity
          | apply tau_expand_cfg_withCall_trigger].
      + intros [s' y]; pstep; apply TE_TauL, TE_Ret.
  Qed.

  Lemma tau_expand_exc_withCall_EOU {A}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (m : EOU A) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (EOU_to_itree m)) s)
      (mcfg_inr_exc (EOU_to_itree m) s).
  Proof using.
    destruct m as [msg | msg | msg | v]; cbn [EOU_to_itree].
    - unfold raise, trigger_cast; eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_trigger; reflexivity | intros ? []].
    - unfold raiseOOM, trigger_cast; eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_trigger; reflexivity | intros ? []].
    - unfold raiseUB, trigger_cast; eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_trigger; reflexivity | intros ? []].
    - apply tau_expand_exc_withCall_ret.
  Qed.

  Lemma tau_expand_exc_withCall_map_monad {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (f : A -> @MCFGtop (@ParamsV IP IPT) B) (xs : list A)
    (Hf : forall a s0,
            In a xs ->
            tau_expand (interp_cfg_exc ctx (withCall (f a)) s0) (mcfg_inr_exc (f a) s0)) :
    forall s,
      tau_expand
        (interp_cfg_exc ctx (withCall (map_monad f xs)) s)
        (mcfg_inr_exc (map_monad f xs) s).
  Proof using.
    induction xs as [| a xs' IH]; intros s; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - apply tau_expand_exc_withCall_ret.
    - eapply tau_expand_exc_withCall_bind; [apply Hf; left; reflexivity |].
      intros s1 b; eapply tau_expand_exc_withCall_bind.
      + apply IH; intros a' s0 Ha'; apply Hf; right; exact Ha'.
      + intros s2 bs; apply tau_expand_exc_withCall_ret.
  Qed.

  Lemma tau_expand_exc_withCall_convert
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (ct : conversion_type) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (convert ct t_from dv t_to)) s)
      (mcfg_inr_exc (convert ct t_from dv t_to) s).
  Proof using.
    unfold convert; destruct ct as [| pct | ict].
    - destruct (dtyp_eqb t_from t_to); [apply tau_expand_exc_withCall_ret |].
      match goal with |- context [(?a =? ?b)%N] => destruct (a =? b)%N end.
      + apply tau_expand_exc_withCall_EOU.
      + apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
    - apply tau_expand_exc_withCall_EOU.
    - unfold conv, Subevent.trigger; try unfold trigger_cast;
        apply tau_expand_exc_withCall_trigger; reflexivity.
  Qed.

  Lemma tau_expand_exc_withCall_freeze_base
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (db : @dvalue_base (@ParamsV IP IPT)) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (freeze_base dt db)) s)
      (mcfg_inr_exc (freeze_base dt db) s).
  Proof using.
    unfold freeze_base.
    destruct db as [| | | | | | | sz bv].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold draw, Subevent.trigger; try unfold trigger_cast;
        apply tau_expand_exc_withCall_trigger; reflexivity.
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - destruct bv as [| | bits].
      + unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
          eapply tau_expand_exc_withCall_bind;
          [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
      + unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
          eapply tau_expand_exc_withCall_bind;
          [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
      + destruct (existsb is_poison_bit bits); cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        * eapply tau_expand_exc_withCall_bind.
          -- unfold draw, Subevent.trigger; try unfold trigger_cast;
               apply tau_expand_exc_withCall_trigger; reflexivity.
          -- intros s' x; apply tau_expand_exc_withCall_ret.
        * unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
            eapply tau_expand_exc_withCall_bind;
            [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
  Qed.

  Lemma tau_expand_exc_withCall_freeze
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (freeze dt dv)) s)
      (mcfg_inr_exc (freeze dt dv) s).
  Proof using.
    remember (m2r_dvalue_size dv) as sz eqn:Esz.
    assert (Hle : (m2r_dvalue_size dv <= sz)%nat) by lia; clear Esz.
    revert dv dt s Hle; induction sz as [| sz IH]; intros dv dt s Hle.
    - pose proof (m2r_dvalue_size_pos dv); lia.
    - destruct dv as [db | p fields | vec elts]; cbn [freeze].
      + apply tau_expand_exc_withCall_freeze_base.
      + destruct dt as [| p' dts |];
          [apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)
          |
          | apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)].
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply tau_expand_exc_withCall_bind; [| intros ? ?; apply tau_expand_exc_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Hfld : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) fields <= sz)%nat) by lia.
        clear Hle.
        lazymatch goal with
        | |- tau_expand (interp_cfg_exc ctx (withCall (?go1 fields dts [])) s)
                        (mcfg_inr_exc (?go2 fields dts []) s) =>
            cut (forall acc : list (@dvalue (@ParamsV IP IPT)),
                    tau_expand (interp_cfg_exc ctx (withCall (go1 fields dts acc)) s)
                               (mcfg_inr_exc (go2 fields dts acc) s));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert dts s Hfld; induction fields as [| v vs IHf]; intros [| t ts] s Hfld acc;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        * apply tau_expand_exc_withCall_ret.
        * apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
        * apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
        * eapply tau_expand_exc_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _ t v); apply IH; lia.
          -- intros s1 v'; apply IHf; lia.
      + destruct dt as [| | v' sz_n t];
          [apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)
          | apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)
          |].
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply tau_expand_exc_withCall_bind; [| intros ? ?; apply tau_expand_exc_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Helt : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) elts <= sz)%nat) by lia.
        clear Hle.
        lazymatch goal with
        | |- tau_expand (interp_cfg_exc ctx (withCall (?go1 elts [])) s)
                        (mcfg_inr_exc (?go2 elts []) s) =>
            cut (forall acc : list (@dvalue (@ParamsV IP IPT)),
                    tau_expand (interp_cfg_exc ctx (withCall (go1 elts acc)) s)
                               (mcfg_inr_exc (go2 elts acc) s));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert s Helt; induction elts as [| v vs IHe]; intros s Helt acc;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        * apply tau_expand_exc_withCall_ret.
        * eapply tau_expand_exc_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _ t v); apply IH; lia.
          -- intros s1 v1; apply IHe; lia.
  Qed.

  Lemma tau_expand_exc_withCall_denote_exp
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (top : option dtyp) (e : exp dtyp) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (denote_exp' top e) s)
      (mcfg_inr_exc (denote_exp top e) s).
  Proof using.
    unfold denote_exp'.
    remember (m2r_exp_size e) as sz eqn:Esz.
    assert (Hle : (m2r_exp_size e <= sz)%nat) by lia; clear Esz.
    revert top e s Hle; induction sz as [| sz IH]; intros top e s Hle.
    - pose proof (m2r_exp_size_pos e); lia.
    - assert (Hlist :
        forall (elts : list (dtyp * exp dtyp)) s0,
          (S ((fix list_sz l := match l with [] => O | (_, ex) :: r => S (m2r_exp_size ex + list_sz r) end) elts) <= S sz)%nat ->
          tau_expand
            (interp_cfg_exc ctx (withCall (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts)) s0)
            (mcfg_inr_exc (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts) s0)).
      { intros elts s0 Helts; apply tau_expand_exc_withCall_map_monad.
        intros [dt0 ex0] s1 Hin.
        apply IH.
        clear -Hin Helts; induction elts as [| [d1 e1] rest IHr]; [contradiction |].
        destruct Hin as [Heq | Hin]; [inversion Heq; subst; lia | apply IHr; [lia | exact Hin]]. }
      destruct e; cbn [denote_exp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; cbn [m2r_exp_size] in Hle.
      + destruct id as [gid | lid]; cbn [lookup_id];
          unfold gread, lread, Subevent.trigger; try unfold trigger_cast;
          apply tau_expand_exc_withCall_trigger; reflexivity.
      + destruct top as [t |]; [apply tau_expand_exc_withCall_EOU | apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)].
      + destruct top as [t |]; [apply tau_expand_exc_withCall_EOU | apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)].
      + destruct b; apply tau_expand_exc_withCall_ret.
      + apply tau_expand_exc_withCall_ret.
      + destruct top as [t |]; [apply tau_expand_exc_withCall_EOU | apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)].
      + eapply tau_expand_exc_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + apply tau_expand_exc_withCall_ret.
      + apply tau_expand_exc_withCall_ret.
      + eapply tau_expand_exc_withCall_bind; [apply (Hlist fields s Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + eapply tau_expand_exc_withCall_bind; [apply tau_expand_exc_withCall_EOU |].
        intros s1 []; eapply tau_expand_exc_withCall_bind; [apply (Hlist fields s1 Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + eapply tau_expand_exc_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + eapply tau_expand_exc_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + destruct v as [dt1 op1]; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_convert].
      + destruct ptrval as [dt2 ptr_e].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros s1 vptr; eapply tau_expand_exc_withCall_bind; [apply Hlist; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
      + destruct vec as [dt1 e1], idx as [dt2 e2].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + destruct vec as [dt1 e1], elt as [dt2 e2], idx as [dt3 e3].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros s1 v1; eapply tau_expand_exc_withCall_bind.
        * eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
        * intros s2 elt_v; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
      + destruct vec1 as [dt1 e1], vec2 as [dt2 e2], idxmask as [dt3 e3].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s2 v2; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]]].
      + destruct vec as [dt1 e1]; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
      + destruct vec as [dt1 e1], elt as [dt2 e2].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + destruct cnd as [dt1 e1], v1 as [dt2 e2], v2 as [dt3 e3].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 vc; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s2 vv1; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]]].
      + destruct v as [dt1 e1]; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_freeze].
      + apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
      + match goal with m0 : metadata _ |- _ => destruct m0 as [| | [dt1 ex1] | | | |] end;
          try apply tau_expand_exc_withCall_ret.
        apply IH; cbn in Hle; lia.
      + destruct elt as [dt1 e1].
        eapply tau_expand_exc_withCall_bind; [apply tau_expand_exc_withCall_EOU |].
        intros s1 [sz_v t_v]; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_ret].
      + unfold gread, Subevent.trigger; try unfold trigger_cast;
          apply tau_expand_exc_withCall_trigger; reflexivity.
  Qed.

  (** *** Parametric Expression Simulation Across All Memory Invariants *)

  Lemma refine_mcfg_gread_same_g
    (gid : raw_id) (U : list N)
    (σ1 σ2 : state)
    (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
    (g : @global_env (@ParamsV IP IPT)) :
    let s1 := (σ1, (ls1, g)) in
    let s2 := (σ2, (ls2, g)) in
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
         (forall P_unprom, genv_safe P_unprom g -> is_safe_ptr_dvalue P_unprom v2))
      U
      (interp_mcfg_model (gread gid) s1)
      (interp_mcfg_model (gread gid) s2).
  Proof using.
    cbv zeta; unfold gread, Subevent.trigger; try unfold trigger_cast.
    destruct (Maps.lookup gid g) as [v |] eqn:Elk.
    - assert (H1 : interp_vellvm_prov_h (subevent _ (GlobalRead gid)) (σ1, (ls1, g)) ≅ Ret ((σ1, (ls1, g)), v)).
      { unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
        unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref;
          cbn - [Maps.lookup Maps.add lift_bot_prov].
        rewrite Elk, !lift_bot_prov_bind_ret, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity. }
      assert (H2 : interp_vellvm_prov_h (subevent _ (GlobalRead gid)) (σ2, (ls2, g)) ≅ Ret ((σ2, (ls2, g)), v)).
      { unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
        unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref;
          cbn - [Maps.lookup Maps.add lift_bot_prov].
        rewrite Elk, !lift_bot_prov_bind_ret, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity. }
      eapply refine_prov_tau_star_l; [eapply tau_star_mcfg_det; [reflexivity | exact H1] |].
      eapply refine_prov_tau_star_r; [eapply tau_star_mcfg_det; [reflexivity | exact H2] |].
      apply refine_prov_ret.
      repeat split; [intros P_unprom Hg; exact (Hg gid v Elk)].
    - eapply refine_prov_obs_eq.
      + symmetry; apply interp_mcfg_model_non_intr; reflexivity.
      + symmetry; apply interp_mcfg_model_non_intr; reflexivity.
      + unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
        unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref;
          cbn - [Maps.lookup Maps.add lift_bot_prov].
        rewrite Elk.
        unfold raise, trigger_cast, ITree.trigger, lift_bot_prov;
          cbn - [Maps.lookup Maps.add].
        pstep; apply RP_Step; unfold rp_step_body.
        repeat (rewrite observe_bind || rewrite observe_translate);
          cbn; try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun; cbn;
          right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_mcfg_lread_same_opt
    (lid : local_id) (U : list N)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g1 g2 : @global_env (@ParamsV IP IPT))
    (Hlk_eq : Maps.lookup lid (stack_vars sf1) = Maps.lookup lid (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g1)) in
    let s2 := (σ2, ((sf2, fstk2), g2)) in
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
         Maps.lookup lid (stack_vars sf2) = Some v2)
      U
      (interp_mcfg_model (lread lid) s1)
      (interp_mcfg_model (lread lid) s2).
  Proof using.
    cbv zeta; unfold lread, Subevent.trigger; try unfold trigger_cast.
    destruct (Maps.lookup lid (stack_vars sf2)) as [v |] eqn:Elk2.
    - assert (Elk1 : Maps.lookup lid (stack_vars sf1) = Some v) by congruence.
      eapply refine_prov_tau_star_l.
      + eapply tau_star_mcfg_det; [reflexivity | apply (fused_local_prov_read_some lid v (σ1, ((sf1, fstk1), g1)) Elk1)].
      + eapply refine_prov_tau_star_r.
        * eapply tau_star_mcfg_det; [reflexivity | apply (fused_local_prov_read_some lid v (σ2, ((sf2, fstk2), g2)) Elk2)].
        * apply refine_prov_ret; repeat split; exact Elk2.
    - assert (Elk1 : Maps.lookup lid (stack_vars sf1) = None) by congruence.
      destruct (fused_local_prov_read_none lid (σ1, ((sf1, fstk1), g1)) Elk1) as (msg1 & k1 & H1).
      destruct (fused_local_prov_read_none lid (σ2, ((sf2, fstk2), g2)) Elk2) as (msg2 & k2 & H2).
      eapply refine_prov_obs_eq.
      + symmetry; etransitivity; [apply interp_mcfg_model_non_intr; reflexivity |].
        unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
        rewrite H1, Eqit.bind_vis; reflexivity.
      + symmetry; etransitivity; [apply interp_mcfg_model_non_intr; reflexivity |].
        unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
        rewrite H2, Eqit.bind_vis; reflexivity.
      + pstep; apply RP_Step; cbn; try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun; cbn;
          right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_mcfg_draw_sync
    (dt : dtyp) (U : list N) (s1 s2 : FusedS) :
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2)
      U
      (interp_mcfg_model (draw dt) s1)
      (interp_mcfg_model (draw dt) s2).
  Proof using.
    unfold draw, Subevent.trigger; try unfold trigger_cast.
    destruct (default_dvalue_of_dtyp dt) as [msg | msg | msg | dv] eqn:Edef.
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_non_intr; reflexivity
        | symmetry; apply interp_mcfg_model_non_intr; reflexivity |].
      unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
      try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
      unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree].
      unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
        cbn; try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun; cbn;
        right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_non_intr; reflexivity
        | symmetry; apply interp_mcfg_model_non_intr; reflexivity |].
      unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
      try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
      unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree].
      unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
        cbn; try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun; cbn; left; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_non_intr; reflexivity
        | symmetry; apply interp_mcfg_model_non_intr; reflexivity |].
      unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
      try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
      unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree].
      unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
        cbn; try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun; cbn; left; reflexivity.
    - assert (Hd1 : interp_vellvm_prov_h (subevent _ (Draw dt)) s1 ≅ Ret (s1, dv)).
      { unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
        unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
        rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity. }
      assert (Hd2 : interp_vellvm_prov_h (subevent _ (Draw dt)) s2 ≅ Ret (s2, dv)).
      { unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
        unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
        rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity. }
      eapply refine_prov_tau_star_l; [eapply tau_star_mcfg_det; [reflexivity | exact Hd1] |].
      eapply refine_prov_tau_star_r; [eapply tau_star_mcfg_det; [reflexivity | exact Hd2] |].
      apply refine_prov_ret; repeat split.
  Qed.

  Lemma refine_mcfg_convert_sync
    (ct : conversion_type) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (U : list N) (s1 s2 : FusedS) :
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2)
      U
      (interp_mcfg_model (convert ct t_from dv t_to) s1)
      (interp_mcfg_model (convert ct t_from dv t_to) s2).
  Proof using.
    unfold convert; destruct ct as [| pct | ict].
    - destruct (dtyp_eqb t_from t_to).
      + eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split].
      + match goal with |- context [(?a =? ?b)%N] => destruct (a =? b)%N end.
        * eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split].
        * apply refine_mcfg_raise_both.
    - eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split].
    - destruct s1 as [σ1 rest1], s2 as [σ2 rest2].
      unfold conv, Subevent.trigger; try unfold trigger_cast.
      apply refine_mcfg_memory_event.
      cbn [handle_memoryM].
      eapply refine_prov_weaken; [apply convert_impure_id_sync |].
      intros U' [σ1' r1] [σ2' r2] (-> & -> & -> & ->); repeat split.
  Qed.

  Lemma refine_mcfg_freeze_sync
    (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT))
    (U : list N) (s1 s2 : FusedS) :
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2)
      U
      (interp_mcfg_model (freeze dt dv) s1)
      (interp_mcfg_model (freeze dt dv) s2).
  Proof using.
    assert (Hret_sync :
      forall A (x : A) U0 a1 a2,
        refine_prov (fun U' '(s1', r1) '(s2', r2) => U' = U0 /\ s1' = a1 /\ s2' = a2 /\ r1 = r2) U0
          (interp_mcfg_model (Ret x) a1) (interp_mcfg_model (Ret x) a2)).
    { intros A x U0 a1 a2; eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split]. }
    assert (Hfmap_ret :
      forall db0 U0 a1 a2,
        refine_prov (fun U' '(s1', r1) '(s2', r2) => U' = U0 /\ s1' = a1 /\ s2' = a2 /\ r1 = r2) U0
          (interp_mcfg_model (DVALUE_Base <$> ExtLib.Structures.Monad.ret db0) a1)
          (interp_mcfg_model (DVALUE_Base <$> ExtLib.Structures.Monad.ret db0) a2)).
    { intros db0 U0 a1 a2; unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree.
      eapply refine_mcfg_model_bind; [apply Hret_sync | intros ? ? ? ? ? _ (-> & -> & -> & ->); apply Hret_sync]. }
    assert (Hbase :
      forall dt0 db0 U0 a1 a2,
        refine_prov (fun U' '(s1', r1) '(s2', r2) => U' = U0 /\ s1' = a1 /\ s2' = a2 /\ r1 = r2) U0
          (interp_mcfg_model (freeze_base dt0 db0) a1)
          (interp_mcfg_model (freeze_base dt0 db0) a2)).
    { intros dt0 db0 U0 a1 a2; unfold freeze_base; destruct db0 as [| | | | | | | sz_b bv];
        try apply Hfmap_ret; [apply refine_mcfg_draw_sync |].
      destruct bv as [| | bits]; try apply Hfmap_ret.
      destruct (existsb is_poison_bit bits); [| apply Hfmap_ret].
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      eapply refine_mcfg_model_bind; [apply refine_mcfg_draw_sync | intros ? ? ? ? ? _ (-> & -> & -> & ->); apply Hret_sync]. }
    remember (m2r_dvalue_size dv) as sz eqn:Esz.
    assert (Hle : (m2r_dvalue_size dv <= sz)%nat) by lia; clear Esz.
    revert dv dt U s1 s2 Hle; induction sz as [| sz IH]; intros dv dt U s1 s2 Hle.
    - pose proof (m2r_dvalue_size_pos dv); lia.
    - destruct dv as [db | p fields | vec elts]; cbn [freeze].
      + apply Hbase.
      + destruct dt as [| p' dts |];
          [apply refine_mcfg_raise_both | | apply refine_mcfg_raise_both].
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply refine_mcfg_model_bind with (RA := fun U' '(s1', r1) '(s2', r2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2);
          [| intros ? ? ? ? ? _ (-> & -> & -> & ->); apply Hret_sync].
        cbn [m2r_dvalue_size] in Hle.
        assert (Hfld : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) fields <= sz)%nat) by lia.
        clear Hle.
        lazymatch goal with
        | |- refine_prov ?R U (interp_mcfg_model (?go fields dts []) s1)
                              (interp_mcfg_model (?go fields dts []) s2) =>
            cut (forall acc : list (@dvalue (@ParamsV IP IPT)),
                    refine_prov R U (interp_mcfg_model (go fields dts acc) s1)
                                    (interp_mcfg_model (go fields dts acc) s2));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert dts U s1 s2 Hfld; induction fields as [| v vs IHf]; intros [| t ts] U s1 s2 Hfld acc;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          [apply Hret_sync | apply refine_mcfg_raise_both | apply refine_mcfg_raise_both |].
        eapply refine_mcfg_model_bind.
        * fold (@freeze (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _ t v); apply IH; lia.
        * intros ? ? ? ? ? _ (-> & -> & -> & ->); apply IHf; lia.
      + destruct dt as [| | v' sz_n t];
          [apply refine_mcfg_raise_both | apply refine_mcfg_raise_both |].
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply refine_mcfg_model_bind with (RA := fun U' '(s1', r1) '(s2', r2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2);
          [| intros ? ? ? ? ? _ (-> & -> & -> & ->); apply Hret_sync].
        cbn [m2r_dvalue_size] in Hle.
        assert (Helt : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) elts <= sz)%nat) by lia.
        clear Hle.
        lazymatch goal with
        | |- refine_prov ?R U (interp_mcfg_model (?go elts []) s1)
                              (interp_mcfg_model (?go elts []) s2) =>
            cut (forall acc : list (@dvalue (@ParamsV IP IPT)),
                    refine_prov R U (interp_mcfg_model (go elts acc) s1)
                                    (interp_mcfg_model (go elts acc) s2));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert U s1 s2 Helt; induction elts as [| v vs IHe]; intros U s1 s2 Helt acc;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; [apply Hret_sync |].
        eapply refine_mcfg_model_bind.
        * fold (@freeze (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _ t v); apply IH; lia.
        * intros ? ? ? ? ? _ (-> & -> & -> & ->); apply IHe; lia.
  Qed.

  Lemma denote_exp_mcfg_sim
    (top : option dtyp) (e : exp dtyp) (U : list N)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (full_exp_uses e) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
         (forall P_unprom safe_locals,
            genv_safe P_unprom g ->
            safe_locals_env P_unprom safe_locals (stack_vars sf2) ->
            m2r_safe_ptr_exp safe_locals e = true ->
            is_safe_ptr_dvalue P_unprom v2))
      U
      (interp_mcfg_model (denote_exp top e) s1)
      (interp_mcfg_model (denote_exp top e) s2).
  Proof using.
    cbv zeta.
    remember (m2r_exp_size e) as sz eqn:Esz.
    assert (Hle : (m2r_exp_size e <= sz)%nat) by lia; clear Esz.
    revert top e U σ1 σ2 sf1 sf2 fstk1 fstk2 Hle Hvars;
      induction sz as [| sz IH];
      intros top e U σ1 σ2 sf1 sf2 fstk1 fstk2 Hle Hvars.
    - pose proof (m2r_exp_size_pos e); lia.
    - set (s1 := (σ1, ((sf1, fstk1), g))).
      set (s2 := (σ2, ((sf2, fstk2), g))).
      assert (Hlist :
        forall (elts : list (dtyp * exp dtyp)),
          (S ((fix list_sz l := match l with [] => O | (_, ex) :: r => S (m2r_exp_size ex + list_sz r) end) elts) <= S sz)%nat ->
          (forall x,
             In x ((fix go l := match l with [] => [] | (_, ex) :: r => full_exp_uses ex ++ go r end) elts) ->
             Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) ->
          refine_prov
            (fun U' '(s1', vs1) '(s2', vs2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ vs1 = vs2)
            U
            (interp_mcfg_model (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts) s1)
            (interp_mcfg_model (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts) s2)).
      { induction elts as [| [dt0 ex0] rest IHr]; intros Hsz0 Hv0;
          cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        - eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split].
        - eapply refine_mcfg_model_bind.
          + apply IH; [lia | intros x Hx; apply Hv0, in_app_iff; left; exact Hx].
          + intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
            eapply refine_mcfg_model_bind.
            * apply IHr; [lia | intros x Hx; apply Hv0, in_app_iff; right; exact Hx].
            * intros ? ? ? ? ? _ (-> & -> & -> & <-).
              eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split]. }
      assert (Hnosafe :
        forall v : @dvalue (@ParamsV IP IPT),
          m2r_safe_ptr_exp = m2r_safe_ptr_exp ->
          (forall safe_locals, m2r_safe_ptr_exp safe_locals e = false) ->
          forall P_unprom safe_locals,
            genv_safe P_unprom g ->
            safe_locals_env P_unprom safe_locals (stack_vars sf2) ->
            m2r_safe_ptr_exp safe_locals e = true ->
            is_safe_ptr_dvalue P_unprom v).
      { intros v _ Hfalse ? safe_locals _ _ Htrue; rewrite (Hfalse safe_locals) in Htrue; discriminate Htrue. }
      destruct e; cbn [denote_exp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; cbn [m2r_exp_size] in Hle.
      + destruct id as [gid | lid]; cbn [lookup_id].
        * eapply refine_prov_weaken; [apply refine_mcfg_gread_same_g |].
          intros U' [s1' v1] [s2' v2] (-> & -> & -> & -> & Hsafe).
          repeat split; intros P_unprom safe_locals Hg _ _; apply Hsafe, Hg.
        * eapply refine_prov_weaken.
          -- apply refine_mcfg_lread_same_opt; apply Hvars; left; reflexivity.
          -- intros U' [s1' v1] [s2' v2] (-> & -> & -> & -> & Hlk2).
             repeat split; intros P_unprom safe_locals _ Hloc Hsafe.
             cbn [m2r_safe_ptr_exp] in Hsafe; apply in_raw_ids_spec in Hsafe.
             exact (Hloc lid v2 Hsafe Hlk2).
      + destruct top as [t |]; [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate] | apply refine_mcfg_raise_both].
      + destruct top as [t |]; [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate] | apply refine_mcfg_raise_both].
      + destruct b; eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate.
      + eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
        apply refine_prov_ret; repeat split; intros; apply null_safe_ptr_dvalue.
      + destruct top as [t |]; [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate] | apply refine_mcfg_raise_both].
      + eapply refine_mcfg_model_bind; [apply (Hlist elts Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
        apply refine_prov_ret; repeat split; intros; apply poison_safe_ptr_dvalue.
      + eapply refine_mcfg_model_bind; [apply (Hlist fields Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind with (RA := fun U' '(s1', r1) '(s2', r2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2);
          [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros [] ? <-; repeat split] |].
        intros ? ? [] ? [] _ (-> & -> & -> & _).
        eapply refine_mcfg_model_bind; [apply (Hlist fields Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply (Hlist elts Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply (Hlist elts Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct v as [dt1 op1]; eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_prov_weaken; [apply refine_mcfg_convert_sync | intros ? [? ?] [? ?] (-> & -> & -> & ->); repeat split; intros; discriminate].
      + destruct ptrval as [dt2 ptr_e].
        eapply refine_mcfg_model_bind.
        * apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx].
        * intros ? ? vptr ? ? _ (-> & -> & -> & <- & Hptr_safe).
          eapply refine_mcfg_model_bind.
          -- apply Hlist; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; exact Hx].
          -- intros ? ? vs ? ? _ (-> & -> & -> & <-).
             destruct (eval_gep flags t vptr vs) as [msg | msg | msg | res] eqn:Egep; cbn [EOU_to_itree].
             ++ apply refine_mcfg_raise_both.
             ++ apply refine_mcfg_raiseOOM_l.
             ++ apply refine_mcfg_raiseUB_l.
             ++ eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
                apply refine_prov_ret; repeat split.
                intros P_unprom safe_locals Hg Hloc Hsafe; cbn [m2r_safe_ptr_exp] in Hsafe.
                eapply eval_gep_safe_ptr; [exact (Hptr_safe P_unprom safe_locals Hg Hloc Hsafe) | exact Egep].
      + destruct vec as [dt1 e1], idx as [dt2 e2].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct vec as [dt1 e1], elt as [dt2 e2], idx as [dt3 e3].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind with (RA := fun U' '(s1', r1) '(s2', r2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2).
        * eapply refine_mcfg_model_bind;
            [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hx]
            | intros ? ? ? ? ? _ (-> & -> & -> & <- & _); eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split]].
        * intros ? ? ? ? ? _ (-> & -> & -> & <-).
          eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; right; exact Hx] |].
          intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
          eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct vec1 as [dt1 e1], vec2 as [dt2 e2], idxmask as [dt3 e3].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct vec as [dt1 e1]; eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct vec as [dt1 e1], elt as [dt2 e2].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct cnd as [dt1 e1], v1 as [dt2 e2], v2 as [dt3 e3].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? vc ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hx] |].
        intros ? ? vv1 ? ? _ (-> & -> & -> & <- & Hs1).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; right; exact Hx] |].
        intros ? ? vv2 ? ? _ (-> & -> & -> & <- & Hs2).
        destruct (eval_select vc dt2 vv1 vv2) as [msg | msg | msg | res] eqn:Esel; cbn [EOU_to_itree].
        * apply refine_mcfg_raise_both.
        * apply refine_mcfg_raiseOOM_l.
        * apply refine_mcfg_raiseUB_l.
        * eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
          apply refine_prov_ret; repeat split.
          intros P_unprom safe_locals Hg Hloc Hsafe; cbn [m2r_safe_ptr_exp] in Hsafe.
          rewrite andb_true_iff in Hsafe; destruct Hsafe as [Hs_e2 Hs_e3].
          eapply eval_select_safe_ptr;
            [exact (Hs1 P_unprom safe_locals Hg Hloc Hs_e2)
            | exact (Hs2 P_unprom safe_locals Hg Hloc Hs_e3)
            | exact Esel].
      + destruct v as [dt1 e1]; eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_prov_weaken; [apply refine_mcfg_freeze_sync | intros ? [? ?] [? ?] (-> & -> & -> & ->); repeat split; intros; discriminate].
      + apply refine_mcfg_raise_both.
      + match goal with m0 : metadata _ |- _ => destruct m0 as [| | [dt1 ex1] | | | |] end;
          try (eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split; intros; discriminate]).
        eapply refine_prov_weaken; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? [? ?] [? ?] (-> & -> & -> & -> & _); repeat split; intros; discriminate.
      + destruct elt as [dt1 e1].
        eapply refine_mcfg_model_bind with
          (RA := fun U' '(s1', r1) '(s2', r2) =>
                   U' = U /\ s1' = (σ1, ((sf1, fstk1), g)) /\ s2' = (σ2, ((sf2, fstk2), g)) /\ r1 = r2);
          [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split] |].
        intros ? ? [sz_v t_v] ? ? _ (-> & -> & -> & <-).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_prov_weaken; [apply refine_mcfg_gread_same_g |].
        intros ? [? ?] [? ?] (-> & -> & -> & -> & _); repeat split; intros; discriminate.
  Qed.

  Lemma denote_exp_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (top : option dtyp) (e : exp dtyp) (U : list N)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (full_exp_uses e) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
         (forall P_unprom safe_locals,
            genv_safe P_unprom g ->
            safe_locals_env P_unprom safe_locals (stack_vars sf2) ->
            m2r_safe_ptr_exp safe_locals e = true ->
            is_safe_ptr_dvalue P_unprom v2))
      U
      (interp_cfg_model ctx1 (denote_exp' top e) s1)
      (interp_cfg_model ctx2 (denote_exp' top e) s2).
  Proof using.
    cbv zeta.
    eapply refine_prov_tau_expand;
      [apply tau_expand_cfg_withCall_denote_exp
      | apply tau_expand_cfg_withCall_denote_exp
      | apply denote_exp_mcfg_sim, Hvars].
  Qed.

  Lemma denote_exp_cfg_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (top : option dtyp) (e : exp dtyp) (U : list N)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (full_exp_uses e) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' v1 v2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
            (forall P_unprom safe_locals,
               genv_safe P_unprom g ->
               safe_locals_env P_unprom safe_locals (stack_vars sf2) ->
               m2r_safe_ptr_exp safe_locals e = true ->
               is_safe_ptr_dvalue P_unprom v2)))
      U
      (interp_cfg_exc ctx1 (denote_exp' top e) s1)
      (interp_cfg_exc ctx2 (denote_exp' top e) s2).
  Proof using.
    cbv zeta.
    eapply refine_prov_tau_expand;
      [apply tau_expand_exc_withCall_denote_exp
      | apply tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc.
    eapply PassCommonModel.refine_prov_bind; [apply denote_exp_mcfg_sim, Hvars |].
    intros U' [s1' v1] [s2' v2] _ Hpost.
    apply refine_prov_ret; exact Hpost.
  Qed.


  (** ** 3G. Exception-Level Memory Lifters, Loop Splitting & Pass-1 Specs *)

  Lemma refine_cfg_exc_raise_both {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N) (msg1 msg2 : string) (s1 s2 : FusedS) :
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (raise msg1) s1)
      (interp_cfg_exc ctx2 (raise msg2) s2).
  Proof using.
    unfold raise, trigger_cast; eapply refine_cfg_exc_bind.
    - eapply refine_cfg_exc_trigger with (RA := fun _ _ _ (v1 : void) (_ : void) => match v1 with end);
        [reflexivity | reflexivity |].
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_model_non_intr; reflexivity
        | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
      cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
      unfold fused_trigger_prov, ITree.trigger.
      eapply refine_prov_obs_eq;
        [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - intros _ _ [] _ _ _ _.
  Qed.

  Lemma refine_cfg_exc_raiseOOM_l {A1 R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res (@exc (@ParamsV IP IPT) + A1) -> R2 -> Prop)
    (U : list N) (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_cfg_exc ctx1 (raiseOOM msg) s1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast, interp_cfg_exc.
    assert (Hoom : run_exc (A := A1)
                     (ITree.bind (ITree.trigger (subevent _ (ThrowOOM (print_msg msg))))
                        (fun v : void => match v with end))
                    ≅ ITree.bind (ITree.trigger (subevent _ (ThrowOOM (print_msg msg))))
                        (fun v : void => match v with end)).
    { rewrite run_exc_bind_eq, run_exc_trigger_non_exc;
        [rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _]
        | reflexivity]. }
    eapply refine_prov_obs_eq;
      [symmetry; apply (interp_cfg_model_obs_eq ctx1 _ _ s1 Hoom) | reflexivity |].
    apply (refine_cfg_raiseOOM_l ctx1 RR U msg s1 t2).
  Qed.

  Lemma refine_cfg_exc_raiseLLVM_both {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N) (x1 x2 : @exc (@ParamsV IP IPT)) (s1 s2 : FusedS) :
    RExc U s1 s2 x1 x2 ->
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (raiseLLVM x1) s1)
      (interp_cfg_exc ctx2 (raiseLLVM x2) s2).
  Proof using.
    intros Hx.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_raiseLLVM
      | symmetry; apply interp_cfg_exc_raiseLLVM |].
    apply refine_prov_ret; exact Hx.
  Qed.

  Lemma refine_cfg_exc_memory_event {X1 X2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> X1 -> X2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (me2 : @MemoryE (@ParamsV IP IPT) X2)
    (U : list N) (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env) :
    refine_prov
      (fun U' '(σ1', x1) '(σ2', x2) => RA U' (σ1', rest1) (σ2', rest2) x1 x2)
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      (memM_interp_prov (handle_memoryM me2) σ2) ->
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (ITree.trigger (subevent _ me1)) (σ1, rest1))
      (interp_cfg_exc ctx2 (ITree.trigger (subevent _ me2)) (σ2, rest2)).
  Proof using.
    intros Hmem.
    eapply refine_cfg_exc_trigger; [reflexivity | reflexivity |].
    apply refine_cfg_memory_event, Hmem.
  Qed.

  Lemma refine_cfg_exc_memory_event_l {X1 R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res (@exc (@ParamsV IP IPT) + X1) -> R2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (U : list N) (σ1 : state)
    (rest1 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (t2 : itree ProvBotE R2) :
    refine_prov
      (fun U' '(σ1', x1) r2 => RR U' ((σ1', rest1), inr x1) r2)
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      t2 ->
    refine_prov RR U
      (interp_cfg_exc ctx1 (ITree.trigger (subevent _ me1)) (σ1, rest1))
      t2.
  Proof using.
    intros Hmem.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_trigger_non_exc; reflexivity
      | apply Eqit.bind_ret_r |].
    eapply refine_prov_bind with
      (RR := fun U' '(s1', x1) r2 => RR U' (s1', inr x1) r2).
    - apply refine_cfg_memory_event_l, Hmem.
    - intros U' [s1' x1] r2 HRR.
      apply refine_prov_tau_l, refine_prov_ret, HRR.
  Qed.

  Lemma loop_monad_app_eq {E : Type -> Type} {A : Type}
    (f : A -> itree E unit) (l1 l2 : list A) :
    loop_monad f (l1 ++ l2) ≅
    ITree.bind (loop_monad f l1) (fun _ => loop_monad f l2).
  Proof using.
    induction l1 as [| a l1' IH]; cbn [List.app loop_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - symmetry; rewrite Eqit.bind_ret_l; reflexivity.
    - symmetry; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [] _ _; symmetry; exact IH.
  Qed.

  Lemma denote_code_app_eq
    (c1 c2 : code dtyp) (va : option (@ptr ProvenanceV (@PointerV IP))) :
    @denote_code (@ParamsV IP IPT) (c1 ++ c2) va ≅
    ITree.bind (denote_code c1 va) (fun _ => denote_code c2 va).
  Proof using.
    unfold denote_code; apply loop_monad_app_eq.
  Qed.

  Lemma rewrite_non_entry_blocks_pass1_spec
    (avoid0 : list raw_id)
    (init_bid : block_id) (p : local_id) (dt : dtyp)
    (init_end_reg : local_id) (init_code' : code dtyp)
    (avoid : list raw_id) (bk_phis : list (block dtyp * local_id))
    (pass1_out : list (block dtyp * local_id * code dtyp * local_id))
    (avoid_out : list raw_id) :
    rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid bk_phis =
      (pass1_out, avoid_out) ->
    incl avoid0 avoid ->
    ~ In init_end_reg avoid0 ->
    (forall r, In r (List.map snd bk_phis) -> ~ In r avoid0) ->
    List.map (fun '(bk, _, _, _) => bk) pass1_out = List.map fst bk_phis /\
    List.map (fun '(_, phi_r, _, _) => phi_r) pass1_out = List.map snd bk_phis /\
    incl avoid avoid_out /\
    (forall bk phi_r cd' end_r,
       In (bk, phi_r, cd', end_r) pass1_out ->
       ~ In phi_r avoid0 /\
       ~ In end_r avoid0 /\
       (if raw_id_eqb (blk_id bk) init_bid then
          cd' = init_code' /\ end_r = init_end_reg
        else
          exists av_in av_out,
            incl avoid0 av_in /\
            rewrite_code_for_slot p dt phi_r av_in (blk_code bk) = (cd', end_r, av_out))).
  Proof using.
    revert avoid pass1_out avoid_out;
      induction bk_phis as [| [bk0 phi0] rest IH];
      intros avoid pass1_out avoid_out Hpass Hinc Hinit_er Hphis;
      cbn [rewrite_non_entry_blocks_pass1] in Hpass.
    - inversion Hpass; subst.
      split; [reflexivity |].
      split; [reflexivity |].
      split; [apply incl_refl |].
      intros ? ? ? ? [].
    - assert (Hphi0 : ~ In phi0 avoid0) by (apply Hphis; left; reflexivity).
      assert (Hphis_tl : forall r, In r (List.map snd rest) -> ~ In r avoid0)
        by (intros r Hr; apply Hphis; right; exact Hr).
      destruct (raw_id_eqb (blk_id bk0) init_bid) eqn:Einit.
      + destruct (rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid rest)
          as [rest_out av'] eqn:Erest.
        inversion Hpass; subst; clear Hpass.
        destruct (IH avoid rest_out avoid_out Erest Hinc Hinit_er Hphis_tl)
          as (Hbks & Hprs & Hav & Hall).
        cbn [List.map fst snd]; split; [f_equal; exact Hbks |].
        split; [f_equal; exact Hprs |].
        split; [exact Hav |].
        intros bk phi_r cd' end_r [Heq | Hin].
        * inversion Heq; subst; rewrite Einit; repeat split; assumption.
        * apply Hall, Hin.
      + destruct (rewrite_code_for_slot p dt phi0 avoid (blk_code bk0))
          as [[cd0 end0] av1] eqn:Erw.
        destruct (rewrite_code_for_slot_fresh_inv avoid0 p dt phi0 avoid (blk_code bk0)
                    cd0 end0 av1 Erw Hinc Hphi0) as [Hav1 Hend0].
        assert (Hinc1 : incl avoid0 av1) by (eapply incl_tran; eassumption).
        destruct (rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' av1 rest)
          as [rest_out av2] eqn:Erest.
        inversion Hpass; subst; clear Hpass.
        destruct (IH av1 rest_out avoid_out Erest Hinc1 Hinit_er Hphis_tl)
          as (Hbks & Hprs & Hav2 & Hall).
        cbn [List.map fst snd]; split; [f_equal; exact Hbks |].
        split; [f_equal; exact Hprs |].
        split; [eapply incl_tran; eassumption |].
        intros bk phi_r cd' end_r [Heq | Hin].
        * inversion Heq; subst; rewrite Einit.
          split; [exact Hphi0 | split; [exact Hend0 | exists avoid, av1; split; assumption]].
        * apply Hall, Hin.
  Qed.

  Lemma build_promoted_blocks_map_blk_id
    (init_bid : block_id) (dt : dtyp) (init_reg : local_id)
    (all_bks : ocfg dtyp)
    (pass1_out : list (block dtyp * local_id * code dtyp * local_id)) :
    List.map blk_id (build_promoted_blocks init_bid dt init_reg all_bks pass1_out) =
    List.map (fun '(bk, _, _, _) => blk_id bk) pass1_out.
  Proof using.
    unfold build_promoted_blocks; cbv zeta.
    set (em := List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) pass1_out); clearbody em.
    induction pass1_out as [| [[[bk phi_r] cd'] end_r] rest IH]; cbn [List.map]; [reflexivity |].
    destruct (raw_id_eqb (blk_id bk) init_bid); cbn [blk_id]; f_equal; exact IH.
  Qed.

  Lemma combine_fst_eq {A B} (xs : list A) (ys : list B) :
    List.length xs = List.length ys ->
    List.map fst (List.combine xs ys) = xs.
  Proof using.
    revert ys; induction xs as [| x xs' IH]; intros [| y ys'] Hlen;
      cbn in *; try lia; [reflexivity | f_equal; apply IH; lia].
  Qed.

  Lemma combine_snd_eq {A B} (xs : list A) (ys : list B) :
    List.length xs = List.length ys ->
    List.map snd (List.combine xs ys) = ys.
  Proof using.
    revert ys; induction xs as [| x xs' IH]; intros [| y ys'] Hlen;
      cbn in *; try lia; [reflexivity | f_equal; apply IH; lia].
  Qed.


  Lemma m2r_dtyp_eqb_eq (t1 t2 : dtyp) :
    dtyp_eqb t1 t2 = true -> t1 = t2.
  Proof using.
    unfold dtyp_eqb; destruct (dtyp_eq_dec t1 t2) as [Heq | _];
      [intros _; exact Heq | intros H; discriminate H].
  Qed.

  Lemma is_promotable_load_of_inv
    (p : local_id) (dt : dtyp)
    (im : instr_id * instr dtyp * list (metadata dtyp))
    (dst : local_id) :
    is_promotable_load_of p dt im = Some dst ->
    dst <> p /\
    exists anns_ld md,
      im = (IId dst,
            INSTR_Load dt (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_ld,
            md) /\
      flat_map full_ann_uses anns_ld = [] /\
      is_debug_or_file_md md = true.
  Proof using.
    destruct im as [[iid ins] md].
    destruct iid as [dst0 |]; [| intros H; discriminate H].
    destruct ins; try (intros H; discriminate H).
    destruct ptr as [du_ld ptr_e].
    destruct ptr_e; try (intros H; discriminate H).
    destruct id as [| q]; [intros H; discriminate H |].
    cbn [is_promotable_load_of].
    destruct (raw_id_eqb q p
              && negb (raw_id_eqb dst0 p)
              && dtyp_eqb t dt
              && dtyp_eqb du_ld (DTYPE_Base DTYPE_Pointer)
              && m2r_is_empty (flat_map full_ann_uses anns)
              && is_non_volatile_non_atomic_anns anns
              && is_debug_or_file_md md) eqn:Econd;
      [| intros H; discriminate H].
    intros Hsome; inversion Hsome; subst dst0; clear Hsome.
    rewrite !andb_true_iff, negb_true_iff in Econd.
    destruct Econd as ((((((Hq & Hdst) & Hdt) & Hdu) & Hanns) & _) & Hmd).
    apply raw_id_eqb_spec in Hq; subst q.
    apply raw_id_eqb_neq in Hdst; rename Hdst into Hne.
    apply m2r_dtyp_eqb_eq in Hdt; subst t.
    apply m2r_dtyp_eqb_eq in Hdu; subst du_ld.
    apply m2r_is_empty_spec in Hanns.
    split; [exact Hne | exists anns, md; repeat split; assumption].
  Qed.

  Lemma is_promotable_store_of_inv
    (p : local_id) (dt : dtyp)
    (im : instr_id * instr dtyp * list (metadata dtyp))
    (val_exp : exp dtyp) :
    is_promotable_store_of p dt im = Some val_exp ->
    ~ In p (full_exp_uses val_exp) /\
    exists vid anns_st md,
      im = (IVoid vid,
            INSTR_Store (dt, val_exp) (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_st,
            md) /\
      flat_map full_ann_uses anns_st = [] /\
      is_debug_or_file_md md = true.
  Proof using.
    destruct im as [[iid ins] md].
    destruct iid as [| vid]; [intros H; discriminate H |].
    destruct ins; try (intros H; discriminate H).
    destruct val as [dt_st v_e], ptr as [du_st ptr_e].
    destruct ptr_e; try (intros H; discriminate H).
    destruct id as [| q]; [intros H; discriminate H |].
    cbn [is_promotable_store_of].
    destruct (raw_id_eqb q p
              && dtyp_eqb dt_st dt
              && dtyp_eqb du_st (DTYPE_Base DTYPE_Pointer)
              && negb (in_raw_ids p (full_exp_uses v_e))
              && m2r_is_empty (flat_map full_ann_uses anns)
              && is_non_volatile_non_atomic_anns anns
              && is_debug_or_file_md md) eqn:Econd;
      [| intros H; discriminate H].
    intros Hsome; inversion Hsome; subst v_e; clear Hsome.
    rewrite !andb_true_iff, negb_true_iff in Econd.
    destruct Econd as ((((((Hq & Hdt) & Hdu) & Hnin) & Hanns) & _) & Hmd).
    apply raw_id_eqb_spec in Hq; subst q.
    apply m2r_dtyp_eqb_eq in Hdt; subst dt_st.
    apply m2r_dtyp_eqb_eq in Hdu; subst du_st.
    apply in_raw_ids_false in Hnin.
    apply m2r_is_empty_spec in Hanns.
    split; [exact Hnin | exists vid, anns, md; repeat split; assumption].
  Qed.

  Lemma check_other_instr_for_slot_inv
    (allow_calls : bool) (safe_no_p : list local_id) (p : local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp)) :
    check_other_instr_for_slot allow_calls safe_no_p p im = true ->
    ~ In p (m2r_code_entry_uses im) /\
    m2r_safe_mem_instr_any safe_no_p im = true /\
    (allow_calls = false ->
     forall iid fn args anns obs md,
       im <> (iid, INSTR_Call fn args anns obs, md)).
  Proof using.
    destruct im as [[iid ins] md].
    unfold check_other_instr_for_slot.
    rewrite andb_true_iff, negb_true_iff, in_raw_ids_false.
    intros [Hnin Hrest].
    split; [exact Hnin |].
    destruct iid as [id0 | vid0], ins;
      try discriminate Hrest;
      try (split; [exact Hrest | intros _ ? ? ? ? ? ? H; discriminate H]).
    - destruct fn as [dt_fn fn_e].
      rewrite !andb_true_iff in Hrest; destruct Hrest as [[Hac Hobs] Hintr].
      split.
      + cbn [m2r_safe_mem_instr_any]; rewrite andb_true_iff; split; assumption.
      + intros Hfalse; rewrite Hfalse in Hac; discriminate Hac.
    - destruct fn as [dt_fn fn_e].
      rewrite !andb_true_iff in Hrest; destruct Hrest as [[Hac Hobs] Hintr].
      split.
      + cbn [m2r_safe_mem_instr_any]; rewrite andb_true_iff; split; assumption.
      + intros Hfalse; rewrite Hfalse in Hac; discriminate Hac.
  Qed.

  Lemma check_no_alloca_or_call_instr_inv
    (safe_no_p : list local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp)) :
    check_no_alloca_or_call_instr safe_no_p im = true ->
    (exists id0 op md, im = (IId id0, INSTR_Op op, md)) \/
    (exists id0 dt du ptr_e anns md,
       im = (IId id0, INSTR_Load dt (du, ptr_e) anns, md) /\
       m2r_safe_ptr_exp safe_no_p ptr_e = true /\
       load_metadata_dereferenceable md = None) \/
    (exists vid0 dt val_e du ptr_e anns md,
       im = (IVoid vid0, INSTR_Store (dt, val_e) (du, ptr_e) anns, md) /\
       m2r_safe_ptr_exp safe_no_p ptr_e = true) \/
    (exists vid0 s md, im = (IVoid vid0, INSTR_Comment s, md)) \/
    (exists iid0 sync ord md, im = (iid0, INSTR_Fence sync ord, md)).
  Proof using.
    destruct im as [[iid ins] md]; cbn [check_no_alloca_or_call_instr].
    destruct iid as [id0 | vid0], ins; try (intros H; discriminate H).
    - intros _; left; exists id0, op, md; reflexivity.
    - destruct ptr as [du ptr_e]; rewrite andb_true_iff.
      intros [Hsafe Hderef].
      destruct (load_metadata_dereferenceable md) eqn:Ed; [discriminate Hderef |].
      right; left; exists id0, t, du, ptr_e, anns, md; repeat split; assumption.
    - intros _; right; right; right; right; exists (IId id0), syncscope, o, md; reflexivity.
    - intros _; right; right; right; left; eexists vid0, _, md; reflexivity.
    - destruct val as [dt val_e], ptr as [du ptr_e]; intros Hsafe.
      right; right; left; exists vid0, dt, val_e, du, ptr_e, anns, md; split; [reflexivity | exact Hsafe].
    - intros _; right; right; right; right; exists (IVoid vid0), syncscope, o, md; reflexivity.
  Qed.

  (** ** 3H. Fused Environment Steps & Stage 1 Attribute / Call Helpers *)

  Lemma tau_star_cfg_lwrite
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_model ctx (lwrite x v) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((upd_local_sf sf (Maps.add x v (stack_vars sf)), fstk), g)), tt)).
  Proof using.
    unfold lwrite, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_cfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    apply fused_local_prov_write.
  Qed.

  Lemma tau_star_cfg_exc_lwrite
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_exc ctx (lwrite x v) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((upd_local_sf sf (Maps.add x v (stack_vars sf)), fstk), g)), inr tt)).
  Proof using.
    unfold lwrite, Subevent.trigger; try unfold trigger_cast.
    eapply TS_Eq; [apply interp_cfg_exc_trigger_non_exc; reflexivity |].
    eapply tau_star_trans.
    - apply tau_star_bind, (tau_star_cfg_lwrite ctx x v σ sf fstk g).
    - eapply TS_Eq; [apply Eqit.bind_ret_l | apply TS_Tau, TS_Refl].
  Qed.

  Lemma tau_star_cfg_lread_some
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env)
    (Hlk : Maps.lookup x (stack_vars sf) = Some v) :
    tau_star
      (interp_cfg_model ctx (lread x) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((sf, fstk), g)), v)).
  Proof using.
    unfold lread, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_cfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    exact (fused_local_prov_read_some x v (σ, ((sf, fstk), g)) Hlk).
  Qed.

  Lemma tau_star_cfg_exc_lread_some
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env)
    (Hlk : Maps.lookup x (stack_vars sf) = Some v) :
    tau_star
      (interp_cfg_exc ctx (lread x) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((sf, fstk), g)), inr v)).
  Proof using.
    unfold lread, Subevent.trigger; try unfold trigger_cast.
    eapply TS_Eq; [apply interp_cfg_exc_trigger_non_exc; reflexivity |].
    eapply tau_star_trans.
    - apply tau_star_bind, (tau_star_cfg_lread_some ctx x v σ sf fstk g Hlk).
    - eapply TS_Eq; [apply Eqit.bind_ret_l | apply TS_Tau, TS_Refl].
  Qed.

  Lemma tau_star_cfg_stack_push
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (bs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_model ctx (stack_push bs) (σ, ((sf, fstk), g)))
      (Ret ((σ, (({| stack_vars := init_local_env bs;
                     stack_exc  := None;
                     stack_loc  := Some ""%string |}, sf :: fstk), g)), tt)).
  Proof using.
    unfold stack_push, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_cfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
    unfold fused_stack_prov, on_ls_prov, handle_stack;
      cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env].
    rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma tau_star_cfg_stack_pop
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (σ : state) (sf_cur sf_prev : @stack_frame (@ParamsV IP IPT))
    (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_model ctx stack_pop (σ, ((sf_cur, sf_prev :: fstk), g)))
      (Ret ((σ, ((sf_prev, fstk), g)), tt)).
  Proof using.
    unfold stack_pop, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_cfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
    unfold fused_stack_prov, on_ls_prov, handle_stack;
      cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env].
    rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma tau_star_mcfg_gwrite
    (gid : raw_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : global_env) :
    tau_star
      (interp_mcfg_model (gwrite gid v) (σ, (ls, g)))
      (Ret ((σ, (ls, Maps.add gid v g)), tt)).
  Proof using.
    unfold gwrite, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_mcfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    try unfold resum; try unfold ReSum_id; try unfold id_; try unfold Id_IFun.
    unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref;
      cbn - [Maps.lookup Maps.add Maps.empty lift_bot_prov].
    rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma denote_operand_bundles_empty_eq
    (loc : string) (f : exp dtyp) :
    @denote_operand_bundles (@ParamsV IP IPT) loc f [] ≅ Ret tt.
  Proof using.
    unfold denote_operand_bundles; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma assert_dereferenceable_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (or_null : bool) (n : N) (v : @dvalue (@ParamsV IP IPT)) (msg1 msg2 : string)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = tt /\ r2 = tt)
      U
      (interp_cfg_model ctx1 (assert_dereferenceable or_null n v msg1) (σ1, rest1))
      (interp_cfg_model ctx2 (assert_dereferenceable or_null n v msg2) (σ2, rest2)).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [[pt | | | | | | |] | |]; cbv beta iota;
      lazymatch goal with
      | |- refine_prov _ _ (interp_cfg_model _ (raise _) _) _ => apply refine_cfg_raise_both
      | _ => idtac
      end.
    - destruct ((or_null && (ptr_to_int pt =? ptr_to_int null)%Z) || (n =? 0)%N).
      + eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret; repeat split; reflexivity.
      + eapply refine_cfg_model_bind with
          (RA := fun U' '(s1', _) '(s2', _) =>
                   U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2)).
        * unfold load, Subevent.trigger; try unfold trigger_cast.
          apply refine_cfg_memory_event.
          eapply refine_prov_weaken.
          -- exact (stage1_load_b8_array_any_ptr n (DVALUE_Base (DVALUE_Pointer pt))
                      U P_unprom G σ1 σ2 Hinv).
          -- intros U' [σ1' _] [σ2' _] (-> & -> & ->); repeat split; reflexivity.
        * intros U' s1' _ s2' _ _ (-> & -> & ->).
          eapply refine_prov_obs_eq;
            [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
          apply refine_prov_ret; repeat split; reflexivity.
    - apply refine_cfg_raiseUB_l.
  Qed.

  Lemma assert_dereferenceable_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (or_null : bool) (n : N) (v : @dvalue (@ParamsV IP IPT)) (msg1 msg2 : string)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = tt /\ r2 = tt))
      U
      (interp_cfg_exc ctx1 (assert_dereferenceable or_null n v msg1) (σ1, rest1))
      (interp_cfg_exc ctx2 (assert_dereferenceable or_null n v msg2) (σ2, rest2)).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [[pt | | | | | | |] | |]; cbv beta iota;
      lazymatch goal with
      | |- refine_prov _ _ (interp_cfg_exc _ (raise _) _) _ => apply refine_cfg_exc_raise_both
      | _ => idtac
      end.
    - destruct ((or_null && (ptr_to_int pt =? ptr_to_int null)%Z) || (n =? 0)%N).
      + apply refine_cfg_exc_ret; repeat split; reflexivity.
      + eapply refine_cfg_exc_bind with
          (RA := fun U' s1' s2' _ _ =>
                   U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2)).
        * unfold load, Subevent.trigger; try unfold trigger_cast.
          apply refine_cfg_exc_memory_event.
          eapply refine_prov_weaken.
          -- exact (stage1_load_b8_array_any_ptr n (DVALUE_Base (DVALUE_Pointer pt))
                      U P_unprom G σ1 σ2 Hinv).
          -- intros U' [σ1' _] [σ2' _] (-> & -> & ->); repeat split; reflexivity.
        * intros U' s1' _ s2' _ _ (-> & -> & ->).
          apply refine_cfg_exc_ret; repeat split; reflexivity.
    - apply refine_cfg_exc_raiseUB_l.
  Qed.

  Lemma assert_load_dereferenceable_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (md : list (metadata dtyp)) (v : @dvalue (@ParamsV IP IPT)) (msg1 msg2 : string)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = tt /\ r2 = tt))
      U
      (interp_cfg_exc ctx1 (assert_load_dereferenceable md v msg1) (σ1, rest1))
      (interp_cfg_exc ctx2 (assert_load_dereferenceable md v msg2) (σ2, rest2)).
  Proof using.
    unfold assert_load_dereferenceable.
    destruct (load_metadata_dereferenceable md) as [[or_null n] |].
    - exact (assert_dereferenceable_stage1_exc_sim ctx1 ctx2 RExc or_null
               (Z.to_N (denote_int_syntax n)) v msg1 msg2 U P_unprom G σ1 σ2 rest1 rest2 Hinv).
    - apply refine_cfg_exc_ret; repeat split; reflexivity.
  Qed.

  Lemma apply_attrs_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (attrs : list param_attr) (msg : string) (v : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2)
      U
      (interp_cfg_model ctx1 (apply_attrs attrs msg v) (σ1, rest1))
      (interp_cfg_model ctx2 (apply_attrs attrs msg v) (σ2, rest2)).
  Proof using.
    unfold apply_attrs.
    eapply refine_cfg_model_bind with
      (RA := fun U' '(s1', r1) '(s2', r2) =>
               U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2).
    - eapply refine_cfg_EOU; [apply refine_EOU_refl |].
      intros a1 a2 <-; exact (conj (Logic.eq_refl U) (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
    - intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <-).
      eapply refine_cfg_model_bind with
        (RA := fun U' '(s1', r1) '(s2', r2) =>
                 U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = tt /\ r2 = tt).
      + unfold assert_attrs_dereferenceable.
        destruct (find_option attr_dereferenceable attrs) as [[or_null n] |],
                 v1 as [[pt | | | | | | |] | |];
          try (eapply refine_prov_obs_eq;
               [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |];
               apply refine_prov_ret; exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))))).
        exact (assert_dereferenceable_stage1_cfg_sim ctx1 ctx2 or_null
                 (Z.to_N (denote_int_syntax n)) (DVALUE_Base (DVALUE_Pointer pt))
                 msg msg U P_unprom G σ1 σ2 rest1 rest2 Hinv).
      + intros U2 s1'' _ s2'' _ _ (-> & -> & -> & _ & _).
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma apply_attrs_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (attrs : list param_attr) (msg : string) (v : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2))
      U
      (interp_cfg_exc ctx1 (apply_attrs attrs msg v) (σ1, rest1))
      (interp_cfg_exc ctx2 (apply_attrs attrs msg v) (σ2, rest2)).
  Proof using.
    unfold apply_attrs.
    eapply refine_cfg_exc_bind with
      (RA := fun U' s1' s2' r1 r2 =>
               U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2).
    - eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
      intros a1 a2 <-; repeat split; reflexivity.
    - intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <-).
      eapply refine_cfg_exc_bind with
        (RA := fun U' s1' s2' r1 r2 =>
                 U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = tt /\ r2 = tt).
      + unfold assert_attrs_dereferenceable.
        destruct (find_option attr_dereferenceable attrs) as [[or_null n] |],
                 v1 as [[pt | | | | | | |] | |];
          try (apply refine_cfg_exc_ret; exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))))).
        exact (assert_dereferenceable_stage1_exc_sim ctx1 ctx2 RExc or_null
                 (Z.to_N (denote_int_syntax n)) (DVALUE_Base (DVALUE_Pointer pt))
                 msg msg U P_unprom G σ1 σ2 rest1 rest2 Hinv).
      + intros U2 s1'' _ s2'' _ _ (-> & -> & -> & _ & _).
        apply refine_cfg_exc_ret; repeat split; reflexivity.
  Qed.

  Lemma apply_args_attrs_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (attrss : list (list param_attr)) (msg : string)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2)
      U
      (interp_cfg_model ctx1 (apply_args_attrs attrss msg args) (σ1, rest1))
      (interp_cfg_model ctx2 (apply_args_attrs attrss msg args) (σ2, rest2)).
  Proof using.
    revert attrss; induction args as [| v vs IH]; intros attrss; cbn [apply_args_attrs].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
      apply refine_prov_ret; repeat split; reflexivity.
    - destruct attrss as [| a r];
        (eapply refine_cfg_model_bind;
         [exact (apply_attrs_stage1_cfg_sim ctx1 ctx2 _ msg v U P_unprom G σ1 σ2 rest1 rest2 Hinv) |];
         intros U1 s1' v' s2' v2' _ (-> & -> & -> & <-);
         eapply refine_cfg_model_bind; [apply IH |];
         intros U2 s1'' vs' s2'' vs2' _ (-> & -> & -> & <-);
         eapply refine_prov_obs_eq;
           [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |];
         apply refine_prov_ret; repeat split; reflexivity).
  Qed.

  Lemma check_call_return_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (rv : @exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2)
      U
      (interp_cfg_model ctx1 (check_call_return fattrs ret_attrs ranges loc args rv) (σ1, rest1))
      (interp_cfg_model ctx2 (check_call_return fattrs ret_attrs ranges loc args rv) (σ2, rest2)).
  Proof using.
    unfold check_call_return.
    eapply refine_cfg_model_bind with
      (RA := fun U' '(s1', _) '(s2', _) =>
               U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2)).
    - eapply refine_cfg_EOU; [apply refine_EOU_refl |].
      intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1' _ s2' _ _ (-> & -> & ->).
      destruct rv as [ex | v].
      + eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret; repeat split; reflexivity.
      + eapply refine_cfg_model_bind.
        * exact (apply_attrs_stage1_cfg_sim ctx1 ctx2 ret_attrs
                   (loc ++ " return value violates noundef.")%string
                   (value_metadata_range ranges v) U P_unprom G σ1 σ2 rest1 rest2 Hinv).
        * intros U2 s1'' v' s2'' v2' _ (-> & -> & -> & <-).
          eapply refine_prov_obs_eq;
            [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
          apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma check_call_return_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (rv : @exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2))
      U
      (interp_cfg_exc ctx1 (check_call_return fattrs ret_attrs ranges loc args rv) (σ1, rest1))
      (interp_cfg_exc ctx2 (check_call_return fattrs ret_attrs ranges loc args rv) (σ2, rest2)).
  Proof using.
    unfold check_call_return.
    eapply refine_cfg_exc_bind with
      (RA := fun U' s1' s2' _ _ =>
               U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2)).
    - eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
      intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1' _ s2' _ _ (-> & -> & ->).
      destruct rv as [ex | v].
      + apply refine_cfg_exc_ret; repeat split; reflexivity.
      + eapply refine_cfg_exc_bind.
        * exact (apply_attrs_stage1_exc_sim ctx1 ctx2 RExc ret_attrs
                   (loc ++ " return value violates noundef.")%string
                   (value_metadata_range ranges v) U P_unprom G σ1 σ2 rest1 rest2 Hinv).
        * intros U2 s1'' v' s2'' v2' _ (-> & -> & -> & <-).
          apply refine_cfg_exc_ret; repeat split; reflexivity.
  Qed.

  Lemma denote_call_args_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (args : list (texp dtyp * list param_attr)) (msg : string)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (Hvars : forall x,
               In x (flat_map (fun '(te, _) => full_texp_uses te) args) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' vs1 vs2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ vs1 = vs2))
      U
      (interp_cfg_exc ctx1 (denote_call_args args msg) s1)
      (interp_cfg_exc ctx2 (denote_call_args args msg) s2).
  Proof using.
    cbv zeta; unfold denote_call_args.
    induction args as [| [[t op] attrs] rest IH]; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - apply refine_cfg_exc_ret; repeat split; reflexivity.
    - eapply refine_cfg_exc_bind.
      + eapply refine_cfg_exc_bind.
        * apply denote_exp_cfg_exc_sim.
          intros x Hx; apply Hvars; cbn [flat_map full_texp_uses snd]; apply in_app_iff; left; exact Hx.
        * intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <- & _).
          exact (apply_attrs_stage1_exc_sim ctx1 ctx2 RExc attrs msg v1
                   U P_unprom G σ1 σ2 ((sf1, fstk1), g) ((sf2, fstk2), g) Hinv).
      + intros U1 s1' v' s2' v2' _ (-> & -> & -> & <-).
        eapply refine_cfg_exc_bind.
        * apply IH; intros x Hx; apply Hvars; cbn [flat_map]; apply in_app_iff; right; exact Hx.
        * intros U2 s1'' vs' s2'' vs2' _ (-> & -> & -> & <-).
          apply refine_cfg_exc_ret; repeat split; reflexivity.
  Qed.

  Lemma putchar_denotation_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT)))
    (U : list N) (s1 s2 : FusedS) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2)
      U
      (interp_cfg_model ctx1 (putchar_denotation cc args) s1)
      (interp_cfg_model ctx2 (putchar_denotation cc args) s2).
  Proof using.
    unfold putchar_denotation.
    destruct args as [| ch [| ? ?]];
      [apply refine_cfg_raise_both | | apply refine_cfg_raise_both].
    cbn [Functor.fmap Functor_itree ITree.map].
    eapply refine_cfg_model_bind with
      (RA := fun U' '(s1', r1) '(s2', r2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2).
    - destruct ch as [[| sz x32 | | | | | |] | |];
        [apply refine_cfg_raiseUB_l | | apply refine_cfg_raiseUB_l ..].
      destruct (Pos.eq_dec 32 sz) as [<- | _];
        [| apply refine_cfg_raiseUB_l].
      eapply refine_cfg_model_bind with
        (RA := fun U' '(s1', a1) '(s2', a2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ a1 = a2).
      + unfold io_stdout, Subevent.trigger; try unfold trigger_cast.
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_non_intr; reflexivity
          | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
        cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        unfold fused_trigger_prov, ITree.trigger.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
        pstep; apply RP_Step; cbn; right; right; split; [reflexivity |].
        intros a1 a2 <-; left.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
        apply refine_prov_tau_both, refine_prov_tau_both, refine_prov_tau_both, refine_prov_ret.
        repeat split; reflexivity.
      + intros U1 s1' _ s2' _ _ (-> & -> & -> & _).
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret; repeat split; reflexivity.
    - intros U1 s1' dv1 s2' dv2 _ (-> & -> & -> & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.


End MemoryAndSerialization.
