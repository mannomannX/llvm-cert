(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Mem2Reg Base Memory, Serialization & Safe Provenance ([CertPasses.Mem2RegMemBase])

    Purpose:
      Proves monadic laws for [memM_interp_prov], [mem_stack_equal]
      synchronization, scalar byte-serialization identities, consecutive-pointer
      frame facts, and safe-provenance preservation ([safe_prov], [genv_safe]).

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml. Supplies memory-model base
      lemmas for Stage 1 and Stage 2 [Mem2Reg] simulation invariants.

    Assumptions:
      Parametric over [IP : IPtr] and [IPT : @IPtrTheory IP] (with
      [IPtrWellBehaved IP] for [get_consecutive_ptrs_well_behaved]); depends on
      [PassCommon] and [Mem2RegModel]; zero custom axioms or [Admitted].

    Section Outline:
      - [MemoryAndSerialization]: 3A. [mem_stack_equal] sync; 3B. scalar byte
        serialization; 3C. allocation keys, frames, and safe provenance. *)

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

From CertPasses Require Import Mem2RegModel.

#[local] Notation refine_prov_bind := m2r_refine_prov_bind (only parsing).

(** * 3. Memory Model, Byte Serialization & Ghost-Slot Simulation *)

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

  (** ** 3A. [memM_interp_prov] Monadic Laws & [mem_stack_equal] Synchronization *)

  Lemma memM_interp_prov_ret {A} (x : A) (σ : state) :
    memM_interp_prov (ExtLib.Structures.Monad.ret x) σ = Ret (σ, x).
  Proof using.
    reflexivity.
  Qed.

  Lemma memM_interp_prov_bind {A B}
    (m : @memM (@ParamsV IP IPT) _ A)
    (k : A -> @memM (@ParamsV IP IPT) _ B)
    (σ : state) :
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
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros p _ <-; apply IH.
      + apply IH.
  Qed.

  Lemma memM_interp_prov_map_monad_acc {A B}
    (f : A -> @memM (@ParamsV IP IPT) _ B) (l : list A) (σ : state) :
    memM_interp_prov (map_monad_acc f l) σ ≅
    memM_interp_prov (map_monad f l) σ.
  Proof using.
    unfold map_monad_acc.
    set (go := fix loop (acc : list B) (xs : list A) : @memM (@ParamsV IP IPT) _ (list B) :=
                 match xs with
                 | [] => ExtLib.Structures.Monad.ret (rev_append acc [])
                 | a :: xs' => ExtLib.Structures.Monad.bind (f a) (fun b => loop (b :: acc) xs')
                 end).
    change (memM_interp_prov (go [] l) σ ≅ memM_interp_prov (map_monad f l) σ).
    assert (Hgo : forall xs acc σ0,
              memM_interp_prov (go acc xs) σ0 ≅
              memM_interp_prov (ExtLib.Structures.Monad.bind (map_monad f xs) (fun bs => ExtLib.Structures.Monad.ret (rev_append acc bs))) σ0).
    { induction xs as [| a xs' IH]; intros acc σ0; cbn [go map_monad].
      - rewrite memM_interp_prov_bind, !memM_interp_prov_ret, Eqit.bind_ret_l; reflexivity.
      - rewrite !memM_interp_prov_bind, !Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [σ1 b] _ <-.
        rewrite IH, !memM_interp_prov_bind, !Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [σ2 bs] _ <-.
        rewrite !memM_interp_prov_ret, !Eqit.bind_ret_l, !memM_interp_prov_ret.
        cbn [rev_append]; reflexivity. }
    rewrite Hgo, memM_interp_prov_bind; cbn [rev_append].
    rewrite <- (Eqit.bind_ret_r (memM_interp_prov (map_monad f l) σ)) at 2.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [σ' bs] _ <-; reflexivity.
  Qed.

  Lemma memM_interp_prov_raiseUB_l {A R2}
    (RR : list N -> (state * A) -> R2 -> Prop)
    (U : list N) (msg : string) (σ1 : state) (t2 : itree ProvBotE R2) :
    refine_prov RR U
      (memM_interp_prov (@Mub state (@ptr ProvenanceV (@PointerV IP)) provenance A msg) σ1)
      t2.
  Proof using.
    cbn [memM_interp_prov]; unfold raiseUB, trigger_cast, ITree.trigger.
    eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_vis | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma memM_interp_prov_raiseOOM_l {A R2}
    (RR : list N -> (state * A) -> R2 -> Prop)
    (U : list N) (msg : string) (σ1 : state) (t2 : itree ProvBotE R2) :
    refine_prov RR U
      (memM_interp_prov (@Moom state (@ptr ProvenanceV (@PointerV IP)) provenance A msg) σ1)
      t2.
  Proof using.
    cbn [memM_interp_prov]; unfold raiseOOM, trigger_cast, ITree.trigger.
    eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_vis | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma memM_interp_prov_raise_both {A1 A2}
    (RR : list N -> (state * A1) -> (state * A2) -> Prop)
    (U : list N) (msg1 msg2 : string) (σ1 σ2 : state) :
    refine_prov RR U
      (memM_interp_prov (@Merr _ _ _ A1 msg1) σ1)
      (memM_interp_prov (@Merr _ _ _ A2 msg2) σ2).
  Proof using.
    cbn [memM_interp_prov]; unfold raise, trigger_cast, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_vis | symmetry; apply Eqit.bind_vis |].
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_EOU_refl {A} (e : EOU A) :
    refine_EOU Logic.eq e e.
  Proof using.
    destruct e; constructor; reflexivity.
  Qed.

  Lemma memM_interp_prov_lift_EOU {A1 A2}
    (RVal : A1 -> A2 -> Prop)
    (RR : list N -> (state * A1) -> (state * A2) -> Prop)
    (U : list N) (e1 : EOU A1) (e2 : EOU A2) (σ1 σ2 : state)
    (He : refine_EOU RVal e1 e2)
    (Hret : forall a1 a2, RVal a1 a2 -> RR U (σ1, a1) (σ2, a2)) :
    refine_prov RR U
      (memM_interp_prov (Interfaces.Memory.lift e1) σ1)
      (memM_interp_prov (Interfaces.Memory.lift e2) σ2).
  Proof using.
    destruct He as [a1 a2 Ha | msg1 msg2 | msg1 msg2 | msg1 e2'];
      cbn [Interfaces.Memory.lift].
    - cbn [memM_interp_prov]; apply refine_prov_ret, Hret, Ha.
    - apply memM_interp_prov_raise_both.
    - apply memM_interp_prov_raiseOOM_l.
    - apply memM_interp_prov_raiseUB_l.
  Qed.

  Lemma lookup_delete_eq {A} (k : Z) (m : IntMap A) :
    IntMaps.lookup k (IntMaps.delete k m) = None.
  Proof using.
    unfold IntMaps.lookup, IntMaps.delete.
    apply IntMaps.IP.F.remove_eq_o; reflexivity.
  Qed.

  Lemma lookup_delete_neq {A} (z k : Z) (m : IntMap A) :
    z <> k ->
    IntMaps.lookup z (IntMaps.delete k m) = IntMaps.lookup z m.
  Proof using.
    intros Hne; unfold IntMaps.lookup, IntMaps.delete.
    apply IntMaps.IP.F.remove_neq_o; lia.
  Qed.

  Lemma Equal_add {A} (k : Z) (v : A) (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (IntMaps.add k v m1) (IntMaps.add k v m2).
  Proof using.
    intros Heq z.
    destruct (Z.eq_dec z k) as [-> | Hne].
    - rewrite !IntMaps.lookup_add_eq; reflexivity.
    - rewrite !IntMaps.lookup_add_ineq by exact Hne; apply Heq.
  Qed.

  Lemma Equal_delete {A} (k : Z) (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (IntMaps.delete k m1) (IntMaps.delete k m2).
  Proof using.
    intros Heq z.
    destruct (Z.eq_dec z k) as [-> | Hne].
    - rewrite !lookup_delete_eq; reflexivity.
    - rewrite !lookup_delete_neq by exact Hne; apply Heq.
  Qed.

  Lemma Equal_member_iff {A} (m1 m2 : IntMap A) (k : Z) :
    IntMaps.Equal m1 m2 ->
    (IntMaps.member k m1 <-> IntMaps.member k m2).
  Proof using.
    intros Heq; split; intros Hm.
    - apply IntMaps.member_lookup in Hm as [v Hv].
      rewrite Heq in Hv; eapply IntMaps.lookup_member; exact Hv.
    - apply IntMaps.member_lookup in Hm as [v Hv].
      rewrite <- Heq in Hv; eapply IntMaps.lookup_member; exact Hv.
  Qed.

  Lemma Equal_IM_greatest_key {A} (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IM_greatest_key m1 = IM_greatest_key m2.
  Proof using.
    intros Heq; apply IM_greatest_key_morph.
    intros k; apply Equal_member_iff, Heq.
  Qed.

  Lemma Equal_next_key_with_alignment {A} (m1 m2 : IntMap A) (align : N) :
    IntMaps.Equal m1 m2 ->
    next_key_with_alignment m1 align = next_key_with_alignment m2 align.
  Proof using.
    intros Heq; unfold next_key_with_alignment.
    rewrite (Equal_IM_greatest_key m1 m2 Heq); reflexivity.
  Qed.

  Lemma Equal_add_all_index {A} (vs : list A) (base : Z) (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (IntMaps.add_all_index vs base m1) (IntMaps.add_all_index vs base m2).
  Proof using.
    revert base m1 m2; induction vs as [| v vs' IH]; intros base m1 m2 Heq;
      cbn [IntMaps.add_all_index]; [exact Heq |].
    apply Equal_add, IH, Heq.
  Qed.

  Lemma Equal_add_all_index_acc {A} (vs : list A) (base : Z) (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (IntMaps.add_all_index_acc vs base m1) (IntMaps.add_all_index_acc vs base m2).
  Proof using.
    intros Heq z.
    pose proof (IntMaps.add_all_index_acc_eq vs base m1 z) as H1.
    pose proof (IntMaps.add_all_index_acc_eq vs base m2 z) as H2.
    rewrite H1, H2; apply Equal_add_all_index, Heq.
  Qed.

  Lemma Equal_free_frame_memory
    (f : @Frame (@ParamsV IP IPT))
    (m1 m2 : @memory (@ParamsV IP IPT)) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (free_frame_memory f m1) (free_frame_memory f m2).
  Proof using.
    revert m1 m2; induction f as [| k f' IH]; intros m1 m2 Heq;
      cbn [free_frame_memory fold_left]; [exact Heq |].
    apply IH; unfold free_byte; apply Equal_delete, Heq.
  Qed.

  Definition mem_stack_equal (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) : Prop :=
    IntMaps.Equal (Memory_stack_memory ms1) (Memory_stack_memory ms2) /\
    Memory_stack_frame_stack ms1 = Memory_stack_frame_stack ms2 /\
    Memory_stack_heap ms1 = Memory_stack_heap ms2.

  Lemma mem_stack_equal_refl (ms : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms ms.
  Proof using.
    repeat split; reflexivity.
  Qed.

  Lemma mem_stack_equal_sym (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms1 ms2 ->
    mem_stack_equal ms2 ms1.
  Proof using.
    intros (Hm & Hfs & Hh); repeat split; symmetry; assumption.
  Qed.

  Lemma mem_stack_equal_trans (ms1 ms2 ms3 : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms1 ms2 ->
    mem_stack_equal ms2 ms3 ->
    mem_stack_equal ms1 ms3.
  Proof using.
    intros (Hm12 & Hfs12 & Hh12) (Hm23 & Hfs23 & Hh23).
    repeat split; etransitivity; eassumption.
  Qed.

  Definition eq_sync_post {R : Type} (U0 : list N)
    (U' : list N) (sr1 sr2 : state * R) : Prop :=
    let '(σ1', r1) := sr1 in
    let '(σ2', r2) := sr2 in
    incl U0 U' /\
    mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2') /\
    r1 = r2.

  Lemma Read_byte_equal_sync (p : @ptr ProvenanceV (@PointerV IP))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Read_byte p) σ1)
      (memM_interp_prov (Read_byte p) σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2))).
    rewrite (Hmem (ptr_to_int p)).
    destruct (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2)))
      as [[b aid] |].
    - eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      cbv iota.
      match goal with |- context [if ?c then _ else _] => destruct c end.
      + cbn [memM_interp_prov]; apply refine_prov_ret; repeat split; [apply incl_refl | exact Hmem | exact Hfs | exact Hh].
      + apply memM_interp_prov_raiseUB_l.
    - cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma Write_byte_equal_sync
    (p : @ptr ProvenanceV (@PointerV IP)) (mb : @memory_byte (@ParamsV IP IPT))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Write_byte p mb) σ1)
      (memM_interp_prov (Write_byte p mb) σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Write_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2))).
    rewrite (Hmem (ptr_to_int p)).
    destruct (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2)))
      as [[b0 aid] |].
    - eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      cbv iota.
      match goal with |- context [if ?c then _ else _] => destruct c end.
      + unfold set_byte_raw, get_mem, upd_mem, app_mem, set_byte_raw_mem, get, put;
          cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
        apply refine_prov_ret; repeat split; cbn;
          [apply incl_refl
          | apply Equal_add, Hmem
          | exact Hfs
          | exact Hh].
      + apply memM_interp_prov_raiseUB_l.
    - cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma map_monad_Read_byte_equal_sync
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (map_monad Read_byte ptrs) σ1)
      (memM_interp_prov (map_monad Read_byte ptrs) σ2).
  Proof using.
    revert U σ1 σ2 Heq; induction ptrs as [| p ptrs' IH]; intros U σ1 σ2 Heq;
      cbn [map_monad].
    - apply refine_prov_ret; split; [apply incl_refl | split; [exact Heq | reflexivity]].
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply Read_byte_equal_sync, Heq |].
      intros U1 [σ1' b1] [σ2' b2] (Hinc1 & Heq1 & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply IH, Heq1 |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (Hinc2 & Heq2 & <-).
      apply refine_prov_ret; split; [eapply incl_tran; eassumption | split; [exact Heq2 | reflexivity]].
  Qed.

  Lemma read_bytes_equal_sync
    (p : @ptr ProvenanceV (@PointerV IP)) (sz : N)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (read_bytes p sz) σ1)
      (memM_interp_prov (read_bytes p sz) σ2).
  Proof using.
    unfold read_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind with (RR := eq_sync_post U).
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros ptrs _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - intros U1 [σ1' ptrs1] [σ2' ptrs2] (Hinc1 & Heq1 & <-).
      cbn [read_byte MemoryModelPrimitivesV].
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_map_monad_acc
        | symmetry; apply memM_interp_prov_map_monad_acc |].
      eapply refine_prov_weaken; [apply map_monad_Read_byte_equal_sync, Heq1 |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)].
  Qed.

  Lemma loop_Write_byte_equal_sync
    (pbs : list (@ptr ProvenanceV (@PointerV IP) * @memory_byte (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ1)
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ2).
  Proof using.
    revert U σ1 σ2 Heq; induction pbs as [| [pt mb] pbs' IH]; intros U σ1 σ2 Heq;
      cbn [loop_monad].
    - apply refine_prov_ret; split; [apply incl_refl | split; [exact Heq | reflexivity]].
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply Write_byte_equal_sync, Heq |].
      intros U1 [σ1' []] [σ2' []] (Hinc1 & Heq1 & _).
      eapply refine_prov_weaken; [apply IH, Heq1 |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)].
  Qed.

  Lemma write_bytes_equal_sync
    (p : @ptr ProvenanceV (@PointerV IP)) (bs : list (@memory_byte (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (write_bytes p bs) σ1)
      (memM_interp_prov (write_bytes p bs) σ2).
  Proof using.
    unfold write_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind with (RR := eq_sync_post U).
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros ptrs _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - intros U1 [σ1' ptrs1] [σ2' ptrs2] (Hinc1 & Heq1 & <-).
      cbn [write_byte MemoryModelPrimitivesV].
      eapply refine_prov_weaken; [apply loop_Write_byte_equal_sync, Heq1 |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)].
  Qed.

  Lemma read_dvalue_equal_sync (dt : dtyp) (p : @ptr ProvenanceV (@PointerV IP))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (read_dvalue dt p) σ1)
      (memM_interp_prov (read_dvalue dt p) σ2).
  Proof using.
    unfold read_dvalue.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind; [apply read_bytes_equal_sync, Heq |].
    intros U1 [σ1' bs1] [σ2' bs2] (Hinc1 & Heq1 & <-).
    eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
    intros dv _ <-; exact (conj Hinc1 (conj Heq1 Logic.eq_refl)).
  Qed.

  Lemma write_dvalue_equal_sync
    (p : @ptr ProvenanceV (@PointerV IP)) (dt : dtyp) (v : @dvalue (@ParamsV IP IPT))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (write_dvalue p dt v) σ1)
      (memM_interp_prov (write_dvalue p dt v) σ2).
  Proof using.
    unfold write_dvalue.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind with (RR := eq_sync_post U).
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros bs _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - intros U1 [σ1' bs1] [σ2' bs2] (Hinc1 & Heq1 & <-).
      eapply refine_prov_weaken; [apply write_bytes_equal_sync, Heq1 |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)].
  Qed.

  Lemma get_free_block_equal_sync (sz align : N) (pr : provenance)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (get_free_block sz align pr) σ1)
      (memM_interp_prov (get_free_block sz align pr) σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold get_free_block, next_key, Mnext_key;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
    rewrite (Equal_next_key_with_alignment _ _ align Hmem).
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack σ2)) align).
    match goal with
    | |- context [int_to_ptr ?a ?p] =>
        destruct (int_to_ptr a p) as [s | s | s | pt]
    end;
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret].
    - apply memM_interp_prov_raise_both.
    - apply memM_interp_prov_raiseOOM_l.
    - apply memM_interp_prov_raiseUB_l.
    - match goal with
      | |- context [get_consecutive_ptrs ?p ?sz] =>
          destruct (get_consecutive_ptrs p sz) as [s | s | s | ptrs]
      end;
        cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret].
      + apply memM_interp_prov_raise_both.
      + apply memM_interp_prov_raiseOOM_l.
      + apply memM_interp_prov_raiseUB_l.
      + apply refine_prov_ret; exact (conj (incl_refl U) (conj (conj Hmem (conj Hfs Hh)) Logic.eq_refl)).
  Qed.

  Lemma add_all_to_frame_equal
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms1 ms2 ->
    mem_stack_equal (add_all_to_frame ks ms1) (add_all_to_frame ks ms2).
  Proof using.
    revert ms1 ms2; induction ks as [| k ks' IH]; intros [m1 s1 h1] [m2 s2 h2] (Hm & Hfs & Hh);
      cbn [add_all_to_frame fold_left Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap] in *.
    - exact (conj Hm (conj Hfs Hh)).
    - subst s2 h2; destruct s1; apply IH; repeat (first [exact Hm | reflexivity | split]).
  Qed.

  Lemma add_all_to_heap_equal
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms1 ms2 ->
    mem_stack_equal (add_all_to_heap ks ms1) (add_all_to_heap ks ms2).
  Proof using.
    destruct ks as [| root ks']; [intros H; exact H |].
    unfold add_all_to_heap; set (all_ks := root :: ks'); clearbody all_ks.
    revert ms1 ms2; induction all_ks as [| k rest IH]; intros [m1 s1 h1] [m2 s2 h2] (Hm & Hfs & Hh);
      cbn [add_all_to_heap' fold_left add_to_heap Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap] in *.
    - exact (conj Hm (conj Hfs Hh)).
    - subst s2 h2; apply IH; split; [exact Hm | split; reflexivity].
  Qed.

  Lemma Allocate_bytes_with_pr_equal_sync
    (bs : list (@memory_byte (@ParamsV IP IPT))) (align : N) (pr : provenance)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Allocate_bytes_with_pr bs align pr) σ1)
      (memM_interp_prov (Allocate_bytes_with_pr bs align pr) σ2).
  Proof using.
    unfold Allocate_bytes_with_pr.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind; [apply get_free_block_equal_sync, Heq |].
    intros U1 [σ1' [pt1 ptrs1]] [σ2' [pt2 ptrs2]] (Hinc1 & Heq1 & Hpair).
    inversion Hpair; subst pt2 ptrs2; clear Hpair.
    unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    destruct Heq1 as (Hm1 & Hfs1 & Hh1).
    apply refine_prov_ret; split; [exact Hinc1 | split; [| reflexivity]].
    apply add_all_to_frame_equal; repeat split; cbn;
      [apply Equal_add_all_index_acc, Hm1 | exact Hfs1 | exact Hh1].
  Qed.

  Lemma Malloc_bytes_with_pr_equal_sync
    (bs : list (@memory_byte (@ParamsV IP IPT))) (align : N) (pr : provenance)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Malloc_bytes_with_pr bs align pr) σ1)
      (memM_interp_prov (Malloc_bytes_with_pr bs align pr) σ2).
  Proof using.
    unfold Malloc_bytes_with_pr.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind; [apply get_free_block_equal_sync, Heq |].
    intros U1 [σ1' [pt1 ptrs1]] [σ2' [pt2 ptrs2]] (Hinc1 & Heq1 & Hpair).
    inversion Hpair; subst pt2 ptrs2; clear Hpair.
    unfold add_block_to_heap, add_block, add_ptrs_to_heap, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    destruct Heq1 as (Hm1 & Hfs1 & Hh1).
    apply refine_prov_ret; split; [exact Hinc1 | split; [| reflexivity]].
    apply add_all_to_heap_equal; repeat split; cbn;
      [apply Equal_add_all_index_acc, Hm1 | exact Hfs1 | exact Hh1].
  Qed.

  Lemma refine_prov_trigger_fresh_both {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (k1 : N -> itree ProvBotE R1) (k2 : N -> itree ProvBotE R2) :
    (forall p : N, ~ In p U -> refine_prov RR (p :: U) (k1 p) (k2 p)) ->
    refine_prov RR U
      (ITree.bind (ITree.trigger (inl1 FreshProv)) k1)
      (ITree.bind (ITree.trigger (inl1 FreshProv)) k2).
  Proof using.
    intros Hk.
    eapply refine_prov_obs_eq;
      [symmetry; apply bind_trigger | symmetry; apply bind_trigger |].
    apply refine_prov_fresh_both, Hk.
  Qed.

  Lemma refine_prov_trigger_fresh_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (k1 : N -> itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    (forall p : N, ~ In p U -> refine_prov RR (p :: U) (k1 p) t2) ->
    refine_prov RR U (ITree.bind (ITree.trigger (inl1 FreshProv)) k1) t2.
  Proof using.
    intros Hk.
    eapply refine_prov_obs_eq; [symmetry; apply bind_trigger | reflexivity |].
    apply refine_prov_fresh_l, Hk.
  Qed.

  Lemma allocate_bytes_equal_sync
    (bs : list (@memory_byte (@ParamsV IP IPT))) (align : N)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (allocate_bytes bs align) σ1)
      (memM_interp_prov (allocate_bytes bs align) σ2).
  Proof using.
    unfold allocate_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    apply refine_prov_trigger_fresh_both; intros p Hp.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    eapply refine_prov_weaken; [apply Allocate_bytes_with_pr_equal_sync; cbn; exact Heq |].
    intros U' [s1 r1] [s2 r2] (Hinc & Heq' & Hr).
    split; [intros z Hz; apply Hinc; right; exact Hz | exact (conj Heq' Hr)].
  Qed.

  Lemma malloc_bytes_equal_sync
    (bs : list (@memory_byte (@ParamsV IP IPT))) (align : N)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (malloc_bytes bs align) σ1)
      (memM_interp_prov (malloc_bytes bs align) σ2).
  Proof using.
    unfold malloc_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.ret memS_mon memM_interp_prov malloc_bytes_with_pr MemoryModelPrimitivesV].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    apply refine_prov_trigger_fresh_both; intros p Hp.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    eapply refine_prov_weaken; [apply Malloc_bytes_with_pr_equal_sync; cbn; exact Heq |].
    intros U' [s1 r1] [s2 r2] (Hinc & Heq' & Hr).
    split; [intros z Hz; apply Hinc; right; exact Hz | exact (conj Heq' Hr)].
  Qed.

  Lemma allocate_dtyp_equal_sync (dt : dtyp) (num align : N)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (allocate_dtyp dt num align) σ1)
      (memM_interp_prov (allocate_dtyp dt num align) σ2).
  Proof using.
    unfold allocate_dtyp.
    destruct (dtyp_eqb dt DTYPE_Void).
    - apply memM_interp_prov_raiseUB_l.
    - apply allocate_bytes_equal_sync, Heq.
  Qed.

  Lemma Mempush_equal_sync (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov Mempush σ1)
      (memM_interp_prov Mempush σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Mempush, app_frame_stack, get, put;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
    apply refine_prov_ret; repeat split; cbn;
      [apply incl_refl | exact Hmem | unfold push_frame_stack; congruence | exact Hh].
  Qed.

  Lemma Mempop_equal_sync (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov Mempop σ1)
      (memM_interp_prov Mempop σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
           upd_frame_stack, app_frame_stack, app_mem, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hfs.
    destruct (Memory_stack_frame_stack (state_memory_stack σ2)) as [f | s f] eqn:Efs;
      (cbn [memM_interp_prov];
       eapply refine_prov_obs_eq;
         [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |];
       rewrite Hfs, Efs).
    - cbn [pop_frame_stack Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind].
      apply memM_interp_prov_raise_both.
    - cbn [pop_frame_stack Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
      apply refine_prov_ret; repeat split; cbn;
        [apply incl_refl | apply Equal_free_frame_memory, Hmem | exact Hh].
  Qed.

  Lemma Free_equal_sync (p : @ptr ProvenanceV (@PointerV IP))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Free p) σ1)
      (memM_interp_prov (Free p) σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Free, get_heap, app_mem, upd_heap, app_heap, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hh.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    match goal with
    | |- context [match ?x with Some _ => _ | None => _ end] =>
        destruct x as [blk |]
    end.
    - cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
      apply refine_prov_ret; repeat split; cbn;
        [apply incl_refl | unfold free_block_memory; apply Equal_free_frame_memory, Hmem | exact Hfs].
    - apply memM_interp_prov_raiseUB_l.
  Qed.

  Lemma convert_impure_base_equal_sync
    (ct : impure_conversion) (t1 : dtyp_base) (dv : @dvalue_base (@ParamsV IP IPT)) (t2 : dtyp_base)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (convert_impure_base ct t1 dv t2) σ1)
      (memM_interp_prov (convert_impure_base ct t1 dv t2) σ2).
  Proof using.
    unfold convert_impure_base, assert_inttoptr_types_ok.
    destruct ct.
    - destruct t1; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret];
        (destruct dv;
         (eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |]);
         intros r _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl))).
    - destruct dv; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        ((eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |]);
         intros r _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl))).
    - destruct dv; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        ((eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |]);
         intros r _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl))).
    - apply memM_interp_prov_raise_both.
  Qed.

  Lemma map_monad_convert_impure_base_equal_sync
    (ct : impure_conversion) (t1 t2 : dtyp_base) (elts : list (@dvalue_base (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (map_monad (fun v => convert_impure_base ct t1 v t2) elts) σ1)
      (memM_interp_prov (map_monad (fun v => convert_impure_base ct t1 v t2) elts) σ2).
  Proof using.
    revert U σ1 σ2 Heq; induction elts as [| v vs IH]; intros U σ1 σ2 Heq; cbn [map_monad].
    - apply refine_prov_ret; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply convert_impure_base_equal_sync, Heq |].
      intros U1 [σ1' b1] [σ2' b2] (Hinc1 & Heq1 & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply IH, Heq1 |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (Hinc2 & Heq2 & <-).
      apply refine_prov_ret; split; [eapply incl_tran; eassumption | exact (conj Heq2 Logic.eq_refl)].
  Qed.

  Lemma convert_impure_equal_sync
    (ct : impure_conversion) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (convert_impure ct t_from dv t_to) σ1)
      (memM_interp_prov (convert_impure ct t_from dv t_to) σ2).
  Proof using.
    unfold convert_impure.
    destruct dv as [db | | vec elts].
    - destruct (get_base_conversion_type t_from t_to) as [[t1 t2] |];
        [| apply memM_interp_prov_raise_both].
      unfold Functor.fmap, Functor_Monad.
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply convert_impure_base_equal_sync, Heq |].
      intros U1 [σ1' b1] [σ2' b2] (Hinc1 & Heq1 & <-).
      apply refine_prov_ret; exact (conj Hinc1 (conj Heq1 Logic.eq_refl)).
    - apply memM_interp_prov_raise_both.
    - destruct vec; [| apply memM_interp_prov_raise_both].
      destruct (get_vector_conversion_type t_from t_to) as [[t1 t2] |];
        [| apply memM_interp_prov_raise_both].
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind with (RR := eq_sync_post U).
      + eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
        intros elts' _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
      + intros U1 [σ1' elts1'] [σ2' elts2'] (Hinc1 & Heq1 & <-).
        eapply refine_prov_obs_eq;
          [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
        eapply refine_prov_bind; [apply map_monad_convert_impure_base_equal_sync, Heq1 |].
        intros U2 [σ1'' vs1] [σ2'' vs2] (Hinc2 & Heq2 & <-).
        apply refine_prov_ret; split; [eapply incl_tran; eassumption | exact (conj Heq2 Logic.eq_refl)].
  Qed.

  Lemma handle_memoryM_equal_sync {X} (me : @MemoryE (@ParamsV IP IPT) X)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (handle_memoryM me) σ1)
      (memM_interp_prov (handle_memoryM me) σ2).
  Proof using.
    destruct me as [| | dt num al | dt a | dt a v | ct t1 v t2];
      cbn [handle_memoryM mempush mempop MemoryModelPrimitivesV].
    - apply Mempush_equal_sync, Heq.
    - apply Mempop_equal_sync, Heq.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply allocate_dtyp_equal_sync, Heq |].
      intros U1 [σ1' pt1] [σ2' pt2] (Hinc1 & Heq1 & <-).
      apply refine_prov_ret; exact (conj Hinc1 (conj Heq1 Logic.eq_refl)).
    - destruct a as [[pt | | | | | | |] | |]; cbv beta iota;
        lazymatch goal with
        | |- refine_prov _ _ (memM_interp_prov (Mub _) _) _ => apply memM_interp_prov_raiseUB_l
        | |- refine_prov _ _ (memM_interp_prov (mub _) _) _ => apply memM_interp_prov_raiseUB_l
        | _ => idtac
        end.
      apply read_dvalue_equal_sync, Heq.
    - destruct a as [[pt | | | | | | |] | |]; cbv beta iota;
        lazymatch goal with
        | |- refine_prov _ _ (memM_interp_prov (Mub _) _) _ => apply memM_interp_prov_raiseUB_l
        | |- refine_prov _ _ (memM_interp_prov (mub _) _) _ => apply memM_interp_prov_raiseUB_l
        | _ => idtac
        end.
      apply write_dvalue_equal_sync, Heq.
    - apply convert_impure_equal_sync, Heq.
  Qed.

  Lemma handle_memtransfer_equal_sync (ov : bool) (args : list (@dvalue_base (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (handle_memtransfer ov args) σ1)
      (memM_interp_prov (handle_memtransfer ov args) σ2).
  Proof using.
    unfold handle_memtransfer.
    destruct args as [| dst [| src [| len [| vlt rest]]]];
      try apply memM_interp_prov_raise_both.
    destruct vlt, rest; try apply memM_interp_prov_raise_both.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    assert (Hlen : refine_prov (eq_sync_post U) U
                     (memM_interp_prov
                        (match len with
                         | DVALUE_I _ sz => ExtLib.Structures.Monad.ret (Z.to_N (unsigned sz))
                         | DVALUE_Iptr sz => ExtLib.Structures.Monad.ret (Z.to_N (to_Z sz))
                         | DVALUE_Poison => mub ((if ov then "memmove" else "memcpy") ++ " with poison length.")%string
                         | _ => merr ("Unsupported arguments to " ++ (if ov then "memmove" else "memcpy") ++ ".")%string
                         end) σ1)
                     (memM_interp_prov
                        (match len with
                         | DVALUE_I _ sz => ExtLib.Structures.Monad.ret (Z.to_N (unsigned sz))
                         | DVALUE_Iptr sz => ExtLib.Structures.Monad.ret (Z.to_N (to_Z sz))
                         | DVALUE_Poison => mub ((if ov then "memmove" else "memcpy") ++ " with poison length.")%string
                         | _ => merr ("Unsupported arguments to " ++ (if ov then "memmove" else "memcpy") ++ ".")%string
                         end) σ2)).
    { destruct len;
        try apply memM_interp_prov_raise_both;
        try apply memM_interp_prov_raiseUB_l;
        apply refine_prov_ret; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)). }
    eapply refine_prov_bind; [exact Hlen |].
    intros U1 [σ1' sz1] [σ2' sz2] (Hinc1 & Heq1 & <-).
    assert (Hbody : forall (m : @memM (@ParamsV IP IPT) _ unit),
              refine_prov (eq_sync_post U1) U1 (memM_interp_prov m σ1') (memM_interp_prov m σ2') ->
              refine_prov (eq_sync_post U) U1 (memM_interp_prov m σ1') (memM_interp_prov m σ2')).
    { intros m Hm; eapply refine_prov_weaken; [exact Hm |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)]. }
    apply Hbody.
    destruct dst, src;
      try apply memM_interp_prov_raise_both;
      try (destruct (sz1 =? 0)%N;
           [apply refine_prov_ret; exact (conj (incl_refl U1) (conj Heq1 Logic.eq_refl))
           | apply memM_interp_prov_raiseUB_l]).
    destruct ov; unfold memmove, memcpy.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply read_bytes_equal_sync, Heq1 |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (Hinc2 & Heq2 & <-).
      eapply refine_prov_weaken; [apply write_bytes_equal_sync, Heq2 |].
      intros U3 [s1 r1] [s2 r2] (Hinc3 & Heq3 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq3 Hr)].
    - destruct (orb (no_overlap p sz1 p0 sz1) (Z.eqb (ptr_to_int p0) (ptr_to_int p)));
        [| apply memM_interp_prov_raiseUB_l].
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply read_bytes_equal_sync, Heq1 |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (Hinc2 & Heq2 & <-).
      eapply refine_prov_weaken; [apply write_bytes_equal_sync, Heq2 |].
      intros U3 [s1 r1] [s2 r2] (Hinc3 & Heq3 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq3 Hr)].
  Qed.

  Lemma handle_intrinsicM_equal_sync {X} (ie : @IntrinsicE (@ParamsV IP IPT) X)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (handle_intrinsicM ie) σ1)
      (memM_interp_prov (handle_intrinsicM ie) σ2).
  Proof using.
    destruct ie as [dt name args va]; unfold handle_intrinsicM.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind with (RR := eq_sync_post U).
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros args' _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - intros U1 [σ1' args1'] [σ2' args2'] (Hinc1 & Heq1 & <-).
      assert (Hwk : forall R (m : @memM (@ParamsV IP IPT) _ R),
                refine_prov (eq_sync_post U1) U1 (memM_interp_prov m σ1') (memM_interp_prov m σ2') ->
                refine_prov (eq_sync_post U) U1 (memM_interp_prov m σ1') (memM_interp_prov m σ2')).
      { intros R m Hm; eapply refine_prov_weaken; [exact Hm |].
        intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)]. }
      apply Hwk.
      destruct (is_memcpy_name name).
      + eapply refine_prov_obs_eq;
          [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
        eapply refine_prov_bind; [apply handle_memtransfer_equal_sync, Heq1 |].
        intros U2 [s1 []] [s2 []] (Hinc2 & Heq2 & _); apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
      + destruct (is_memmove_name name).
        * eapply refine_prov_obs_eq;
            [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
          eapply refine_prov_bind; [apply handle_memtransfer_equal_sync, Heq1 |].
          intros U2 [s1 []] [s2 []] (Hinc2 & Heq2 & _); apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
        * destruct (is_memset_name name).
          -- eapply refine_prov_obs_eq;
               [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
             eapply refine_prov_bind with (RR := eq_sync_post U1).
             ++ unfold handle_memset.
                destruct args1' as [| dst [| val [| len [| vlt rest]]]];
                  try apply memM_interp_prov_raise_both.
                destruct vlt, rest; try apply memM_interp_prov_raise_both.
                eapply refine_prov_obs_eq;
                  [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
                assert (Hval : refine_prov (eq_sync_post U1) U1
                                 (memM_interp_prov
                                    (match val with
                                     | DVALUE_I sz v => if Pos.eqb sz 8 then ExtLib.Structures.Monad.ret (BYTE_I (VellvmIntegers.repr (VellvmIntegers.unsigned v) : VellvmIntegers.int8)) else merr "Unsupported arguments to memset."%string
                                     | DVALUE_Poison => ExtLib.Structures.Monad.ret poison_memory_byte
                                     | _ => merr "Unsupported arguments to memset."%string
                                     end) σ1')
                                 (memM_interp_prov
                                    (match val with
                                     | DVALUE_I sz v => if Pos.eqb sz 8 then ExtLib.Structures.Monad.ret (BYTE_I (VellvmIntegers.repr (VellvmIntegers.unsigned v) : VellvmIntegers.int8)) else merr "Unsupported arguments to memset."%string
                                     | DVALUE_Poison => ExtLib.Structures.Monad.ret poison_memory_byte
                                     | _ => merr "Unsupported arguments to memset."%string
                                     end) σ2')).
                { destruct val; try apply memM_interp_prov_raise_both.
                  - match goal with
                    | |- context [Pos.eqb ?s 8] => destruct (Pos.eqb s 8)
                    end;
                      [apply refine_prov_ret; exact (conj (incl_refl U1) (conj Heq1 Logic.eq_refl))
                      | apply memM_interp_prov_raise_both].
                  - apply refine_prov_ret; exact (conj (incl_refl U1) (conj Heq1 Logic.eq_refl)). }
                eapply refine_prov_bind; [exact Hval |].
                intros U2 [s1 mb1] [s2 mb2] (Hinc2 & Heq2 & <-).
                eapply refine_prov_obs_eq;
                  [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
                assert (Hsz : refine_prov (eq_sync_post U2) U2
                                (memM_interp_prov
                                   (match len with
                                    | DVALUE_I _ l => ExtLib.Structures.Monad.ret (Z.to_N (unsigned l))
                                    | DVALUE_Poison => mub "memset with poison length."%string
                                    | _ => merr "Unsupported arguments to memset."%string
                                    end) s1)
                                (memM_interp_prov
                                   (match len with
                                    | DVALUE_I _ l => ExtLib.Structures.Monad.ret (Z.to_N (unsigned l))
                                    | DVALUE_Poison => mub "memset with poison length."%string
                                    | _ => merr "Unsupported arguments to memset."%string
                                    end) s2)).
                { destruct len;
                    try apply memM_interp_prov_raise_both;
                    try apply memM_interp_prov_raiseUB_l;
                    apply refine_prov_ret; exact (conj (incl_refl U2) (conj Heq2 Logic.eq_refl)). }
                eapply refine_prov_bind with (RR := eq_sync_post U1).
                ** eapply refine_prov_weaken; [exact Hsz |].
                   intros U3 [sa ra] [sb rb] (Hinc3 & Heq3 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq3 Hr)].
                ** intros U3 [sa sz1] [sb sz2] (Hinc3 & Heq3 & <-).
                   destruct dst;
                     try apply memM_interp_prov_raise_both.
                   --- unfold memset; eapply refine_prov_weaken; [apply write_bytes_equal_sync, Heq3 |].
                       intros U4 [x1 y1] [x2 y2] (Hinc4 & Heq4 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq4 Hr)].
                   --- destruct (sz1 =? 0)%N;
                         [apply refine_prov_ret; exact (conj Hinc3 (conj Heq3 Logic.eq_refl))
                         | apply memM_interp_prov_raiseUB_l].
             ++ intros U2 [s1 []] [s2 []] (Hinc2 & Heq2 & _); apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
          -- destruct (Rocqlib.proj_sumbool (string_dec name "malloc"%string)).
             ++ eapply refine_prov_obs_eq;
                  [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
                eapply refine_prov_bind with (RR := eq_sync_post U1).
                ** unfold handle_malloc.
                   destruct args1' as [| a0 rest]; [apply memM_interp_prov_raise_both |].
                   destruct a0, rest; try apply memM_interp_prov_raise_both;
                     apply malloc_bytes_equal_sync, Heq1.
                ** intros U2 [s1 pt1] [s2 pt2] (Hinc2 & Heq2 & <-).
                   apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
             ++ destruct (Rocqlib.proj_sumbool (string_dec name "free"%string)).
                ** eapply refine_prov_obs_eq;
                     [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
                   eapply refine_prov_bind with (RR := eq_sync_post U1).
                   --- unfold handle_free.
                       destruct args1' as [| a0 rest]; [apply memM_interp_prov_raise_both |].
                       destruct a0, rest; try apply memM_interp_prov_raise_both.
                       +++ destruct (ptr_to_int p =? ptr_to_int null)%Z;
                             [apply refine_prov_ret; exact (conj (incl_refl U1) (conj Heq1 Logic.eq_refl))
                             | apply Free_equal_sync, Heq1].
                       +++ apply memM_interp_prov_raiseUB_l.
                   --- intros U2 [s1 []] [s2 []] (Hinc2 & Heq2 & _).
                       apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
                ** apply memM_interp_prov_raise_both.
  Qed.

  (** ** 3B. Scalar Types & Byte Serialization Identities *)

  Lemma is_scalar_dtyp_inv (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    exists dtb,
      dt = DTYPE_Base dtb /\
      ((exists sz, dtb = DTYPE_I sz) \/
       dtb = DTYPE_Pointer \/
       dtb = DTYPE_FP FP_float \/
       dtb = DTYPE_FP FP_double).
  Proof using.
    intros Hsc; destruct dt as [dtb | |]; try discriminate Hsc.
    exists dtb; split; [reflexivity |].
    cbn [is_scalar_dtyp is_scalar_dtyp_base] in Hsc.
    destruct dtb as [sz | | | | fp | | | | | |]; try discriminate Hsc.
    - left; exists sz; reflexivity.
    - right; left; reflexivity.
    - destruct fp; try discriminate Hsc;
        [right; right; left; reflexivity | right; right; right; reflexivity].
  Qed.

  Lemma scalar_dtyp_not_void (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    dtyp_eqb dt DTYPE_Void = false.
  Proof using.
    intros Hsc; apply is_scalar_dtyp_inv in Hsc as (dtb & -> & Hdtb).
    unfold dtyp_eqb; destruct (dtyp_eq_dec (DTYPE_Base dtb) (DTYPE_Base DTYPE_Void)) as [Heq | _];
      [| reflexivity].
    inversion Heq; subst dtb.
    destruct Hdtb as [[sz H] | [H | [H | H]]]; discriminate H.
  Qed.

  Lemma scalar_store_size_pos (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    (1 <= @store_size_dtyp SizeofV dt)%N.
  Proof using.
    intros Hsc; apply is_scalar_dtyp_inv in Hsc as (dtb & -> & Hdtb).
    destruct Hdtb as [[sz ->] | [-> | [-> | ->]]];
      cbn [store_size_dtyp SizeofV Store_size_dtyp Sizeof_dtyp_base ptr_size byte_sizeof_floating_point_variant];
      unfold ptr_size; cbn [N.of_nat];
      try lia.
    rewrite round_up_to_eight_div by lia.
    apply N.div_le_lower_bound; lia.
  Qed.

  Lemma bit_sizeof_vec1_eq (dt : dtyp) :
    (@bit_sizeof_dtyp SizeofV (DTYPE_Array true 1%N dt) =? @bit_sizeof_dtyp SizeofV dt)%N = true.
  Proof using.
    cbn [bit_sizeof_dtyp SizeofV Bit_sizeof_dtyp].
    rewrite N.mul_1_l; apply N.eqb_refl.
  Qed.

  Lemma vec1_neq_base (dt : dtyp) (dtb : dtyp_base) :
    dtyp_eqb (DTYPE_Array true 1%N dt) (DTYPE_Base dtb) = false.
  Proof using.
    unfold dtyp_eqb.
    destruct (dtyp_eq_dec (DTYPE_Array true 1%N dt) (DTYPE_Base dtb)) as [Heq | _];
      [discriminate Heq | reflexivity].
  Qed.

  Lemma N_length_h_eq {A} (l : list A) (acc : N) :
    ListUtil.N.length_h l acc = (N.of_nat (List.length l) + acc)%N.
  Proof using.
    revert acc; induction l as [| x xs IH]; intros acc;
      cbn [ListUtil.N.length_h List.length]; [lia |].
    rewrite IH; lia.
  Qed.

  Lemma N_length_eq {A} (l : list A) :
    ListUtil.N.length l = N.of_nat (List.length l).
  Proof using.
    unfold ListUtil.N.length; rewrite N_length_h_eq; lia.
  Qed.

  Lemma dvalue_to_memory_bytes_base_ok
    (dtb : dtyp_base) (db : @dvalue_base (@ParamsV IP IPT)) :
    exists bs : list (@memory_byte (@ParamsV IP IPT)),
      dvalue_to_memory_bytes (DTYPE_Base dtb) (DVALUE_Base db) None = raise_ret bs /\
      List.length bs = N.to_nat (@store_size_dtyp SizeofV (DTYPE_Base dtb)).
  Proof using.
    unfold dvalue_to_memory_bytes, acc_dvalue_to_memory_bytes_h,
           acc_memory_bytes_of_dvalue_base, accumulate_padding.
    eexists; split; [reflexivity |].
    rewrite rev_append_rev, app_nil_r, length_rev, rev_loop_acc_length.
    cbn [Datatypes.length]; rewrite Nat.add_0_r; reflexivity.
  Qed.

  Lemma dvalue_to_memory_bytes_base_err
    (dtb : dtyp_base) (v : @dvalue (@ParamsV IP IPT))
    (Hnot_base : forall db, v <> DVALUE_Base db) :
    exists msg : string,
      dvalue_to_memory_bytes (DTYPE_Base dtb) v None = raise_error msg.
  Proof using.
    destruct v as [db | |]; [exfalso; exact (Hnot_base db Logic.eq_refl) | |];
      eexists; reflexivity.
  Qed.

  Lemma dvalue_to_memory_bytes_vec1_eq
    (dtb : dtyp_base) (db : @dvalue_base (@ParamsV IP IPT)) :
    dvalue_to_memory_bytes (DTYPE_Array true 1%N (DTYPE_Base dtb))
      (DVALUE_Array true [DVALUE_Base db]) None =
    dvalue_to_memory_bytes (DTYPE_Base dtb) (DVALUE_Base db) None.
  Proof using.
    unfold dvalue_to_memory_bytes.
    cbn -[acc_memory_bytes_of_dvalue_base].
    destruct (acc_memory_bytes_of_dvalue_base dtb db 0%N []) as [off bs].
    cbn; reflexivity.
  Qed.

  Lemma alloc_poison_bytes_eq (dt : dtyp) :
    concat_acc (repeatN 1%N (@generate_poison_bytes (@ParamsV IP IPT) dt)) =
    List.repeat (@poison_memory_byte (@ParamsV IP IPT))
      (N.to_nat (@store_size_dtyp SizeofV dt)).
  Proof using.
    rewrite concat_acc_eq.
    change (repeatN 1%N (@generate_poison_bytes (@ParamsV IP IPT) dt))
      with [@generate_poison_bytes (@ParamsV IP IPT) dt].
    cbn [List.concat]; rewrite app_nil_r.
    unfold generate_poison_bytes, generate_num_poison_bytes, generate_num_poison_bytes_h.
    rewrite N_to_nat_safe_eq, seq_map_acc_eq, map_const_Nseq; reflexivity.
  Qed.

  Lemma dvalue_to_memory_bytes_poison_base (dtb : dtyp_base) :
    @dvalue_to_memory_bytes (@ParamsV IP IPT) (DTYPE_Base dtb) (DVALUE_Base DVALUE_Poison) None =
    raise_ret (List.repeat (@poison_memory_byte (@ParamsV IP IPT))
                 (N.to_nat (@store_size_dtyp SizeofV (DTYPE_Base dtb)))).
  Proof using.
    unfold dvalue_to_memory_bytes, acc_dvalue_to_memory_bytes_h,
           acc_memory_bytes_of_dvalue_base, accumulate_padding.
    cbn -[ListUtil.N.rev_loop_acc store_size_dtyp poison_memory_byte].
    rewrite rev_loop_acc_const, app_nil_r, rev_append_rev, app_nil_r, rev_repeat.
    reflexivity.
  Qed.

  Lemma memory_bytes_to_dvalue_b8_total
    (dbs : list (@memory_byte (@ParamsV IP IPT))) :
    exists dv : @dvalue (@ParamsV IP IPT),
      memory_bytes_to_dvalue dbs (DTYPE_Base (DTYPE_B 8)) = raise_ret dv.
  Proof using.
    cbn [memory_bytes_to_dvalue memory_bytes_to_dvalue_base liftM Functor.fmap Functor_Monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_either].
    match goal with |- context [all_poison_bytes ?x] => set (td := x) end.
    destruct (all_poison_bytes td); [eexists; reflexivity |].
    assert (Hbv : exists bv, memory_bytes_to_byte_value 8 td = raise_ret bv).
    { unfold memory_bytes_to_byte_value.
      destruct (memory_bytes_to_pointer_slice td) as [[p k] |];
        [destruct (pointer_chunk_aligned 8 k); eexists; reflexivity | eexists; reflexivity]. }
    destruct Hbv as [bv Hbv]; rewrite Hbv;
      cbn [liftM Functor.fmap Functor_Monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_either].
    destruct (dvalue_bv_all_poison bv); eexists; reflexivity.
  Qed.

  Lemma memory_bytes_to_dvalue_b8_array_total
    (dbs : list (@memory_byte (@ParamsV IP IPT))) (n : N) :
    exists dv : @dvalue (@ParamsV IP IPT),
      memory_bytes_to_dvalue dbs (DTYPE_Array false n (DTYPE_Base (DTYPE_B 8))) = raise_ret dv.
  Proof using.
    cbn [memory_bytes_to_dvalue].
    destruct (poison_split dbs) as [np rest].
    destruct rest as [| b0 rest']; [eexists; reflexivity |].
    match goal with
    | |- exists dv, ExtLib.Structures.Monad.bind (?g (N.to_nat n) 0%N dbs) _ = _ =>
        set (go := g)
    end.
    assert (Hgo : forall cnt off bs, exists elts, go cnt off bs = raise_ret elts).
    { induction cnt as [| cnt' IH]; intros off bs; cbn [go]; [eexists; reflexivity |].
      match goal with
      | |- context [if ?c then ?a else ?b] =>
          assert (He : exists e, (if c then a else b) = raise_ret e);
          [destruct c; [eexists; reflexivity | apply memory_bytes_to_dvalue_b8_total] |]
      end.
      destruct He as [e ->];
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_either].
      match goal with
      | |- context [go cnt' ?off' ?bs'] =>
          destruct (IH off' bs') as [elts Hel]; rewrite Hel
      end;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_either].
      eexists; reflexivity. }
    destruct (Hgo (N.to_nat n) 0%N dbs) as [elts Helts].
    rewrite Helts; cbn; eexists; reflexivity.
  Qed.

  (** ** 3C. Allocation Keys, Consecutive Pointers, Frame Memory & Safe Provenance *)

  Lemma next_key_le_aligned {A} (m : IntMap A) (align : N) :
    (IntMaps.next_key m <= next_key_with_alignment m align)%Z.
  Proof using.
    unfold IntMaps.next_key, next_key_with_alignment, Handlers.Memory.pad_to.
    destruct (IM_greatest_key m) as [gk |]; lia.
  Qed.

  Lemma next_key_with_alignment_pos {A} (m : IntMap A) (align : N) :
    (1 <= next_key_with_alignment m align)%Z.
  Proof using.
    unfold next_key_with_alignment, Handlers.Memory.pad_to.
    destruct (IM_greatest_key m); lia.
  Qed.

  Lemma next_key_with_alignment_fresh {A} (m : IntMap A) (align : N) (z : Z) :
    (next_key_with_alignment m align <= z)%Z ->
    IntMaps.lookup z m = None.
  Proof using.
    intros Hz.
    destruct (IntMaps.lookup z m) as [v |] eqn:Efind; [| reflexivity].
    exfalso.
    assert (Hin : IM.In z m).
    { exists v; apply IM.find_2, Efind. }
    pose proof (IntMaps.next_key_correct m z Hin) as Hlt.
    pose proof (next_key_le_aligned m align) as Hle.
    lia.
  Qed.

  Lemma map_monad_acc_EOU_eq {A B} (f : A -> EOU B) (l : list A) :
    map_monad_acc f l = map_monad f l.
  Proof using.
    unfold map_monad_acc.
    set (go := fix loop (acc : list B) (xs : list A) : EOU (list B) :=
                 match xs with
                 | [] => ExtLib.Structures.Monad.ret (rev_append acc [])
                 | a :: xs' => ExtLib.Structures.Monad.bind (f a) (fun b => loop (b :: acc) xs')
                 end).
    change (go [] l = map_monad f l).
    assert (Hgo : forall xs acc,
              go acc xs = ExtLib.Structures.Monad.bind (map_monad f xs) (fun bs => ExtLib.Structures.Monad.ret (rev_append acc bs))).
    { induction xs as [| a xs' IH]; intros acc; cbn [go map_monad]; [reflexivity |].
      destruct (f a) eqn:Efa; cbn; try reflexivity.
      rewrite IH; destruct (map_monad f xs'); reflexivity. }
    rewrite Hgo; destruct (map_monad f l); reflexivity.
  Qed.

  Lemma ptr_byte_offset_spec (p q : @ptr ProvenanceV (@PointerV IP)) (ix : iptr) :
    ptr_byte_offset p ix = raise_ret q ->
    ptr_to_int q = (ptr_to_int p + to_Z ix)%Z /\
    ptr_provenance q = ptr_provenance p.
  Proof using.
    destruct p as [p_i p_pr].
    unfold ptr_byte_offset.
    replace (@alloc_size_dtyp _ (DTYPE_Base (DTYPE_B 8))) with 1%N by reflexivity.
    cbn [int_to_ptr PIV P2I ptr_to_int ptr_provenance PointerV PTR ParamsV fst snd ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad].
    match goal with
    | |- context [from_Z ?z] =>
        destruct (from_Z z) as [| | | ip] eqn:Efz
    end;
      cbn; try discriminate.
    intros Hq; inversion Hq; subst q; cbn.
    apply from_Z_to_Z in Efz.
    change (Z.of_N 1) with 1%Z in Efz.
    split; [rewrite Efz, Z.mul_1_l; reflexivity | reflexivity].
  Qed.

  Lemma get_consecutive_ptrs_seq_spec
    (p : @ptr ProvenanceV (@PointerV IP))
    (n : nat) (start : N) (ixs : list iptr)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP))) :
    map_monad (fun k : N => from_Z (Z.of_N k)) (Nseq start n) = raise_ret ixs ->
    map_monad (ptr_byte_offset p) ixs = raise_ret ptrs ->
    List.length ptrs = n /\
    (forall k q,
       nth_error ptrs k = Some q ->
       (k < n)%nat /\
       ptr_to_int q = (ptr_to_int p + Z.of_N start + Z.of_nat k)%Z /\
       ptr_provenance q = ptr_provenance p) /\
    (forall k,
       (k < n)%nat ->
       exists q,
         nth_error ptrs k = Some q /\
         ptr_to_int q = (ptr_to_int p + Z.of_N start + Z.of_nat k)%Z /\
         ptr_provenance q = ptr_provenance p).
  Proof using.
    revert start ixs ptrs; induction n as [| n' IH]; intros start ixs ptrs Hixs Hptrs;
      cbn [Nseq map_monad] in Hixs.
    - inversion Hixs; subst ixs; cbn [map_monad] in Hptrs; inversion Hptrs; subst ptrs.
      split; [reflexivity | split].
      + intros [| k] q Hk; discriminate Hk.
      + intros k Hk; lia.
    - apply EOU_bind_ret_inv in Hixs as (ix0 & Hfz0 & Hixs').
      apply EOU_bind_ret_inv in Hixs' as (ixs_tl & Hmap_ix & Heq_ixs).
      inversion Heq_ixs; subst ixs; clear Heq_ixs.
      cbn [map_monad] in Hptrs.
      apply EOU_bind_ret_inv in Hptrs as (q0 & Hq0 & Hptrs').
      apply EOU_bind_ret_inv in Hptrs' as (ptrs_tl & Hmap_tl & Heq_ptrs).
      inversion Heq_ptrs; subst ptrs; clear Heq_ptrs.
      apply from_Z_to_Z in Hfz0.
      apply ptr_byte_offset_spec in Hq0 as [Hq0_int Hq0_pr].
      destruct (IH (N.succ start) ixs_tl ptrs_tl Hmap_ix Hmap_tl) as (Hlen & Hnth_inv & Hnth_ex).
      split; [cbn [List.length]; lia | split].
      + intros [| k] q Hnth; cbn [nth_error] in Hnth.
        * inversion Hnth; subst q.
          split; [lia | split; [lia | exact Hq0_pr]].
        * destruct (Hnth_inv k q Hnth) as (Hk & Hq_int & Hq_pr).
          split; [lia | split; [lia | exact Hq_pr]].
      + intros [| k] Hk; cbn [nth_error].
        * exists q0; split; [reflexivity | split; [lia | exact Hq0_pr]].
        * assert (Hk' : (k < n')%nat) by lia.
          destruct (Hnth_ex k Hk') as (q & Hnth & Hq_int & Hq_pr).
          exists q; split; [exact Hnth | split; [lia | exact Hq_pr]].
  Qed.

  Lemma get_consecutive_ptrs_spec
    (p : @ptr ProvenanceV (@PointerV IP)) (size : N)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP))) :
    get_consecutive_ptrs p size = raise_ret ptrs ->
    List.length ptrs = N.to_nat size /\
    (forall k q,
       nth_error ptrs k = Some q ->
       (k < N.to_nat size)%nat /\
       ptr_to_int q = (ptr_to_int p + Z.of_nat k)%Z /\
       ptr_provenance q = ptr_provenance p) /\
    (forall k,
       (k < N.to_nat size)%nat ->
       exists q,
         nth_error ptrs k = Some q /\
         ptr_to_int q = (ptr_to_int p + Z.of_nat k)%Z /\
         ptr_provenance q = ptr_provenance p).
  Proof using.
    unfold get_consecutive_ptrs, intptr_seq.
    rewrite N_to_nat_safe_eq, seq_map_monad_acc_eq.
    intros H; apply EOU_bind_ret_inv in H as (ixs & Hixs & Hptrs).
    rewrite map_monad_acc_EOU_eq in Hptrs.
    destruct (get_consecutive_ptrs_seq_spec p (N.to_nat size) 0%N ixs ptrs Hixs Hptrs)
      as (Hlen & Hinv & Hex).
    split; [exact Hlen | split].
    - intros k q Hnth; destruct (Hinv k q Hnth) as (Hk & Hq_int & Hq_pr).
      split; [exact Hk | split; [lia | exact Hq_pr]].
    - intros k Hk; destruct (Hex k Hk) as (q & Hnth & Hq_int & Hq_pr).
      exists q; split; [exact Hnth | split; [lia | exact Hq_pr]].
  Qed.

  Lemma get_consecutive_ptrs_in_addrs
    (p : @ptr ProvenanceV (@PointerV IP)) (size : N)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP))) (z : Z)
    (Hptrs : get_consecutive_ptrs p size = raise_ret ptrs) :
    In z (List.map ptr_to_int ptrs) <->
    (ptr_to_int p <= z < ptr_to_int p + Z.of_nat (N.to_nat size))%Z.
  Proof using.
    destruct (get_consecutive_ptrs_spec p size ptrs Hptrs) as (Hlen & Hinv & Hex).
    split.
    - intros Hin; apply in_map_iff in Hin as (q & <- & Hin_q).
      apply In_nth_error in Hin_q as [k Hnth].
      destruct (Hinv k q Hnth) as (Hk & Hq_int & _); lia.
    - intros Hz.
      set (k := Z.to_nat (z - ptr_to_int p)).
      assert (Hk : (k < N.to_nat size)%nat) by lia.
      destruct (Hex k Hk) as (q & Hnth & Hq_int & _).
      replace z with (ptr_to_int q) by lia.
      apply in_map, (nth_error_In ptrs k Hnth).
  Qed.

  Lemma get_consecutive_ptrs_well_behaved {IPWB : IPtrWellBehaved IP}
    (p : @ptr ProvenanceV (@PointerV IP)) (size : N) :
    (exists ptrs, get_consecutive_ptrs p size = raise_ret ptrs) \/
    (exists msg, get_consecutive_ptrs p size = raise_oom msg).
  Proof using.
    unfold get_consecutive_ptrs, intptr_seq; cbn [IPTR ParamsV].
    rewrite N_to_nat_safe_eq, seq_map_monad_acc_eq.
    lazymatch goal with
    | |- context [map_monad ?f (Nseq _ _)] =>
        assert (Hix : forall n start,
                  (exists ixs, map_monad f (Nseq start n) = raise_ret ixs) \/
                  (exists msg, map_monad f (Nseq start n) = raise_oom msg))
    end.
    { induction n as [| n' IH]; intros start; cbn [Nseq map_monad]; [left; exists []; reflexivity |].
      unfold Basics.compose; unfold Basics.compose in IH; cbn beta; cbn beta in IH.
      destruct (@from_Z_ret_or_oom IP IPWB (Z.of_N start)) as [[ix Hfx] | [msg Hfx]]; rewrite Hfx; cbn;
        [| right; exists msg; reflexivity].
      destruct (IH (N.succ start)) as [[ixs Hixs] | [msg Hmsg]].
      - rewrite Hixs; cbn; left; exists (ix :: ixs); reflexivity.
      - rewrite Hmsg; cbn; right; exists msg; reflexivity. }
    destruct (Hix (N.to_nat size) 0%N) as [[ixs Hixs] | [msg Hmsg]].
    - rewrite Hixs; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad].
      rewrite map_monad_acc_EOU_eq.
      clear Hixs; induction ixs as [| ix ixs' IH]; cbn [map_monad]; [left; exists []; reflexivity |].
      destruct IH as [[ptrs Hptrs] | [msg Hmsg]]; [rewrite Hptrs | rewrite Hmsg];
        unfold ptr_byte_offset; cbn [P2I IPTR ParamsV];
        unfold int_to_ptr, PIV;
        cbn [IPTR ParamsV ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad Monad_either];
        match goal with
        | |- context [from_Z ?z] =>
            pose proof (@from_Z_ret_or_oom IP IPWB z) as Hfz
        end;
        destruct Hfz as [[i Hfi] | [msg' Hfi]]; rewrite Hfi;
        cbn [ExtLib.Structures.Monad.bind EOU_monad Monad_either ExtLib.Structures.Monad.ret];
        [left; exists ((i, ptr_provenance p) :: ptrs); reflexivity
        | right; exists msg'; reflexivity
        | right; exists msg; reflexivity
        | right; exists msg'; reflexivity].
    - rewrite Hmsg; right; exists msg; reflexivity.
  Qed.

  Lemma lookup_add_all_index_in {A} (vs : list A) (base : Z) (m : IntMap A)
    (k : nat) (v : A) (z : Z) :
    nth_error vs k = Some v ->
    z = (base + Z.of_nat k)%Z ->
    IntMaps.lookup z (IntMaps.add_all_index vs base m) = Some v.
  Proof using.
    revert base k z; induction vs as [| v0 vs' IH]; intros base [| k] z Hnth ->;
      cbn [nth_error] in Hnth; try discriminate Hnth.
    - inversion Hnth; subst v0.
      replace (base + Z.of_nat 0)%Z with base by lia.
      cbn [IntMaps.add_all_index]; apply IntMaps.lookup_add_eq.
    - cbn [IntMaps.add_all_index].
      rewrite IntMaps.lookup_add_ineq by lia.
      apply (IH (base + 1)%Z k); [exact Hnth | lia].
  Qed.

  Lemma lookup_add_all_index_out {A} (vs : list A) (base : Z) (m : IntMap A) (z : Z) :
    ~ (base <= z < base + Z.of_nat (List.length vs))%Z ->
    IntMaps.lookup z (IntMaps.add_all_index vs base m) = IntMaps.lookup z m.
  Proof using.
    revert base; induction vs as [| v0 vs' IH]; intros base Hout;
      cbn [IntMaps.add_all_index List.length] in *; [reflexivity |].
    rewrite IntMaps.lookup_add_ineq by lia.
    apply IH; lia.
  Qed.

  Lemma lookup_add_all_index_acc_in {A} (vs : list A) (base : Z) (m : IntMap A)
    (k : nat) (v : A) (z : Z) :
    nth_error vs k = Some v ->
    z = (base + Z.of_nat k)%Z ->
    IntMaps.lookup z (IntMaps.add_all_index_acc vs base m) = Some v.
  Proof using.
    intros Hnth Hz.
    pose proof (IntMaps.add_all_index_acc_eq vs base m z) as Heq.
    rewrite Heq; eapply lookup_add_all_index_in; eassumption.
  Qed.

  Lemma lookup_add_all_index_acc_out {A} (vs : list A) (base : Z) (m : IntMap A) (z : Z) :
    ~ (base <= z < base + Z.of_nat (List.length vs))%Z ->
    IntMaps.lookup z (IntMaps.add_all_index_acc vs base m) = IntMaps.lookup z m.
  Proof using.
    intros Hout.
    pose proof (IntMaps.add_all_index_acc_eq vs base m z) as Heq.
    rewrite Heq; apply lookup_add_all_index_out, Hout.
  Qed.

  Lemma add_all_to_frame_Singleton
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (mem : @memory (@ParamsV IP IPT))
    (f : @Frame (@ParamsV IP IPT))
    (h : @Heap (@ParamsV IP IPT)) :
    add_all_to_frame ks (mkMemoryStack mem (Singleton f) h) =
    mkMemoryStack mem (Singleton (rev ks ++ f)) h.
  Proof using.
    unfold add_all_to_frame.
    revert f; induction ks as [| k ks' IH]; intros f;
      cbn [fold_left add_to_frame rev app]; [reflexivity |].
    rewrite IH, <- app_assoc; reflexivity.
  Qed.

  Lemma add_all_to_frame_Snoc
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (mem : @memory (@ParamsV IP IPT))
    (s : @Framestack (@ParamsV IP IPT))
    (f : @Frame (@ParamsV IP IPT))
    (h : @Heap (@ParamsV IP IPT)) :
    add_all_to_frame ks (mkMemoryStack mem (Snoc s f) h) =
    mkMemoryStack mem (Snoc s (rev ks ++ f)) h.
  Proof using.
    unfold add_all_to_frame.
    revert f; induction ks as [| k ks' IH]; intros f;
      cbn [fold_left add_to_frame rev app]; [reflexivity |].
    rewrite IH, <- app_assoc; reflexivity.
  Qed.

  Lemma in_map_rev_app_iff {A B} (g : A -> B) (xs ys : list A) (y : B) :
    In y (List.map g (rev xs ++ ys)) <->
    In y (List.map g xs) \/ In y (List.map g ys).
  Proof using.
    rewrite map_app, map_rev, in_app_iff, <- in_rev; reflexivity.
  Qed.

  Lemma lookup_free_frame_memory_out
    (f : @Frame (@ParamsV IP IPT))
    (m : @memory (@ParamsV IP IPT)) (z : Z) :
    ~ In z (List.map ptr_to_int f) ->
    IntMaps.lookup z (free_frame_memory f m) = IntMaps.lookup z m.
  Proof using.
    unfold free_frame_memory.
    revert m; induction f as [| k0 f' IH]; intros m Hnin;
      cbn [fold_left List.map] in *; [reflexivity |].
    rewrite IH by (intros Hx; apply Hnin; right; exact Hx).
    unfold free_byte; apply lookup_delete_neq.
    intros ->; apply Hnin; left; reflexivity.
  Qed.

  Lemma lookup_free_frame_memory_in
    (f : @Frame (@ParamsV IP IPT))
    (m : @memory (@ParamsV IP IPT)) (z : Z) :
    In z (List.map ptr_to_int f) ->
    IntMaps.lookup z (free_frame_memory f m) = None.
  Proof using.
    revert m; induction f as [| k0 f' IH]; intros m Hin;
      cbn [free_frame_memory fold_left List.map] in *; [contradiction |].
    change (fold_left (fun m0 key => free_byte (ptr_to_int key) m0) f' (free_byte (ptr_to_int k0) m))
      with (free_frame_memory f' (free_byte (ptr_to_int k0) m)).
    destruct (in_dec Z.eq_dec z (List.map ptr_to_int f')) as [Hin' | Hnin'].
    - apply IH, Hin'.
    - destruct Hin as [<- | Hin]; [| contradiction].
      rewrite lookup_free_frame_memory_out by exact Hnin'.
      unfold free_byte; apply lookup_delete_eq.
  Qed.

  Definition safe_prov (P_unprom : list N) (pr : @prov ProvenanceV) : Prop :=
    match pr with
    | None => False
    | Some ps => incl ps P_unprom
    end.

  Definition is_safe_ptr_dvalue (P_unprom : list N) (v : @dvalue (@ParamsV IP IPT)) : Prop :=
    forall pt, v = DVALUE_Base (DVALUE_Pointer pt) -> safe_prov P_unprom (ptr_provenance pt).

  Definition genv_safe (P_unprom : list N) (g : @global_env (@ParamsV IP IPT)) : Prop :=
    forall gid v, Maps.lookup gid g = Some v -> is_safe_ptr_dvalue P_unprom v.

  Lemma safe_prov_incl (P1 P2 : list N) (pr : @prov ProvenanceV) :
    incl P1 P2 ->
    safe_prov P1 pr ->
    safe_prov P2 pr.
  Proof using.
    intros Hinc Hpr; destruct pr as [ps |]; [eapply incl_tran; eassumption | exact Hpr].
  Qed.

  Lemma is_safe_ptr_dvalue_incl (P1 P2 : list N) (v : @dvalue (@ParamsV IP IPT)) :
    incl P1 P2 ->
    is_safe_ptr_dvalue P1 v ->
    is_safe_ptr_dvalue P2 v.
  Proof using.
    intros Hinc Hv pt Hpt; eapply safe_prov_incl; [exact Hinc | apply Hv, Hpt].
  Qed.

  Lemma genv_safe_incl (P1 P2 : list N) (g : @global_env (@ParamsV IP IPT)) :
    incl P1 P2 ->
    genv_safe P1 g ->
    genv_safe P2 g.
  Proof using.
    intros Hinc Hg gid v Hlk; eapply is_safe_ptr_dvalue_incl; [exact Hinc | eapply Hg, Hlk].
  Qed.

  Lemma null_safe_ptr_dvalue (P_unprom : list N) :
    is_safe_ptr_dvalue P_unprom (DVALUE_Base (DVALUE_Pointer null)).
  Proof using.
    intros pt Hpt; inversion Hpt; subst pt; cbn; intros x [].
  Qed.

  Lemma poison_safe_ptr_dvalue (P_unprom : list N) :
    is_safe_ptr_dvalue P_unprom (DVALUE_Base DVALUE_Poison).
  Proof using.
    intros pt Hpt; discriminate Hpt.
  Qed.

  Lemma fresh_ptr_safe_dvalue (P_unprom : list N) (pt : @ptr ProvenanceV (@PointerV IP)) (pr : N) :
    ptr_provenance pt = Some [pr] ->
    is_safe_ptr_dvalue (pr :: P_unprom) (DVALUE_Base (DVALUE_Pointer pt)).
  Proof using.
    intros Hpr pt' Hpt'; inversion Hpt'; subst pt'.
    unfold safe_prov; cbn in Hpr |- *; rewrite Hpr; intros z [<- | []]; left; reflexivity.
  Qed.

  Lemma safe_prov_access_disjoint (P_unprom : list N) (pr : @prov ProvenanceV) (pr_prom : N) :
    safe_prov P_unprom pr ->
    ~ In pr_prom P_unprom ->
    @access_allowed ProvenanceV pr (Some pr_prom) = false.
  Proof using.
    intros Hsafe Hnin.
    destruct pr as [ps |]; [| contradiction Hsafe].
    cbn [access_allowed ProvenanceV].
    destruct (existsb (N.eqb pr_prom) ps) eqn:Eex; [| reflexivity].
    exfalso; apply existsb_exists in Eex as (x & Hx & Heqb).
    apply N.eqb_eq in Heqb; subst x.
    apply Hnin, Hsafe, Hx.
  Qed.

  Lemma eval_gep_safe_ptr (P_unprom : list N) (flags : gep_flags) (dt : dtyp)
    (dv : @dvalue (@ParamsV IP IPT)) (vs : list (@dvalue (@ParamsV IP IPT)))
    (res : @dvalue (@ParamsV IP IPT)) :
    is_safe_ptr_dvalue P_unprom dv ->
    eval_gep flags dt dv vs = raise_ret res ->
    is_safe_ptr_dvalue P_unprom res.
  Proof using.
    intros Hdv Hgep.
    unfold eval_gep in Hgep.
    destruct dv as [[pt | | | | | | |] | |]; try discriminate Hgep.
    - unfold catch_pois, Functor.fmap, Functor_Monad in Hgep.
      destruct (handle_gep_ptr flags dt pt vs) as [| | | [pt' |]] eqn:Eh;
        cbn [catch_pois liftM Functor.fmap Functor_Monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOUP_Monad EOU_monad Monad_either] in Hgep;
        try discriminate Hgep; inversion Hgep; subst res.
      + intros pt0 Hpt0; inversion Hpt0; subst pt0.
        pose proof (@handle_gep_ptr_preserves_provenance (@ParamsV IP IPT) flags dt vs pt pt' Eh) as Hpr.
        rewrite <- Hpr; apply (Hdv pt Logic.eq_refl).
      + apply poison_safe_ptr_dvalue.
    - inversion Hgep; subst res; apply poison_safe_ptr_dvalue.
  Qed.

  Lemma eval_select_safe_ptr (P_unprom : list N)
    (cnd : @dvalue (@ParamsV IP IPT)) (vt : dtyp)
    (v1 v2 res : @dvalue (@ParamsV IP IPT)) :
    is_safe_ptr_dvalue P_unprom v1 ->
    is_safe_ptr_dvalue P_unprom v2 ->
    eval_select cnd vt v1 v2 = raise_ret res ->
    is_safe_ptr_dvalue P_unprom res.
  Proof using.
    intros Hv1 Hv2 Hsel; unfold eval_select in Hsel.
    destruct cnd as [cb | | vec conds]; try discriminate Hsel.
    - unfold eval_select_base_dvalue in Hsel.
      destruct cb as [| sz i | | | | | |]; try discriminate Hsel.
      + destruct sz; try discriminate Hsel.
        destruct (@Integers.unsigned 1 i =? 1)%Z; inversion Hsel; subst res; assumption.
      + inversion Hsel; subst res; apply poison_safe_ptr_dvalue.
    - destruct vec; [| discriminate Hsel].
      destruct vt as [| | vec_t sz_t elt_t]; try discriminate Hsel.
      destruct vec_t; [| discriminate Hsel].
      destruct (map_monad dvalue_to_dvalue_base conds) as [| | | conds'];
        cbn in Hsel; try discriminate Hsel.
      destruct v1 as [[| | | | | | |] | | [|] elts1],
               v2 as [[| | | | | | |] | | [|] elts2];
        cbn in Hsel; try discriminate Hsel;
        try (inversion Hsel; subst res; apply poison_safe_ptr_dvalue);
        (unfold Functor.fmap, Functor_Monad in Hsel;
         destruct (vec_loop _ _) as [| | | out]; cbn in Hsel; try discriminate Hsel;
         inversion Hsel; subst res; unfold canonicalize_vector in *;
         destruct (forallb dvalue_is_poison out);
         [apply poison_safe_ptr_dvalue | intros pt Hpt; discriminate Hpt]).
  Qed.


End MemoryAndSerialization.
