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

From CertPasses Require Import Mem2RegModel Mem2RegMemBase.

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

  (** ** 3D. Stage 1 Ghost-Slot Memory Invariant & Primitive Simulation *)

  Record ghost_slot : Type := mkGhostSlot {
    gs_pt    : @ptr ProvenanceV (@PointerV IP);
    gs_ptrs  : list (@ptr ProvenanceV (@PointerV IP));
    gs_pr    : N;
    gs_dt    : dtyp;
    gs_db    : @dvalue_base (@ParamsV IP IPT);
    gs_bytes : list (@memory_byte (@ParamsV IP IPT))
  }.

  Definition gs_len (gs : ghost_slot) : nat :=
    N.to_nat (@store_size_dtyp SizeofV (gs_dt gs)).

  Definition gs_addr (gs : ghost_slot) : Z :=
    ptr_to_int (gs_pt gs).

  Definition gs_in_range (gs : ghost_slot) (z : Z) : Prop :=
    (gs_addr gs <= z < gs_addr gs + Z.of_nat (gs_len gs))%Z.

  Definition gs_wf (gs : ghost_slot) : Prop :=
    is_scalar_dtyp (gs_dt gs) = true /\
    ptr_provenance (gs_pt gs) = Some [gs_pr gs] /\
    get_consecutive_ptrs (gs_pt gs) (@store_size_dtyp SizeofV (gs_dt gs)) = raise_ret (gs_ptrs gs) /\
    dvalue_to_memory_bytes (gs_dt gs) (DVALUE_Base (gs_db gs)) None = raise_ret (gs_bytes gs) /\
    List.length (gs_bytes gs) = gs_len gs /\
    (1 <= gs_addr gs)%Z.

  Definition gs_disjoint (gs1 gs2 : ghost_slot) : Prop :=
    forall z, gs_in_range gs1 z -> ~ gs_in_range gs2 z.

  Fixpoint ghost_list_disjoint (G : list ghost_slot) : Prop :=
    match G with
    | [] => True
    | gs :: G' => (forall gs', In gs' G' -> gs_disjoint gs gs') /\ ghost_list_disjoint G'
    end.

  Lemma ghost_list_disjoint_sym_neq (G : list ghost_slot) :
    ghost_list_disjoint G ->
    forall gs1 gs2 z,
      In gs1 G ->
      In gs2 G ->
      gs_in_range gs1 z ->
      gs_in_range gs2 z ->
      gs1 = gs2.
  Proof using.
    induction G as [| gs0 G' IH]; intros Hdisj gs1 gs2 z Hin1 Hin2 Hr1 Hr2;
      [contradiction |].
    destruct Hdisj as [Hhd Htl].
    destruct Hin1 as [<- | Hin1], Hin2 as [<- | Hin2].
    - reflexivity.
    - exfalso; eapply (Hhd gs2 Hin2 z Hr1 Hr2).
    - exfalso; eapply (Hhd gs1 Hin1 z Hr2 Hr1).
    - eapply IH; eassumption.
  Qed.

  Lemma gs_in_range_dec (gs : ghost_slot) (z : Z) :
    {gs_in_range gs z} + {~ gs_in_range gs z}.
  Proof using.
    unfold gs_in_range.
    destruct (Z_le_gt_dec (gs_addr gs) z) as [Hle | Hgt].
    - destruct (Z_lt_ge_dec z (gs_addr gs + Z.of_nat (gs_len gs))) as [Hlt | Hge].
      + left; lia.
      + right; lia.
    - right; lia.
  Qed.

  Lemma stage1_find_gs_at (G : list ghost_slot) (z : Z) :
    {gs : ghost_slot | In gs G /\ gs_in_range gs z} +
    {forall gs, In gs G -> ~ gs_in_range gs z}.
  Proof using.
    induction G as [| gs0 G' IH].
    - right; intros gs [].
    - destruct (gs_in_range_dec gs0 z) as [Hin0 | Hout0].
      + left; exists gs0; split; [left; reflexivity | exact Hin0].
      + destruct IH as [[gs [Hgs Hr]] | Hall].
        * left; exists gs; split; [right; exact Hgs | exact Hr].
        * right; intros gs [<- | Hgs]; [exact Hout0 | apply Hall, Hgs].
  Qed.

  Inductive framestack_ghost_wf
    : list ghost_slot -> @Framestack (@ParamsV IP IPT) -> Prop :=
  | FGW_Base fs :
      framestack_ghost_wf [] fs
  | FGW_Snoc_Unprom G fs f :
      framestack_ghost_wf G fs ->
      (forall z, In z (List.map ptr_to_int f) -> forall gs, In gs G -> ~ gs_in_range gs z) ->
      framestack_ghost_wf G (Snoc fs f)
  | FGW_Snoc_Prom gs G fs f :
      framestack_ghost_wf G fs ->
      (forall z, gs_in_range gs z -> In z (List.map ptr_to_int f)) ->
      (forall z, In z (List.map ptr_to_int f) -> forall gs', In gs' G -> ~ gs_in_range gs' z) ->
      framestack_ghost_wf (gs :: G) (Snoc fs f).

  Definition stage1_mem_inv (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) : Prop :=
    incl P_unprom U /\
    NoDup (List.map gs_pr G) /\
    Forall (fun gs => gs_wf gs /\ In (gs_pr gs) U /\ ~ In (gs_pr gs) P_unprom) G /\
    ghost_list_disjoint G /\
    framestack_ghost_wf G (Memory_stack_frame_stack (state_memory_stack σ2)) /\
    Memory_stack_frame_stack (state_memory_stack σ1) = Memory_stack_frame_stack (state_memory_stack σ2) /\
    Memory_stack_heap (state_memory_stack σ1) = Memory_stack_heap (state_memory_stack σ2) /\
    (forall z,
       (forall gs, In gs G -> ~ gs_in_range gs z) ->
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ1)) =
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ2))) /\
    (forall gs k mb,
       In gs G ->
       nth_error (gs_bytes gs) k = Some mb ->
       IntMaps.lookup (gs_addr gs + Z.of_nat k)%Z (Memory_stack_memory (state_memory_stack σ1)) =
         Some (mb, Some (gs_pr gs)) /\
       IntMaps.lookup (gs_addr gs + Z.of_nat k)%Z (Memory_stack_memory (state_memory_stack σ2)) =
         Some (poison_memory_byte, Some (gs_pr gs))).

  Lemma stage1_mem_inv_incl_U (U U' P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    incl U U' ->
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    stage1_mem_inv U' P_unprom G σ1 σ2.
  Proof using.
    intros Hinc (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    split; [eapply incl_tran; eassumption |].
    split; [exact Hnd |].
    split.
    - eapply Forall_impl; [| exact Hall].
      intros gs (Hwf & HinU & HninP); split; [exact Hwf | split; [apply Hinc, HinU | exact HninP]].
    - exact (conj Hdisj (conj Hfgw (conj Hfs (conj Hh (conj Hout Hgs))))).
  Qed.

  Lemma stage1_mem_nil_is_equal (U P_unprom : list N) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom [] σ1 σ2 ->
    mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2).
  Proof using.
    intros (_ & _ & _ & _ & _ & Hfs & Hh & Hout & _).
    repeat split; [| exact Hfs | exact Hh].
    intros z; apply Hout; intros gs [].
  Qed.

  Lemma stage1_equal_to_mem_inv (U P_unprom : list N) (σ1 σ2 : state) :
    incl P_unprom U ->
    mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
    stage1_mem_inv U P_unprom [] σ1 σ2.
  Proof using.
    intros Hpu (Hm & Hfs & Hh).
    split; [exact Hpu |].
    split; [constructor |].
    split; [constructor |].
    split; [exact I |].
    split; [apply FGW_Base |].
    split; [exact Hfs |].
    split; [exact Hh |].
    split; [intros z _; apply Hm | intros gs _ _ []].
  Qed.

  Lemma stage1_gs_lookup_range (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) (gs : ghost_slot) (z : Z) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    In gs G ->
    gs_in_range gs z ->
    exists mb,
      nth_error (gs_bytes gs) (Z.to_nat (z - gs_addr gs)) = Some mb /\
      IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ1)) = Some (mb, Some (gs_pr gs)) /\
      IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ2)) = Some (poison_memory_byte, Some (gs_pr gs)).
  Proof using.
    intros (_ & _ & Hall & _ & _ & _ & _ & _ & Hgs) Hin Hr.
    rewrite Forall_forall in Hall.
    destruct (Hall gs Hin) as [Hwf _].
    destruct Hwf as (_ & _ & _ & _ & Hlen & _).
    unfold gs_in_range in Hr.
    set (k := Z.to_nat (z - gs_addr gs)).
    assert (Hk : (k < List.length (gs_bytes gs))%nat) by lia.
    destruct (nth_error_Some (gs_bytes gs) k) as [_ Hsome].
    destruct (nth_error (gs_bytes gs) k) as [mb |] eqn:Enth;
      [| exfalso; apply Hsome; [exact Hk | reflexivity]].
    destruct (Hgs gs k mb Hin Enth) as [Hlk1 Hlk2].
    replace z with (gs_addr gs + Z.of_nat k)%Z by lia.
    exists mb; split; [reflexivity | split; [exact Hlk1 | exact Hlk2]].
  Qed.

  Lemma stage1_mem_member_iff (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) (z : Z) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    (IntMaps.member z (Memory_stack_memory (state_memory_stack σ1)) <->
     IntMaps.member z (Memory_stack_memory (state_memory_stack σ2))).
  Proof using.
    intros Hinv.
    destruct (stage1_find_gs_at G z) as [[gs [Hin Hr]] | Hout_z].
    - destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs z Hinv Hin Hr)
        as (mb & _ & Hlk1 & Hlk2).
      split; intros _.
      + eapply IntMaps.lookup_member; exact Hlk2.
      + eapply IntMaps.lookup_member; exact Hlk1.
    - destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & Hout & _).
      pose proof (Hout z Hout_z) as Heq.
      split; intros Hm; apply IntMaps.member_lookup in Hm as [v Hv];
        [rewrite Heq in Hv | rewrite <- Heq in Hv];
        eapply IntMaps.lookup_member; exact Hv.
  Qed.

  Lemma stage1_mem_next_key_eq (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) (align : N) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    next_key_with_alignment (Memory_stack_memory (state_memory_stack σ1)) align =
    next_key_with_alignment (Memory_stack_memory (state_memory_stack σ2)) align.
  Proof using.
    intros Hinv; unfold next_key_with_alignment.
    erewrite IM_greatest_key_morph; [reflexivity |].
    intros k; eapply stage1_mem_member_iff; exact Hinv.
  Qed.

  Lemma stage1_gs_fresh_above_next_key (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) (align : N) (z : Z) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    (next_key_with_alignment (Memory_stack_memory (state_memory_stack σ1)) align <= z)%Z ->
    forall gs, In gs G -> ~ gs_in_range gs z.
  Proof using.
    intros Hinv Hge gs Hin Hr.
    destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs z Hinv Hin Hr)
      as (mb & _ & Hlk1 & _).
    rewrite (next_key_with_alignment_fresh _ align z Hge) in Hlk1.
    discriminate Hlk1.
  Qed.

  Lemma int_to_ptr_spec (addr : Z) (pr_opt : @prov ProvenanceV)
    (pt : @ptr ProvenanceV (@PointerV IP)) :
    int_to_ptr addr pr_opt = raise_ret pt ->
    ptr_to_int pt = addr /\ ptr_provenance pt = pr_opt.
  Proof using IP IPT.
    cbn [int_to_ptr PIV P2I ptr_to_int ptr_provenance PointerV PTR ParamsV fst snd ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad].
    destruct (from_Z addr) as [| | | ip] eqn:Efz; cbn; try discriminate.
    intros H; inversion H; subst pt; cbn.
    apply from_Z_to_Z in Efz; split; [exact Efz | reflexivity].
  Qed.

  Lemma memory_bytes_to_bytes_eq (aid : @allocationId ProvenanceV)
    (bs : list (@memory_byte (@ParamsV IP IPT))) :
    memory_bytes_to_bytes aid bs = List.map (fun b => (b, aid)) bs.
  Proof using.
    unfold memory_bytes_to_bytes; apply map_acc_eq.
  Qed.

  Lemma convert_impure_base_id_sync
    (ct : impure_conversion) (t1 : dtyp_base) (dv : @dvalue_base (@ParamsV IP IPT)) (t2 : dtyp_base)
    (U : list N) (σ1 σ2 : state) :
    refine_prov (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2) U
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
         intros r _ <-; repeat split; reflexivity).
    - destruct dv; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        ((eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |]);
         intros r _ <-; repeat split; reflexivity).
    - destruct dv; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        ((eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |]);
         intros r _ <-; repeat split; reflexivity).
    - apply memM_interp_prov_raise_both.
  Qed.

  Lemma map_monad_convert_impure_base_id_sync
    (ct : impure_conversion) (t1 t2 : dtyp_base) (elts : list (@dvalue_base (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state) :
    refine_prov (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2) U
      (memM_interp_prov (map_monad (fun v => convert_impure_base ct t1 v t2) elts) σ1)
      (memM_interp_prov (map_monad (fun v => convert_impure_base ct t1 v t2) elts) σ2).
  Proof using.
    induction elts as [| v vs IH]; cbn [map_monad].
    - apply refine_prov_ret; repeat split; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply convert_impure_base_id_sync |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & -> & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [exact IH |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (-> & -> & -> & <-).
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma convert_impure_id_sync
    (ct : impure_conversion) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (U : list N) (σ1 σ2 : state) :
    refine_prov (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2) U
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
      eapply refine_prov_bind; [apply convert_impure_base_id_sync |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & -> & <-).
      apply refine_prov_ret; repeat split; reflexivity.
    - apply memM_interp_prov_raise_both.
    - destruct vec; [| apply memM_interp_prov_raise_both].
      destruct (get_vector_conversion_type t_from t_to) as [[t1 t2] |];
        [| apply memM_interp_prov_raise_both].
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind with
        (RR := fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2).
      + eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
        intros elts' _ <-; repeat split; reflexivity.
      + intros U1 [σ1' elts1'] [σ2' elts2'] (-> & -> & -> & <-).
        eapply refine_prov_obs_eq;
          [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
        eapply refine_prov_bind; [apply map_monad_convert_impure_base_id_sync |].
        intros U2 [σ1'' vs1] [σ2'' vs2] (-> & -> & -> & <-).
        apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  (** Updating a single ghost slot [gs] in [G] (uniquely identified by [gs_pr]). *)
  Definition gs_set_val (gs : ghost_slot)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) : ghost_slot :=
    {| gs_pt    := gs_pt gs;
       gs_ptrs  := gs_ptrs gs;
       gs_pr    := gs_pr gs;
       gs_dt    := gs_dt gs;
       gs_db    := db';
       gs_bytes := bs' |}.

  Fixpoint update_ghost_slot (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) : list ghost_slot :=
    match G with
    | [] => []
    | gs :: G' =>
        if N.eqb (gs_pr gs) pr then gs_set_val gs db' bs' :: G'
        else gs :: update_ghost_slot G' pr db' bs'
    end.

  Lemma map_gs_pr_update_ghost_slot (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) :
    List.map gs_pr (update_ghost_slot G pr db' bs') = List.map gs_pr G.
  Proof using.
    induction G as [| gs G' IH]; cbn [update_ghost_slot List.map]; [reflexivity |].
    destruct (N.eqb (gs_pr gs) pr); cbn [List.map gs_set_val gs_pr]; [reflexivity | f_equal; exact IH].
  Qed.

  Lemma update_ghost_slot_in_range_iff (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) (z : Z) :
    (exists g', In g' (update_ghost_slot G pr db' bs') /\ gs_in_range g' z) <->
    (exists g, In g G /\ gs_in_range g z).
  Proof using.
    induction G as [| gs G' IH]; cbn [update_ghost_slot In]; [split; intros [? [[] _]] |].
    destruct (N.eqb (gs_pr gs) pr); cbn [In].
    - split.
      + intros [g' [[<- | Hin] Hr]].
        * exists gs; split; [left; reflexivity | exact Hr].
        * exists g'; split; [right; exact Hin | exact Hr].
      + intros [g [[<- | Hin] Hr]].
        * exists (gs_set_val gs db' bs'); split; [left; reflexivity | exact Hr].
        * exists g; split; [right; exact Hin | exact Hr].
    - split.
      + intros [g' [[<- | Hin] Hr]].
        * exists gs; split; [left; reflexivity | exact Hr].
        * destruct (proj1 IH (ex_intro _ g' (conj Hin Hr))) as [g [Hg Hrg]].
          exists g; split; [right; exact Hg | exact Hrg].
      + intros [g [[<- | Hin] Hr]].
        * exists gs; split; [left; reflexivity | exact Hr].
        * destruct (proj2 IH (ex_intro _ g (conj Hin Hr))) as [g' [Hg' Hrg']].
          exists g'; split; [right; exact Hg' | exact Hrg'].
  Qed.

  Lemma ghost_list_disjoint_update (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) :
    ghost_list_disjoint G ->
    ghost_list_disjoint (update_ghost_slot G pr db' bs').
  Proof using.
    induction G as [| gs G' IH]; cbn [update_ghost_slot ghost_list_disjoint]; [tauto |].
    intros [Hhd Htl].
    destruct (N.eqb (gs_pr gs) pr); cbn [ghost_list_disjoint].
    - split; [intros gs' Hin z Hr; apply (Hhd gs' Hin z Hr) | exact Htl].
    - split; [| apply IH, Htl].
      intros g' Hin z Hr Hrg'.
      destruct (proj1 (update_ghost_slot_in_range_iff G' pr db' bs' z)
                  (ex_intro _ g' (conj Hin Hrg'))) as [g [Hg Hrg]].
      exact (Hhd g Hg z Hr Hrg).
  Qed.

  Lemma framestack_ghost_wf_update (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT)))
    (fs : @Framestack (@ParamsV IP IPT)) :
    framestack_ghost_wf G fs ->
    framestack_ghost_wf (update_ghost_slot G pr db' bs') fs.
  Proof using.
    intros Hfgw; induction Hfgw as [fs0 | G0 fs0 f Hsub IH Hout | gs G0 fs0 f Hsub IH Hin Hout].
    - cbn [update_ghost_slot]; apply FGW_Base.
    - apply FGW_Snoc_Unprom; [exact IH |].
      intros z Hz g' Hg' Hrg'.
      destruct (proj1 (update_ghost_slot_in_range_iff G0 pr db' bs' z)
                  (ex_intro _ g' (conj Hg' Hrg'))) as [g [Hg Hrg]].
      exact (Hout z Hz g Hg Hrg).
    - cbn [update_ghost_slot].
      destruct (N.eqb (gs_pr gs) pr).
      + apply FGW_Snoc_Prom; [exact Hsub | exact Hin | exact Hout].
      + apply FGW_Snoc_Prom; [exact IH | exact Hin |].
        intros z Hz g' Hg' Hrg'.
        destruct (proj1 (update_ghost_slot_in_range_iff G0 pr db' bs' z)
                    (ex_intro _ g' (conj Hg' Hrg'))) as [g [Hg Hrg]].
        exact (Hout z Hz g Hg Hrg).
  Qed.

  Lemma in_update_ghost_slot_nodup (G : list ghost_slot) (gs : ghost_slot)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) :
    NoDup (List.map gs_pr G) ->
    In gs G ->
    In (gs_set_val gs db' bs') (update_ghost_slot G (gs_pr gs) db' bs') /\
    (forall g',
       In g' (update_ghost_slot G (gs_pr gs) db' bs') ->
       g' = gs_set_val gs db' bs' \/ (In g' G /\ gs_pr g' <> gs_pr gs)).
  Proof using.
    induction G as [| gs0 G' IH]; intros Hnd Hin; [contradiction |].
    inversion Hnd as [| ? ? Hnin_pr Hnd']; subst.
    cbn [update_ghost_slot].
    destruct Hin as [-> | Hin].
    - rewrite N.eqb_refl; split; [left; reflexivity |].
      intros g' [<- | Hg']; [left; reflexivity | right].
      split; [right; exact Hg' |].
      intros Heq; apply Hnin_pr; rewrite <- Heq; apply in_map, Hg'.
    - assert (Hne : gs_pr gs0 <> gs_pr gs).
      { intros Heq; apply Hnin_pr; rewrite Heq; apply in_map, Hin. }
      destruct (N.eqb_spec (gs_pr gs0) (gs_pr gs)) as [Heq | _]; [contradiction |].
      destruct (IH Hnd' Hin) as [Hin_set Hinv].
      split; [right; exact Hin_set |].
      intros g' [<- | Hg'].
      + right; split; [left; reflexivity | exact Hne].
      + destruct (Hinv g' Hg') as [-> | [Hg0 Hne_g']].
        * left; reflexivity.
        * right; split; [right; exact Hg0 | exact Hne_g'].
  Qed.

  Lemma framestack_ghost_wf_add_ptrs (G : list ghost_slot)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (ms : @Memory_stack (@ParamsV IP IPT)) :
    framestack_ghost_wf G (Memory_stack_frame_stack ms) ->
    (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) ->
    framestack_ghost_wf G (Memory_stack_frame_stack (add_all_to_frame ptrs ms)).
  Proof using.
    destruct ms as [mem fs h]; cbn [Memory_stack_frame_stack].
    intros Hfgw Hdisj.
    inversion Hfgw as [fs0 HeqG Heqfs | G0 fs0 f Hsub Hout HeqG Heqfs | gs G0 fs0 f Hsub Hin Hout HeqG Heqfs]; subst.
    - apply FGW_Base.
    - rewrite add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
      apply FGW_Snoc_Unprom; [exact Hsub |].
      intros z Hz gs Hgs; apply in_map_rev_app_iff in Hz as [Hz | Hz].
      + exact (Hdisj z Hz gs Hgs).
      + exact (Hout z Hz gs Hgs).
    - rewrite add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
      apply FGW_Snoc_Prom; [exact Hsub | |].
      + intros z Hr; apply in_map_rev_app_iff; right; apply Hin, Hr.
      + intros z Hz gs' Hgs'; apply in_map_rev_app_iff in Hz as [Hz | Hz].
        * exact (Hdisj z Hz gs' (or_intror Hgs')).
        * exact (Hout z Hz gs' Hgs').
  Qed.

  Lemma zip_combine_eq {X Y} (xs : list X) (ys : list Y) :
    zip_acc xs ys = List.combine xs ys.
  Proof using.
    rewrite zip_acc_eq.
    revert ys; induction xs as [| x xs' IH]; intros [| y ys'];
      cbn [zip zipWith List.combine]; try reflexivity.
    f_equal; apply IH.
  Qed.

  Lemma add_all_to_frame_fs_eq
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    Memory_stack_frame_stack ms1 = Memory_stack_frame_stack ms2 ->
    Memory_stack_frame_stack (add_all_to_frame ks ms1) =
    Memory_stack_frame_stack (add_all_to_frame ks ms2).
  Proof using.
    destruct ms1 as [m1 fs1 h1], ms2 as [m2 fs2 h2]; cbn [Memory_stack_frame_stack].
    intros ->; destruct fs2 as [f | s f].
    - rewrite !add_all_to_frame_Singleton; reflexivity.
    - rewrite !add_all_to_frame_Snoc; reflexivity.
  Qed.

  Lemma framestack_ghost_wf_unprom_inv (G : list ghost_slot)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f : @Frame (@ParamsV IP IPT)) :
    Forall (fun gs => gs_wf gs) G ->
    framestack_ghost_wf G (Snoc fs0 f) ->
    (forall z, In z (List.map ptr_to_int f) -> forall gs, In gs G -> ~ gs_in_range gs z) ->
    framestack_ghost_wf G fs0.
  Proof using.
    intros Hall Hfgw Hout.
    inversion Hfgw as [fs1 HeqG HeqS | G0 fs1 f1 Hsub _ HeqG HeqS | gs G0 fs1 f1 Hsub Hin _ HeqG HeqS]; subst.
    - apply FGW_Base.
    - exact Hsub.
    - exfalso; inversion Hall as [| ? ? Hwf _]; subst.
      destruct Hwf as (Hsc & _).
      pose proof (scalar_store_size_pos (gs_dt gs) Hsc) as Hpos.
      assert (Hr : gs_in_range gs (gs_addr gs)) by (unfold gs_in_range, gs_len; lia).
      exact (Hout (gs_addr gs) (Hin (gs_addr gs) Hr) gs (or_introl Logic.eq_refl) Hr).
  Qed.

  Lemma framestack_ghost_wf_prom_inv (gs : ghost_slot) (G : list ghost_slot)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f : @Frame (@ParamsV IP IPT)) :
    gs_wf gs ->
    framestack_ghost_wf (gs :: G) (Snoc fs0 f) ->
    (forall z, gs_in_range gs z -> In z (List.map ptr_to_int f)) ->
    framestack_ghost_wf G fs0.
  Proof using.
    intros Hwf Hfgw Hin.
    inversion Hfgw as [| G0 fs1 f1 Hsub Hout HeqG HeqS | gs' G0 fs1 f1 Hsub _ _ HeqG HeqS]; subst.
    - exfalso; destruct Hwf as (Hsc & _).
      pose proof (scalar_store_size_pos (gs_dt gs) Hsc) as Hpos.
      assert (Hr : gs_in_range gs (gs_addr gs)) by (unfold gs_in_range, gs_len; lia).
      exact (Hout (gs_addr gs) (Hin (gs_addr gs) Hr) gs (or_introl Logic.eq_refl) Hr).
    - exact Hsub.
  Qed.

  Definition top_frame_unprom_from
    (fs0 : @Framestack (@ParamsV IP IPT)) (G : list ghost_slot)
    (ms : @Memory_stack (@ParamsV IP IPT)) : Prop :=
    exists f,
      Memory_stack_frame_stack ms = Snoc fs0 f /\
      (forall z, In z (List.map ptr_to_int f) -> forall gs, In gs G -> ~ gs_in_range gs z).

  Definition top_frame_prom_from
    (fs0 : @Framestack (@ParamsV IP IPT)) (gs : ghost_slot) (G : list ghost_slot)
    (ms : @Memory_stack (@ParamsV IP IPT)) : Prop :=
    exists f,
      Memory_stack_frame_stack ms = Snoc fs0 f /\
      (forall z, gs_in_range gs z -> In z (List.map ptr_to_int f)) /\
      (forall z, In z (List.map ptr_to_int f) -> forall gs', In gs' G -> ~ gs_in_range gs' z).

  Lemma top_frame_prom_set_val
    (fs0 : @Framestack (@ParamsV IP IPT)) (gs : ghost_slot) (G : list ghost_slot)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT)))
    (ms : @Memory_stack (@ParamsV IP IPT)) :
    top_frame_prom_from fs0 gs G ms ->
    top_frame_prom_from fs0 (gs_set_val gs db' bs') G ms.
  Proof using.
    intros (f & Hfs & Hin & Hout).
    exists f; split; [exact Hfs | split; [exact Hin | exact Hout]].
  Qed.

  Lemma top_frame_unprom_add_ptrs
    (fs0 : @Framestack (@ParamsV IP IPT)) (G : list ghost_slot)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (ms : @Memory_stack (@ParamsV IP IPT)) :
    top_frame_unprom_from fs0 G ms ->
    (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) ->
    top_frame_unprom_from fs0 G (add_all_to_frame ptrs ms).
  Proof using.
    destruct ms as [mem fs h].
    intros (f & Hfs & Hout) Hdisj; cbn [Memory_stack_frame_stack] in Hfs; subst fs.
    rewrite add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
    exists (rev ptrs ++ f); split; [reflexivity |].
    intros z Hz gs Hgs; apply in_map_rev_app_iff in Hz as [Hz | Hz].
    - exact (Hdisj z Hz gs Hgs).
    - exact (Hout z Hz gs Hgs).
  Qed.

  Lemma top_frame_prom_add_ptrs
    (fs0 : @Framestack (@ParamsV IP IPT)) (gs : ghost_slot) (G : list ghost_slot)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (ms : @Memory_stack (@ParamsV IP IPT)) :
    top_frame_prom_from fs0 gs G ms ->
    (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 (gs :: G) -> ~ gs_in_range gs0 z) ->
    top_frame_prom_from fs0 gs G (add_all_to_frame ptrs ms).
  Proof using.
    destruct ms as [mem fs h].
    intros (f & Hfs & Hin & Hout) Hdisj; cbn [Memory_stack_frame_stack] in Hfs; subst fs.
    rewrite add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
    exists (rev ptrs ++ f); split; [reflexivity | split].
    - intros z Hr; apply in_map_rev_app_iff; right; apply Hin, Hr.
    - intros z Hz gs' Hgs'; apply in_map_rev_app_iff in Hz as [Hz | Hz].
      + exact (Hdisj z Hz gs' (or_intror Hgs')).
      + exact (Hout z Hz gs' Hgs').
  Qed.

  Lemma stage1_mempush (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         top_frame_unprom_from (Memory_stack_frame_stack (state_memory_stack σ2)) G (state_memory_stack σ2'))
      U
      (memM_interp_prov (handle_memoryM MemPush) σ1)
      (memM_interp_prov (handle_memoryM MemPush) σ2).
  Proof using.
    intros (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    cbn [handle_memoryM mempush MemoryModelPrimitivesV].
    unfold Mempush, app_frame_stack, get, put, push_frame_stack, initial_frame;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
    apply refine_prov_ret.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    - split; [exact Hpu |].
      split; [exact Hnd |].
      split; [exact Hall |].
      split; [exact Hdisj |].
      split; [cbn; apply FGW_Snoc_Unprom; [exact Hfgw | intros z []] |].
      split; [cbn; congruence |].
      split; [cbn; exact Hh |].
      split; [cbn; exact Hout | cbn; exact Hgs].
    - exists []; split; [reflexivity | intros z []].
  Qed.

  Lemma stage1_alloca_unprom (dt : dtyp) (num : N) (align : option N)
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         exists pr ptrs,
           ~ In pr U /\
           U' = pr :: U /\
           r1 = r2 /\
           is_safe_ptr_dvalue (pr :: P_unprom) r2 /\
           stage1_mem_inv (pr :: U) (pr :: P_unprom) G σ1' σ2' /\
           (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) /\
           Memory_stack_frame_stack (state_memory_stack σ2') =
             Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack σ2)))
      U
      (memM_interp_prov (handle_memoryM (Alloca dt num align)) σ1)
      (memM_interp_prov (handle_memoryM (Alloca dt num align)) σ2).
  Proof using.
    intros Hinv.
    cbn [handle_memoryM].
    set (al := match align with None => preferred_alignment (dtyp_alignment dt) | Some a => a end).
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    unfold allocate_dtyp.
    destruct (dtyp_eqb dt DTYPE_Void).
    { eapply refine_prov_obs_eq;
        [symmetry; unfold mub; cbn [MemoryModelStateV]; reflexivity | reflexivity |].
      cbn [memM_interp_prov].
      eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity. }
    set (bs := concat_acc (repeatN num (@generate_poison_bytes (@ParamsV IP IPT) dt))).
    unfold allocate_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind; cbn [ExtLib.Structures.Monad.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
       rewrite !Eqit.bind_bind; reflexivity
      | symmetry; rewrite memM_interp_prov_bind; cbn [ExtLib.Structures.Monad.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
        rewrite !Eqit.bind_bind; reflexivity |].
    apply refine_prov_trigger_fresh_both; intros pr Hpr.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
    unfold Allocate_bytes_with_pr, get_free_block, next_key, Mnext_key.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind;
       cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_memory_stack];
       rewrite !Eqit.bind_bind, !Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind;
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_memory_stack];
        rewrite !Eqit.bind_bind, !Eqit.bind_ret_l; reflexivity |].
    rewrite (stage1_mem_next_key_eq U P_unprom G σ1 σ2 al Hinv).
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack σ2)) al).
    set (sz := ListUtil.N.length bs).
    match goal with
    | |- context [allocation_id_to_prov ?aid] =>
        let T := type of (allocation_id_to_prov aid) in
        change (allocation_id_to_prov aid) with (Some [pr] : T)
    end.
    match goal with
    | |- context [@int_to_ptr ?P ?A ?PI ?a ?p] =>
        destruct (@int_to_ptr P A PI a p) as [s | s | s | pt] eqn:Ept
    end;
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - match goal with
      | |- context [get_consecutive_ptrs ?p ?sz] =>
          destruct (get_consecutive_ptrs p sz) as [s | s | s | ptrs] eqn:Eptrs
      end;
        cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
        pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
      + unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l;
           cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV];
           rewrite !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite !Eqit.bind_ret_l;
            cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV];
            rewrite !Eqit.bind_ret_l; reflexivity |].
        apply refine_prov_ret.
        destruct (int_to_ptr_spec addr (Some [pr]) pt Ept) as [Hpt_int Hpt_pr].
        pose proof (stage1_mem_next_key_eq U P_unprom G σ1 σ2 al Hinv) as Hnk_eq.
        assert (Hsz_nat : N.to_nat sz = List.length bs).
        { unfold sz; rewrite N_length_eq, Nat2N.id; reflexivity. }
        assert (Hptrs_disj : forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z).
        { intros z Hz gs Hgs.
          apply (get_consecutive_ptrs_in_addrs pt sz ptrs z Eptrs) in Hz.
          rewrite Hpt_int in Hz.
          eapply (stage1_gs_fresh_above_next_key U P_unprom G σ1 σ2 al z Hinv); [| exact Hgs].
          rewrite Hnk_eq; fold addr; lia. }
        pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
        exists pr, ptrs.
        split; [exact Hpr |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [apply fresh_ptr_safe_dvalue, Hpt_pr |].
        lazymatch goal with
        | |- context [@memory_bytes_to_bytes ?Pa ?aid bs] =>
            set (mbs := @memory_bytes_to_bytes Pa aid bs)
        end.
        assert (Hmbs_len : List.length mbs = List.length bs).
        { unfold mbs; rewrite memory_bytes_to_bytes_eq, length_map; reflexivity. }
        split.
        * split.
          { intros x [<- | Hx]; [left; reflexivity | right; apply Hpu, Hx]. }
          split; [exact Hnd |].
          split.
          { eapply Forall_impl; [| exact Hall].
            intros gs (Hwf & HinU & HninP).
            split; [exact Hwf | split; [right; exact HinU |]].
            intros [Heq | HinP]; [subst pr; exact (Hpr HinU) | exact (HninP HinP)]. }
          split; [exact Hdisj |].
          split.
          { cbn [state_memory_stack].
            apply framestack_ghost_wf_add_ptrs;
              [cbn [Memory_stack_frame_stack]; exact Hfgw | exact Hptrs_disj]. }
          split.
          { cbn [state_memory_stack]; apply add_all_to_frame_fs_eq; cbn; exact Hfs. }
          split.
          { cbn [state_memory_stack].
            assert (Hheap : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                      Memory_stack_heap (add_all_to_frame ks ms) = Memory_stack_heap ms).
            { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
              destruct fss; apply IH. }
            rewrite !Hheap; cbn; exact Hh. }
          assert (Hmem_frame : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                    Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms).
          { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
            destruct fss; apply IH. }
          split.
          { intros z Hz_out; cbn [state_memory_stack]; rewrite !Hmem_frame; cbn [Memory_stack_memory].
            repeat match goal with
                   | |- context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                       progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q))
                   end.
            assert (Hpt_z : @to_Z IP (fst pt) = addr) by exact Hpt_int.
            rewrite ?Hpt_z.
            destruct (Z_le_gt_dec addr z) as [Hlo | Hgt].
            - destruct (Z_lt_ge_dec z (addr + Z.of_nat (List.length mbs))) as [Hhi | Hge].
              + set (k := Z.to_nat (z - addr)).
                assert (Hk : (k < List.length mbs)%nat) by lia.
                destruct (nth_error_Some mbs k) as [_ Hsome].
                destruct (nth_error mbs k) as [v |] eqn:Enth;
                  [| exfalso; apply Hsome; [exact Hk | reflexivity]].
                erewrite !lookup_add_all_index_acc_in; try exact Enth;
                  [reflexivity | unfold k; lia | unfold k; lia].
              + rewrite !lookup_add_all_index_acc_out by lia; apply Hout, Hz_out.
            - rewrite !lookup_add_all_index_acc_out by lia; apply Hout, Hz_out. }
          { intros gs k mb Hin_gs Enth; cbn [state_memory_stack]; rewrite !Hmem_frame; cbn [Memory_stack_memory].
            pose proof Hall as Hall'.
            rewrite Forall_forall in Hall'.
            destruct (Hall' gs Hin_gs) as [(Hsc & _ & _ & _ & Hlen_gs & _) _].
            pose proof (nth_error_Some (gs_bytes gs) k) as [Hsome _].
            assert (Hk : (k < List.length (gs_bytes gs))%nat).
            { apply Hsome; rewrite Enth; discriminate. }
            assert (Hr_z : gs_in_range gs (gs_addr gs + Z.of_nat k)%Z).
            { unfold gs_in_range; lia. }
            assert (Hlt_addr : (gs_addr gs + Z.of_nat k < addr)%Z).
            { destruct (Z_lt_ge_dec (gs_addr gs + Z.of_nat k) addr) as [Hlt | Hge]; [exact Hlt |].
              exfalso; eapply (stage1_gs_fresh_above_next_key U P_unprom G σ1 σ2 al (gs_addr gs + Z.of_nat k)%Z Hinv);
                [rewrite Hnk_eq; fold addr; lia | exact Hin_gs | exact Hr_z]. }
            repeat match goal with
                   | |- context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                       progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q))
                   end.
            assert (Hpt_z : @to_Z IP (fst pt) = addr) by exact Hpt_int.
            rewrite ?Hpt_z.
            rewrite !lookup_add_all_index_acc_out by lia.
            apply (Hgs gs k mb Hin_gs Enth). }
        * split; [exact Hptrs_disj |].
          cbn [state_memory_stack]; apply add_all_to_frame_fs_eq; reflexivity.
  Qed.

  Lemma stage1_alloca_prom (dt : dtyp) (align : option N)
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    is_scalar_dtyp dt = true ->
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    top_frame_unprom_from fs0 G (state_memory_stack σ2) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         exists gs0,
           ~ In (gs_pr gs0) U /\
           U' = gs_pr gs0 :: U /\
           gs_dt gs0 = dt /\
           gs_db gs0 = DVALUE_Poison /\
           r1 = DVALUE_Base (DVALUE_Pointer (gs_pt gs0)) /\
           r2 = DVALUE_Base (DVALUE_Pointer (gs_pt gs0)) /\
           stage1_mem_inv (gs_pr gs0 :: U) P_unprom (gs0 :: G) σ1' σ2' /\
           top_frame_prom_from fs0 gs0 G (state_memory_stack σ2'))
      U
      (memM_interp_prov (handle_memoryM (Alloca dt 1%N align)) σ1)
      (memM_interp_prov (handle_memoryM (Alloca dt 1%N align)) σ2).
  Proof using.
    intros Hsc Hinv Htop.
    cbn [handle_memoryM].
    set (al := match align with None => preferred_alignment (dtyp_alignment dt) | Some a => a end).
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    unfold allocate_dtyp.
    rewrite (scalar_dtyp_not_void dt Hsc).
    set (bs := concat_acc (repeatN 1%N (@generate_poison_bytes (@ParamsV IP IPT) dt))).
    unfold allocate_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind; cbn [ExtLib.Structures.Monad.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
       rewrite !Eqit.bind_bind; reflexivity
      | symmetry; rewrite memM_interp_prov_bind; cbn [ExtLib.Structures.Monad.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
        rewrite !Eqit.bind_bind; reflexivity |].
    apply refine_prov_trigger_fresh_both; intros pr Hpr.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
    unfold Allocate_bytes_with_pr, get_free_block, next_key, Mnext_key.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind;
       cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_memory_stack];
       rewrite !Eqit.bind_bind, !Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind;
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_memory_stack];
        rewrite !Eqit.bind_bind, !Eqit.bind_ret_l; reflexivity |].
    rewrite (stage1_mem_next_key_eq U P_unprom G σ1 σ2 al Hinv).
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack σ2)) al).
    set (sz := ListUtil.N.length bs).
    match goal with
    | |- context [allocation_id_to_prov ?aid] =>
        let T := type of (allocation_id_to_prov aid) in
        change (allocation_id_to_prov aid) with (Some [pr] : T)
    end.
    match goal with
    | |- context [@int_to_ptr ?P ?A ?PI ?a ?p] =>
        destruct (@int_to_ptr P A PI a p) as [s | s | s | pt] eqn:Ept
    end;
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - match goal with
      | |- context [get_consecutive_ptrs ?p ?sz] =>
          destruct (get_consecutive_ptrs p sz) as [s | s | s | ptrs] eqn:Eptrs
      end;
        cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
        pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
      + unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l;
           cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV];
           rewrite !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite !Eqit.bind_ret_l;
            cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV];
            rewrite !Eqit.bind_ret_l; reflexivity |].
        apply refine_prov_ret.
        destruct (int_to_ptr_spec addr (Some [pr]) pt Ept) as [Hpt_int Hpt_pr].
        pose proof (stage1_mem_next_key_eq U P_unprom G σ1 σ2 al Hinv) as Hnk_eq.
        assert (Hbs_eq : bs = List.repeat (@poison_memory_byte (@ParamsV IP IPT))
                                (N.to_nat (@store_size_dtyp SizeofV dt))).
        { unfold bs; apply alloc_poison_bytes_eq. }
        assert (Hbs_len : List.length bs = N.to_nat (@store_size_dtyp SizeofV dt)).
        { rewrite Hbs_eq, repeat_length; reflexivity. }
        assert (Hsz_eq : sz = @store_size_dtyp SizeofV dt).
        { unfold sz; rewrite N_length_eq, Hbs_len, N2Nat.id; reflexivity. }
        destruct (is_scalar_dtyp_inv dt Hsc) as (dtb & Hdt_eq & _).
        set (gs0 := {| gs_pt := pt;
                       gs_ptrs := ptrs;
                       gs_pr := pr;
                       gs_dt := dt;
                       gs_db := DVALUE_Poison;
                       gs_bytes := bs |}).
        assert (Hwf0 : gs_wf gs0).
        { unfold gs0; repeat split; cbn [gs_pt gs_ptrs gs_pr gs_dt gs_db gs_bytes].
          - exact Hsc.
          - exact Hpt_pr.
          - rewrite <- Hsz_eq; exact Eptrs.
          - rewrite Hdt_eq, dvalue_to_memory_bytes_poison_base, <- Hdt_eq, <- Hbs_eq; reflexivity.
          - unfold gs_len; cbn [gs_dt]; exact Hbs_len.
          - unfold gs_addr; cbn [gs_pt]; rewrite Hpt_int; unfold addr; apply next_key_with_alignment_pos. }
        pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
        destruct Htop as (f & Hfs_top & Hout_f).
        assert (Hfgw_fs0 : framestack_ghost_wf G fs0).
        { eapply (framestack_ghost_wf_unprom_inv G fs0 f);
            [eapply Forall_impl; [| exact Hall]; intros g [Hw _]; exact Hw
            | rewrite <- Hfs_top; exact Hfgw
            | exact Hout_f]. }
        assert (Hptrs_in : forall z, In z (List.map ptr_to_int ptrs) <-> gs_in_range gs0 z).
        { intros z; rewrite (get_consecutive_ptrs_in_addrs pt sz ptrs z Eptrs).
          unfold gs_in_range, gs_addr, gs_len, gs0; cbn [gs_pt gs_dt]; rewrite Hsz_eq; reflexivity. }
        assert (Hgs0_disj : forall gs', In gs' G -> gs_disjoint gs0 gs').
        { intros gs' Hgs' z Hr0.
          unfold gs_in_range, gs_addr, gs0 in Hr0; cbn [gs_pt] in Hr0; rewrite Hpt_int in Hr0.
          eapply (stage1_gs_fresh_above_next_key U P_unprom G σ1 σ2 al z Hinv); [| exact Hgs'].
          rewrite Hnk_eq; fold addr; lia. }
        lazymatch goal with
        | |- context [@memory_bytes_to_bytes ?Pa ?aid bs] =>
            set (mbs := @memory_bytes_to_bytes Pa aid bs)
        end.
        assert (Hmbs_len : List.length mbs = List.length bs).
        { unfold mbs; rewrite memory_bytes_to_bytes_eq, length_map; reflexivity. }
        assert (Hmem_frame : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                  Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms).
        { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
          destruct fss; apply IH. }
        exists gs0; cbn [gs_pr gs_dt gs_db gs_pt].
        split; [exact Hpr |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split.
        * split; [intros x Hx; right; apply Hpu, Hx |].
          split.
          { cbn [List.map]; constructor; [| exact Hnd].
            intros Hin_map; apply in_map_iff in Hin_map as (gs' & Heq_pr & Hin_gs').
            rewrite Forall_forall in Hall.
            destruct (Hall gs' Hin_gs') as (_ & HinU & _).
            rewrite Heq_pr in HinU; exact (Hpr HinU). }
          split.
          { constructor.
            - split; [exact Hwf0 | split; [left; reflexivity | intros Hp; exact (Hpr (Hpu pr Hp))]].
            - eapply Forall_impl; [| exact Hall].
              intros gs' (Hw & Hu & Hnp); exact (conj Hw (conj (or_intror Hu) Hnp)). }
          split; [split; [exact Hgs0_disj | exact Hdisj] |].
          split.
          { cbn [state_memory_stack]; rewrite Hfs_top, add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
            apply FGW_Snoc_Prom; [exact Hfgw_fs0 | |].
            - intros z Hr; apply in_map_rev_app_iff; left; apply Hptrs_in, Hr.
            - intros z Hz gs' Hgs'; apply in_map_rev_app_iff in Hz as [Hz | Hz].
              + apply Hptrs_in in Hz; exact (Hgs0_disj gs' Hgs' z Hz).
              + exact (Hout_f z Hz gs' Hgs'). }
          split.
          { cbn [state_memory_stack]; apply add_all_to_frame_fs_eq; cbn; exact Hfs. }
          split.
          { cbn [state_memory_stack].
            assert (Hheap : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                      Memory_stack_heap (add_all_to_frame ks ms) = Memory_stack_heap ms).
            { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
              destruct fss; apply IH. }
            rewrite !Hheap; cbn; exact Hh. }
          split.
          { intros z Hz_out; cbn [state_memory_stack]; rewrite !Hmem_frame; cbn [Memory_stack_memory].
            assert (Hout0 : ~ gs_in_range gs0 z) by (apply Hz_out; left; reflexivity).
            unfold gs_in_range, gs_addr, gs_len, gs0 in Hout0; cbn [gs_pt gs_dt] in Hout0.
            repeat match goal with
                   | |- context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                       progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q))
                   end.
            repeat match type of Hout0 with
                   | context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                       progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q)) in Hout0
                   end.
            rewrite !lookup_add_all_index_acc_out;
              [apply Hout; intros gs' Hgs'; apply Hz_out; right; exact Hgs'
              | rewrite Hmbs_len, Hbs_len; lia
              | rewrite Hmbs_len, Hbs_len; lia]. }
          { intros gs' k mb [<- | Hin_gs'] Enth;
              cbn [state_memory_stack]; rewrite !Hmem_frame; cbn [Memory_stack_memory].
            - unfold gs0 in Enth; cbn [gs_bytes] in Enth.
              pose proof (nth_error_In bs k Enth) as Hin_bs.
              rewrite Hbs_eq in Hin_bs; apply repeat_spec in Hin_bs; subst mb.
              assert (Enth_mbs : nth_error mbs k = Some (poison_memory_byte, Some pr)).
              { unfold mbs; cbn [PROV ParamsV ProvenanceV]; rewrite memory_bytes_to_bytes_eq, nth_error_map, Enth; reflexivity. }
              split; eapply lookup_add_all_index_acc_in; try exact Enth_mbs; reflexivity.
            - pose proof Hall as Hall'; rewrite Forall_forall in Hall'.
              destruct (Hall' gs' Hin_gs') as [(_ & _ & _ & _ & Hlen_gs' & _) _].
              pose proof (nth_error_Some (gs_bytes gs') k) as [Hsome _].
              assert (Hk : (k < List.length (gs_bytes gs'))%nat) by (apply Hsome; rewrite Enth; discriminate).
              assert (Hr_gs' : gs_in_range gs' (gs_addr gs' + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
              assert (Hn0 : ~ gs_in_range gs0 (gs_addr gs' + Z.of_nat k)%Z).
              { intros Hr0; exact (Hgs0_disj gs' Hin_gs' _ Hr0 Hr_gs'). }
              unfold gs_in_range, gs_addr, gs_len, gs0 in Hn0; cbn [gs_pt gs_dt] in Hn0.
              unfold gs_addr.
              repeat match goal with
                     | |- context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                         progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q))
                     end.
              repeat match type of Hn0 with
                     | context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                         progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q)) in Hn0
                     end.
              rewrite !lookup_add_all_index_acc_out;
                [apply (Hgs gs' k mb Hin_gs' Enth)
                | rewrite Hmbs_len, Hbs_len; lia
                | rewrite Hmbs_len, Hbs_len; lia]. }
        * cbn [state_memory_stack]; rewrite Hfs_top, add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
          exists (rev ptrs ++ f); split; [reflexivity | split].
          -- intros z Hr; apply in_map_rev_app_iff; left; apply Hptrs_in, Hr.
          -- intros z Hz gs' Hgs'; apply in_map_rev_app_iff in Hz as [Hz | Hz].
             ++ apply Hptrs_in in Hz; exact (Hgs0_disj gs' Hgs' z Hz).
             ++ exact (Hout_f z Hz gs' Hgs').
  Qed.

  Lemma Read_byte_hit_eq (q : @ptr ProvenanceV (@PointerV IP))
    (mb : @memory_byte (@ParamsV IP IPT)) (pr : N) (σ : state)
    (Hpr : ptr_provenance q = Some [pr])
    (Hlk : IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ)) = Some (mb, Some pr)) :
    memM_interp_prov (Read_byte q) σ ≅ Ret (σ, mb).
  Proof using.
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    rewrite memM_interp_prov_bind.
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ))).
    cbn [PROV PTR ParamsV]; rewrite Hlk; cbn [memM_interp_prov]; rewrite Eqit.bind_ret_l, Hpr.
    cbn [access_allowed ProvenanceV existsb]; rewrite N.eqb_refl; cbn; reflexivity.
  Qed.

  Lemma map_monad_Read_gs_bytes_eq
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (bs : list (@memory_byte (@ParamsV IP IPT)))
    (base : Z) (j : nat) (pr : N) (σ : state)
    (Hlen : List.length ptrs = List.length bs)
    (Hptrs : forall i q,
               nth_error ptrs i = Some q ->
               ptr_to_int q = (base + Z.of_nat (j + i))%Z /\
               ptr_provenance q = Some [pr])
    (Hmem : forall i mb,
              nth_error bs i = Some mb ->
              IntMaps.lookup (base + Z.of_nat (j + i))%Z (Memory_stack_memory (state_memory_stack σ)) =
                Some (mb, Some pr)) :
    memM_interp_prov (map_monad Read_byte ptrs) σ ≅ Ret (σ, bs).
  Proof using.
    revert bs j Hlen Hptrs Hmem; induction ptrs as [| q ptrs' IH]; intros [| mb bs'] j Hlen Hptrs Hmem;
      cbn [List.length map_monad] in *; try lia.
    - reflexivity.
    - destruct (Hptrs 0%nat q Logic.eq_refl) as [Hq_int Hq_pr].
      pose proof (Hmem 0%nat mb Logic.eq_refl) as Hlk0.
      replace (j + 0)%nat with j in Hq_int, Hlk0 by lia.
      rewrite <- Hq_int in Hlk0.
      rewrite memM_interp_prov_bind, (Read_byte_hit_eq q mb pr σ Hq_pr Hlk0), Eqit.bind_ret_l.
      rewrite memM_interp_prov_bind.
      rewrite (IH bs' (S j) ltac:(lia)); [rewrite Eqit.bind_ret_l; reflexivity | |].
      + intros i q' Hnth; destruct (Hptrs (S i) q' Hnth) as [Hi Hpr']; split; [lia | exact Hpr'].
      + intros i mb' Hnth; pose proof (Hmem (S i) mb' Hnth) as Hlk';
          replace (j + S i)%nat with (S j + i)%nat in Hlk' by lia; exact Hlk'.
  Qed.

  Lemma stage1_load_prom (U P_unprom : list N) (G : list ghost_slot)
    (gs : ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    In gs G ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (handle_memoryM (Load (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))) σ1)
      (memM_interp_prov (Interfaces.Memory.lift (memory_bytes_to_dvalue (gs_bytes gs) (gs_dt gs))) σ2).
  Proof using.
    intros Hinv Hin.
    pose proof Hinv as (_ & _ & Hall & _ & _ & _ & _ & _ & Hgs).
    rewrite Forall_forall in Hall.
    destruct (Hall gs Hin) as [(_ & Hpr & Eptrs & _ & Hlen_bs & _) _].
    destruct (get_consecutive_ptrs_spec (gs_pt gs) (@store_size_dtyp SizeofV (gs_dt gs)) (gs_ptrs gs) Eptrs)
      as (Hlen_ptrs & Hinv_ptrs & _).
    cbn [handle_memoryM]; unfold read_dvalue, read_bytes.
    eapply refine_prov_obs_eq.
    - symmetry.
      rewrite memM_interp_prov_bind, memM_interp_prov_bind; cbn [SIZE ParamsV]; rewrite Eptrs.
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov read_byte MemoryModelPrimitivesV].
      rewrite Eqit.bind_ret_l, memM_interp_prov_map_monad_acc.
      rewrite (map_monad_Read_gs_bytes_eq (gs_ptrs gs) (gs_bytes gs) (gs_addr gs) 0%nat (gs_pr gs) σ1).
      + rewrite Eqit.bind_ret_l; reflexivity.
      + unfold gs_len in Hlen_bs; lia.
      + intros i q Hnth; destruct (Hinv_ptrs i q Hnth) as (_ & Hqi & Hqpr).
        rewrite Hpr in Hqpr; unfold gs_addr; split; [lia | exact Hqpr].
      + intros i mb Hnth; destruct (Hgs gs i mb Hin Hnth) as [Hlk1 _]; exact Hlk1.
    - reflexivity.
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros dv _ <-; repeat split; reflexivity.
  Qed.

  Lemma Write_byte_hit_eq (q : @ptr ProvenanceV (@PointerV IP))
    (mb0 mb : @memory_byte (@ParamsV IP IPT)) (pr : N) (σ : state)
    (Hpr : ptr_provenance q = Some [pr])
    (Hlk : IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ)) = Some (mb0, Some pr)) :
    memM_interp_prov (Write_byte q mb) σ ≅
    Ret ({| state_memory_stack :=
              {| Memory_stack_memory :=
                   IntMaps.add (ptr_to_int q) (mb, Some pr) (Memory_stack_memory (state_memory_stack σ));
                 Memory_stack_frame_stack := Memory_stack_frame_stack (state_memory_stack σ);
                 Memory_stack_heap := Memory_stack_heap (state_memory_stack σ) |};
            state_provenance := state_provenance σ |}, tt).
  Proof using.
    unfold Write_byte, read_byte_raw, read_byte_raw_mem.
    rewrite memM_interp_prov_bind.
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ))).
    cbn [PROV PTR ParamsV]; rewrite Hlk; cbn [memM_interp_prov]; rewrite Eqit.bind_ret_l, Hpr.
    cbn [access_allowed ProvenanceV existsb]; rewrite N.eqb_refl; cbn [orb].
    unfold set_byte_raw, get_mem, upd_mem, app_mem, set_byte_raw_mem, get, put;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    reflexivity.
  Qed.

  Lemma loop_Write_gs_bytes_spec
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (bs : list (@memory_byte (@ParamsV IP IPT)))
    (base : Z) (j : nat) (pr : N) (σ : state)
    (Hlen : List.length ptrs = List.length bs)
    (Hptrs : forall i q,
               nth_error ptrs i = Some q ->
               ptr_to_int q = (base + Z.of_nat (j + i))%Z /\
               ptr_provenance q = Some [pr])
    (Hmem : forall i,
              (i < List.length bs)%nat ->
              exists mb0,
                IntMaps.lookup (base + Z.of_nat (j + i))%Z (Memory_stack_memory (state_memory_stack σ)) =
                  Some (mb0, Some pr)) :
    exists σ',
      memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) (List.combine ptrs bs)) σ ≅
        Ret (σ', tt) /\
      Memory_stack_frame_stack (state_memory_stack σ') = Memory_stack_frame_stack (state_memory_stack σ) /\
      Memory_stack_heap (state_memory_stack σ') = Memory_stack_heap (state_memory_stack σ) /\
      (forall i mb,
         nth_error bs i = Some mb ->
         IntMaps.lookup (base + Z.of_nat (j + i))%Z (Memory_stack_memory (state_memory_stack σ')) =
           Some (mb, Some pr)) /\
      (forall z,
         ~ (base + Z.of_nat j <= z < base + Z.of_nat (j + List.length bs))%Z ->
         IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ')) =
         IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ))).
  Proof using.
    revert bs j σ Hlen Hptrs Hmem;
      induction ptrs as [| q ptrs' IH];
      intros [| mb bs'] j σ Hlen Hptrs Hmem;
      cbn [List.length List.combine loop_monad] in *; try lia.
    - exists σ; repeat (match goal with |- _ /\ _ => split end); try reflexivity.
      intros [| i] mb Hnth; discriminate Hnth.
    - destruct (Hptrs 0%nat q Logic.eq_refl) as [Hq_int Hq_pr].
      destruct (Hmem 0%nat ltac:(lia)) as [mb0 Hlk0].
      replace (j + 0)%nat with j in Hq_int, Hlk0 by lia.
      rewrite <- Hq_int in Hlk0.
      set (σ_mid := {| state_memory_stack :=
                         {| Memory_stack_memory :=
                              IntMaps.add (ptr_to_int q) (mb, Some pr) (Memory_stack_memory (state_memory_stack σ));
                            Memory_stack_frame_stack := Memory_stack_frame_stack (state_memory_stack σ);
                            Memory_stack_heap := Memory_stack_heap (state_memory_stack σ) |};
                       state_provenance := state_provenance σ |}).
      assert (Hptrs' : forall i q',
                 nth_error ptrs' i = Some q' ->
                 ptr_to_int q' = (base + Z.of_nat (S j + i))%Z /\
                 ptr_provenance q' = Some [pr]).
      { intros i q' Hnth; destruct (Hptrs (S i) q' Hnth) as [Hi Hpr']; split; [lia | exact Hpr']. }
      assert (Hmem' : forall i,
                 (i < List.length bs')%nat ->
                 exists mb1,
                   IntMaps.lookup (base + Z.of_nat (S j + i))%Z (Memory_stack_memory (state_memory_stack σ_mid)) =
                     Some (mb1, Some pr)).
      { intros i Hi; cbn [state_memory_stack Memory_stack_memory σ_mid].
        rewrite IntMaps.lookup_add_ineq by lia.
        destruct (Hmem (S i) ltac:(lia)) as [mb1 Hlk1].
        replace (j + S i)%nat with (S j + i)%nat in Hlk1 by lia; exists mb1; exact Hlk1. }
      destruct (IH bs' (S j) σ_mid ltac:(lia) Hptrs' Hmem')
        as (σ' & Heq_tl & Hfs' & Hh' & Hin' & Hout').
      exists σ'; split.
      + rewrite memM_interp_prov_bind, (Write_byte_hit_eq q mb0 mb pr σ Hq_pr Hlk0), Eqit.bind_ret_l.
        exact Heq_tl.
      + split; [exact Hfs' | split; [exact Hh' | split]].
        * intros [| i] mb1 Hnth; cbn [nth_error] in Hnth.
          -- inversion Hnth; subst mb1.
             replace (j + 0)%nat with j by lia.
             rewrite (Hout' (base + Z.of_nat j)%Z ltac:(lia)).
             cbn [state_memory_stack Memory_stack_memory σ_mid].
             rewrite Hq_int; apply IntMaps.lookup_add_eq.
          -- replace (j + S i)%nat with (S j + i)%nat by lia.
             apply (Hin' i mb1 Hnth).
        * intros z Hz.
          rewrite (Hout' z ltac:(lia)).
          cbn [state_memory_stack Memory_stack_memory σ_mid].
          apply IntMaps.lookup_add_ineq; lia.
  Qed.

  Lemma stage1_store_prom_base (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (fs0 : @Framestack (@ParamsV IP IPT))
    (db' : @dvalue_base (@ParamsV IP IPT)) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom (gs :: G) σ1 σ2 ->
    top_frame_prom_from fs0 gs G (state_memory_stack σ2) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         exists bs',
           U' = U /\ r1 = tt /\ r2 = tt /\
           dvalue_to_memory_bytes (gs_dt gs) (DVALUE_Base db') None = raise_ret bs' /\
           stage1_mem_inv U P_unprom (gs_set_val gs db' bs' :: G) σ1' σ2 /\
           top_frame_prom_from fs0 (gs_set_val gs db' bs') G (state_memory_stack σ2))
      U
      (memM_interp_prov (handle_memoryM (Store (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) (DVALUE_Base db'))) σ1)
      (Ret (σ2, tt)).
  Proof using.
    intros Hinv Htop.
    pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    inversion Hall as [| ? ? (Hwf & HinU & HninP) Hall_tl]; subst.
    destruct Hwf as (Hsc & Hpr & Eptrs & _ & Hlen_old & Hpos_addr).
    destruct (is_scalar_dtyp_inv (gs_dt gs) Hsc) as (dtb & Hdt_eq & _).
    destruct (dvalue_to_memory_bytes_base_ok dtb db') as (bs' & Hser & Hlen_bs').
    rewrite <- Hdt_eq in Hser, Hlen_bs'.
    destruct (get_consecutive_ptrs_spec (gs_pt gs) (@store_size_dtyp SizeofV (gs_dt gs)) (gs_ptrs gs) Eptrs)
      as (Hlen_ptrs & Hinv_ptrs & _).
    assert (Hsz_bs' : ListUtil.N.length bs' = @store_size_dtyp SizeofV (gs_dt gs)).
    { rewrite N_length_eq, Hlen_bs', N2Nat.id; reflexivity. }
    assert (Hmem_pre : forall i,
               (i < List.length bs')%nat ->
               exists mb0,
                 IntMaps.lookup (gs_addr gs + Z.of_nat (0 + i))%Z (Memory_stack_memory (state_memory_stack σ1)) =
                   Some (mb0, Some (gs_pr gs))).
    { intros i Hi.
      assert (Hi_old : (i < List.length (gs_bytes gs))%nat) by (unfold gs_len in Hlen_old; lia).
      destruct (nth_error_Some (gs_bytes gs) i) as [_ Hsome].
      destruct (nth_error (gs_bytes gs) i) as [mb0 |] eqn:Enth0;
        [| exfalso; apply Hsome; [exact Hi_old | reflexivity]].
      destruct (Hgs gs i mb0 (or_introl Logic.eq_refl) Enth0) as [Hlk1 _].
      exists mb0; exact Hlk1. }
    assert (Hptrs_gs : forall i q,
               nth_error (gs_ptrs gs) i = Some q ->
               ptr_to_int q = (gs_addr gs + Z.of_nat (0 + i))%Z /\
               ptr_provenance q = Some [gs_pr gs]).
    { intros i q Hnth; destruct (Hinv_ptrs i q Hnth) as (_ & Hqi & Hqp).
      unfold gs_addr; cbn [P2I ptr_to_int ptr_provenance PointerV PTR ParamsV PROV] in Hqi, Hqp, Hpr |- *.
      split; [rewrite Hqi; lia | rewrite Hqp, Hpr; reflexivity]. }
    destruct (loop_Write_gs_bytes_spec (gs_ptrs gs) bs' (gs_addr gs) 0%nat (gs_pr gs) σ1
                ltac:(lia) Hptrs_gs Hmem_pre)
      as (σ1' & Hloop_eq & Hfs' & Hh' & Hin' & Hout').
    cbn [handle_memoryM]; unfold write_dvalue, write_bytes.
    eapply refine_prov_obs_eq.
    - symmetry.
      rewrite memM_interp_prov_bind, Hser; cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
      rewrite Eqit.bind_ret_l, memM_interp_prov_bind, Hsz_bs', Eptrs.
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov write_byte MemoryModelPrimitivesV].
      rewrite Eqit.bind_ret_l, zip_combine_eq, Hloop_eq; reflexivity.
    - reflexivity.
    - apply refine_prov_ret.
      exists bs'; split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hser |]]]].
      destruct Hdisj as [Hdisj_hd Hdisj_tl].
      split; [| apply top_frame_prom_set_val, Htop].
      split; [exact Hpu |].
      split; [exact Hnd |].
      split.
      + constructor.
        * split; [| exact (conj HinU HninP)].
          repeat split; cbn [gs_set_val gs_dt gs_pt gs_pr gs_ptrs gs_db gs_bytes];
            try assumption; unfold gs_len; cbn [gs_dt]; exact Hlen_bs'.
        * exact Hall_tl.
      + split; [exact (conj Hdisj_hd Hdisj_tl) |].
        split.
        * pose proof (framestack_ghost_wf_update (gs :: G) (gs_pr gs) db' bs' _ Hfgw) as Hfgw'.
          cbn [update_ghost_slot] in Hfgw'; rewrite N.eqb_refl in Hfgw'.
          cbn [update_ghost_slot]; try rewrite N.eqb_refl; exact Hfgw'.
        * split; [congruence | split; [congruence | split]].
          -- intros z Hz_out.
             assert (Hn0 : ~ gs_in_range gs z).
             { intros Hr; exact (Hz_out (gs_set_val gs db' bs') (or_introl Logic.eq_refl) Hr). }
             unfold gs_in_range, gs_len in Hn0.
             rewrite (Hout' z ltac:(lia)).
             apply Hout; intros g0 [<- | Hg0];
               [exact Hn0 | apply Hz_out; right; exact Hg0].
          -- intros g0 k mb [<- | Hg0] Enth.
             ++ cbn [gs_set_val gs_bytes gs_pr] in *.
                split; [exact (Hin' k mb Enth) |].
                pose proof (nth_error_Some bs' k) as [Hsome _].
                assert (Hk : (k < List.length bs')%nat) by (apply Hsome; rewrite Enth; discriminate).
                assert (Hk_old : (k < List.length (gs_bytes gs))%nat) by (unfold gs_len in Hlen_old; lia).
                destruct (nth_error_Some (gs_bytes gs) k) as [_ Hsome_old].
                destruct (nth_error (gs_bytes gs) k) as [mb_old |] eqn:Enth_old;
                  [| exfalso; apply Hsome_old; [exact Hk_old | reflexivity]].
                destruct (Hgs gs k mb_old (or_introl Logic.eq_refl) Enth_old) as [_ Hlk2].
                exact Hlk2.
             ++ pose proof Hall_tl as Hall_tl'; rewrite Forall_forall in Hall_tl'.
                destruct (Hall_tl' g0 Hg0) as [(_ & _ & _ & _ & Hlen_g0 & _) _].
                pose proof (nth_error_Some (gs_bytes g0) k) as [Hsome _].
                assert (Hk : (k < List.length (gs_bytes g0))%nat) by (apply Hsome; rewrite Enth; discriminate).
                assert (Hr_g0 : gs_in_range g0 (gs_addr g0 + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
                assert (Hn0 : ~ gs_in_range gs (gs_addr g0 + Z.of_nat k)%Z).
                { intros Hr0; exact (Hdisj_hd g0 Hg0 _ Hr0 Hr_g0). }
                unfold gs_in_range, gs_len in Hn0.
                rewrite (Hout' (gs_addr g0 + Z.of_nat k)%Z ltac:(lia)).
                exact (Hgs g0 k mb (or_intror Hg0) Enth).
  Qed.

  Lemma stage1_store_prom_err {R2}
    (RR : list N -> (state * unit) -> (state * R2) -> Prop)
    (U : list N) (gs : ghost_slot) (v : @dvalue (@ParamsV IP IPT))
    (msg2 : string) (σ1 σ2 : state) :
    is_scalar_dtyp (gs_dt gs) = true ->
    (forall db, v <> DVALUE_Base db) ->
    refine_prov RR U
      (memM_interp_prov (handle_memoryM (Store (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) v)) σ1)
      (memM_interp_prov (Merr msg2) σ2).
  Proof using.
    intros Hsc Hnot_base.
    destruct (is_scalar_dtyp_inv (gs_dt gs) Hsc) as (dtb & Hdt_eq & _).
    destruct (dvalue_to_memory_bytes_base_err dtb v Hnot_base) as [msg1 Hser].
    cbn [handle_memoryM]; unfold write_dvalue.
    rewrite Hdt_eq, Hser; cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind].
    apply memM_interp_prov_raise_both.
  Qed.

  Lemma stage1_Read_byte_unprom (q : @ptr ProvenanceV (@PointerV IP))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    safe_prov P_unprom (ptr_provenance q) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (Read_byte q) σ1)
      (memM_interp_prov (Read_byte q) σ2).
  Proof using.
    intros Hinv Hsafe.
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage1_find_gs_at G (ptr_to_int q)) as [[gs [Hin Hr]] | Hout_z].
    - destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs (ptr_to_int q) Hinv Hin Hr)
        as (mb & _ & Hlk1 & _).
      pose proof Hinv as (_ & _ & Hall & _).
      rewrite Forall_forall in Hall.
      destruct (Hall gs Hin) as (_ & _ & HninP).
      rewrite Hlk1.
      eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
      cbn [PROV PTR ParamsV];
      rewrite (safe_prov_access_disjoint P_unprom (ptr_provenance q) (gs_pr gs) Hsafe HninP).
      apply memM_interp_prov_raiseUB_l.
    - pose proof Hinv as (_ & _ & _ & _ & _ & _ & _ & Hout & _).
      rewrite (Hout (ptr_to_int q) Hout_z).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        cbv iota.
        match goal with |- context [if ?c then _ else _] => destruct c end.
        * cbn [memM_interp_prov]; apply refine_prov_ret; repeat split; reflexivity.
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage1_map_monad_Read_byte_unprom
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    Forall (fun q => safe_prov P_unprom (ptr_provenance q)) ptrs ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (map_monad Read_byte ptrs) σ1)
      (memM_interp_prov (map_monad Read_byte ptrs) σ2).
  Proof using.
    intros Hinv Hall; induction Hall as [| q ptrs' Hq _ IH]; cbn [map_monad].
    - apply refine_prov_ret; repeat split; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply (stage1_Read_byte_unprom q U P_unprom G σ1 σ2 Hinv Hq) |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & -> & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [exact IH |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (-> & -> & -> & <-).
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma stage1_load_unprom (dt : dtyp) (a : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    is_safe_ptr_dvalue P_unprom a ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (handle_memoryM (Load dt a)) σ1)
      (memM_interp_prov (handle_memoryM (Load dt a)) σ2).
  Proof using.
    intros Hinv Ha; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |]; cbv beta iota;
      lazymatch goal with
      | |- refine_prov _ _ (memM_interp_prov (Mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | |- refine_prov _ _ (memM_interp_prov (mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | _ => idtac
      end.
    pose proof (Ha pt Logic.eq_refl) as Hsafe.
    unfold read_dvalue, read_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind; reflexivity |].
    cbn [SIZE ParamsV].
    match goal with
    | |- context [get_consecutive_ptrs ?p ?s] =>
        destruct (get_consecutive_ptrs p s) as [s0 | s0 | s0 | ptrs] eqn:Eptrs
    end;
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
         rewrite memM_interp_prov_map_monad_acc; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
          rewrite memM_interp_prov_map_monad_acc; reflexivity |].
      assert (Hall_safe : Forall (fun q => safe_prov P_unprom (ptr_provenance q)) ptrs).
      { destruct (get_consecutive_ptrs_spec pt (@store_size_dtyp SizeofV dt) ptrs Eptrs) as (_ & Hinv_p & _).
        rewrite Forall_forall; intros q Hin_q.
        apply In_nth_error in Hin_q as [k Hnth].
        destruct (Hinv_p k q Hnth) as (_ & _ & Hpr_q);
          cbn [PROV PTR ParamsV ptr_provenance PointerV] in Hpr_q, Hsafe |- *;
          rewrite Hpr_q; exact Hsafe. }
      eapply refine_prov_bind;
        [apply (stage1_map_monad_Read_byte_unprom ptrs U P_unprom G σ1 σ2 Hinv Hall_safe) |].
      intros U1 [σ1' bs1] [σ2' bs2] (-> & -> & -> & <-).
      eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros dv _ <-; repeat split; reflexivity.
  Qed.

  Lemma stage1_Write_byte_unprom
    (q : @ptr ProvenanceV (@PointerV IP)) (mb : @memory_byte (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    safe_prov P_unprom (ptr_provenance q) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') =
           Memory_stack_frame_stack (state_memory_stack σ2))
      U
      (memM_interp_prov (Write_byte q mb) σ1)
      (memM_interp_prov (Write_byte q mb) σ2).
  Proof using.
    intros Hinv Hsafe.
    unfold Write_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage1_find_gs_at G (ptr_to_int q)) as [[gs [Hin Hr]] | Hout_z].
    - destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs (ptr_to_int q) Hinv Hin Hr)
        as (mb0 & _ & Hlk1 & _).
      pose proof Hinv as (_ & _ & Hall & _).
      rewrite Forall_forall in Hall.
      destruct (Hall gs Hin) as (_ & _ & HninP).
      rewrite Hlk1.
      eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
      cbn [PROV PTR ParamsV];
      rewrite (safe_prov_access_disjoint P_unprom (ptr_provenance q) (gs_pr gs) Hsafe HninP).
      apply memM_interp_prov_raiseUB_l.
    - pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
      rewrite (Hout (ptr_to_int q) Hout_z).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b0 aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        cbv iota.
        match goal with |- context [if ?c then _ else _] => destruct c end.
        * unfold set_byte_raw, get_mem, upd_mem, app_mem, set_byte_raw_mem, get, put;
            cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
          apply refine_prov_ret; unfold stage1_mem_inv; repeat match goal with |- _ /\ _ => split end;
            cbn - [IntMaps.lookup IntMaps.add ptr_to_int];
            try reflexivity;
            try exact Hpu; try exact Hnd; try exact Hall; try exact Hdisj;
            try exact Hfgw; try exact Hfs; try exact Hh.
          -- intros z Hz.
             destruct (Z.eq_dec z (ptr_to_int q)) as [-> | Hne].
             ++ rewrite !IntMaps.lookup_add_eq; reflexivity.
             ++ rewrite !IntMaps.lookup_add_ineq by exact Hne; apply Hout, Hz.
          -- intros gs k mb1 Hin_gs Enth.
             pose proof Hall as Hall'; rewrite Forall_forall in Hall'.
             destruct (Hall' gs Hin_gs) as [(_ & _ & _ & _ & Hlen_gs & _) _].
             pose proof (nth_error_Some (gs_bytes gs) k) as [Hsome _].
             assert (Hk : (k < List.length (gs_bytes gs))%nat) by (apply Hsome; rewrite Enth; discriminate).
             assert (Hr_gs : gs_in_range gs (gs_addr gs + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
             assert (Hne : (gs_addr gs + Z.of_nat k)%Z <> ptr_to_int q).
             { intros Heq; rewrite Heq in Hr_gs; exact (Hout_z gs Hin_gs Hr_gs). }
             rewrite !IntMaps.lookup_add_ineq by exact Hne.
             apply (Hgs gs k mb1 Hin_gs Enth).
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage1_loop_Write_byte_unprom
    (pbs : list (@ptr ProvenanceV (@PointerV IP) * @memory_byte (@ParamsV IP IPT)))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    Forall (fun '(q, _) => safe_prov P_unprom (ptr_provenance q)) pbs ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') =
           Memory_stack_frame_stack (state_memory_stack σ2))
      U
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ1)
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ2).
  Proof using.
    intros Hinv Hall; revert σ1 σ2 Hinv;
      induction Hall as [| [q mb] pbs' Hq _ IH]; intros σ1 σ2 Hinv; cbn [loop_monad].
    - apply refine_prov_ret; repeat (first [exact Hinv | reflexivity | split]).
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply (stage1_Write_byte_unprom q mb U P_unprom G σ1 σ2 Hinv Hq) |].
      intros U1 [σ1' []] [σ2' []] (-> & _ & _ & Hinv1 & Hfs1).
      eapply refine_prov_weaken; [apply IH, Hinv1 |].
      intros U2 [σ1'' r1] [σ2'' r2] (-> & -> & -> & Hinv2 & Hfs2).
      repeat (first [exact Hinv2 | reflexivity | split]); congruence.
  Qed.

  Lemma stage1_store_unprom (dt : dtyp) (a v : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    is_safe_ptr_dvalue P_unprom a ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') =
           Memory_stack_frame_stack (state_memory_stack σ2))
      U
      (memM_interp_prov (handle_memoryM (Store dt a v)) σ1)
      (memM_interp_prov (handle_memoryM (Store dt a v)) σ2).
  Proof using.
    intros Hinv Ha; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |]; cbv beta iota;
      lazymatch goal with
      | |- refine_prov _ _ (memM_interp_prov (Mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | |- refine_prov _ _ (memM_interp_prov (mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | _ => idtac
      end.
    pose proof (Ha pt Logic.eq_refl) as Hsafe.
    unfold write_dvalue, write_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    destruct (dvalue_to_memory_bytes dt v None) as [s | s | s | bs];
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |];
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |];
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |];
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l, memM_interp_prov_bind; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l, memM_interp_prov_bind; reflexivity |].
      match goal with
      | |- context [get_consecutive_ptrs ?p ?sz] =>
          destruct (get_consecutive_ptrs p sz) as [s | s | s | ptrs] eqn:Eptrs
      end;
        cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |];
        pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |];
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |];
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l, zip_combine_eq; reflexivity
          | symmetry; rewrite Eqit.bind_ret_l, zip_combine_eq; reflexivity |].
        cbn [write_byte MemoryModelPrimitivesV].
        apply stage1_loop_Write_byte_unprom; [exact Hinv |].
        destruct (get_consecutive_ptrs_spec pt (ListUtil.N.length bs) ptrs Eptrs) as (_ & Hinv_p & _).
        rewrite Forall_forall; intros [q mb] Hin_c.
        apply in_combine_l in Hin_c.
        apply In_nth_error in Hin_c as [k Hnth].
        destruct (Hinv_p k q Hnth) as (_ & _ & Hpr_q);
          cbn [PROV PTR ParamsV ptr_provenance PointerV] in Hpr_q, Hsafe |- *;
          rewrite Hpr_q; exact Hsafe.
  Qed.

  Lemma stage1_Read_byte_any_ptr (q : @ptr ProvenanceV (@PointerV IP))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', _) '(σ2', _) => U' = U /\ σ1' = σ1 /\ σ2' = σ2)
      U
      (memM_interp_prov (Read_byte q) σ1)
      (memM_interp_prov (Read_byte q) σ2).
  Proof using.
    intros Hinv.
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage1_find_gs_at G (ptr_to_int q)) as [[gs [Hin Hr]] | Hout_z].
    - destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs (ptr_to_int q) Hinv Hin Hr)
        as (mb & _ & Hlk1 & Hlk2).
      rewrite Hlk1, Hlk2.
      eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      cbv iota.
      match goal with |- context [if ?c then _ else _] => destruct c end.
      + cbn [memM_interp_prov]; apply refine_prov_ret; repeat split; reflexivity.
      + apply memM_interp_prov_raiseUB_l.
    - pose proof Hinv as (_ & _ & _ & _ & _ & _ & _ & Hout & _).
      cbn [PROV PTR ParamsV]; rewrite (Hout (ptr_to_int q) Hout_z).
      match goal with
      | |- context [IntMaps.lookup ?k ?m] => destruct (IntMaps.lookup k m) as [[b aid] |]
      end.
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        cbv iota.
        match goal with |- context [if ?c then _ else _] => destruct c end.
        * cbn [memM_interp_prov]; apply refine_prov_ret; repeat split; reflexivity.
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage1_map_monad_Read_byte_any_ptr
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', _) '(σ2', _) => U' = U /\ σ1' = σ1 /\ σ2' = σ2)
      U
      (memM_interp_prov (map_monad Read_byte ptrs) σ1)
      (memM_interp_prov (map_monad Read_byte ptrs) σ2).
  Proof using.
    intros Hinv; induction ptrs as [| q ptrs' IH]; cbn [map_monad].
    - apply refine_prov_ret; repeat split; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply (stage1_Read_byte_any_ptr q U P_unprom G σ1 σ2 Hinv) |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & ->).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [exact IH |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (-> & -> & ->).
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma stage1_load_b8_array_any_ptr (n : N) (a : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', _) '(σ2', _) => U' = U /\ σ1' = σ1 /\ σ2' = σ2)
      U
      (memM_interp_prov (handle_memoryM (Load (DTYPE_Array false n (DTYPE_Base (DTYPE_B 8))) a)) σ1)
      (memM_interp_prov (handle_memoryM (Load (DTYPE_Array false n (DTYPE_Base (DTYPE_B 8))) a)) σ2).
  Proof using.
    intros Hinv; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |]; cbv beta iota;
      lazymatch goal with
      | |- refine_prov _ _ (memM_interp_prov (Mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | |- refine_prov _ _ (memM_interp_prov (mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | _ => idtac
      end.
    unfold read_dvalue, read_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind; reflexivity |].
    match goal with
    | |- context [get_consecutive_ptrs ?p ?s] =>
        destruct (get_consecutive_ptrs p s) as [msg | msg | msg | ptrs]
    end;
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
         rewrite memM_interp_prov_map_monad_acc; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
          rewrite memM_interp_prov_map_monad_acc; reflexivity |].
      eapply refine_prov_bind;
        [apply (stage1_map_monad_Read_byte_any_ptr ptrs U P_unprom G σ1 σ2 Hinv) |].
      intros U1 [σ1' bs1] [σ2' bs2] (-> & -> & ->).
      destruct (memory_bytes_to_dvalue_b8_array_total bs1 n) as [dv1 ->].
      destruct (memory_bytes_to_dvalue_b8_array_total bs2 n) as [dv2 ->].
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma stage1_mempop_unprom (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    top_frame_unprom_from fs0 G (state_memory_stack σ2) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (memM_interp_prov (handle_memoryM MemPop) σ1)
      (memM_interp_prov (handle_memoryM MemPop) σ2).
  Proof using.
    intros Hinv (f & Hfs_top & Hout_f).
    pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    assert (Hfgw_fs0 : framestack_ghost_wf G fs0).
    { eapply (framestack_ghost_wf_unprom_inv G fs0 f);
        [eapply Forall_impl; [| exact Hall]; intros g [Hw _]; exact Hw
        | rewrite <- Hfs_top; exact Hfgw
        | exact Hout_f]. }
    cbn [handle_memoryM mempop MemoryModelPrimitivesV].
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
           upd_frame_stack, app_frame_stack, app_mem, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hfs, Hfs_top.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    rewrite Hfs, Hfs_top.
    cbn [pop_frame_stack Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
    apply refine_prov_ret; unfold stage1_mem_inv;
      cbn [state_memory_stack Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap];
      repeat (match goal with
              | |- _ /\ _ => split
              | |- ?x = ?x => reflexivity
              end);
      try exact Hpu; try exact Hnd; try exact Hall; try exact Hdisj;
      try exact Hfgw_fs0; try exact Hh.
    - intros z Hz_out.
      destruct (in_dec Z.eq_dec z (List.map ptr_to_int f)) as [Hin_f | Hnin_f].
      + rewrite !lookup_free_frame_memory_in by exact Hin_f; reflexivity.
      + rewrite !lookup_free_frame_memory_out by exact Hnin_f; apply Hout, Hz_out.
    - intros gs k mb Hin_gs Enth.
      pose proof Hall as Hall'; rewrite Forall_forall in Hall'.
      destruct (Hall' gs Hin_gs) as [(_ & _ & _ & _ & Hlen_gs & _) _].
      pose proof (nth_error_Some (gs_bytes gs) k) as [Hsome _].
      assert (Hk : (k < List.length (gs_bytes gs))%nat) by (apply Hsome; rewrite Enth; discriminate).
      assert (Hr_gs : gs_in_range gs (gs_addr gs + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
      assert (Hnin_f : ~ In (gs_addr gs + Z.of_nat k)%Z (List.map ptr_to_int f)).
      { intros Hin_f; exact (Hout_f _ Hin_f gs Hin_gs Hr_gs). }
      rewrite !lookup_free_frame_memory_out by exact Hnin_f.
      apply (Hgs gs k mb Hin_gs Enth).
  Qed.

  Lemma stage1_mempop_prom (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom (gs :: G) σ1 σ2 ->
    top_frame_prom_from fs0 gs G (state_memory_stack σ2) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (memM_interp_prov (handle_memoryM MemPop) σ1)
      (memM_interp_prov (handle_memoryM MemPop) σ2).
  Proof using.
    intros Hinv (f & Hfs_top & Hin_f & Hout_f).
    pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    inversion Hnd as [| ? ? _ Hnd_tl]; subst.
    inversion Hall as [| ? ? (Hwf0 & _ & _) Hall_tl]; subst.
    destruct Hdisj as [_ Hdisj_tl].
    assert (Hfgw_fs0 : framestack_ghost_wf G fs0).
    { eapply (framestack_ghost_wf_prom_inv gs G fs0 f);
        [exact Hwf0 | rewrite <- Hfs_top; exact Hfgw | exact Hin_f]. }
    cbn [handle_memoryM mempop MemoryModelPrimitivesV].
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
           upd_frame_stack, app_frame_stack, app_mem, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hfs, Hfs_top.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    rewrite Hfs, Hfs_top.
    cbn [pop_frame_stack Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
    apply refine_prov_ret; unfold stage1_mem_inv;
      cbn [state_memory_stack Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap];
      repeat (match goal with
              | |- _ /\ _ => split
              | |- ?x = ?x => reflexivity
              end);
      try exact Hpu; try exact Hnd_tl; try exact Hall_tl; try exact Hdisj_tl;
      try exact Hfgw_fs0; try exact Hh.
    - intros z Hz_out.
      destruct (gs_in_range_dec gs z) as [Hr0 | Hnr0].
      + rewrite !lookup_free_frame_memory_in by (apply Hin_f, Hr0); reflexivity.
      + destruct (in_dec Z.eq_dec z (List.map ptr_to_int f)) as [Hzf | Hnzf].
        * rewrite !lookup_free_frame_memory_in by exact Hzf; reflexivity.
        * rewrite !lookup_free_frame_memory_out by exact Hnzf.
          apply Hout; intros g0 [<- | Hg0]; [exact Hnr0 | apply Hz_out, Hg0].
    - intros gs' k mb Hin_gs' Enth.
      pose proof Hall_tl as Hall_tl'; rewrite Forall_forall in Hall_tl'.
      destruct (Hall_tl' gs' Hin_gs') as [(_ & _ & _ & _ & Hlen_gs' & _) _].
      pose proof (nth_error_Some (gs_bytes gs') k) as [Hsome _].
      assert (Hk : (k < List.length (gs_bytes gs'))%nat) by (apply Hsome; rewrite Enth; discriminate).
      assert (Hr_gs' : gs_in_range gs' (gs_addr gs' + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
      assert (Hnin_f : ~ In (gs_addr gs' + Z.of_nat k)%Z (List.map ptr_to_int f)).
      { intros Hzf; exact (Hout_f _ Hzf gs' Hin_gs' Hr_gs'). }
      rewrite !lookup_free_frame_memory_out by exact Hnin_f.
      apply (Hgs gs' k mb (or_intror Hin_gs') Enth).
  Qed.

  (** ** 3E. Stage 2 Dead-Alloca Memory Invariant & Primitive Simulation *)

  Definition stage2_in_range (base : Z) (sz : nat) (z : Z) : Prop :=
    (base <= z < base + Z.of_nat sz)%Z.

  Lemma stage2_in_range_dec (base : Z) (sz : nat) (z : Z) :
    {stage2_in_range base sz z} + {~ stage2_in_range base sz z}.
  Proof using.
    unfold stage2_in_range.
    destruct (Z_le_gt_dec base z) as [Hle | Hgt].
    - destruct (Z_lt_ge_dec z (base + Z.of_nat sz)) as [Hlt | Hge]; [left; lia | right; lia].
    - right; lia.
  Qed.

  Definition stage2_mem_inv (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) : Prop :=
    incl P_safe U /\
    In pr_dead U /\
    ~ In pr_dead P_safe /\
    Memory_stack_heap (state_memory_stack σ1) = Memory_stack_heap (state_memory_stack σ2) /\
    Memory_stack_frame_stack (state_memory_stack σ2) = Snoc fs0 f2 /\
    (exists ptrs_dead,
       (forall z, In z (List.map ptr_to_int ptrs_dead) <-> stage2_in_range base_dead sz_dead z) /\
       Memory_stack_frame_stack (state_memory_stack σ1) = Snoc fs0 (rev ptrs_dead ++ f2)) /\
    (forall z,
       stage2_in_range base_dead sz_dead z ->
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ1)) =
         Some (poison_memory_byte, Some pr_dead) /\
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ2)) = None) /\
    (forall z,
       ~ stage2_in_range base_dead sz_dead z ->
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ1)) =
         IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ2))).

  Lemma stage2_mem_inv_incl_U (U U' P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat) (σ1 σ2 : state) :
    incl U U' ->
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    stage2_mem_inv U' P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2.
  Proof using.
    intros Hinc (Hpu & Hin & Hnin & Hh & Hfs2 & Hfs1 & Hrng & Hout).
    split; [eapply incl_tran; eassumption |].
    split; [apply Hinc, Hin |].
    exact (conj Hnin (conj Hh (conj Hfs2 (conj Hfs1 (conj Hrng Hout))))).
  Qed.

  Lemma stage2_alloca_dead_l {IPWB : IPtrWellBehaved IP}
    {R2} (r2 : R2)
    (dt : dtyp) (align : option N)
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (σ1 σ2 : state)
    (Hsc : is_scalar_dtyp dt = true)
    (Hpu : incl P_safe U)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2))
    (Hfs2 : Memory_stack_frame_stack (state_memory_stack σ2) = Snoc fs0 f2) :
    refine_prov
      (fun U' '(σ1', r1) y2 =>
         exists pr pt,
           ~ In pr U /\
           U' = pr :: U /\
           r1 = DVALUE_Base (DVALUE_Pointer pt) /\
           y2 = r2 /\
           stage2_mem_inv (pr :: U) P_safe fs0 f2 (ptr_to_int pt) pr
             (N.to_nat (@store_size_dtyp SizeofV dt)) σ1' σ2)
      U
      (memM_interp_prov (handle_memoryM (Alloca dt 1%N align)) σ1)
      (Ret r2).
  Proof using.
    destruct Heq as (Hm_eq & Hfs_eq & Hh_eq).
    cbn [handle_memoryM].
    set (al := match align with None => preferred_alignment (dtyp_alignment dt) | Some a => a end).
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | reflexivity |].
    unfold allocate_dtyp.
    rewrite (scalar_dtyp_not_void dt Hsc).
    set (bs := concat_acc (repeatN 1%N (@generate_poison_bytes (@ParamsV IP IPT) dt))).
    unfold allocate_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind;
       cbn [ExtLib.Structures.Monad.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
       rewrite !Eqit.bind_bind; reflexivity
      | reflexivity |].
    apply refine_prov_trigger_fresh_l; intros pr Hpr.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity | reflexivity |].
    unfold Allocate_bytes_with_pr, get_free_block, next_key, Mnext_key.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind;
       cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_memory_stack];
       rewrite !Eqit.bind_bind, !Eqit.bind_ret_l; reflexivity
      | reflexivity |].
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack σ1)) al).
    set (sz := ListUtil.N.length bs).
    unfold int_to_ptr; cbn [P2I IPTR ParamsV PIV]; cbn beta iota.
    destruct (@from_Z_ret_or_oom IP IPWB addr) as [[ip Hip] | [msg Hoom]].
    - rewrite Hip; cbn [ExtLib.Structures.Monad.bind EOU_monad ExtLib.Structures.Monad.ret Interfaces.Memory.lift memS_mon memS_bind memM_interp_prov PROV PTR ParamsV].
      match goal with
      | |- context [get_consecutive_ptrs ?p0 sz] =>
          set (pt := p0 : @ptr ProvenanceV (@PointerV IP))
      end.
      destruct (get_consecutive_ptrs_well_behaved pt sz) as [[ptrs Eptrs] | [msg Hoom]].
      + rewrite Eptrs; cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
        unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l;
           cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV];
           rewrite !Eqit.bind_ret_l; reflexivity
          | reflexivity |].
        apply refine_prov_ret.
        assert (Hip_Z : to_Z ip = addr) by (apply from_Z_to_Z; exact Hip).
        assert (Hpt_int : ptr_to_int pt = addr) by (cbn; exact Hip_Z).
        assert (Hbs_eq : bs = List.repeat (@poison_memory_byte (@ParamsV IP IPT))
                                (N.to_nat (@store_size_dtyp SizeofV dt))).
        { unfold bs; apply alloc_poison_bytes_eq. }
        assert (Hbs_len : List.length bs = N.to_nat (@store_size_dtyp SizeofV dt)).
        { rewrite Hbs_eq, repeat_length; reflexivity. }
        assert (Hsz_eq : sz = @store_size_dtyp SizeofV dt).
        { unfold sz; rewrite N_length_eq, Hbs_len, N2Nat.id; reflexivity. }
        lazymatch goal with
        | |- context [@memory_bytes_to_bytes ?Pa ?aid bs] =>
            set (mbs := @memory_bytes_to_bytes Pa aid bs)
        end.
        assert (Hmbs_len : List.length mbs = List.length bs).
        { unfold mbs; rewrite memory_bytes_to_bytes_eq, length_map; reflexivity. }
        assert (Hmem_frame : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                  Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms).
        { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
          destruct fss; apply IH. }
        assert (Hheap_frame : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                  Memory_stack_heap (add_all_to_frame ks ms) = Memory_stack_heap ms).
        { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
          destruct fss; apply IH. }
        exists pr, pt.
        split; [exact Hpr |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [intros x Hx; right; apply Hpu, Hx |].
        split; [left; reflexivity |].
        split; [intros Hp; exact (Hpr (Hpu pr Hp)) |].
        split; [cbn [state_memory_stack]; rewrite Hheap_frame; cbn; exact Hh_eq |].
        split; [exact Hfs2 |].
        split.
        * exists ptrs; split.
          -- intros z; rewrite (get_consecutive_ptrs_in_addrs pt sz ptrs z Eptrs), Hsz_eq.
             unfold stage2_in_range; reflexivity.
          -- cbn [state_memory_stack].
             assert (Hfs1_top : Memory_stack_frame_stack (state_memory_stack σ1) = Snoc fs0 f2) by congruence.
             rewrite Hfs1_top, add_all_to_frame_Snoc; reflexivity.
        * split.
          -- intros z Hz; unfold stage2_in_range in Hz.
             cbn [state_memory_stack]; rewrite Hmem_frame; cbn [Memory_stack_memory].
             set (k := Z.to_nat (z - addr)).
             assert (Hk_bs : (k < List.length bs)%nat) by lia.
             destruct (nth_error_Some bs k) as [_ Hsome].
             destruct (nth_error bs k) as [mb0 |] eqn:Enth_bs;
               [| exfalso; apply Hsome; [exact Hk_bs | reflexivity]].
             pose proof (nth_error_In bs k Enth_bs) as Hin_bs.
             rewrite Hbs_eq in Hin_bs; apply repeat_spec in Hin_bs; subst mb0.
             assert (Enth_mbs : nth_error mbs k = Some (poison_memory_byte, Some pr)).
             { unfold mbs; cbn [PROV ParamsV ProvenanceV]; rewrite memory_bytes_to_bytes_eq, nth_error_map, Enth_bs; reflexivity. }
             split.
             ++ eapply lookup_add_all_index_acc_in;
                  [exact Enth_mbs
                  | repeat match goal with
                           | |- context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                               progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q))
                           end;
                    assert (Hpt_z : @to_Z IP (fst pt) = addr) by exact Hpt_int;
                    rewrite Hpt_z; lia].
             ++ rewrite <- (Hm_eq z).
                apply (next_key_with_alignment_fresh (Memory_stack_memory (state_memory_stack σ1)) al z).
                fold addr; lia.
          -- intros z Hz; unfold stage2_in_range in Hz.
             cbn [state_memory_stack]; rewrite Hmem_frame; cbn [Memory_stack_memory].
             repeat match goal with
                    | |- context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                        progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q))
                    end.
             assert (Hpt_z : @to_Z IP (fst pt) = addr) by exact Hpt_int.
             rewrite Hpt_z.
             repeat match type of Hz with
                    | context [@ptr_to_int ?Pr ?Pt ?Pi ?q] =>
                        progress change (@ptr_to_int Pr Pt Pi q) with (@to_Z IP (fst q)) in Hz
                    end.
             rewrite Hpt_z in Hz.
             rewrite lookup_add_all_index_acc_out;
               [apply Hm_eq | rewrite Hmbs_len, Hbs_len; lia].
      + rewrite Hoom; cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind memM_interp_prov].
        eapply refine_prov_obs_eq;
          [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
    - rewrite Hoom; cbn [ExtLib.Structures.Monad.bind EOU_monad ExtLib.Structures.Monad.ret Interfaces.Memory.lift memS_mon memS_bind memM_interp_prov].
      eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage2_Read_byte_safe (q : @ptr ProvenanceV (@PointerV IP))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    safe_prov P_safe (ptr_provenance q) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (Read_byte q) σ1)
      (memM_interp_prov (Read_byte q) σ2).
  Proof using.
    intros (Hpu & Hin & Hnin & Hh & Hfs2 & Hfs1 & Hrng & Hout) Hsafe.
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage2_in_range_dec base_dead sz_dead (ptr_to_int q)) as [Hr | Hnr].
    - destruct (Hrng (ptr_to_int q) Hr) as [Hlk1 _].
      rewrite Hlk1.
      eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
      cbn [PROV PTR ParamsV];
      rewrite (safe_prov_access_disjoint P_safe (ptr_provenance q) pr_dead Hsafe Hnin).
      apply memM_interp_prov_raiseUB_l.
    - rewrite (Hout (ptr_to_int q) Hnr).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        cbv iota.
        match goal with |- context [if ?c then _ else _] => destruct c end.
        * cbn [memM_interp_prov]; apply refine_prov_ret; repeat split; reflexivity.
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage2_map_monad_Read_byte_safe
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    Forall (fun q => safe_prov P_safe (ptr_provenance q)) ptrs ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (map_monad Read_byte ptrs) σ1)
      (memM_interp_prov (map_monad Read_byte ptrs) σ2).
  Proof using.
    intros Hinv Hall; induction Hall as [| q ptrs' Hq _ IH]; cbn [map_monad].
    - apply refine_prov_ret; repeat split; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind;
        [apply (stage2_Read_byte_safe q U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Hq) |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & -> & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [exact IH |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (-> & -> & -> & <-).
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma stage2_load_safe (dt : dtyp) (a : @dvalue (@ParamsV IP IPT))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    is_safe_ptr_dvalue P_safe a ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (handle_memoryM (Load dt a)) σ1)
      (memM_interp_prov (handle_memoryM (Load dt a)) σ2).
  Proof using.
    intros Hinv Ha; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |]; cbv beta iota;
      lazymatch goal with
      | |- refine_prov _ _ (memM_interp_prov (Mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | |- refine_prov _ _ (memM_interp_prov (mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | _ => idtac
      end.
    pose proof (Ha pt Logic.eq_refl) as Hsafe.
    unfold read_dvalue, read_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind; reflexivity |].
    cbn [SIZE ParamsV].
    match goal with
    | |- context [get_consecutive_ptrs ?p ?s] =>
        destruct (get_consecutive_ptrs p s) as [s0 | s0 | s0 | ptrs] eqn:Eptrs
    end;
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
         rewrite memM_interp_prov_map_monad_acc; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
          rewrite memM_interp_prov_map_monad_acc; reflexivity |].
      assert (Hall_safe : Forall (fun q => safe_prov P_safe (ptr_provenance q)) ptrs).
      { destruct (get_consecutive_ptrs_spec pt (@store_size_dtyp SizeofV dt) ptrs Eptrs) as (_ & Hinv_p & _).
        rewrite Forall_forall; intros q Hin_q.
        apply In_nth_error in Hin_q as [k Hnth].
        destruct (Hinv_p k q Hnth) as (_ & _ & Hpr_q);
          cbn [PROV PTR ParamsV ptr_provenance PointerV] in Hpr_q, Hsafe |- *;
          rewrite Hpr_q; exact Hsafe. }
      eapply refine_prov_bind;
        [apply (stage2_map_monad_Read_byte_safe ptrs U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Hall_safe) |].
      intros U1 [σ1' bs1] [σ2' bs2] (-> & -> & -> & <-).
      eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros dv _ <-; repeat split; reflexivity.
  Qed.

  Lemma stage2_Write_byte_safe
    (q : @ptr ProvenanceV (@PointerV IP)) (mb : @memory_byte (@ParamsV IP IPT))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    safe_prov P_safe (ptr_provenance q) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2')
      U
      (memM_interp_prov (Write_byte q mb) σ1)
      (memM_interp_prov (Write_byte q mb) σ2).
  Proof using.
    intros (Hpu & Hin & Hnin & Hh & Hfs2 & Hfs1 & Hrng & Hout) Hsafe.
    unfold Write_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage2_in_range_dec base_dead sz_dead (ptr_to_int q)) as [Hr | Hnr].
    - destruct (Hrng (ptr_to_int q) Hr) as [Hlk1 _].
      rewrite Hlk1.
      eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
      cbn [PROV PTR ParamsV];
      rewrite (safe_prov_access_disjoint P_safe (ptr_provenance q) pr_dead Hsafe Hnin).
      apply memM_interp_prov_raiseUB_l.
    - rewrite (Hout (ptr_to_int q) Hnr).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b0 aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        cbv iota.
        match goal with |- context [if ?c then _ else _] => destruct c end.
        * unfold set_byte_raw, get_mem, upd_mem, app_mem, set_byte_raw_mem, get, put;
            cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
          apply refine_prov_ret; unfold stage2_mem_inv; repeat match goal with |- _ /\ _ => split end;
            cbn - [IntMaps.lookup IntMaps.add ptr_to_int];
            try reflexivity;
            try exact Hpu; try exact Hin; try exact Hnin;
            try exact Hh; try exact Hfs2; try exact Hfs1.
          -- intros z Hz.
             assert (Hne : z <> ptr_to_int q) by (intros Heq; rewrite Heq in Hz; exact (Hnr Hz)).
             rewrite !IntMaps.lookup_add_ineq by exact Hne.
             exact (Hrng z Hz).
          -- intros z Hz.
             destruct (Z.eq_dec z (ptr_to_int q)) as [-> | Hne].
             ++ rewrite !IntMaps.lookup_add_eq; reflexivity.
             ++ rewrite !IntMaps.lookup_add_ineq by exact Hne; apply Hout, Hz.
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage2_loop_Write_byte_safe
    (pbs : list (@ptr ProvenanceV (@PointerV IP) * @memory_byte (@ParamsV IP IPT)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    Forall (fun '(q, _) => safe_prov P_safe (ptr_provenance q)) pbs ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2')
      U
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ1)
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ2).
  Proof using.
    intros Hinv Hall; revert σ1 σ2 Hinv;
      induction Hall as [| [q mb] pbs' Hq _ IH]; intros σ1 σ2 Hinv; cbn [loop_monad].
    - apply refine_prov_ret; repeat (first [exact Hinv | reflexivity | split]).
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind;
        [apply (stage2_Write_byte_safe q mb U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Hq) |].
      intros U1 [σ1' []] [σ2' []] (-> & _ & _ & Hinv1).
      apply IH, Hinv1.
  Qed.

  Lemma stage2_store_safe (dt : dtyp) (a v : @dvalue (@ParamsV IP IPT))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    is_safe_ptr_dvalue P_safe a ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2')
      U
      (memM_interp_prov (handle_memoryM (Store dt a v)) σ1)
      (memM_interp_prov (handle_memoryM (Store dt a v)) σ2).
  Proof using.
    intros Hinv Ha; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |]; cbv beta iota;
      lazymatch goal with
      | |- refine_prov _ _ (memM_interp_prov (Mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | |- refine_prov _ _ (memM_interp_prov (mub _) _) _ => apply memM_interp_prov_raiseUB_l
      | _ => idtac
      end.
    pose proof (Ha pt Logic.eq_refl) as Hsafe.
    unfold write_dvalue, write_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    destruct (dvalue_to_memory_bytes dt v None) as [s | s | s | bs];
      cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |];
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |];
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |];
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l, memM_interp_prov_bind; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l, memM_interp_prov_bind; reflexivity |].
      match goal with
      | |- context [get_consecutive_ptrs ?p ?sz] =>
          destruct (get_consecutive_ptrs p sz) as [s | s | s | ptrs] eqn:Eptrs
      end;
        cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |];
        pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |];
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |];
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l, zip_combine_eq; reflexivity
          | symmetry; rewrite Eqit.bind_ret_l, zip_combine_eq; reflexivity |].
        cbn [write_byte MemoryModelPrimitivesV].
        apply stage2_loop_Write_byte_safe; [exact Hinv |].
        destruct (get_consecutive_ptrs_spec pt (ListUtil.N.length bs) ptrs Eptrs) as (_ & Hinv_p & _).
        rewrite Forall_forall; intros [q mb] Hin_c.
        apply in_combine_l in Hin_c.
        apply In_nth_error in Hin_c as [k Hnth].
        destruct (Hinv_p k q Hnth) as (_ & _ & Hpr_q);
          cbn [PROV PTR ParamsV ptr_provenance PointerV] in Hpr_q, Hsafe |- *;
          rewrite Hpr_q; exact Hsafe.
  Qed.

  Lemma stage2_mempop_restore
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2') /\
         Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (memM_interp_prov (handle_memoryM MemPop) σ1)
      (memM_interp_prov (handle_memoryM MemPop) σ2).
  Proof using.
    intros (_ & _ & _ & Hh & Hfs2 & (ptrs_dead & Hptrs & Hfs1) & Hrng & Hout).
    cbn [handle_memoryM mempop MemoryModelPrimitivesV].
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
           upd_frame_stack, app_frame_stack, app_mem, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hfs1, Hfs2.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    rewrite Hfs1, Hfs2.
    cbn [pop_frame_stack Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
    apply refine_prov_ret; repeat split; cbn; try exact Hh.
    intros z.
    destruct (stage2_in_range_dec base_dead sz_dead z) as [Hr | Hnr].
    - assert (Hin1 : In z (List.map ptr_to_int (rev ptrs_dead ++ f2))).
      { apply in_map_rev_app_iff; left; apply Hptrs, Hr. }
      rewrite (lookup_free_frame_memory_in (rev ptrs_dead ++ f2) _ z Hin1).
      destruct (in_dec Z.eq_dec z (List.map ptr_to_int f2)) as [Hin2 | Hnin2].
      + rewrite (lookup_free_frame_memory_in f2 _ z Hin2); reflexivity.
      + rewrite (lookup_free_frame_memory_out f2 _ z Hnin2).
        symmetry; exact (proj2 (Hrng z Hr)).
    - destruct (in_dec Z.eq_dec z (List.map ptr_to_int f2)) as [Hin2 | Hnin2].
      + assert (Hin1 : In z (List.map ptr_to_int (rev ptrs_dead ++ f2))).
        { apply in_map_rev_app_iff; right; exact Hin2. }
        rewrite (lookup_free_frame_memory_in (rev ptrs_dead ++ f2) _ z Hin1),
                (lookup_free_frame_memory_in f2 _ z Hin2); reflexivity.
      + assert (Hnin1 : ~ In z (List.map ptr_to_int (rev ptrs_dead ++ f2))).
        { intros Hin1; apply in_map_rev_app_iff in Hin1 as [Hp | Hf];
            [apply Hptrs in Hp; exact (Hnr Hp) | exact (Hnin2 Hf)]. }
        rewrite (lookup_free_frame_memory_out (rev ptrs_dead ++ f2) _ z Hnin1),
                (lookup_free_frame_memory_out f2 _ z Hnin2).
        exact (Hout z Hnr).
  Qed.


End MemoryAndSerialization.
