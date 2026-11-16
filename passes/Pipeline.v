(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(* ========================================================================= *)
(* CertPasses.Pipeline                                                       *)
(*                                                                           *)
(* End-to-End Verified Optimization Pipeline for LLVMCert (Phase 2.2).       *)
(* Composes Mem2Reg, Inline, SCCP, SimplifyCFG, and DCE via the transitive   *)
(* whole-module semantic refinement relation [prog_refines].                 *)
(* ========================================================================= *)

From Stdlib Require Import
  List.

From ITree Require Import
  Basics.HeterogeneousRelations.

From Vellvm Require Import
  Syntax.LLVMAst
  Syntax.CFG
  Syntax.DynamicTypes
  Semantics.Interfaces.IPtr
  Semantics.Implementations.IPtrInfinite
  Semantics.Implementations.IPtrFinite
  Semantics.Implementations.Memory
  Semantics.Interfaces.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.LLVMEvents
  Theory.I2F.Refinement
  Theory.I2F.I2F_interp
  Theory.I2F.I2F_toplevel.

From CertPasses Require Import
  PassCommon
  SimplifyCFG
  DCE
  SCCP
  Mem2Reg
  Inline.

#[local] Existing Instance MemoryModelStateV.
#[local] Existing Instance MemoryModelPrimitivesV.

(** Canonical multi-stage optimization pipeline over [CFG.mcfg dtyp]:
    1. [mem2reg_mcfg]     : Promote caller/callee stack slots to SSA registers
                            and delete dead leaf [alloca]s before inlining.
    2. [inline_mcfg]      : Inline eligible direct internal calls across module.
    3. [mem2reg_mcfg]     : Promote any newly simplified scalar stack slots.
    4. [sccp_mcfg]        : Sparse Conditional Constant Propagation across the
                            post-inlining SSA graph.
    5. [simplifycfg_mcfg] : Fold newly constant branches, prune unreachable
                            blocks/phi edges, and coalesce linear block chains.
    6. [dce_mcfg]         : Eliminate dead instructions and dead phi nodes.
    7. [simplifycfg_mcfg] : Final control-flow cleanup pass. *)
Definition optimize_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  simplifycfg_mcfg
    (dce_mcfg
      (simplifycfg_mcfg
        (sccp_mcfg
          (mem2reg_mcfg
            (inline_mcfg
              (mem2reg_mcfg M)))))).

(** Convenience entry point from front-end [CFG.mcfg typ] syntax trees. *)
Definition optimize_mcfg_typ (M : CFG.mcfg typ) : CFG.mcfg dtyp :=
  optimize_mcfg (convert_types M).

(** Master Phase 2.2 Soundness Theorem:
    The full optimization pipeline refines the input module under Vellvm 3.0
    whole-program model semantics (preserving external traces and semantic
    [FailureE] 1-to-1 while allowing UB/stack-OOM reduction). *)
Theorem optimize_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (optimize_mcfg M).
Proof.
  intros IP IPT IPWB M.
  unfold optimize_mcfg.
  eapply prog_refines_trans. apply mem2reg_mcfg_refines.
  eapply prog_refines_trans. apply inline_mcfg_refines.
  eapply prog_refines_trans. apply mem2reg_mcfg_refines.
  eapply prog_refines_trans. apply sccp_mcfg_refines.
  eapply prog_refines_trans. apply simplifycfg_mcfg_refines.
  eapply prog_refines_trans. apply dce_mcfg_refines.
  apply simplifycfg_mcfg_refines.
Qed.

(** Concrete zero-hypothesis instantiations for Vellvm 3.0's unbounded
    ([IPZ]) and 64-bit finite ([IP64Bit]) address-space models. *)
Theorem optimize_mcfg_refines_IPZ :
  forall (M : CFG.mcfg dtyp),
    @prog_refines IPZ IPZTheory M (optimize_mcfg M).
Proof.
  intros M; exact (@optimize_mcfg_refines IPZ IPZTheory IPtrWellBehaved_IPZ M).
Qed.

Corollary optimize_mcfg_refines_inf :
  forall (M : CFG.mcfg dtyp),
    @prog_refines IPZ IPZTheory M (optimize_mcfg M).
Proof.
  exact optimize_mcfg_refines_IPZ.
Qed.

Corollary optimize_mcfg_refines_64 :
  forall (M : CFG.mcfg dtyp),
    @prog_refines IP64Bit IP64BitTheory M (optimize_mcfg M).
Proof.
  intros M; exact (@optimize_mcfg_refines IP64Bit IP64BitTheory IP64Bit_WellBehaved M).
Qed.

(** End-to-end [IPZ -> IPZ -> IP64Bit] composition pairing the unbounded-address
    pass-pipeline theorem ([optimize_mcfg_refines_IPZ]) with Vellvm 3.0's
    infinite-to-finite address-space refinement ([I2F_toplevel.model_refine]). *)
Theorem optimize_mcfg_I2F_model_refine :
  forall (M : CFG.mcfg dtyp)
         (ret_typ : dtyp) (entry : function_id)
         (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
         (s1 : @FusedS PInf) (s2 : @FusedS PFin),
    Forall2 I2F_dvalue args1 args2 ->
    I2F_FusedS s1 s2 ->
    @prog_refines IPZ IPZTheory M (optimize_mcfg M) /\
    I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
      (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 (optimize_mcfg M)) s1)
      (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 (optimize_mcfg M)) s2).
Proof.
  intros M ret_typ entry args1 args2 s1 s2 Hargs Hs.
  split.
  - exact (optimize_mcfg_refines_IPZ M).
  - exact (I2F_toplevel.model_refine ret_typ entry args1 args2 (optimize_mcfg M) s1 s2 Hargs Hs).
Qed.
