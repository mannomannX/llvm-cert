# `CertPasses` Architecture & Audit Map

Logical Rocq namespace: `-Q ../../passes CertPasses` (compiled from [`vellvm/src/_RocqProject`](../vellvm/src/_RocqProject)).

This directory contains **34 Rocq source files** (`33` top-level files in `passes/` and `1` ITree tactic helper in `passes/common/`) implementing the **Safe-Path Verified Optimizer** and **Certified Module Merge** over Vellvm 3.0 CFG/MCFG semantics.

---

## 1. Trust Flow & CLI Entrypoints

### 1.1 Safe-Path Verified Optimizer (`verified-opt-fallback`)

When Fast-Path unverified compilation/validation rejects or falls back, untrusted `.ll` IR passes through [`verified_opt_fallback.ml`](../vellvm/src/ml/bin/verified_opt_fallback.ml) into purely Rocq-verified transformations extracted in [`Extract.v`](../vellvm/src/ml/extracted/Extract.v):

```text
input.ll ---> VellvmLib.IO.parse_file ---> McfgExport.resolve_for_opt_tle
         ---> Pipeline.optimize_mcfg_typ  (or per-pass --pass {mem2reg|inline|sccp|dce|simplifycfg})
         ---> McfgExport.export_mcfg_with_tle ---> verified output.ll
```

### 1.2 Compositional Hybrid Module Merge (`cert-validator --check-merge`)

Allows mixing Fast-Path translation-validated function slices (`--slice-cert`), Safe-Path verified slices (`--slice-safe`), and composed safe+certified slices (`--slice-safe-cert`) inside [`cert_validator.ml`](../vellvm/src/ml/bin/cert_validator.ml):

```text
orig.ll + merged.ll + verified/certified slices
  ---> ModuleMerge.validate_module_merge_certified_tle_composed
  ---> whole-program refinement (PassCommonModel.prog_refines + I2F finite-memory lift)
```

### 1.3 Infinite-to-Finite Semantic Lifting

Each individual optimization pass is proven sound under Vellvm infinite-pointer whole-program refinement (`PassCommonModel.prog_refines`, instantiated over `IPZ`). [`Pipeline.v`](./Pipeline.v) and [`ModuleMerge.v`](./ModuleMerge.v) then lift whole-module soundness via Vellvm 3.0's `Theory.I2F.I2F_toplevel` to finite 64-bit pointer semantics (`IP64Bit`):

- `Pipeline.optimize_mcfg_I2F_model_refine`
- `ModuleMerge.validate_module_merge_parsed_I2F_model_refine`

---

## 2. Shared Pass Infrastructure (4 files)

Dependency order: `common/ItreeTactics.v` + `PassCommonSyntax.v` $\to$ `PassCommonModel.v` $\to$ `PassCommon.v`.

| File | Role |
| :--- | :--- |
| [`common/ItreeTactics.v`](./common/ItreeTactics.v) | Focused Interaction Tree (`eutt` / `rutt`) rewriting and inversion tactics |
| [`PassCommonSyntax.v`](./PassCommonSyntax.v) | Pure AST utilities (`map_mcfg`, register/block-address/name helpers, 0 semantic deps) |
| [`PassCommonModel.v`](./PassCommonModel.v) | Event relations, `ProvE` / `refine_prov`, whole-program `prog_refines`, `lift_cfg_pass` |
| [`PassCommon.v`](./PassCommon.v) | Per-function `cfg_local_sim`, `cfg_stack_sim`, `lift_cfg_with_args_local_pass`, and facade re-export |

---

## 3. Verified Optimization Passes (23 files)

Listed in pipeline execution order:

### 3.1 `Mem2Reg` — Stack-Slot Promotion to SSA (10 files)

`Mem2RegSpec.v` + parallel `Mem2RegModel.v` $\to$ `Mem2RegMemBase.v` $\to$ `Mem2RegGhostInv.v` $\to$ `Mem2RegExprLift.v` $\to$ `Mem2RegCpsSSA.v` $\to$ `Mem2RegLeafKnot.v` $\to$ `Mem2RegStage2.v` $\to$ `Mem2RegStage1.v` $\to$ `Mem2Reg.v`.

| File | Role |
| :--- | :--- |
| [`Mem2RegSpec.v`](./Mem2RegSpec.v) | Extracted transform (`mem2reg_mcfg`, `mem2reg_mcfg_typ`) and slot-promotion / dead-alloca deciders |
| [`Mem2RegModel.v`](./Mem2RegModel.v) | Memory/serialization context model relations and single-step local invariants |
| [`Mem2RegMemBase.v`](./Mem2RegMemBase.v) | Base stack-memory frame reasoning (`Sec 3A–3C`: allocation, load/store disjointness) |
| [`Mem2RegGhostInv.v`](./Mem2RegGhostInv.v) | Ghost-memory invariants (`Sec 3D–3E`) linking promoted SSA registers to dead stack slots |
| [`Mem2RegExprLift.v`](./Mem2RegExprLift.v) | Expression and instruction semantic lifting (`Sec 3F–3H`) across ghost state |
| [`Mem2RegCpsSSA.v`](./Mem2RegCpsSSA.v) | CPS-style SSA edge renaming and phi-insertion simulation (`Sec 3I–3L`) |
| [`Mem2RegLeafKnot.v`](./Mem2RegLeafKnot.v) | Event-relation knot (`ev_ok`, `LeafKnotG`) for non-recursive leaf functions |
| [`Mem2RegStage2.v`](./Mem2RegStage2.v) | Stage-2 per-slot promotion soundness proof |
| [`Mem2RegStage1.v`](./Mem2RegStage1.v) | Stage-1 dead-alloca elimination and leaf function lifting |
| [`Mem2Reg.v`](./Mem2Reg.v) | Interprocedural knot (`InterprocKnot`), top-level `mem2reg_mcfg` theorem, and facade re-export |

### 3.2 `Inline` — Hygienic Direct-Call Inlining (7 files)

`InlineSpec.v` + parallel `InlineSim.v` $\to$ `InlineSyntaxProof.v` $\to$ `InlineFrameGenv.v` $\to$ `InlineCalleeProof.v` $\to$ `InlineCallerProof.v` $\to$ `Inline.v`.

| File | Role |
| :--- | :--- |
| [`InlineSpec.v`](./InlineSpec.v) | Extracted pass (`inline_mcfg`, `inline_mcfg_typ`), hygiene checks, and bounded call-site iteration |
| [`InlineSyntaxProof.v`](./InlineSyntaxProof.v) | CFG block/phi splicing and alpha-renaming hygiene preservation proofs |
| [`InlineFrameGenv.v`](./InlineFrameGenv.v) | Stack-frame and global-environment invariance lemmas across call inlining |
| [`InlineSim.v`](./InlineSim.v) | Core simulation relations for inlined callee/caller stack states |
| [`InlineCalleeProof.v`](./InlineCalleeProof.v) | Callee body denotation and local-simulation proof inside spliced caller blocks |
| [`InlineCallerProof.v`](./InlineCallerProof.v) | Caller continuation and return-edge simulation lemmas |
| [`Inline.v`](./Inline.v) | `CallerInlineLoop`, top-level `inline_mcfg` soundness theorems, and facade re-export |

### 3.3 `SCCP` — Sparse Conditional Constant Propagation (2 files)

| File | Role |
| :--- | :--- |
| [`SCCPSpec.v`](./SCCPSpec.v) | Extracted pass (`sccp_mcfg`, `sccp_mcfg_typ`), lattice transfer functions, and worklist solver |
| [`SCCP.v`](./SCCP.v) | Lattice soundness invariant, branch folding, `sccp_cfg_sim`, and `sccp_mcfg` refinement proof |

### 3.4 `SimplifyCFG` — Control-Flow Cleanup (1 file)

| File | Role |
| :--- | :--- |
| [`SimplifyCFG.v`](./SimplifyCFG.v) | Constant branch folding, unreachable-block/phi pruning, linear block coalescing, and soundness proof |

### 3.5 `DCE` — Dead Code & Dead Phi Elimination (3 files)

Dependency order: `DCESpec.v` $\to$ `DCESafety.v` $\to$ `DCE.v`.

| File | Role |
| :--- | :--- |
| [`DCESpec.v`](./DCESpec.v) | Extracted pass (`dce_mcfg`, `dce_mcfg_typ`), liveness fixpoint, and dead instruction/phi sweep |
| [`DCESafety.v`](./DCESafety.v) | Pure `EOU` non-UB / non-side-effect safety proofs for removable instructions |
| [`DCE.v`](./DCE.v) | Simulation proof (`dce_cfg_once_sim`) and top-level `dce_mcfg` soundness theorem |

---

## 4. Pipeline, MCFG Export & Certified Module Merge (7 files)

| File | Role |
| :--- | :--- |
| [`Pipeline.v`](./Pipeline.v) | 7-stage pipeline (`mem2reg -> inline -> mem2reg -> sccp -> simplifycfg -> dce -> simplifycfg`) + I2F theorem |
| [`McfgExport.v`](./McfgExport.v) | Verified front-end resolver (`resolve_for_opt_tle`) and MCFG-to-TLE exporter (`export_mcfg_with_tle`) |
| [`ModuleMergeEqb.v`](./ModuleMergeEqb.v) | Transparent boolean AST equality deciders (`Defined.`) for module-merge verification |
| [`ModuleMergeLink.v`](./ModuleMergeLink.v) | Whole-module linking semantics, slice composition (`validate_module_merge`), and per-pass slice lemmas |
| [`ModuleMergeVDrawCore.v`](./ModuleMergeVDrawCore.v) | Open-world draw-strategy core infrastructure (`Sec 8.0–8.3`) for certified module composition |
| [`ModuleMergeVDrawLift.v`](./ModuleMergeVDrawLift.v) | Refinement lifting across draw strategies and finite memory (`Sec 8.4–8.5`) |
| [`ModuleMerge.v`](./ModuleMerge.v) | TLE/CLI entrypoints (`validate_module_merge_*_tle*`), I2F composition theorems, and facade re-export |

---

## 5. Axiom & Extraction Contract

1. **Kernel `Print Assumptions` contract ([`rocq-ci.yml`](../.github/workflows/rocq-ci.yml)):** All four top-level pass theorems (`Pipeline.optimize_mcfg_I2F_model_refine`, `ModuleMerge.validate_module_merge_parsed_I2F_model_refine`, `ModuleMerge.validate_module_merge_tle_refines`, `ModuleMerge.validate_module_merge_certified_tle_refines`) introduce zero axioms beyond upstream Vellvm 3.0 `vellvm_base` (and zero `Admitted`).
2. **Checked in [`CheckAssumptions.v`](../validator/CheckAssumptions.v)** and compiled under `Set Default Goal Selector "!"`.
3. **OCaml extraction ([`Extract.v`](../vellvm/src/ml/extracted/Extract.v)):** Extracts only the executable specs and exporters (`SimplifyCFG.*`, `DCE.*`, `SCCPSpec.*`, `Mem2RegSpec.*`, `InlineSpec.*`, `Pipeline.*`, `McfgExport.*`, `ModuleMergeLink.validate_module_merge`, `ModuleMerge.*`), keeping OCaml TCB glue minimal in [`verified_opt_fallback.ml`](../vellvm/src/ml/bin/verified_opt_fallback.ml) and [`cert_validator.ml`](../vellvm/src/ml/bin/cert_validator.ml).
