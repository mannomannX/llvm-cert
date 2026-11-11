# Master Plan & Roadmap (`cert-llvm`)

**Target Baseline:** LLVM `23.1.5` (`llvmorg-23.1.5`, released 2026-11-03) + Vellvm (`main` on Rocq `9.1`)  
**Last Updated:** 2026-11-11

---

## Current Progress Snapshot

| Phase | Timeframe | Status | Completion |
| :--- | :--- | :--- | :--- |
| **Phase 1: Repository Setup & Minimal Build** | Weeks 1–2 | **In Progress** | **~50%** (1.1 Done + Vellvm Clean Import Done; 1.2 & 1.3 Pending) |
| **Phase 2: Verified Fallback Core (Rocq)** | Months 1–3 | Not Started *(Foundation Ready)* | **~10%** (Vellvm 3.0/`main` already includes Opaque Pointers `TYPE_Pointer None` & `Theory/`) |
| **Phase 3: Verified Translation Validator** | Months 3–6 | Not Started | **0%** |
| **Phase 4: Orchestration, Backend Check & Audit** | Months 6–9 | Not Started | **0%** |

---

## 1. System Architecture: The 4-Stage Pipeline Model

`cert-llvm` orchestrates compilation **per function** to combine full `-O2` speed with mathematical soundness:

```mermaid
flowchart TD
    Src["Customer Source Code (C / C++ / Rust)"] -->|"clang / rustc\n-O0 -Xclang -disable-O0-optnone"| IR["Stage 1: Unoptimized LLVM 23 IR (input.ll)"]
    IR -->|"opt -O2 (Unmodified LLVM 23.1.5)"| Fast["Stage 2: Fast-Path IR (opt_fast.ll)"]
    IR --> Gate["Stage 3: Gatekeeper\nZ3 Certificate Search + Rocq Proof Checker (cert-validator)"]
    Fast --> Gate
    Gate -->|"Verified (~95–98% of functions)"| Accept["Accept opt_fast.ll"]
    Gate -->|"Rejected (complex loop/vector transforms)"| Safe["Stage 4: Safe-Path\nRocq-Verified Fallback Passes (verified-opt-fallback)\n-> opt_safe.ll"]
    IR -.->|"Fallback input"| Safe
    Accept --> Backend["AArch64 / RISCV Codegen (llc + lld)\n+ Symbolic Backend Disassembly Check"]
    Safe --> Backend
    Backend --> Out["Verified Binary + Signed Audit Report (.proof.json)"]
```

1. **Stage 1 — Frontend (Clean Unoptimized IR):** `clang` or `rustc` compiles customer code with `-O0 -Xclang -disable-O0-optnone` into clean, unoptimized LLVM 23 IR (`input.ll`).
2. **Stage 2 — Fast-Path (Unmodified LLVM 23 `-O2`):** Upstream `opt` optimizes `input.ll` at full speed into `opt_fast.ll`.
3. **Stage 3 — Gatekeeper (Verified Rocq Translation Validator):**
   - An untrusted SMT solver (`Z3`) searches for a semantic equivalence proof between `input.ll` and `opt_fast.ll` and emits a machine-checkable proof certificate (`.cert`).
   - `cert-validator` (100% formally proven in Rocq and extracted to OCaml) checks the certificate against Vellvm semantics.
   - **Pass (~95–98% of functions):** `opt_fast.ll` is accepted.
   - **Fail:** `opt_fast.ll` is discarded.
4. **Stage 4 — Safe-Path (Verified Rocq Fallback Core):** Rejected functions fall back to `input.ll` and pass through `verified-opt-fallback` (core optimization passes written and proven directly in Rocq, producing `opt_safe.ll`), followed by `AArch64` or `RISCV` machine code emission and audit logging.

---

## 2. Technology Stack

| Component | Tool / Baseline | Role in System | License |
| :--- | :--- | :--- | :--- |
| **Compiler Base** | LLVM `23.1.5` (`llvmorg-23.1.5`) | Delivers `clang`, high-speed `opt`, linker `lld`, and `AArch64` & `RISCV` backends | `Apache-2.0 WITH LLVM-exception` |
| **Formal IR Semantics** | Vellvm (`vellvm/`, Rocq `9.1`) | Defines mathematical semantics for LLVM IR instructions, memory provenance, opaque pointers, and poison/UB | `MIT` (`Numeric/`: `LGPL-2.1+`) |
| **Translation Validator** | Rocq + `Z3` / `CVC5` | `Z3` generates equivalence certificates; Rocq-proven `cert-validator` verifies certificates | `Z3`: `MIT`; Checker: `MIT`/`LGPL-3.0` |
| **Fallback Compiler Core** | Rocq Extraction to OCaml | 5–8 core passes (`mem2reg`, `sccp`, `dce`, `simplifycfg`, `inline`) proven in Rocq and compiled to `verified-opt-fallback` | Isolated CLI (`LGPL-3.0` compliant) |
| **Orchestration Driver** | Rust (`cert-llvm`) | Drop-in CLI replacement for `clang`/`opt`, splits modules into functions, drives Fast-Path vs. Safe-Path, signs `.proof.json` | **100% Proprietary** |
| **AI Proof Pipeline** | LLM Agents + `rocq-lsp` / `rocq top` | Automated proof synthesis & repair loop against the Rocq typechecker for Vellvm lemmas and validator rules | Internal Tooling |

See [`licensing-and-boundaries.md`](./licensing-and-boundaries.md) for mandatory commercial license isolation rules and [`business-model-and-ip-strategy.md`](./business-model-and-ip-strategy.md) for the CompCert-style Dual-License, anti-cloning Open-Core split, and GitHub Actions CI strategy.

---

## 3. 4-Phase Implementation Plan & Task Checklist

### Phase 1: Repository Setup & Minimal Build (Weeks 1–2)

- [x] **1.1 Freeze & Prune LLVM 23.1.5 Baseline:**
  - Pinned exact release tag `llvmorg-23.1.5` (`392dfff97d29b59d77e5cac6d4b6ef2585fe7117`), zero Git history.
  - Pruned repository from 180,650 files to 11,776 files (kept `llvm`, `clang`, `lld`, `cmake`, full backends `AArch64` & `RISCV`, plus minimal header/TableGen dependencies).
  - Verified CMake + Ninja configuration and `LLVMTargetParser` / `LLVMSupport` build targets.
- [x] **1.1b Clean Vellvm Import & License Sanitization *(pulled forward)*:**
  - Imported Vellvm (`main`, Rocq 9.1, including restored `src/rocq/Theory/`) into [`../vellvm/`](../vellvm).
  - Stripped all `GPL-3.0+` driver files and `GPL-2.0+` `Camlcoq.ml`; synced `Zbits.v` with upstream CompCert `LGPL-2.1+` and added a clean-room MIT [`Camlcoq.ml`](../vellvm/src/ml/libvellvm/Camlcoq.ml).
- [ ] **1.2 (`TODO`) Server-Optimized Release Build & Rocq Toolchain Setup:**
  - Build `clang`, `opt`, `lld`, `llc`, `llvm-as`, `llvm-dis`, `llvm-extract`, and `llvm-objdump` in `Release` mode (`-DLLVM_TARGETS_TO_BUILD="AArch64;RISCV" -DLLVM_PARALLEL_LINK_JOBS=1` for ≤ 12 GB RAM).
  - Provision Rocq `9.1.x` + OCaml `>= 4.14` (`opam`) environment and verify `make -C vellvm/src` compiles all `.vo` targets and OCaml extraction cleanly.
- [ ] **1.3 (`TODO`) Fix LLVM 23 <-> Vellvm AST Interface (`ir-bridge`):**
  - Implement a lean parser/serializer (OCaml/Rust) translating LLVM 23.1.5 IR / bitcode into Vellvm's `LLVMAst.toplevel_entities` and serializing verified ASTs back to valid LLVM 23.1.5 IR.

---

### Phase 2: Verified Rocq Fallback Core (Months 1–3)

> **Baseline Note:** Inspecting [`LLVMAst.v`](../vellvm/src/rocq/Syntax/LLVMAst.v) confirms that Vellvm 3.0/`main` **already models Opaque Pointers (`TYPE_Pointer None`)**, `bfloat`, and `undef`-free semantics (tested up to LLVM 20). Phase 2.1 therefore focuses specifically on the **LLVM 20 -> 23.1.5 delta** rather than a legacy LLVM 14 rewrite.

- [ ] **2.1 (`TODO`) Lift Vellvm Semantics to Full LLVM 23.1.5:**
  - Add LLVM 21–23 instruction flags & modifiers (`zext nneg`, `or disjoint`, `trunc nuw/nsw`, `icmp samesign`, `getelementptr nusw/nuw`) to `LLVMAst.v`, `Denotation.v`, `Operations.v`, `ShowAST.v`, and `llvm_parser.mly`.
  - Add missing LLVM 23 memory/arithmetic intrinsics in `IntrinsicsDefinitions.v` as required by target C/C++/Rust workloads.
- [ ] **2.2 (`TODO`) Implement & Prove 5 Core Optimization Passes in Rocq:**
  1. `mem2reg` — Promote stack allocations (`alloca` + `load`/`store`) into SSA registers (highest-impact pass).
  2. `sccp` — Sparse Conditional Constant Propagation.
  3. `dce` — Dead Code Elimination.
  4. `simplifycfg` — Control-Flow Graph simplification (dead blocks, constant branches, block merging).
  5. `inline` — Non-recursive / bounded function inlining.
- [ ] **2.3 (`TODO`) Extract Standalone `verified-opt-fallback` Binary:**
  - Extract proven Rocq passes to OCaml and compile into the standalone CLI tool `verified-opt-fallback` (`input.ll -> opt_safe.ll`).

---

### Phase 3: Verified Translation Validator (Months 3–6)

- [ ] **3.1 (`TODO`) Certificate Format & SMT Certificate Generator (`Z3`):**
  - Design a compact, deterministic proof certificate schema (`.cert`) capturing SSA value equivalence, memory state refinement, and UB/poison non-increase (Alive2-style encoding).
  - Build the untrusted `Z3`-backed certificate generator comparing `input.ll` and `opt_fast.ll` per function.
- [ ] **3.2 (`TODO`) 100% Rocq-Proven Proof Checker (`cert-validator`):**
  - Implement and prove soundness in Rocq against Vellvm's `Theory/Equational.v` & `Refinement.v`: if `check_cert fn_src fn_tgt cert = true`, then `fn_tgt` refines `fn_src`.
  - Extract to standalone native CLI binary `cert-validator`.
- [ ] **3.3 (`TODO`) Iterative Rule Expansion (AI-Assisted Proof Loop):**
  - Extend validator rules step-by-step for loop unrolling/rotation, alias/memory forwarding, and `AArch64`/`RISCV` vector idioms.

---

### Phase 4: Orchestration, Backend Assurance & Productization (Months 6–9)

- [ ] **4.1 (`TODO`) Rust Orchestrator (`cert-llvm`):**
  - Build the drop-in CLI driver (`cert-clang` / `cert-llvm`) accepting C, C++, and Rust inputs.
  - Split modules per function (`llvm-extract` / bitcode splitter), run Fast-Path + `cert-validator` in parallel, fall back seamlessly to `verified-opt-fallback` on rejection, and re-link verified functions.
- [ ] **4.2 (`TODO`) Symbolic Backend Checker (IR-to-Assembly for `AArch64` & `RISCV`):**
  - Implement a symbolic disassembler/MC equivalence check validating that emitted `AArch64` and `RISCV` machine instructions match the verified IR semantics.
- [ ] **4.3 (`TODO`) Cryptographically Signed Customer Audit Report (`.proof.json`):**
  - Emit a deterministic, signed per-build verification manifest (e.g., *"97.4% of functions verified via Fast-Path, 2.6% compiled via Rocq Fallback Core — 0 unproven transformations"*), ready for ISO 26262 / DO-178C / IEC 61508 qualification artifacts.

