# Two-Stage Hardening & Continuous Assurance Strategy (`cert-llvm`)

**Scope:** Post-Implementation Security, Soundness, and Tool-Qualification Hardening (`ISO 26262-8 §11 TCL3` / `DO-178C` & `DO-330 TQL-1` / `IEC 61508 T3`)  
**Repositories:** Public Open-Core (`llvm-cert`) & Private Enterprise (`llvm-cert-enterprise`)

---

## 1. Threat & Fault Model for a Formally Verified Compiler

Empirical studies of verified compilers (e.g., Yang et al., PLDI 2011 on CompCert) establish that kernel-checked Rocq proofs (`0 Admitted`) eliminate miscompilations inside proven passes, shifting **100% of residual soundness, security, and reliability risk** to four concrete boundary zones:

1. **Zone A — Unverified TCB Glue, Parsers, Printers, Orchestration & Cryptography:**
   - OCaml surface frontend/backend (`llvm_lexer.mll`, `llvm_parser.mly`, `Camlcoq.ml`, `IO.ml`, `verified_opt_fallback.ml`, `cert_validator.ml`) and extraction directives (`vellvm/src/ml/extracted/Extract.v`).
   - Rust pipeline boundaries: `ir-bridge` (FP hex rewriting, per-function `split`/`merge`, `#N`/`!N` remapping), `cert-llvm` (`orchestrator.rs`, TOCTOU scratch-file handling, CLI flag filtering in `SafetyDriverProfile`), and `cert-attestation` (`ed25519.rs` malleability, canonical `.proof.json` encoding).
2. **Zone B — Specification-vs.-Silicon Semantics Gap:**
   - Divergences between Vellvm's Rocq IR/memory model (`Denotation.v`, `DynamicValues.v`, `MemoryBytes.v`, `Sizeof.v`) and actual LLVM 23 `llc`/`lld` execution on `AArch64` and `RISCV` targets.
3. **Zone C — Vacuous or Over-Constrained Top-Level Theorems:**
   - Top-level Rocq theorems carrying hidden assumptions, overly restrictive preconditions, unexamined helper definitions, or `Extract Inlined Constant` overrides that diverge from Rocq definitions.
4. **Zone D — Adversarial Inputs, Forged Witnesses & Completeness Cliffs:**
   - **Soundness Exploits:** Crafted `(src.ll, miscompiled_tgt.ll, forged.cert)` triples attempting to trick `cert-validator` into returning exit code `0`.
   - **Resource / Availability Attacks:** Deeply nested S-expressions (`>1,024` depth), oversized `.cert`/`.ll` payloads, path-traversal function names, or Z3 solver hangs.
   - **Completeness Regressions:** Valid embedded C/Rust workloads failing parsing or unnecessarily dropping from Fast-Path (`opt -O2` + `cert-validator`) to Safe-Path (`verified-opt-fallback`).

---

## 2. The Four Assurance Layers ("Agents Build Permanent Oracles")

Rather than choosing between one-off bug-hunting agent swarms (which find conceptual blindspots once but provide zero regression protection) and standard compiler test suites (which execute only honest `-O2` + `Z3` outputs and never test forged certificates), `cert-llvm` combines **four permanent layers**:

### Layer 1: Mechanical Theorem & TCB Assumption Gate (Closes Zone C)
- **Kernel Assumption Gate (`CheckAssumptions.v` & `rocq-ci.yml`):** Automated CI gate invoking `Print Assumptions` on top-level soundness theorems (`I2F_toplevel.model_refine`, `Pipeline.optimize_mcfg_I2F_model_refine`, `ModuleMerge.validate_module_merge_*_refines`, `AigLrat.check_lrat_unsat_sound`, `AlgRules.check_expr_refines_with_lrat_sound`, and `CertValidator.validate_tle_pair_with_cert_str_sound`), enforcing that `AigLrat` remains `"Closed under the global context"` and `CertPasses`/`CertValidator` introduce `0` custom axioms beyond the 5 audited upstream Vellvm 3.0 classical stdlib axioms (`F-05`; `Eqdep.Eq_rect_eq.eq_rect_eq` excluded from `AlgRules`/`CertValidator`).
- **Extraction Directive Audit:** Line-by-line verification of every `Extract Constant` / `Extract Inlined Constant` directive in `vellvm/src/ml/extracted/Extract.v` and `Camlcoq.ml` against Rocq `9.1` types and evaluation semantics.

### Layer 2: Adversarial Forgery, Mutation & Crypto Exploit Suite (Closes Zones A & D)
- **Negative / Forged-Certificate Corpus (`cert-validator`):** Curated + property-generated corpus of invalid and malicious `(src.ll, buggy_tgt.ll, forged.cert)` triples covering:
  - Poison/UB laundering (`nsw`/`nuw`/`exact`/`disjoint`/`samesign`/`noundef` erasure or target invention),
  - Target-invented `getelementptr inbounds` (`F-21`) and fast-math flags (`F-17`),
  - Corrupted or circular `AigLrat` LRAT resolution chains and width-confused DAG nodes,
  - Swapped CFG branch targets, dropped side-effecting `CallE`/`MemoryE` events, and stack-slot aliasing,
  - SHA-256 binding mismatches, truncated/overlong inputs, null bytes, and deep S-expression nesting bombs.
  - **Strict Invariant:** Every negative case MUST exit non-zero cleanly with zero crashes, panics, or stack overflows.
- **Wycheproof & Orchestrator Security Suite (`llvm-cert-enterprise`):**
  - Project Wycheproof Ed25519 edge-case vectors (`S >= L` malleability, small-order points `A`/`R`, bit-flipped signatures, canonical JSON tampering) against `cert-attestation`.
  - Adversarial CLI flag-smuggling (`-Xclang`, `-mllvm`, response files), symlink/path-traversal function names, and scratch-directory isolation tests against `cert-llvm`.

### Layer 3: Differential Execution Fuzzing & Real-World Embedded Corpus (Closes Zone B)
- **Differential Execution Harness (`QEMU aarch64` & `QEMU riscv64`):**
  - Randomized UB-free C and LLVM IR generators (`Csmith` / `YARPGen` / `proptest` IR synthesis) compiled through:
    1. Reference unoptimized baseline (`clang -O0`),
    2. `cert-llvm -O2` (exercising `opt -O2` + `Z3` + `cert-validator`),
    3. `cert-llvm` forced Safe-Path (`verified-opt-fallback`),
    and executed under `qemu-aarch64` and `qemu-riscv64` (plus reference Vellvm semantics checks where applicable). Any output, exit-code, or memory-checksum divergence triggers automatic test-case reduction and a `critical` `feedback.csv` entry.
- **Real-World Embedded Qualification Corpus & Fast-Path Telemetry:**
  - License-clean embedded workloads (`runtime/` self-checks, Embench-IoT / CoreMark-class kernels, fixed-point/control-loop DSP routines, cryptographic primitives, and curated C torture tests).
  - Automated `.proof.json` telemetry tracking the **Fast-Path vs. Safe-Path certification ratio (%)** and `static_stack_bytes` across releases to prevent silent completeness cliffs.

### Layer 4: Domain-Isolated 4-Persona Red-Team Audits
Targeted adversarial agent reviews are run across strictly separated attack surfaces rather than unfocused whole-repo scans. Every confirmed finding MUST be logged in `plan/feedback.csv` (and/or `llvm-cert-enterprise/plan/feedback.csv`) **and** converted into a permanent automated regression test in Layers 1–3:

1. **Persona 1 — Theorem & Extraction Auditor:** Attacks top-level Rocq theorem statements, preconditions, `Extract.v`, and `Camlcoq.ml` looking for vacuity or model/extraction mismatches.
2. **Persona 2 — Certificate Forger:** Actively constructs miscompiled `tgt.ll` + forged `.cert` witnesses attempting to bypass `CertFormat.v`, `AigLrat.v`, `AlgRules.v`, `CertValidator.v`, or `cert_validator.ml`.
3. **Persona 3 — Parser & IR-Bridge Desync Hunter:** Hunts grammar, attribute, literal, alignment, and linkage asymmetries across Clang 23, `ir-bridge`, `llvm_lexer.mll`/`llvm_parser.mly`, and `ShowAST.v`/`McfgExport.v`.
4. **Persona 4 — Orchestrator, Runtime & Crypto Security Breaker:** Attacks `cert-llvm` subprocess/filesystem boundaries, `SafetyDriverProfile` flag filtering, `cert-attestation` Ed25519/JSON verification, and `runtime/` C boundary conditions.

---

## 3. Two-Stage Execution Roadmap

### Prerequisite Baseline (Current Step)
- Complete Phase `3.2` (`validator/*.v` + `cert-validator` CLI) and achieve **100% green GitHub Actions CI** across both `llvm-cert` (`quality-gate.yml` + `rocq-ci.yml`) and `llvm-cert-enterprise` (`Enterprise Rust Quality & Security Gate`).

### Stage A — Immediate High-Leverage TCB & Adversarial Hardening
1. Add `CheckAssumptions.v` to `rocq-ci.yml` and audit `Extract.v` / `Camlcoq.ml` (**Layer 1**).
2. Build and wire the **Adversarial Forged-Certificate Corpus** (`cert-validator`) and **Wycheproof / CLI-Security Suite** (`cert-attestation` + `cert-llvm`) into CI (**Layer 2**).
3. Run the **4-Persona Red-Team Audit** (**Layer 4**) end-to-end across Stage 1 -> Stage 4, logging every finding in `feedback.csv`, remediating root causes cleanly, and locking each fix with a regression test.

### Stage B — Scale Differential Fuzzing, Silicon Emulation & Qualification Corpus
1. Build the automated **Differential Execution Harness** (`clang -O0` vs. `cert-llvm -O2` vs. `verified-opt-fallback` under `qemu-aarch64` and `qemu-riscv64`) + `proptest`/`YARPGen`/`Csmith` runners (**Layer 3a**).
2. Integrate the **Embedded Benchmark & Torture Corpus** with `.proof.json` Fast-Path ratio and stack-bound regression tracking in CI / scheduled workflows (**Layer 3b**).
