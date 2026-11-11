# Code Quality Standards, Agent Knowledge System & High-Performance CI Architecture

This document defines how `LLVMCert` (`llvm-cert` + `llvm-cert-enterprise`) enforces **safety-critical ("MISRA-grade") engineering discipline**, prevents IP/license contamination, guides AI agents systematically, and runs near-dedicated-server-speed CI on stateless GitHub Actions runners.

---

## 1. Multi-Language Quality & Safety Standards

Because `LLVMCert` is a certified compiler targeting ISO 26262 / DO-178C / IEC 61508 workloads, each language in the stack is restricted to a sharply defined role and enforced by automated, **strictly read-only** gates:

| Layer / Directory | Language | Role | Enforced "MISRA-Grade" Standard & Tooling |
| :--- | :--- | :--- | :--- |
| `llvm/`, `clang/`, `lld/` | C++17 (Upstream) | Frozen `llvmorg-23.1.5` compiler & `AArch64`/`RISCV` backends | **Frozen Upstream Rule:** `scripts/verify_repo_integrity.py` rejects any diff unless commit carries `[allow-upstream-patch]`. Never custom-reformatted. |
| `vellvm/`, `passes/`, `validator/` | **Rocq `9.1`** | Formal IR semantics, Safe-Path passes, `cert-validator` proof checker | **Mathematical MISRA:** `0` `Admitted`/`admit`/`give_up`/`Abort` and `0` unapproved `Axiom`s (`verify_repo_integrity.py`) + independent kernel check (`rocq chk`). |
| `llvm-cert-enterprise` & `ir-bridge/` | **Rust (`edition = "2024"`)** | CLI driver, Z3 witness synthesis, `.proof.json` signing, Phase 1.3 IR bridge | **High-Assurance Rust:** `unsafe_code = "forbid"`, `unwrap`/`expect`/`panic`/`todo`/`indexing_slicing`/lossy casts = `"deny"`, `rustfmt --check`, `cargo-deny` license/CVE gate. |
| `vellvm/src/ml/` | **OCaml (`4.14+`)** | **Minimal extraction glue ONLY** (`Camlcoq.ml`, Menhir lexer/parser, CLI shims) | **Hard TCB Budget:** Capped at `<= 750` handwritten LOC repository-wide (`verify_repo_integrity.py`) + `.ocamlformat`. Zero unverified passes or drivers in OCaml. |
| `runtime/`, `c-quality/` | **C17** | Freestanding target runtime shims & qualification suites | **SEI CERT C & MISRA C Alignment:** `c-quality/.clang-tidy` (`cert-*`, `bugprone-*`, `clang-analyzer-*`, `WarningsAsErrors: '*'`) + `clang-format --dry-run --Werror`. |

---

## 2. Agent Knowledge Base & Progressive Discovery System

To ensure AI coding and proof agents adhere to strict rules without inventing workarounds or burning context tokens, both repositories implement a **3-layer progressive discovery architecture**:

1. **Always-On Workspace Rules (`AGENTS.md`):**
   - Root [`AGENTS.md`](../AGENTS.md) (and `D:\LLVMCert-Enterprise\AGENTS.md`) is loaded automatically on every agent turn (`< 3.5 KB`).
   - Scoped [`vellvm/AGENTS.md`](../vellvm/AGENTS.md) loads hierarchically **only** when an agent reads or edits files inside `vellvm/`.
2. **Structured Audit & Findings Ledger ([`plan/feedback.csv`](./feedback.csv)):**
   - Schema: `ID,Category,Section,Finding,Action,Severity,Status,Reference` (validated on every commit by `scripts/verify_repo_integrity.py`).
   - Whenever an agent discovers a security issue, soundness subtlety, license edge case, or performance bottleneck outside its immediate task, it logs a structured `F-XX` entry in `plan/feedback.csv` instead of introducing silent workarounds or self-discussion comments.
3. **Living Rocq Proof Playbook ([`plan/rocq-proof-strategies.md`](./rocq-proof-strategies.md)) + On-Demand Skill ([`.agents/skills/rocq-proof-engineering/SKILL.md`](../.agents/skills/rocq-proof-engineering/SKILL.md)):**
   - Uses progressive disclosure (zero context cost during Rust/C/CMake work; full workflow activated automatically on Rocq tasks).
   - Captures empirically fast proof patterns (`[PS-01]` boolean reflection, `[PS-02]` sub-second `Qed.` via `abstract`/`vm_compute`, `[PS-03]` width-indexed `@bit_int w`, `[PS-04]` opaque `ITree` equational rewriting, `[PS-06]` fuel-bounded passes, `[PS-07]` single-file incremental `rocq compile`).

---

## 3. High-Performance Multi-Tier CI Architecture

Directly addressing stateless GitHub Actions runner bottlenecks (cold VM startups, slow GNU `ld` linking, serial test execution, and heavy rebuilds on minor edits), CI is split into **three event-scoped tiers**:

### Tier 1 — Instant Gate (`quality-gate.yml` & `llvm-cert-enterprise/ci.yml`, ~15–30s on every push/PR)
- **Single Combined Job:** Runs secret scan -> `verify_repo_integrity.py` -> `cargo fmt --check` -> `cargo clippy --no-deps` -> `cargo-nextest` -> `cargo-deny` sequentially in **one runner VM** (eliminating 3x container spin-up and cache download overhead).
- **Ultra-Fast Rust Linking & Caching:**
  - `debug = "line-tables-only"` in `Cargo.toml` shrinks debug symbols by ~70% while keeping full file/line stack traces.
  - `rui314/setup-mold@v1` injects the `mold` linker dynamically on Linux CI runners (preserving 100% local portability on Windows/macOS).
  - `taiki-e/install-action@v2` installs precompiled `cargo-nextest` in ~1s (`--no-tests=pass`) for parallel test execution.
  - `Swatinem/rust-cache@v2` uses isolated `shared-key` namespaces (`enterprise-ci-check` vs. `public-ir-bridge-check`) and `CARGO_INCREMENTAL=0` to prevent cache bloat and cross-job eviction.
  - *Deliberate Omission:* `jlumbroso/free-disk-space` is **not** run in Tier 1 because reclaiming 15 GB takes ~60s while Rust checks need < 1 GB and finish in ~25s.

### Tier 2 — Formal Verification CI (`rocq-ci.yml`, PRs touching `vellvm/passes/validator`, milestone tags & manual dispatch)
- Respects incremental build discipline: routine documentation or Rust commits never trigger 87-file Rocq builds.
- Caches both the full `opam` switch (`ocaml/setup-ocaml@v3` pinned to `vellvm/rocq-vellvm.opam`) and compiled `.vo` proof objects (`actions/cache@v4`), followed by `rocq chk` kernel verification.

### Tier 3 — LLVM 23.1.5 SDK Release Build (`llvm-toolchain-build.yml`, `toolchain-*` tags & manual dispatch ONLY)
- Runs `jlumbroso/free-disk-space` (guarded by `vars.CERT_RUNNER == ''` so self-hosted servers are never touched), `hendrikmuhs/ccache-action@v1.2` (`2 GB`), `-DLLVM_USE_LINKER=lld`, and `-DLLVM_PARALLEL_LINK_JOBS=1` (`AArch64;RISCV`), packaging `llvm-cert-sdk-23.1.5-linux-x86_64.tar.zst`.

### Seamless Self-Hosted Server Toggle (`vars.CERT_RUNNER`)
Every workflow uses:
```yaml
runs-on: ${{ vars.CERT_RUNNER || 'ubuntu-latest' }}
```
- **Default (`CERT_RUNNER` unset):** Uses GitHub's free `ubuntu-latest` (4 vCPU / 16 GB RAM) on the public repo and cached fast checks on the private repo.
- **Dedicated NVMe Server Upgrade:** Registering your Linux server as a GitHub Self-Hosted Runner and setting repository variable `CERT_RUNNER=self-hosted` switches builds to persistent local NVMe `target/` and `ccache` storage with **zero workflow file changes**.

