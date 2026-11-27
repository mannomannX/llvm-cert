# Agent Operating Rules (`llvm-cert`)

All AI coding agents operating in this repository MUST follow these rules without exception:

1. **Language:** Write all code, Rocq comments, docstrings, CSV entries, commit messages, and Markdown documentation strictly in **English**.
2. **Architecture & Language Discipline:**
   - **Frozen LLVM 23.1.5 Baseline:** Never edit or reformat files under `llvm/`, `clang/`, `lld/`, `cmake/`, `libc/`, `libunwind/`, or `third-party/` unless explicitly instructed and tagged with `[allow-upstream-patch]`.
   - **Mathematical Proofs in Rocq (`9.1`):** All formal semantics, fallback optimization passes (`passes/`), and certificate checkers (`validator/`) live in Rocq with **zero `Admitted`, `admit`, `give_up`, `Abort`, or unapproved `Axiom`s**.
   - **Rust-First / Minimal OCaml (`<= 750 LOC`):** Write all unverified systems tooling and the Phase 1.3 LLVM 23 <-> Vellvm IR bridge (`ir-bridge/`) in High-Assurance **Rust** (`unsafe_code = "forbid"`, zero `unwrap`/`expect`/`panic`). Keep handwritten OCaml strictly to thin extraction glue (`<= 750 LOC` enforced in CI).
   - **CERT C / MISRA C (`c-quality/`):** Any LLVMCert-authored C runtime shims (`runtime/`) or qualification suites must pass [`c-quality/.clang-tidy`](./c-quality/.clang-tidy) and [`c-quality/.clang-format`](./c-quality/.clang-format) with zero warnings.
3. **Structured Findings Ledger (`plan/feedback.csv`) — Mandatory Proactive Logging:**
   - **No workarounds or silent hacks.** Proactively hunt for and log **every** discovered conceptual blindspot, semantic mismatch (LLVM 23 vs. Vellvm 3.0 vs. hardware ABI), compositional/separate-compilation hazard, edge-case bug, security/license risk, or qualification gap as a structured RFC-4180 row (`ID,Category,Section,Finding,Action,Severity,Status,Reference`) in [`plan/feedback.csv`](./plan/feedback.csv).
   - Log newly discovered gaps immediately with `Status=open` (or `in-progress`) and transition to `Status=resolved` only once verified by tests/proofs. When running as one of multiple parallel subagents, include any discovered findings in your completion report to the coordinator if `plan/feedback.csv` is concurrently edited so zero rows are lost or collided.
4. **Rocq Proof Strategy Playbook (`plan/rocq-proof-strategies.md`):**
   - Before writing or modifying any `.v` file in `vellvm/`, `passes/`, or `validator/`, activate the workspace skill `.agents/skills/rocq-proof-engineering/SKILL.md` and consult [`plan/rocq-proof-strategies.md`](./plan/rocq-proof-strategies.md).
   - Append newly discovered fast-compute tactic patterns (`[PS-XX]`) to `plan/rocq-proof-strategies.md`.
5. **Fast Incremental Checks & Read-Only Gates:**
   - Never trigger full LLVM or full 87-file Vellvm rebuilds on single-file edits; compile single targets incrementally and run full builds only at phase/group milestones.
   - **One-Pass Full-File Rocq Diagnostics:** Because `rocq compile` halts at the first error within a `.v` file, always run [`scripts/rocq_onepass_diag.py`](./scripts/rocq_onepass_diag.py) (`opam exec -- python3 -u /work/scripts/rocq_onepass_diag.py /work/vellvm/src /work/<path/to/File.v>`) on edited or newly created `.v` files to collect **all** failing proof/command chunks (`X failing proof/cmd chunks out of Y`) in a single pass and fix them together before compiling `.vo` targets (`make -k -j2`).
   - **Two-Tier Loop vs. Milestone Gate (`.agent/rules/fast_verification_loop.md`):** During iterative edits, use incremental `-j4` target builds plus `run_forged_mc_suite.py --adv-only` (~22s); reserve full `make all`, `rocq check -o`, 26 `Print Assumptions`, and the full `run_forged_mc_suite.py` (`-j4`) for grouped wave/milestone gates.
   - Never create auto-mutating formatting/tagging scripts; all CI gates are strictly read-only.
   - Always run `python scripts/verify_repo_integrity.py` before finishing any task.
6. **Workflow Runbook ([`plan/dev-and-verification-workflow.md`](./plan/dev-and-verification-workflow.md)):**
   - Follow this runbook for Docker Rocq `9.1` builds (`/src:ro` -> `/work`, `rocq check -o`), manual `rocq-ci.yml` triggers on `main`, release-bundle LF checksums, and keeping `Discussion.md` untouched.

