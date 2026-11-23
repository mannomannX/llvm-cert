---
name: rocq-proof-engineering
description: >-
  Workflow and fast-compute proof tactics for Rocq 9.1 and Vellvm 3.0 in LLVMCert.
  Activate this skill whenever writing, debugging, optimizing, or extracting Rocq (.v)
  definitions, semantics, optimization passes, or translation-validation checkers.
---

# Rocq 9.1 & Vellvm Proof Engineering Workflow

Follow this exact loop whenever working on `.v` files in `vellvm/`, `passes/`, or `validator/`:

## 1. Load Relevant Proof Strategies
Read [`plan/rocq-proof-strategies.md`](../../../plan/rocq-proof-strategies.md) before starting proof work, paying particular attention to:
- **`[PS-01]` Computational Reflection:** Implement passes/validators as `bool`/`option` functions and prove `check ... = true -> refines ...` rather than building dependent `Prop` terms.
- **`[PS-02]` Sub-Second `Qed.` Hygiene:** Use `abstract (zify; lia)` and `compute_this` (`vm_compute`) so closed width constants (`32`, `64`) never blow up kernel `Qed.` checking.
- **`[PS-03]` Width-Indexed `@bit_int w`:** Pin explicit widths (`@repr 32`, `@unsigned 64`) and use `Integers.bit_solve`.
- **`[PS-04]` Equational `ITree` Rewriting:** Never `unfold ITree.bind`; use `setoid_rewrite` with `bind_bind`, `interp_bind`, and `Theory/Equational.v`.
- **`[PS-06]` Fuel-Bounded Iteration:** Use explicit `fuel : nat` with identity/rejection fallback on `0` to avoid `Program Fixpoint` termination proof overhead.

## 2. Incremental & Full Docker Verification
Do **not** invoke full `make -C vellvm/src` on every tactic step (and note `rocq compile` stops at the first error inside a single `.v` file, whereas `make -k` builds all independent modules):
1. Run incremental and full Rocq `9.1` builds locally in Docker image `llvmcert-rocq-env:9.1` using a read-only bind mount (`/src:ro`) copied into container-local `/work` (see [`plan/dev-and-verification-workflow.md`](../../../plan/dev-and-verification-workflow.md)):
   ```bash
   make -C vellvm/src RocqMakefile
   make -C vellvm/src --no-print-directory -f RocqMakefile TIMED=1 -j2 <path/to/File.vo>
   ```
2. Use `-vos` when checking downstream type signatures quickly.
3. After finishing a logical group of lemmas/files, run the full 3-stage `make -C vellvm/src` build (`CORE_VOS`, `real-all -k -j2`, `all -j2`), `rocq check -o`, and forged/mutation suites inside `/work`, then trigger `rocq-ci.yml` after pushing to `main`.

## 3. Mandatory Gate & Knowledge Feedback
1. Run the fast read-only repository verifier (< 1s):
   ```bash
   python scripts/verify_repo_integrity.py
   ```
   Confirm `0 Admitted`, `0 unapproved Axiom`, and OCaml TCB within budget.
2. **Knowledge Capture:**
   - If you encountered an architectural/soundness/semantics finding outside current scope, add an entry to [`plan/feedback.csv`](../../../plan/feedback.csv) (never introduce workarounds or `Admitted`).
   - If you discovered a reusable tactic pattern or speedup that noticeably reduced `Qed.` or proof length, append a concise `[PS-XX]` entry to [`plan/rocq-proof-strategies.md`](../../../plan/rocq-proof-strategies.md).

