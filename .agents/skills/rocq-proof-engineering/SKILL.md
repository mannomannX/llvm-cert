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

## 2. Incremental Single-File Verification
Do **not** invoke full `make -C vellvm/src` on every tactic step:
1. Compile only the file under active work:
   ```bash
   rocq compile $(make -s -C vellvm/src print-includes) <path/to/File.v>
   ```
2. Use `-vos` when checking downstream type signatures quickly.
3. Run full `make -C vellvm/src` only after finishing a logical group of lemmas/files.

## 3. Mandatory Gate & Knowledge Feedback
1. Run the fast read-only repository verifier (< 1s):
   ```bash
   python scripts/verify_repo_integrity.py
   ```
   Confirm `0 Admitted`, `0 unapproved Axiom`, and OCaml TCB within budget.
2. **Knowledge Capture:**
   - If you encountered an architectural/soundness/semantics finding outside current scope, add an entry to [`plan/feedback.csv`](../../../plan/feedback.csv) (never introduce workarounds or `Admitted`).
   - If you discovered a reusable tactic pattern or speedup that noticeably reduced `Qed.` or proof length, append a concise `[PS-XX]` entry to [`plan/rocq-proof-strategies.md`](../../../plan/rocq-proof-strategies.md).

