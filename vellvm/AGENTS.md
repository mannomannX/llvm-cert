# Vellvm & Rocq 9.1 Directory Rules (`vellvm/`)

When editing or adding files inside `vellvm/` (or companion Rocq directories `passes/` and `validator/`):

1. **Read the Fast-Compute Playbook First:** Consult [`../plan/rocq-proof-strategies.md`](../plan/rocq-proof-strategies.md) before writing nontrivial tactics.
2. **Key Vellvm 3.0 Conventions:**
   - Machine integers in [`src/rocq/Numeric/Integers.v`](./src/rocq/Numeric/Integers.v) are **width-indexed** (`Context {wordsize: positive}`, `@bit_int 32`, `@bit_int 64`, `@repr 64`, `@unsigned 32`) — do not reference legacy CompCert `Int.int` / `Int64.int` functors.
   - Pointers in [`src/rocq/Syntax/LLVMAst.v`](./src/rocq/Syntax/LLVMAst.v) already support LLVM 23 opaque pointers via `TYPE_Pointer None`.
   - Keep `ITree.bind`, `interp`, and `translate` opaque to `cbn`/`simpl`; rewrite using equational monad laws (`bind_bind`, `interp_bind`, `Theory/Equational.v`) and isolate `paco` (`pcofix`) to CFG loop back-edges.
3. **License & TCB Hygiene:**
   - Zero `GPL` code allowed anywhere in `vellvm/`. `LGPL-2.1-or-later` is restricted strictly to `src/rocq/Numeric/*.v`.
   - Handwritten `.ml`/`.mli` files outside `src/ml/extracted/` are capped at `750` total LOC across the repository.
4. **Incremental Verification:**
   - Compile only the modified `.v` file during iteration (`rocq compile $(make -s -C vellvm/src print-includes) path/to/File.v`), and run `python scripts/verify_repo_integrity.py` to verify zero `Admitted` / unapproved `Axiom`s.

