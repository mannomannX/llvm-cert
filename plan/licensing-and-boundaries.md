# Commercial Licensing & Architectural Boundaries

To ensure `cert-llvm` remains **100% commercially distributable as a proprietary product**, all contributors and automated agents must maintain the following boundaries:

## 1. Zero-GPL Repository Policy

- **No `GPL` / `AGPL` code** may be added anywhere in this repository.
- Upstream Vellvm's `GPL-3.0+` CLI files (`src/ml/{main,driver,interpreter,frontend,platform,assert,test}.ml`) and CompCert's `GPL-2.0` `Camlcoq.ml` were intentionally excluded during import and replaced by clean-room **MIT** code ([`vellvm/src/ml/libvellvm/Camlcoq.ml`](../vellvm/src/ml/libvellvm/Camlcoq.ml)).
- If `CVC5` is used alongside `Z3` (`MIT`), `CVC5` (`BSD-3-Clause`) **must never** be configured with `--gpl` or optional GPL libraries (`CLN`, `glpk`, `CoCoALib`, `Normaliz`).

## 2. Subprocess Isolation for Extracted Rocq Binaries (`LGPL-2.1` / `LGPL-3.0`)

While Vellvm's core (`Syntax/`, `Semantics/`, `Theory/`, `Utils/`) is **MIT**, Rocq-to-OCaml code extraction pulls definitions from:
- `vellvm/src/rocq/Numeric/*.v` (`LGPL-2.1-or-later`, CompCert machine integers & floats)
- `coq-flocq` (`LGPL-3.0-or-later`, IEEE-754 formalization)
- `rocq-stdlib` / `rocq-equations` (`LGPL-2.1-only`)

Unlike the OCaml compiler runtime, `zarith`, and `menhirLib` (which all grant an explicit static-linking exception), `coq-flocq` and `Numeric/*.v` do **not** include an OCaml static-linking exception.

### Mandatory Architectural Rule
1. **Proprietary Main Product (`cert-llvm` in Rust):** The CLI driver, build orchestrator, LLVM 23 bitcode splitter, Z3 certificate search engine, and `.proof.json` audit signer are kept in separate processes/crates with **zero static or dynamic linking** against LGPL-extracted OCaml libraries. They remain **100% closed-source proprietary**.
2. **Isolated Verification Subprocesses (`cert-validator` & `verified-opt-fallback`):** Invoked by `cert-llvm` strictly as standalone CLI executables over standard files/pipes (`input.ll`, `opt_fast.ll`, `.cert`, `opt_safe.ll`). When distributing `cert-llvm`, provide source or relinkable object files for these two small extracted kernel binaries in accordance with `LGPL-2.1` / `LGPL-3.0` (or map `Integers`/`Floats`/`Stdlib` via Rocq `Extract Constant` to clean-room MIT OCaml/`Zarith` primitives if single-binary proprietary distribution is required).
