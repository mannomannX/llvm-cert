# Commercial Licensing & Architectural Boundaries

LLVMCert (`cert-llvm`) uses a **CompCert-style Dual-License** ([`/LICENSE`](../LICENSE)): all original LLVMCert code, proofs, passes, and modifications are available under a **Non-Commercial Evaluation & Research License** on GitHub and require a paid **Commercial Software License Agreement** for any commercial or production use (see [`business-model-and-ip-strategy.md`](./business-model-and-ip-strategy.md)).

To ensure LLVMCert can legally grant commercial licenses without copyleft contamination, all contributors and automated agents must maintain the following boundaries:

## 1. Zero-GPL Repository Policy

- **No `GPL` / `AGPL` code** may be added anywhere in this repository.
- Upstream Vellvm's `GPL-3.0+` CLI files (`src/ml/{main,driver,interpreter,frontend,platform,assert,test}.ml`) and CompCert's `GPL-2.0` `Camlcoq.ml` were intentionally excluded during import and replaced by clean-room LLVMCert dual-licensed code ([`vellvm/src/ml/libvellvm/Camlcoq.ml`](../vellvm/src/ml/libvellvm/Camlcoq.ml)).
- If `CVC5` is used alongside `Z3` (`MIT`), `CVC5` (`BSD-3-Clause`) **must never** be configured with `--gpl` or optional GPL libraries (`CLN`, `glpk`, `CoCoALib`, `Normaliz`).

## 2. Subprocess Isolation for Extracted Rocq Binaries (`LGPL-2.1` / `LGPL-3.0`)

While Vellvm's core (`Syntax/`, `Semantics/`, `Theory/`, `Utils/`) is **MIT** and its surface IR lexer/parser (`llvm_lexer.mll`, `llvm_parser.mly`) is **ISC**, Rocq-to-OCaml code extraction pulls definitions from:
- `vellvm/src/rocq/Numeric/*.v` (`LGPL-2.1-or-later`, CompCert machine integers & floats)
- `coq-flocq >= 4.2.0` (`LGPL-3.0-or-later`, IEEE-754 floating-point formalization declared in [`vellvm/rocq-vellvm.opam`](../vellvm/rocq-vellvm.opam))
- `rocq-stdlib` / `rocq-equations` (`LGPL-2.1-only`)

Unlike the OCaml compiler runtime, `zarith`, and `menhirLib` (which all grant an explicit static-linking exception), `coq-flocq` (`LGPL-3.0-or-later`) and CompCert `Numeric/*.v` (`LGPL-2.1-or-later`) do **not** include an OCaml static-linking exception.

### Mandatory Architectural & LGPL Combined-Work Rules
1. **Proprietary Main Product (`cert-llvm` & `ir-bridge` in Rust):** The CLI driver, build orchestrator, LLVM 23 module splitter/merger (`ir-bridge`), Z3 certificate search engine, and `.proof.json` audit signer live in separate processes/crates with **zero static or dynamic linking** against LGPL-extracted OCaml libraries. They remain **100% closed-source proprietary** (dual-licensed under `/LICENSE`).
2. **Isolated Verification Subprocesses (`cert-validator` & `verified-opt-fallback`):** Invoked by `cert-llvm` strictly as standalone CLI executables over standard files/pipes (`input.ll`, `opt_fast.ll`, `.cert`, `opt_safe.ll`).
3. **LGPL-2.1 §6 & LGPL-3.0 §4(d)-(e) Relinking & Debugging Compliance:**
   - Every binary distribution of `verified-opt-fallback` and `cert-validator` ships complete corresponding source code for `coq-flocq`, CompCert `Numeric/*.v`, and `rocq-stdlib` together with relinkable OCaml object/archive artifacts (`.cmi`, `.cmx`, `.cmxa`, `.cma`, `.a`/`.o` and Dune/linker build scripts) so licensees can modify those LGPL libraries and relink updated `verified-opt-fallback` and `cert-validator` executables.
   - [`/LICENSE`](../LICENSE) §§2(d), 3, and 6 contain an explicit **LGPL Combined-Work Carve-Out** guaranteeing customer rights to modify `coq-flocq` and CompCert `Numeric`, relink the two isolated OCaml helper executables, and reverse-engineer those two isolated executables strictly to debug such LGPL library modifications without breaching or terminating the LLVMCert license or weakening proprietary protection of `cert-llvm`.

