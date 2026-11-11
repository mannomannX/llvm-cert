# llvm-cert (LLVM 23.1.5 + Vellvm Verified Compiler Baseline)

Minimal, history-free baseline combining:
1. **[`llvmorg-23.1.5`](https://github.com/llvm/llvm-project/releases/tag/llvmorg-23.1.5)** (commit `392dfff97d29b59d77e5cac6d4b6ef2585fe7117`, released 2026-11-03) — compiler frontend (`clang`), high-speed optimizer (`opt`), linker (`lld`), and `AArch64` + `RISCV` backends.
2. **[`vellvm/vellvm`](https://github.com/vellvm/vellvm)** (`main` @ `1d651e7a391c`, Rocq 9.1 with restored `Theory/` meta-theory) — formal LLVM IR semantics, ITree infrastructure, and OCaml extraction, cleaned of all GPLv2/GPLv3 files for commercial use.

See **[`plan/README.md`](./plan/README.md)** for the full 4-phase architecture roadmap, **[`plan/licensing-and-boundaries.md`](./plan/licensing-and-boundaries.md)** for architectural license isolation, **[`plan/business-model-and-ip-strategy.md`](./plan/business-model-and-ip-strategy.md)** for the CompCert-style dual-license & Open-Core CI strategy, **[`plan/code-quality-and-ci.md`](./plan/code-quality-and-ci.md)** for our High-Assurance Rust / CERT C / Mathematical Rocq gates, **[`plan/rocq-proof-strategies.md`](./plan/rocq-proof-strategies.md)** for fast-compute Rocq 9.1 proof strategies, and **[`plan/feedback.csv`](./plan/feedback.csv)** for the structured audit ledger.

## Repository Layout

| Path | License | Purpose |
| :--- | :--- | :--- |
| `llvm/` | `Apache-2.0 WITH LLVM-exception` | LLVM Core IR, optimizer (`opt`), bitcode/backend tools (`llc`, `llvm-as`, `llvm-dis`, `llvm-extract`, `llvm-objdump`) |
| `llvm/lib/Target/{AArch64,RISCV}` | `Apache-2.0 WITH LLVM-exception` | Full codegen backends (`ARM/*.td` & `PowerPC/*.td` included only as TableGen specs for `LLVMTargetParser`) |
| `clang/` | `Apache-2.0 WITH LLVM-exception` | C/C++ frontend emitting unoptimized LLVM 23 IR |
| `lld/` | `Apache-2.0 WITH LLVM-exception` | Linker (`ld.lld` / `lld`) |
| `cmake/` | `Apache-2.0 WITH LLVM-exception` | Shared LLVM CMake modules (`LLVMVersion.cmake` = `23.1.5`) |
| `libc/{shared,src/__support,hdr,include}` | `Apache-2.0 WITH LLVM-exception` | Header-only floating-point/math utilities required by `LLVMSupport` (`APFloat`) |
| `libunwind/include/` | `Apache-2.0 WITH LLVM-exception` | Header-only unwind definitions required by `lld` |
| `third-party/siphash/` | `Apache-2.0 WITH LLVM-exception` | Header-only SipHash implementation required by `LLVMSupport` |
| `vellvm/src/rocq/{Syntax,Semantics,Theory,Utils}` | `MIT` | Formal LLVM IR AST, Interaction Trees semantics, memory model, and equational meta-theory |
| `vellvm/src/rocq/Numeric/` | `LGPL-2.1-or-later` | CompCert machine integer (`Integers.v`, `Zbits.v`) and IEEE-754 float (`Floats.v`) formalizations (`Zbits.v` synced with upstream CompCert commit `04f499c632a7`) |
| `vellvm/src/ml/{extracted,libvellvm}` | `MIT` / `ISC` | Rocq-to-OCaml extraction, LLVM IR lexer/parser/printer, and clean-room [`Camlcoq.ml`](./vellvm/src/ml/libvellvm/Camlcoq.ml) (`<= 750` handwritten OCaml LOC cap) |
| `c-quality/` | `LLVMCert Dual-License` | SEI CERT C / MISRA C `.clang-tidy` & `.clang-format` baseline for freestanding runtime shims |
| `scripts/verify_repo_integrity.py` | `LLVMCert Dual-License` | Fast (< 1s) read-only CI gate verifying licenses, zero `Admitted`/unapproved `Axiom`s, OCaml TCB cap, and `plan/feedback.csv` |

All unneeded LLVM subprojects (`mlir`, `flang`, `lldb`, `bolt`, `polly`, `clang-tools-extra`, `compiler-rt`, `libcxx`, `openmp`, …), 21 unneeded backend targets (`X86`, `AMDGPU`, `WebAssembly`, `NVPTX`, `SPIRV`, …), all test/benchmark/doc suites, and all GPLv2/GPLv3 driver files in Vellvm have been removed.

## Minimal LLVM 23.1.5 Release Build (Optimized for ≤ 12 GB RAM)

```bash
cmake -G Ninja -S llvm -B build \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS="clang;lld" \
  -DLLVM_TARGETS_TO_BUILD="AArch64;RISCV" \
  -DLLVM_PARALLEL_LINK_JOBS=1 \
  -DLLVM_INCLUDE_TESTS=OFF \
  -DLLVM_INCLUDE_EXAMPLES=OFF \
  -DLLVM_INCLUDE_BENCHMARKS=OFF \
  -DLLVM_INCLUDE_DOCS=OFF \
  -DLLVM_INCLUDE_RUNTIMES=OFF \
  -DLLVM_INCLUDE_UTILS=OFF

cmake --build build --target clang opt lld llc llvm-as llvm-dis llvm-extract llvm-objdump
```

## License

- **LLVMCert Original Code, Proofs & Modifications:** Dual-licensed under the **LLVMCert Non-Commercial Evaluation & Research License** and a separate **LLVMCert Commercial Software License Agreement** (mandatory for any commercial or production use) — see [`LICENSE`](./LICENSE).
- **Upstream LLVM / Clang / LLD (`23.1.5`):** Apache License v2.0 with LLVM Exceptions — see [`LICENSE-LLVM.TXT`](./LICENSE-LLVM.TXT).
- **Upstream Vellvm Components:** MIT License (with `vellvm/src/rocq/Numeric/` under `LGPL-2.1-or-later`) — see [`vellvm/LICENSE.md`](./vellvm/LICENSE.md).
