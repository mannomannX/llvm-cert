# llvm-cert (LLVM 23.1.5 Minimal Baseline)

Minimaler, historienfreier Snapshot des offiziellen Releases **[`llvmorg-23.1.5`](https://github.com/llvm/llvm-project/releases/tag/llvmorg-23.1.5)** (Commit `392dfff97d29b59d77e5cac6d4b6ef2585fe7117`, veröffentlicht am 03.11.2026) als Compiler-Basis für die zertifizierte Pipeline (`clang`, `opt`, `lld`, Backends `AArch64` & `RISCV`).

## Enthaltene Komponenten

| Pfad | Zweck |
| :--- | :--- |
| `llvm/` | LLVM Core IR, Optimizer (`opt`), Bitcode-/Backend-Tools (`llc`, `llvm-as`, `llvm-dis`, `llvm-extract`, `llvm-objdump`) |
| `llvm/lib/Target/AArch64`, `RISCV` | Einzige vollständige Codegen-Backends (`ARM/*.td` & `PowerPC/*.td` liegen nur als TableGen-Definitionen für `LLVMTargetParser` bei) |
| `clang/` | C/C++-Frontend zur Erzeugung unoptimierter LLVM-23-IR |
| `lld/` | Linker (`ld.lld` / `lld`) |
| `cmake/` | Gemeinsame LLVM-CMake-Module (`LLVMVersion.cmake` = `23.1.5`) |
| `libc/` (`shared`, `src/__support`, `hdr`, `include`) | Header-only Floating-Point-/Math-Utilities für `LLVMSupport` (`APFloat`) |
| `libunwind/include/` | Header-only Unwind-Definitionen für `lld` |
| `third-party/siphash/` | Header-only SipHash-Implementierung für `LLVMSupport` |

Alle übrigen Subprojekte (`mlir`, `flang`, `lldb`, `bolt`, `polly`, `clang-tools-extra`, `compiler-rt`, `libcxx`, `openmp`, …), alle 21 nicht benötigten Backend-Targets (`X86`, `AMDGPU`, `WebAssembly`, `NVPTX`, `SPIRV`, …) sowie sämtliche Test-, Benchmark-, Doku- und Beispiel-Verzeichnisse wurden entfernt (~93,5 % weniger Dateien: **11.777 statt 180.650 Dateien**).

## Minimaler Release-Build (optimiert für ≤ 12 GB RAM)

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

## Lizenz

Apache License v2.0 with LLVM Exceptions — siehe [`LICENSE.TXT`](./LICENSE.TXT).
