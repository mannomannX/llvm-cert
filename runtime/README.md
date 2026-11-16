# Freestanding MISRA C:2023 / CERT C Builtin Runtime (`runtime/`)

`runtime/` provides LLVMCert's clean-room, deterministic, freestanding C11/C17 support runtime (`F-27`) for safety-critical bare-metal and RTOS targets (`aarch64-unknown-none-elf`, `riscv64gc-unknown-none-elf`) qualified toward ISO 26262, DO-178C, and IEC 61508.

## Qualification Scope & TCB Role

During Stage 4 (`llc` + `lld`), LLVM lowers aggregate copies, stack-frame zero-initialization (`-ftrivial-auto-var-init=zero`), and 128-bit integer arithmetic (`i128`) into implicit compiler-rt library calls. Linking an unverified system `libgcc` or assembly-optimized `compiler-rt` introduces unbounded loops, target-specific macro assembly, and unverified undefined-behavior edge cases into the target executable.

This directory replaces those implicit backend libcalls with small, auditable, loop-bounded C primitives built strictly under `-ffreestanding -fno-builtin`.

## Directory Layout

- [`include/cert_runtime.h`](./include/cert_runtime.h) — Pure freestanding header (`<stddef.h>` and `<stdint.h>` only, C++ `extern "C"` safe) declaring `cert_*` primitives, portable little-endian `{ uint64_t low; uint64_t high; }` 128-bit types (`cert_u128_t`, `cert_i128_t`), and optional compiler-rt ABI symbol prototypes (`CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES`).
- [`src/mem_builtins.c`](./src/mem_builtins.c) — Freestanding byte-exact memory primitives and standard ABI entrypoints (`!defined(CERT_RUNTIME_HOSTED_TEST)`).
- [`src/int128_builtins.c`](./src/int128_builtins.c) — Constant-bounded (`<= 128` iterations) 128-bit shift, multiply, bit-count, and total division/modulo primitives plus AAPCS64 / RISC-V64 LP64 `__int128` ABI wrappers.
- [`tests/runtime_selfcheck.c`](./tests/runtime_selfcheck.c) — Deterministic freestanding-clean self-check harness covering overlap directions, zero-length `NULL` calls, unsigned `0x80` byte comparison, boundary shifts (`0`, `1`, `63`, `64`, `65`, `127`, `128`), and `INT128_MIN / -1` & `/ 0` division invariants.

## Exported Symbol Inventory

| Category | `cert_*` Deterministic API | Compiler-RT / Freestanding ABI Alias |
| :--- | :--- | :--- |
| Memory copy & move | `cert_memcpy`, `cert_memmove` | `memcpy`, `memmove` |
| Memory fill & compare | `cert_memset`, `cert_memcmp` | `memset`, `memcmp` |
| DSE-immune zeroize | `cert_memzero_explicit` | *(explicit safety call)* |
| 128-bit shifts | `cert_u128_shl`, `cert_u128_lshr`, `cert_i128_ashr` | `__ashlti3`, `__lshrti3`, `__ashrti3` |
| 128-bit multiply | `cert_u128_mul`, `cert_i128_mul` | `__multi3` |
| 128-bit unsigned div/mod | `cert_udivmod128`, `cert_u128_udiv`, `cert_u128_umod` | `__udivmodti4`, `__udivti3`, `__umodti3` |
| 128-bit signed div/mod | `cert_div128`, `cert_mod128`, `cert_i128_sdiv`, `cert_i128_srem` | `__divti3`, `__modti3` |
| 128-bit bit counts | `cert_u128_clz`, `cert_u128_ctz`, `cert_u128_popcount` | `__clzti2`, `__ctzti2`, `__popcountti2` |

## MISRA C:2023 & SEI CERT C Compliance Summary

- **Zero Recursion (`MISRA C:2023 Rule 17.2`, `misc-no-recursion`):** Call graph is a strict acyclic DAG with zero direct or indirect recursion.
- **Zero VLAs & Dynamic Allocation (`MISRA C:2023 Rule 18.8 / Dir 4.12`):** Fixed-size stack locals only (`-Wvla -Werror`).
- **Structured Control Flow (`MISRA C:2023 Rules 15.1, 15.6`):** Zero `goto`, mandatory braces on every `if`/`else`/`for` block (`readability-braces-around-statements`), and isolated declarations (`readability-isolate-declaration`).
- **Pointer-Order & Null Safety (`CERT C ARR36-C`, `EXP34-C`):** Zero-length (`count == 0U`) calls never dereference pointers; `cert_memmove` orders potentially unrelated buffers via `uintptr_t` rather than relational `<`/`>` on raw pointers, and backward copies index `i - 1U` for `i > 0U` without forming out-of-bounds `ptr - 1`.
- **Dead-Store-Immune Wipe (`CERT C MSC06-C`):** `cert_memzero_explicit` writes through `volatile unsigned char *`.
- **Total Overflow-Free Integer Arithmetic (`CERT C INT32-C`, `INT33-C`, `INT34-C`):** All 128-bit signed operations execute on unsigned two-limb magnitudes (`uint64_t`), avoiding `INT128_MIN / -1` overflow UB, shift-width UB (`>= 64` or `>= 128`), and division-by-zero traps (matching RISC-V M-extension architectural semantics: `u / 0 = UINT128_MAX`, `s / 0 = -1`, `x % 0 = x`, `INT128_MIN / -1 = INT128_MIN`, `INT128_MIN % -1 = 0`).
