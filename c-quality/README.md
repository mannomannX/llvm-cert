# CERT C / MISRA C Quality Baseline (`c-quality/`)

This directory holds the strict static-analysis and formatting rules enforced on all **LLVMCert-authored C code** (such as freestanding target runtime shims in `runtime/` or qualification test harnesses for ISO 26262 / DO-178C / IEC 61508):

- [`.clang-tidy`](./.clang-tidy) — Enforces SEI **CERT C** (`cert-*`), `bugprone-*`, Clang Static Analyzer (`clang-analyzer-*`), mandatory braces (`MISRA C Dir 4.1 / Rule 15.6`), and `WarningsAsErrors: '*'`.
- [`.clang-format`](./.clang-format) — Deterministic formatting with `InsertBraces: true` and 100-column limit (checked strictly in read-only `--dry-run --Werror` mode in CI).

> **Frozen Upstream Rule:** Upstream LLVM/Clang/LLD C++ sources (`llvm/`, `clang/`, `lld/`) are frozen at `llvmorg-23.1.5` and are deliberately excluded from custom reformatting or linting to preserve zero-conflict upstream upgrades.
