# Development & Verification Workflow (`llvm-cert`)

This runbook documents the end-to-end engineering, proof-checking, CI, and release-bundle workflow for `mannomannX/llvm-cert`.

---

## 1. Change-Scope & Verification Matrix

| Changed Paths | Mandatory Local Checks (Read-Only) | Required GitHub Actions Workflow |
| :--- | :--- | :--- |
| `vellvm/src/rocq/**`, `passes/**`, `validator/**`, `vellvm/src/ml/**` | `python scripts/verify_repo_integrity.py`, Docker Rocq `9.1` compile + OCaml extraction + `dune build` + `rocq check -o` + `Print Assumptions` + forged/mutation/`--check-lrat` gates | `quality-gate.yml` (auto) + **`rocq-ci.yml` (manual dispatch on `main` push)** |
| `ir-bridge/**` | `python scripts/verify_repo_integrity.py`; inside `ir-bridge/`: `cargo fmt --all -- --check`, `cargo clippy --workspace --all-targets --no-deps -- -D warnings`, `cargo test --workspace`, `cargo deny check licenses advisories bans sources` | `quality-gate.yml` (auto) |
| `runtime/**`, `c-quality/**` | `python scripts/verify_repo_integrity.py`, `clang-format --style=file:c-quality/.clang-format --dry-run --Werror`, `clang-tidy --config-file=c-quality/.clang-tidy`, `runtime_selfcheck.c`, `stage1_conformance.c` | `quality-gate.yml` (auto) |
| `plan/**`, `scripts/**`, `AGENTS.md`, `.github/workflows/**` | `python scripts/verify_repo_integrity.py` (+ RFC-4180 CSV validation on `plan/feedback.csv`) | `quality-gate.yml` (auto) |
| `llvm/`, `clang/`, `lld/`, `cmake/`, `libc/`, `libunwind/`, `third-party/` | **FROZEN UPSTREAM:** Do not modify unless explicitly instructed with `[allow-upstream-patch]` | `llvm-toolchain-build.yml` (manual/tag only) |

---

## 2. Local Rocq 9.1 Compilation, Extraction & Kernel Check via Docker

Because `LLVMCert` runs on Windows while Rocq `9.1` / Vellvm / OCaml `4.14` dependencies run on Linux, compile and verify Rocq proofs locally using Docker image `llvmcert-rocq-env:9.1` (if missing, build an Ubuntu/OCaml `4.14` container with `opam install -y --deps-only ./vellvm/rocq-vellvm.opam`).

### Critical Container Isolation Rules

1. **Always mount the repository read-only (`-v D:\LLVMCert:/src:ro`)** and copy source directories (`vellvm`, `passes`, `validator`, `scripts`, `LICENSE`) into container-local `/work`.
   - Prevents `.vo`, `.glob`, `.aux`, `_build`, and `RocqMakefile` build artifacts from polluting the host git working tree.
   - Avoids slow Windows NTFS bind-mount compilation I/O.
2. **Incremental vs. Full Builds:**
   - `rocq compile` halts at the first error within a single `.v` file.
   - When iterating on one file, compile that target incrementally instead of rebuilding all theories:
     ```bash
     make -C vellvm/src RocqMakefile
     make -C vellvm/src --no-print-directory -f RocqMakefile TIMED=1 -j2 <path/to/File.vo>
     ```
   - Use `make ... -k -j2` to build all independent `.v` modules in parallel without stopping on the first unrelated failure.
3. **Always finish with a full 3-stage Docker verification** before pushing Rocq/OCaml changes (never rely solely on incremental single-file checks at handoff).

### Full Local Docker Verification Sequence

Launch a container with `llvmcert-rocq-env:9.1` mounting `D:\LLVMCert:/src:ro`, copy into `/work`, and run the exact stages used by `.github/workflows/rocq-ci.yml`:

```bash
rm -rf /work && mkdir -p /work
cp -a /src/vellvm /src/passes /src/validator /src/scripts /src/LICENSE /work/
cd /work

export OPAMROOT=/home/opam/.opam
export OCAMLRUNPARAM="s=2M,o=80"

# Static repository integrity gate
python3 scripts/verify_repo_integrity.py

# Stage [1/3]: Core Vellvm 3.0 & I2F theories
CORE_VOS=$(awk '/^\.\/rocq\/.*\.v$/ { sub(/^\.\//, ""); sub(/\.v$/, ".vo"); print }' vellvm/src/_RocqProject)
opam exec -- make -C vellvm/src RocqMakefile
opam exec -- make -C vellvm/src --no-print-directory -f RocqMakefile TIMED=1 -j2 $CORE_VOS

# Stage [2/3]: All CertPasses & CertValidator proofs
opam exec -- make -C vellvm/src --no-print-directory -f RocqMakefile TIMED=1 real-all -k -j2

# Stage [3/3]: Verified OCaml extraction & Dune release binaries (`cert-validator`, `verified-opt-fallback`, `.bc`)
opam exec -- make -C vellvm/src all -j2

# Independent Rocq kernel proof-checker gate
(cd vellvm/src && opam exec -- rocq check -o -R rocq Vellvm -R ../../passes CertPasses -R ../../validator CertValidator \
  Vellvm.Semantics.TopLevel Vellvm.Theory.Equational CertPasses.Pipeline CertPasses.McfgExport \
  CertPasses.ModuleMerge CertValidator.CertValidator CertValidator.CheckAssumptions)
```

Verify `rocq check -o` reports `Modules were successfully checked` with zero unapproved axioms (`type-in-type: <none>`, `unsafe (co)fixpoints: <none>`), then run the smoke and soundness suites inside `/work`:

```bash
BIN=vellvm/src/_build/default/ml/bin
"$BIN/verified-opt-fallback" --pass pipeline -o /tmp/smoke_out.ll /tmp/smoke_in.ll
python3 scripts/run_forged_cert_suite.py "$BIN/cert-validator" "$BIN/verified-opt-fallback"
python3 scripts/run_cert_mutation_suite.py \
  "$BIN/cert-validator" "$BIN/cert-validator.bc" \
  "$BIN/verified-opt-fallback" "$BIN/verified-opt-fallback.bc"
```

After inspecting exit code `0`, remove temporary containers (`docker rm -f <container-name>`), while keeping the reusable image `llvmcert-rocq-env:9.1` cached.

---

## 3. Fast Local Gates (`verify_repo_integrity.py`, `ir-bridge/`, CERT C)

Always run the read-only integrity gate before committing **any** change:

```powershell
Set-Location D:\LLVMCert; python scripts/verify_repo_integrity.py
```

This enforces:
- Root `LICENSE` and third-party `LICENSE-LLVM.TXT` / `vellvm/LICENSE.md` presence.
- Zero GPL/AGPL text; `LGPL-2.1+` restricted to `vellvm/src/rocq/Numeric/`.
- Zero `Admitted`, `admit`, `give_up`, `Abort` (outside upstream `SurfaceSyntax.v` notation tests), and zero unapproved `Axiom`s.
- Handwritten `.ml`/`.mli` outside `extracted/` capped at `<= 750` LOC.
- Strict RFC-4180 8-column schema on `plan/feedback.csv` (`F-XX`).
- GitHub Actions `uses:` pinned to 40-char commit SHAs with `persist-credentials: false`.
- Zero proprietary leaks, tracked secret keys, or unapproved frozen LLVM diffs.

For `ir-bridge/` Rust edits, also run:

```powershell
Set-Location D:\LLVMCert\ir-bridge; cargo fmt --all -- --check; if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }; cargo clippy --workspace --all-targets --no-deps -- -D warnings; if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }; cargo test --workspace
```

---

## 4. GitHub Actions Workflows & Manual Triggers

- **`.github/workflows/quality-gate.yml`** — Automatically runs on push to `main` and all PRs (`verify_repo_integrity.py`, CERT C checks on `runtime/`/`c-quality/`, `ir-bridge` `fmt`/`clippy`/`nextest`/`cargo-deny`).
- **`.github/workflows/rocq-ci.yml`** — Runs **only** on PRs touching Rocq/validator/pass/mutation-suite paths, `phase-*`/`toolchain-*`/`v*` tags, or **`workflow_dispatch`**. It does **not** trigger automatically on direct pushes to `main`.
  - Whenever you push Rocq or OCaml changes directly to `main`, trigger it manually and monitor until `conclusion: success`:
    ```powershell
    gh workflow run rocq-ci.yml -R mannomannX/llvm-cert --ref main
    gh run list -R mannomannX/llvm-cert --workflow rocq-ci.yml --limit 3 --json databaseId,status,conclusion,headSha,createdAt,updatedAt
    ```
  - Note Layer 1 (`Print Assumptions`) in `rocq-ci.yml` additionally verifies that `CertValidator.AigLrat.check_lrat_unsat_sound` and `CertValidator.CertFormat.validate_dimacs_lrat_str_sound` are closed under the global context (`0` axioms), and that `CertPasses`/`CertValidator` introduce zero custom axioms beyond upstream Vellvm 3.0.
- **`.github/workflows/llvm-toolchain-build.yml`** — Only for `toolchain-*`/`v*` tags or manual dispatch when rebuilding the stripped LLVM `23.1.5` (`AArch64;RISCV`) SDK.

---

## 5. Refreshing Pre-Release Binary Bundles (`e2e-bundle-YYYY-MM-DD`)

Whenever `rocq-ci.yml` (native + bytecode `cert-validator` / `verified-opt-fallback`) or `llvm-toolchain-build.yml` produces new binaries consumed downstream:

1. Wait for `rocq-ci.yml` on the target commit SHA to reach `conclusion: success`.
2. Download the verified artifact into a temporary scratch folder outside git:
   ```powershell
   gh run download <run-id> -R mannomannX/llvm-cert -n llvm-cert-rocq-tools-linux-x86_64 -D <scratch-dir>
   ```
3. Compute lowercase SHA-256 digests (`Get-FileHash -Algorithm SHA256`), write `BUNDLE_SHA256SUMS.txt` using **LF-only line endings (`\n`) and UTF-8 without BOM** (using `[System.IO.File]::WriteAllText(..., [System.Text.UTF8Encoding]::new($false))`), and upload `--clobber` to the release:
   ```powershell
   gh release upload <bundle-tag> <tarball-path> <checksums-path> -R mannomannX/llvm-cert --clobber
   ```
4. Confirm exact uploaded asset digests and byte sizes via:
   ```powershell
   gh release view <bundle-tag> -R mannomannX/llvm-cert --json assets
   ```

---

## 6. Ledger Discipline & Windows/PowerShell Operational Notes

- **Feedback Ledger ([`plan/feedback.csv`](./feedback.csv)):** Log newly discovered bugs, semantic gaps, or TCB issues immediately with `Status=open` or `in-progress`. Transition to `resolved` only in a post-verification commit recording concrete commit SHAs, test results, and CI Run IDs.
- **Untracked User Notes:** Never modify, commit, or delete untracked [`Discussion.md`](../Discussion.md).
- **PowerShell 5.1 Chaining:** PowerShell 5.1 does not support `&&`. Always chain dependent commands with `; if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE };`. Avoid `gh ... --jq` quoting errors in Windows PowerShell by omitting `--jq` or passing properly escaped filters. Never run auto-mutating formatters (`cargo fmt` without `--check`).
