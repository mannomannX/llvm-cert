#!/usr/bin/env python3
"""Read-only repository integrity, license, TCB, and formal-proof gate for LLVMCert.

Enforces six project-wide invariants without modifying any files:
1. Dual-license (`LICENSE`) and upstream attribution (`LICENSE-LLVM.TXT`, `vellvm/LICENSE.md`).
2. Zero GPL/AGPL contamination in non-LLVM directories (`LGPL-2.1+` restricted to `Numeric/`).
3. Public-repo anti-leakage guard (zero tracked keys/secrets or proprietary enterprise crates).
4. Mathematical MISRA for Rocq (zero `Admitted`/`admit`/`give_up`/`Abort` and zero unapproved `Axiom`s).
5. Minimal-OCaml TCB budget (caps handwritten `.ml`/`.mli` lines outside `extracted/`).
6. Frozen-upstream LLVM guard (blocks accidental edits to `llvm/`, `clang/`, `lld/`, etc. in CI).
"""

from __future__ import annotations

import argparse
import csv
import pathlib
import re
import subprocess
import sys

FROZEN_UPSTREAM_PREFIXES = (
    "llvm/",
    "clang/",
    "lld/",
    "cmake/",
    "libc/",
    "libunwind/",
    "third-party/",
)

AUDITED_CODE_DIRS = (
    "vellvm",
    "passes",
    "validator",
    "ir-bridge",
    "runtime",
    "c-quality",
    "scripts",
)

ROCQ_DIRS = (
    "vellvm",
    "passes",
    "validator",
)

ALLOWED_ROCQ_AXIOMS: set[tuple[str, str]] = {
    ("vellvm/src/rocq/Numeric/Integers.v", "wordsize_not_zero"),
    ("vellvm/src/rocq/Utils/ParserHelper.v", "Zlog2_log_inf"),
}

# Upstream `SurfaceSyntax.v` uses `Goal ... Abort.` inside `SurfaceSyntaxTest` purely to test
# notation pretty-printing (`Abort` adds nothing to the Rocq environment, unlike `Admitted`).
# All LLVMCert passes/validators still forbid `Abort` so incomplete lemmas cannot slip through.
ALLOWED_ROCQ_ABORT_FILES: set[str] = {
    "vellvm/src/rocq/Syntax/SurfaceSyntax.v",
}

# Current baseline is ~501 LOC across 5 minimal glue files (`IO.ml`, `Camlcoq.ml`, printers,
# `parse_util.ml`). Headroom of ~250 LOC is reserved strictly for thin CLI entrypoints of
# `verified-opt-fallback` and `cert-validator`; all unverified systems code belongs in Rust.
MAX_HANDWRITTEN_OCAML_LOC = 750

FORBIDDEN_SECRET_PATTERNS = (
    re.compile(r"(^|/)\.env(\..+)?$"),
    re.compile(r"\.(key|pem|p12|pfx|secret)$", re.IGNORECASE),
)

PROPRIETARY_LEAK_MARKERS = (
    "LicenseRef-LLVMCert-Proprietary",
    "CERT_LLVM_SIGNING_KEY",
    "cert-z3-engine",
)

PROOF_HOLE_RE = re.compile(r"\b(Admitted|admit|give_up|Abort)\b")
AXIOM_DECL_RE = re.compile(r"\b(Axiom|Conjecture)\s+([A-Za-z0-9_']+)")


def strip_rocq_comments_and_strings(src: str) -> str:
    """Replaces Rocq `(* ... *)` nested comments and string literals with spaces, keeping newlines."""
    out: list[str] = []
    i = 0
    n = len(src)
    depth = 0
    in_string = False

    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""

        if depth > 0:
            if ch == "(" and nxt == "*":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if ch == "*" and nxt == ")":
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if in_string:
            if ch == '"' and nxt == '"':
                out.append("  ")
                i += 2
                continue
            if ch == '"':
                in_string = False
                out.append(" ")
                i += 1
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if ch == "(" and nxt == "*":
            depth = 1
            out.append("  ")
            i += 2
            continue

        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def check_required_licenses(root: pathlib.Path, errors: list[str]) -> None:
    lic = root / "LICENSE"
    if not lic.is_file():
        errors.append("Missing root LICENSE file.")
    else:
        text = lic.read_text(encoding="utf-8", errors="replace")
        if "LLVMCERT NON-COMMERCIAL EVALUATION & RESEARCH LICENSE AGREEMENT" not in text:
            errors.append("Root LICENSE is missing the LLVMCert Non-Commercial License header.")

    for rel in ("LICENSE-LLVM.TXT", "vellvm/LICENSE.md"):
        if not (root / rel).is_file():
            errors.append(f"Missing required third-party license file: {rel}")


EXPECTED_FEEDBACK_HEADER = [
    "ID",
    "Category",
    "Section",
    "Finding",
    "Action",
    "Severity",
    "Status",
    "Reference",
]
VALID_SEVERITIES = {"critical", "high", "medium", "low"}
VALID_STATUSES = {"open", "in-progress", "resolved", "accepted-risk"}


def check_feedback_ledger(root: pathlib.Path, errors: list[str]) -> int:
    ledger = root / "plan" / "feedback.csv"
    if not ledger.is_file():
        errors.append("Missing structured agent findings ledger: plan/feedback.csv")
        return 0

    seen_ids: set[str] = set()
    row_count = 0
    with ledger.open("r", encoding="utf-8", newline="") as fh:
        reader = csv.reader(fh)
        header = next(reader, None)
        if header != EXPECTED_FEEDBACK_HEADER:
            errors.append(
                f"plan/feedback.csv invalid header {header}; expected {EXPECTED_FEEDBACK_HEADER}"
            )
            return 0

        for lineno, row in enumerate(reader, start=2):
            if not row:
                continue
            row_count += 1
            if len(row) != 8:
                errors.append(
                    f"plan/feedback.csv:{lineno} has {len(row)} columns (expected 8; quote fields containing commas)"
                )
                continue
            fid, _cat, _sec, finding, _act, severity, status, _ref = row
            if not re.match(r"^F-\d{2,}$", fid):
                errors.append(f"plan/feedback.csv:{lineno} invalid ID `{fid}` (expected F-XX)")
            if fid in seen_ids:
                errors.append(f"plan/feedback.csv:{lineno} duplicate ID `{fid}`")
            seen_ids.add(fid)
            if not finding.strip():
                errors.append(f"plan/feedback.csv:{lineno} empty Finding description")
            if severity not in VALID_SEVERITIES:
                errors.append(
                    f"plan/feedback.csv:{lineno} invalid Severity `{severity}` (expected {sorted(VALID_SEVERITIES)})"
                )
            if status not in VALID_STATUSES:
                errors.append(
                    f"plan/feedback.csv:{lineno} invalid Status `{status}` (expected {sorted(VALID_STATUSES)})"
                )
    return row_count


def check_code_licenses_and_leaks(root: pathlib.Path, errors: list[str]) -> None:
    self_rel = "scripts/verify_repo_integrity.py"
    for d in AUDITED_CODE_DIRS:
        base = root / d
        if not base.exists():
            continue
        for path in base.rglob("*"):
            if not path.is_file() or "_build" in path.parts or "target" in path.parts:
                continue
            rel = path.relative_to(root).as_posix()
            if rel == self_rel:
                continue
            text = path.read_text(encoding="utf-8", errors="replace")

            if "GNU General Public License" in text or "GNU Affero General Public License" in text:
                errors.append(f"Forbidden strong copyleft (GPL/AGPL) license text in {rel}")

            if re.search(r"SPDX-License-Identifier:.*\bA?GPL-", text):
                errors.append(f"Forbidden GPL/AGPL SPDX identifier in {rel}")

            if "GNU Lesser General Public License" in text and not rel.startswith(
                "vellvm/src/rocq/Numeric/"
            ):
                errors.append(
                    f"LGPL header outside approved vellvm/src/rocq/Numeric/ boundary: {rel}"
                )

            for marker in PROPRIETARY_LEAK_MARKERS:
                if marker in text:
                    errors.append(
                        f"Proprietary enterprise marker `{marker}` leaked into public file {rel}"
                    )


def check_tracked_secrets(root: pathlib.Path, errors: list[str]) -> None:
    proc = subprocess.run(
        ["git", "ls-files"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return
    for line in proc.stdout.splitlines():
        rel = line.strip()
        if any(p.search(rel) for p in FORBIDDEN_SECRET_PATTERNS):
            errors.append(f"Forbidden secret or key file tracked in git: {rel}")


USES_RE = re.compile(r"^\s*-?\s*uses:\s*([^\s#]+)")


def check_github_workflows(root: pathlib.Path, errors: list[str]) -> None:
    wf_dir = root / ".github" / "workflows"
    if not wf_dir.is_dir():
        return
    for wf in sorted(wf_dir.glob("*.yml")):
        rel = wf.relative_to(root).as_posix()
        lines = wf.read_text(encoding="utf-8", errors="replace").splitlines()
        for idx, line in enumerate(lines):
            m = USES_RE.match(line)
            if not m:
                continue
            target = m.group(1).strip("'\"")
            if target.startswith("./"):
                continue
            if not re.search(r"@[0-9a-f]{40}$", target):
                errors.append(
                    f"{rel}:{idx + 1} GitHub Action `{target}` must be pinned to a 40-char commit SHA"
                )
            if target.startswith("actions/checkout@"):
                window = "\n".join(lines[idx + 1 : idx + 7])
                if "persist-credentials: false" not in window:
                    errors.append(
                        f"{rel}:{idx + 1} actions/checkout must explicitly set `persist-credentials: false`"
                    )


def check_rocq_proofs(root: pathlib.Path, errors: list[str]) -> int:
    checked_files = 0
    for d in ROCQ_DIRS:
        base = root / d
        if not base.exists():
            continue
        for path in sorted(base.rglob("*.v")):
            if "_build" in path.parts:
                continue
            checked_files += 1
            rel = path.relative_to(root).as_posix()
            raw = path.read_text(encoding="utf-8", errors="replace")
            stripped = strip_rocq_comments_and_strings(raw)

            for lineno, line in enumerate(stripped.splitlines(), start=1):
                hole = PROOF_HOLE_RE.search(line)
                if hole and not (hole.group(1) == "Abort" and rel in ALLOWED_ROCQ_ABORT_FILES):
                    errors.append(
                        f"Forbidden Rocq proof hole `{hole.group(1)}` in {rel}:{lineno}"
                    )
                for ax in AXIOM_DECL_RE.finditer(line):
                    kind, ident = ax.group(1), ax.group(2)
                    if (rel, ident) not in ALLOWED_ROCQ_AXIOMS:
                        errors.append(
                            f"Unapproved Rocq `{kind} {ident}` in {rel}:{lineno} "
                            "(prove as Lemma or document in ALLOWED_ROCQ_AXIOMS after TCB review)"
                        )
    return checked_files


def check_ocaml_budget(root: pathlib.Path, errors: list[str]) -> int:
    total_loc = 0
    for d in ("vellvm", "passes", "validator"):
        base = root / d
        if not base.exists():
            continue
        for ext in ("*.ml", "*.mli"):
            for path in base.rglob(ext):
                rel = path.relative_to(root).as_posix()
                if "/extracted/" in rel or "/_build/" in rel:
                    continue
                lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
                total_loc += len(lines)

    if total_loc > MAX_HANDWRITTEN_OCAML_LOC:
        errors.append(
            f"Handwritten OCaml TCB budget exceeded: {total_loc} LOC > {MAX_HANDWRITTEN_OCAML_LOC} LOC. "
            "Implement unverified tooling and IR bridges in Rust."
        )
    return total_loc


def check_frozen_upstream_diff(
    root: pathlib.Path, base_sha: str, head_sha: str, errors: list[str]
) -> None:
    if not base_sha or set(base_sha) == {"0"}:
        return
    diff_proc = subprocess.run(
        ["git", "diff", "--name-only", base_sha, head_sha],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if diff_proc.returncode != 0:
        return

    touched_upstream = [
        f
        for f in diff_proc.stdout.splitlines()
        if f.startswith(FROZEN_UPSTREAM_PREFIXES)
    ]
    if not touched_upstream:
        return

    log_proc = subprocess.run(
        ["git", "log", "--format=%B", f"{base_sha}..{head_sha}"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if "[allow-upstream-patch]" not in log_proc.stdout:
        sample = ", ".join(touched_upstream[:5])
        errors.append(
            f"Frozen LLVM 23.1.5 upstream tree modified ({len(touched_upstream)} file(s), e.g. {sample}) "
            "without `[allow-upstream-patch]` in commit message."
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="", help="Base commit SHA for frozen-upstream diff check")
    parser.add_argument("--head", default="HEAD", help="Head commit SHA for frozen-upstream diff check")
    args = parser.parse_args()

    root = pathlib.Path(__file__).resolve().parent.parent
    errors: list[str] = []

    check_required_licenses(root, errors)
    feedback_rows = check_feedback_ledger(root, errors)
    check_code_licenses_and_leaks(root, errors)
    check_tracked_secrets(root, errors)
    check_github_workflows(root, errors)
    rocq_count = check_rocq_proofs(root, errors)
    ocaml_loc = check_ocaml_budget(root, errors)
    if args.base:
        check_frozen_upstream_diff(root, args.base, args.head, errors)

    if errors:
        print("LLVMCert Repository Integrity Check FAILED:", file=sys.stderr)
        for err in errors:
            print(f"  [FAIL] {err}", file=sys.stderr)
        return 1

    print(
        f"LLVMCert Integrity OK: {rocq_count} Rocq files verified (0 Admitted), "
        f"handwritten OCaml TCB = {ocaml_loc}/{MAX_HANDWRITTEN_OCAML_LOC} LOC, "
        f"feedback ledger = {feedback_rows} entries, 0 GPL/secret/proprietary leaks."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
