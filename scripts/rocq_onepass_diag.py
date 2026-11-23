#!/usr/bin/env python3
"""Read-only single-pass Rocq diagnostic compiler wrapper.

Compiles `.v` files chunk-by-chunk (splitting at `Qed.` / `Defined.`) via an
interactive `rocq top -emacs` session so that failing proofs or commands are
recorded with their error message and open goal, recovered in-memory without
modifying any source file, and reported together in a single run instead of
aborting at the first error.
"""

from __future__ import annotations

import argparse
import os
import re
import signal
import subprocess
import sys
import time


class ChunkTimeout(Exception):
    """Raised when a single proof or command chunk exceeds the timeout."""


def _timeout_handler(_signum: int, _frame: object) -> None:
    raise ChunkTimeout()


def split_chunks(text: str) -> list[tuple[int, int, str]]:
    """Split a Rocq file into chunks ending at top-level `Qed.` / `Defined.`."""
    chunks: list[tuple[int, int, str]] = []
    n = len(text)
    i = 0
    comment = 0
    in_str = False
    chunk_start = 0
    start_line = 1
    cur_line = 1
    end_re = re.compile(r"(?:Qed|Defined)\.(?=\s|$|\(\*)")

    while i < n:
        ch = text[i]
        if ch == "\n":
            cur_line += 1
            i += 1
            continue
        if in_str:
            if ch == '"':
                if i + 1 < n and text[i + 1] == '"':
                    i += 2
                    continue
                in_str = False
            i += 1
            continue
        if ch == "(" and i + 1 < n and text[i + 1] == "*":
            comment += 1
            i += 2
            continue
        if comment > 0:
            if ch == "*" and i + 1 < n and text[i + 1] == ")":
                comment -= 1
                i += 2
                continue
            i += 1
            continue
        if ch == '"':
            in_str = True
            i += 1
            continue
        if ch in ("Q", "D") and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            match = end_re.match(text, i)
            if match:
                end_idx = match.end()
                chunks.append((start_line, cur_line, text[chunk_start:end_idx]))
                chunk_start = end_idx
                start_line = cur_line
                i = end_idx
                continue
        i += 1

    if text[chunk_start:].strip():
        chunks.append((start_line, cur_line, text[chunk_start:]))
    return chunks


PROMPT_RE = re.compile(r"<prompt>([^<]*)<\s*\d+\s*\|([^|]*)\|\s*\d+\s*<\s*</prompt>")
DISABLED_WARNINGS = (
    "-masking-absolute-name,"
    "-deprecated-hint-without-locality,"
    "-deprecated-hint-rewrite-without-locality,"
    "-require-in-module"
)


def run_diag(vfile: str, cwd: str, chunk_timeout: int = 90) -> tuple[int, bool]:
    """Run a full single-pass check on `vfile`; return `(fails, aborted)`."""
    t0 = time.time()
    with open(vfile, "r", encoding="utf-8") as fh:
        text = fh.read()
    chunks = split_chunks(text)

    proc = subprocess.Popen(
        [
            "rocq",
            "top",
            "-emacs",
            "-quiet",
            "-diffs",
            "off",
            "-R",
            "rocq",
            "Vellvm",
            "-R",
            "../../passes",
            "CertPasses",
            "-R",
            "../../validator",
            "CertValidator",
            "-w",
            DISABLED_WARNINGS,
        ],
        cwd=cwd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
        env={**os.environ, "OCAMLRUNPARAM": "o=25"},
    )
    assert proc.stdin is not None and proc.stdout is not None
    signal.signal(signal.SIGALRM, _timeout_handler)

    def read_until_prompt(timeout_s: int) -> str:
        signal.alarm(timeout_s)
        try:
            buf: list[str] = []
            while True:
                ch = proc.stdout.read(1)
                if not ch:
                    raise EOFError("rocq top EOF")
                buf.append(ch)
                if len(buf) >= 9 and "".join(buf[-9:]) == "</prompt>":
                    return "".join(buf)
        finally:
            signal.alarm(0)

    read_until_prompt(chunk_timeout)

    sync_id = 0

    def send_sync(cmd: str, timeout_s: int = chunk_timeout) -> str:
        nonlocal sync_id
        sync_id += 1
        tok = f"__DIAG_SYNC_{sync_id}__"
        try:
            proc.stdin.write(cmd + f"\nLocate {tok}.\n")
            proc.stdin.flush()
        except (BrokenPipeError, OSError):
            return "Error: Broken pipe to rocq top"
        out_chars: list[str] = []
        tail = ""
        signal.alarm(timeout_s)
        try:
            while True:
                ch = proc.stdout.read(1)
                if not ch:
                    break
                out_chars.append(ch)
                tail = (tail + ch)[-160:]
                if tok in "".join(out_chars[-400:]) and tail.endswith("</prompt>"):
                    break
        finally:
            signal.alarm(0)
        return "".join(out_chars)

    def clean_out(raw: str) -> str:
        cleaned = PROMPT_RE.sub("", raw)
        cleaned = re.sub(r"No object of basename __DIAG_(?:SYNC|RECOVER)_\d+__\s*", "", cleaned)
        cleaned = re.sub(r"<infomsg>.*?</infomsg>", "", cleaned, flags=re.S)
        return cleaned.strip()

    def last_open_proofs(raw: str) -> str:
        matches = PROMPT_RE.findall(raw)
        return matches[-1][1].strip() if matches else ""

    def format_goal(goal_txt: str) -> str:
        lines = goal_txt.splitlines()
        if len(lines) > 30:
            return "\n".join(lines[:10] + ["  ..."] + lines[-18:])
        return goal_txt

    fails = 0
    aborted = False
    for sline, eline, chunk in chunks:
        try:
            out = send_sync(chunk, chunk_timeout)
        except ChunkTimeout:
            fails += 1
            try:
                proc.send_signal(signal.SIGINT)
                out_int = read_until_prompt(8)
                out_rec = send_sync("Locate __DIAG_RECOVER_0__.", 8)
                op = last_open_proofs(out_int + "\n" + out_rec)
                goal_txt = ""
                if op != "":
                    goal_txt = clean_out(send_sync("Show.", 8))
                    guard = 0
                    while op != "" and guard < 6:
                        op = last_open_proofs(send_sync("Admitted.", 8))
                        guard += 1
                print(
                    f"=== [{vfile}] FAIL #{fails} (chunk lines {sline}..{eline}) "
                    f"TIMEOUT ({chunk_timeout}s) [recovered via SIGINT] ===",
                    flush=True,
                )
                if goal_txt:
                    print("--- OPEN GOAL AT TIMEOUT ---", flush=True)
                    print(format_goal(goal_txt), flush=True)
                print(flush=True)
                continue
            except (ChunkTimeout, EOFError, BrokenPipeError, OSError) as exc:
                aborted = True
                print(
                    f"=== [{vfile}] FAIL #{fails} (chunk lines {sline}..{eline}) "
                    f"TIMEOUT ({chunk_timeout}s) [recovery failed: {exc}] ===",
                    flush=True,
                )
                proc.kill()
                proc.wait()
                break

        rc = proc.poll()
        if "Error: Broken pipe to rocq top" in out or rc is not None:
            fails += 1
            aborted = True
            rc_str = str(rc) if rc is not None else "unknown"
            print(
                f"=== [{vfile}] FAIL #{fails} (chunk lines {sline}..{eline}) "
                f"[ABORTED: rocq top exited (code={rc_str})] ===",
                flush=True,
            )
            cleaned = clean_out(out)
            if cleaned:
                print(cleaned[:800], flush=True)
            print(flush=True)
            break

        op = last_open_proofs(out)
        has_err = ("Error:" in out) or (op != "")
        if has_err:
            fails += 1
            goal_txt = ""
            try:
                if op != "":
                    goal_txt = clean_out(send_sync("Show.", 15))
                    guard = 0
                    while op != "" and guard < 6:
                        op = last_open_proofs(send_sync("Admitted.", 15))
                        guard += 1
            except ChunkTimeout:
                aborted = True
                print(
                    f"=== [{vfile}] FAIL #{fails} (chunk lines {sline}..{eline}) "
                    f"TIMEOUT during recovery ({chunk_timeout}s) ===",
                    flush=True,
                )
                proc.kill()
                proc.wait()
                break
            cleaned = clean_out(out)
            parts = cleaned.split("\n\n")
            filtered = [p for p in parts if "Attempt to save an incomplete proof" not in p]
            err_msg = "\n\n".join(filtered[:2]) if filtered else cleaned[:800]
            print(f"=== [{vfile}] FAIL #{fails} (chunk lines {sline}..{eline}) ===", flush=True)
            print(err_msg, flush=True)
            if goal_txt:
                print("--- OPEN GOAL ---", flush=True)
                print(format_goal(goal_txt), flush=True)
            print(flush=True)

    if not aborted:
        try:
            proc.stdin.write("Quit.\n")
            proc.stdin.flush()
        except (BrokenPipeError, OSError):
            pass
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()

    dt = time.time() - t0
    suffix = " [ABORTED]" if aborted else ""
    print(
        f"=== SUMMARY {vfile}: {fails} failing proof/cmd chunks out of {len(chunks)} "
        f"({dt:.1f}s){suffix} ===\n",
        flush=True,
    )
    return fails, aborted


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--timeout",
        type=int,
        default=90,
        help="Per-chunk timeout in seconds before SIGINT recovery (default: 90)",
    )
    parser.add_argument("cwd", help="Working directory (normally vellvm/src)")
    parser.add_argument("vfiles", nargs="+", help="Rocq .v file(s) to diagnose")
    args = parser.parse_args()

    total_fails = 0
    any_aborted = False
    for vfile in args.vfiles:
        fails, aborted = run_diag(vfile, args.cwd, chunk_timeout=args.timeout)
        total_fails += fails
        any_aborted = any_aborted or aborted

    return 0 if (total_fails == 0 and not any_aborted) else 1


if __name__ == "__main__":
    sys.exit(main())
