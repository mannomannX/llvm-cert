#!/usr/bin/env python3
# Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
# Licensed under the LLVMCert Non-Commercial Evaluation & Research License
# or a separate LLVMCert Commercial Software License Agreement.
# See /LICENSE in the repository root for details.
"""Layer-2 positive and adversarial forged-certificate CI test suite for cert-validator.

Exercises both CLI entrypoints of the extracted Rocq translation validator:
1. Per-function translation validation:
     cert-validator --src <src.ll> --tgt <tgt.ll> --cert <fn.cert>
2. Certified module merge composition:
     cert-validator --check-merge --orig <orig.ll> --merged <merged.ll>
       [--slice-cert <fn> <src.ll> <tgt.ll> <fn.cert> |
        --slice-safe <fn> <src.ll> <safe.ll>]*

Enforces per-case wall-clock bounds, zero signal crashes (returncode < 0), zero
uncaught OCaml runtime exceptions (Stack_overflow / Fatal error: exception),
exact exit-code polarity (0 for positive refinements, > 0 for forged or unsound
inputs), and local grammar/harness self-verification via --self-test.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import pathlib
import subprocess
import sys
import tempfile
import time
from typing import Callable

DEFAULT_TIMEOUT_SEC = 10.0
LET_DAG_BOMB_TIMEOUT_SEC = 5.0
MAX_SEXP_DEPTH = 1024

SUPPORTED_BIT_WIDTHS = frozenset({1, 8, 16, 32, 64, 128})
CERT_BINOPS = frozenset(
    {
        "add",
        "sub",
        "mul",
        "udiv",
        "sdiv",
        "urem",
        "srem",
        "shl",
        "lshr",
        "ashr",
        "and",
        "or",
        "xor",
    }
)
CERT_ICMPS = frozenset(
    {"eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"}
)
CERT_CASTS = frozenset({"zext", "sext", "trunc"})
CRASH_STDERR_MARKERS = (
    "Stack_overflow",
    "Fatal error: exception",
    "Out_of_memory",
    "Assert_failure",
)


@dataclass(frozen=True)
class CommandOutcome:
    returncode: int
    stdout: str
    stderr: str
    elapsed_sec: float
    timed_out: bool = False


@dataclass(frozen=True)
class PreparedInvocation:
    argv: list[str]
    cert_bytes_for_grammar_check: bytes | None = None


@dataclass(frozen=True)
class SuiteCase:
    name: str
    expect_accept: bool
    description: str
    prepare: Callable[[pathlib.Path, pathlib.Path, pathlib.Path], PreparedInvocation]
    timeout_sec: float = DEFAULT_TIMEOUT_SEC
    allowed_reject_codes: tuple[int, ...] | None = None
    expect_cert_parse_ok: bool | None = None


def sha256_hex(data: bytes | str) -> str:
    raw = data.encode("utf-8") if isinstance(data, str) else data
    return hashlib.sha256(raw).hexdigest()


def build_cert_v1(
    fn_name: str,
    src_ir: str,
    tgt_ir: str,
    return_sexp: str,
    *,
    ub_assumptions: tuple[str, ...] = (),
    src_hash_override: str | None = None,
    tgt_hash_override: str | None = None,
) -> bytes:
    src_h = src_hash_override if src_hash_override is not None else sha256_hex(src_ir)
    tgt_h = tgt_hash_override if tgt_hash_override is not None else sha256_hex(tgt_ir)
    ub_section = (
        "(ub-assumptions)"
        if not ub_assumptions
        else "(ub-assumptions " + " ".join(ub_assumptions) + ")"
    )
    text = (
        "(cert-v1\n"
        f'  (fn "{fn_name}")\n'
        f"  (src-sha256 {src_h})\n"
        f"  (tgt-sha256 {tgt_h})\n"
        "  (blocks\n"
        "    (block\n"
        '      (src-bb "entry")\n'
        '      (tgt-bb "entry")\n'
        "      (kind entry)\n"
        f"      {ub_section}\n"
        "      (value-equivs)\n"
        "      (mem-invariants)))\n"
        f"  (return {return_sexp}))\n"
    )
    return text.encode("utf-8")


def scalar_refines_sexp(
    width: int, src_expr: str, tgt_expr: str, *, smt_verified: bool = False
) -> str:
    smt_tok = "true" if smt_verified else "false"
    return (
        f"(scalar-refines (width {width}) (src {src_expr}) "
        f"(tgt {tgt_expr}) (smt-verified {smt_tok}))"
    )


def write_tv_files(
    workdir: pathlib.Path,
    cert_validator_bin: pathlib.Path,
    src_ir: str,
    tgt_ir: str,
    cert_bytes: bytes,
) -> PreparedInvocation:
    src_path = workdir / "src.ll"
    tgt_path = workdir / "tgt.ll"
    cert_path = workdir / "fn.cert"
    src_path.write_text(src_ir, encoding="utf-8", newline="\n")
    tgt_path.write_text(tgt_ir, encoding="utf-8", newline="\n")
    cert_path.write_bytes(cert_bytes)
    return PreparedInvocation(
        argv=[
            str(cert_validator_bin),
            "--src",
            str(src_path),
            "--tgt",
            str(tgt_path),
            "--cert",
            str(cert_path),
        ],
        cert_bytes_for_grammar_check=cert_bytes,
    )


def run_process(argv: list[str], timeout_sec: float) -> CommandOutcome:
    t0 = time.monotonic()
    try:
        proc = subprocess.run(
            argv,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout_sec,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.monotonic() - t0
        out = (
            exc.stdout.decode("utf-8", errors="replace")
            if isinstance(exc.stdout, bytes)
            else (exc.stdout or "")
        )
        err = (
            exc.stderr.decode("utf-8", errors="replace")
            if isinstance(exc.stderr, bytes)
            else (exc.stderr or "")
        )
        return CommandOutcome(
            returncode=124,
            stdout=out,
            stderr=err,
            elapsed_sec=elapsed,
            timed_out=True,
        )
    elapsed = time.monotonic() - t0
    return CommandOutcome(
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
        elapsed_sec=elapsed,
        timed_out=False,
    )


def evaluate_outcome(
    case: SuiteCase, outcome: CommandOutcome
) -> tuple[bool, str]:
    if outcome.timed_out:
        return (
            False,
            f"timed out after {outcome.elapsed_sec:.2f}s (limit {case.timeout_sec:.1f}s)",
        )
    if outcome.elapsed_sec > case.timeout_sec:
        return (
            False,
            f"exceeded wall-clock budget: {outcome.elapsed_sec:.2f}s > {case.timeout_sec:.1f}s",
        )
    if outcome.returncode < 0:
        return (
            False,
            f"killed by signal {-outcome.returncode} (returncode={outcome.returncode})",
        )
    for marker in CRASH_STDERR_MARKERS:
        if marker in outcome.stderr or marker in outcome.stdout:
            return (
                False,
                f"uncaught runtime crash marker `{marker}` in output "
                f"(returncode={outcome.returncode})",
            )
    if case.expect_accept:
        if outcome.returncode != 0:
            detail = outcome.stderr.strip() or outcome.stdout.strip()
            return (
                False,
                f"expected acceptance (exit 0), got exit {outcome.returncode}: {detail}",
            )
        return (True, f"accepted in {outcome.elapsed_sec * 1000.0:.1f} ms")

    if outcome.returncode <= 0:
        return (
            False,
            "SOUNDNESS/SECURITY BREACH: cert-validator exited 0 on adversarial input",
        )
    if (
        case.allowed_reject_codes is not None
        and outcome.returncode not in case.allowed_reject_codes
    ):
        return (
            False,
            f"expected clean rejection exit in {case.allowed_reject_codes}, "
            f"got exit {outcome.returncode}: {outcome.stderr.strip()}",
        )
    return (
        True,
        f"rejected cleanly (exit {outcome.returncode}) in {outcome.elapsed_sec * 1000.0:.1f} ms",
    )


# ---------------------------------------------------------------------------
# Reference Python mirror of validator/CertFormat.v S-expression & cert-v1 AST
# (used by --self-test to verify every test certificate offline on any OS)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SAtom:
    val: str


@dataclass(frozen=True)
class SStr:
    val: str


@dataclass(frozen=True)
class SList:
    items: tuple[SExp, ...]


SExp = SAtom | SStr | SList


def _is_sexp_ws(b: int) -> bool:
    return b in (9, 10, 12, 13, 32)


def _is_valid_atom_byte(b: int) -> bool:
    return (
        33 <= b <= 126
        and b not in (34, 40, 41, 59, 92)
    )


def parse_cert_sexp_mirror(raw: bytes) -> SExp:
    tokens: list[str | tuple[str, str]] = []
    i = 0
    n = len(raw)
    while i < n:
        b = raw[i]
        if _is_sexp_ws(b):
            i += 1
        elif b == 40:
            tokens.append("(")
            i += 1
        elif b == 41:
            tokens.append(")")
            i += 1
        elif b == 34:
            i += 1
            chars: list[str] = []
            closed = False
            while i < n:
                c = raw[i]
                if c == 34:
                    i += 1
                    closed = True
                    break
                if c == 92:
                    i += 1
                    if i >= n:
                        raise ValueError("unterminated string escape")
                    esc = raw[i]
                    esc_map = {92: "\\", 34: '"', 110: "\n", 114: "\r", 116: "\t"}
                    if esc not in esc_map:
                        raise ValueError("unsupported escape sequence")
                    chars.append(esc_map[esc])
                    i += 1
                elif c < 32 or c >= 127:
                    raise ValueError("control or non-ASCII byte in string literal")
                else:
                    chars.append(chr(c))
                    i += 1
            if not closed:
                raise ValueError("unterminated string literal")
            tokens.append(("str", "".join(chars)))
        elif _is_valid_atom_byte(b):
            start = i
            while i < n and _is_valid_atom_byte(raw[i]):
                i += 1
            if i < n and not (_is_sexp_ws(raw[i]) or raw[i] in (40, 41)):
                raise ValueError("invalid character in bare atom")
            tokens.append(("atom", raw[start:i].decode("ascii")))
        else:
            raise ValueError(f"invalid byte 0x{b:02x} in S-expression")

    stack: list[list[SExp]] = []
    top: list[SExp] = []
    for tok in tokens:
        if tok == "(":
            if len(stack) + 1 > MAX_SEXP_DEPTH:
                raise ValueError("S-expression exceeds maximum nesting depth 1024")
            stack.append([])
        elif tok == ")":
            if not stack:
                raise ValueError("unexpected closing parenthesis")
            done = SList(tuple(stack.pop()))
            if stack:
                stack[-1].append(done)
            else:
                top.append(done)
        else:
            kind, text = tok
            node: SExp = SStr(text) if kind == "str" else SAtom(text)
            if stack:
                stack[-1].append(node)
            else:
                top.append(node)

    if stack:
        raise ValueError("unclosed opening parenthesis")
    if len(top) != 1:
        raise ValueError("expected exactly one root S-expression")
    return top[0]


def _expect_canonical_nat(atom: SExp) -> int:
    if not isinstance(atom, SAtom) or not atom.val.isascii() or not atom.val.isdigit():
        raise ValueError("expected canonical unsigned decimal atom")
    if len(atom.val) > 1 and atom.val.startswith("0"):
        raise ValueError("leading zero in canonical decimal atom")
    return int(atom.val)


def _expect_bit_width(sx: SExp) -> int:
    w = _expect_canonical_nat(sx)
    if w not in SUPPORTED_BIT_WIDTHS:
        raise ValueError(f"unsupported bitwidth {w}")
    return w


def _expect_bool01(sx: SExp) -> int:
    v = _expect_canonical_nat(sx)
    if v not in (0, 1):
        raise ValueError("expected 0 or 1 flag")
    return v


def _validate_cert_expr_mirror(sx: SExp, let_env: dict[str, int]) -> int:
    if not isinstance(sx, SList) or not sx.items or not isinstance(sx.items[0], SAtom):
        raise ValueError("malformed cert_expr")
    tag = sx.items[0].val
    args = sx.items[1:]
    if tag == "bv":
        if len(args) != 2:
            raise ValueError("malformed bv")
        w = _expect_bit_width(args[0])
        val = _expect_canonical_nat(args[1])
        if val >= (1 << w):
            raise ValueError("bv literal out of range for width")
        return w
    if tag == "poison":
        if len(args) != 1:
            raise ValueError("malformed poison")
        return _expect_bit_width(args[0])
    if tag == "var":
        if len(args) != 2 or not isinstance(args[0], SStr) or not args[0].val:
            raise ValueError("malformed var")
        nm = args[0].val
        w = _expect_bit_width(args[1])
        if nm in let_env:
            if let_env[nm] != w:
                raise ValueError("let-bound var width mismatch")
            return w
        if nm.startswith("$"):
            raise ValueError(f"unbound $-variable {nm}")
        return w
    if tag == "binop":
        if len(args) != 5 or not isinstance(args[0], SAtom):
            raise ValueError("malformed binop")
        op = args[0].val
        if op not in CERT_BINOPS:
            raise ValueError(f"unknown binop {op}")
        w = _expect_bit_width(args[1])
        fl = args[2]
        if (
            not isinstance(fl, SList)
            or len(fl.items) != 5
            or fl.items[0] != SAtom("flags")
        ):
            raise ValueError("malformed binop flags")
        nuw, nsw, exact, disj = (_expect_bool01(x) for x in fl.items[1:])
        if op in ("add", "sub", "mul", "shl") and (exact or disj):
            raise ValueError("invalid flags for arithmetic/shl binop")
        if op in ("udiv", "sdiv", "lshr", "ashr") and (nuw or nsw or disj):
            raise ValueError("invalid flags for div/shr binop")
        if op == "or" and (nuw or nsw or exact):
            raise ValueError("invalid flags for or binop")
        if op in ("urem", "srem", "and", "xor") and (nuw or nsw or exact or disj):
            raise ValueError("invalid flags for flagless binop")
        if (
            _validate_cert_expr_mirror(args[3], let_env) != w
            or _validate_cert_expr_mirror(args[4], let_env) != w
        ):
            raise ValueError("binop operand width mismatch")
        return w
    if tag == "icmp":
        if len(args) != 5 or not isinstance(args[0], SAtom) or args[0].val not in CERT_ICMPS:
            raise ValueError("malformed icmp")
        _expect_bool01(args[1])
        w = _expect_bit_width(args[2])
        if (
            _validate_cert_expr_mirror(args[3], let_env) != w
            or _validate_cert_expr_mirror(args[4], let_env) != w
        ):
            raise ValueError("icmp operand width mismatch")
        return 1
    if tag == "cast":
        if len(args) != 5 or not isinstance(args[0], SAtom) or args[0].val not in CERT_CASTS:
            raise ValueError("malformed cast")
        kind = args[0].val
        fw = _expect_bit_width(args[1])
        tw = _expect_bit_width(args[2])
        fl = args[3]
        if (
            not isinstance(fl, SList)
            or len(fl.items) != 4
            or fl.items[0] != SAtom("flags")
        ):
            raise ValueError("malformed cast flags")
        nneg, nuw, nsw = (_expect_bool01(x) for x in fl.items[1:])
        if kind == "zext" and not (fw < tw and not nuw and not nsw):
            raise ValueError("invalid zext cast")
        if kind == "sext" and not (fw < tw and not nneg and not nuw and not nsw):
            raise ValueError("invalid sext cast")
        if kind == "trunc" and not (tw < fw and not nneg):
            raise ValueError("invalid trunc cast")
        if _validate_cert_expr_mirror(args[4], let_env) != fw:
            raise ValueError("cast operand width mismatch")
        return tw
    if tag == "select":
        if len(args) != 4:
            raise ValueError("malformed select")
        w = _expect_bit_width(args[0])
        if (
            _validate_cert_expr_mirror(args[1], let_env) != 1
            or _validate_cert_expr_mirror(args[2], let_env) != w
            or _validate_cert_expr_mirror(args[3], let_env) != w
        ):
            raise ValueError("select operand width mismatch")
        return w
    if tag == "freeze":
        if len(args) != 2:
            raise ValueError("malformed freeze")
        w = _expect_bit_width(args[0])
        if _validate_cert_expr_mirror(args[1], let_env) != w:
            raise ValueError("freeze operand width mismatch")
        return w
    if tag == "let":
        if len(args) != 2 or not isinstance(args[0], SList) or not args[0].items:
            raise ValueError("malformed let")
        cur_env = dict(let_env)
        seen: set[str] = set()
        for bind in args[0].items:
            if (
                not isinstance(bind, SList)
                or len(bind.items) != 2
                or not isinstance(bind.items[0], SStr)
            ):
                raise ValueError("malformed let binding")
            bnm = bind.items[0].val
            if len(bnm) < 2 or not bnm.startswith("$") or bnm in seen:
                raise ValueError(f"invalid or duplicate let variable {bnm!r}")
            bw = _validate_cert_expr_mirror(bind.items[1], cur_env)
            seen.add(bnm)
            cur_env[bnm] = bw
        return _validate_cert_expr_mirror(args[1], cur_env)
    raise ValueError(f"unknown cert_expr tag {tag}")


def validate_cert_v1_mirror(raw: bytes) -> None:
    root = parse_cert_sexp_mirror(raw)
    if (
        not isinstance(root, SList)
        or len(root.items) < 6
        or root.items[0] != SAtom("cert-v1")
    ):
        raise ValueError("expected (cert-v1 ...) root")
    fn_sx, src_h_sx, tgt_h_sx, blocks_sx = root.items[1:5]
    ret_sx = root.items[-1]
    if (
        not isinstance(fn_sx, SList)
        or len(fn_sx.items) != 2
        or fn_sx.items[0] != SAtom("fn")
        or not isinstance(fn_sx.items[1], SStr)
        or not fn_sx.items[1].val
    ):
        raise ValueError("invalid (fn ...) header")
    for expected_tag, hsx in (("src-sha256", src_h_sx), ("tgt-sha256", tgt_h_sx)):
        if (
            not isinstance(hsx, SList)
            or len(hsx.items) != 2
            or hsx.items[0] != SAtom(expected_tag)
            or not isinstance(hsx.items[1], SAtom)
        ):
            raise ValueError(f"invalid ({expected_tag} ...) header")
        hex_str = hsx.items[1].val
        if len(hex_str) != 64 or any(c not in "0123456789abcdef" for c in hex_str):
            raise ValueError(f"non-canonical sha256 in {expected_tag}")
    if (
        not isinstance(blocks_sx, SList)
        or len(blocks_sx.items) < 2
        or blocks_sx.items[0] != SAtom("blocks")
    ):
        raise ValueError("expected non-empty (blocks ...)")
    for blk in blocks_sx.items[1:]:
        if (
            not isinstance(blk, SList)
            or len(blk.items) != 7
            or blk.items[0] != SAtom("block")
        ):
            raise ValueError("malformed (block ...)")
        ub_sx = blk.items[4]
        if not isinstance(ub_sx, SList) or not ub_sx.items or ub_sx.items[0] != SAtom("ub-assumptions"):
            raise ValueError("malformed (ub-assumptions ...)")
        for ua in ub_sx.items[1:]:
            if not isinstance(ua, SList) or not ua.items or not isinstance(ua.items[0], SAtom):
                raise ValueError("malformed ub_assumption")
            utag = ua.items[0].val
            if utag == "param-noundef":
                if (
                    len(ua.items) != 3
                    or not isinstance(ua.items[1], SStr)
                    or not ua.items[1].val
                    or ua.items[1].val.startswith("$")
                ):
                    raise ValueError("malformed param-noundef")
                _expect_bit_width(ua.items[2])
            elif utag == "divisor-nonzero":
                if len(ua.items) != 2:
                    raise ValueError("malformed divisor-nonzero")
                _validate_cert_expr_mirror(ua.items[1], {})
            else:
                raise ValueError(f"unexpected ub_assumption {utag} in mirror")
    if (
        not isinstance(ret_sx, SList)
        or len(ret_sx.items) != 2
        or ret_sx.items[0] != SAtom("return")
        or not isinstance(ret_sx.items[1], SList)
        or not ret_sx.items[1].items
    ):
        raise ValueError("malformed (return ...)")
    ro = ret_sx.items[1]
    if ro.items == (SAtom("void-equiv"),):
        return
    if len(ro.items) != 5 or ro.items[0] != SAtom("scalar-refines"):
        raise ValueError("malformed return obligation")
    w_sx, s_sx, t_sx, smt_sx = ro.items[1:]
    if not isinstance(w_sx, SList) or len(w_sx.items) != 2 or w_sx.items[0] != SAtom("width"):
        raise ValueError("malformed return width")
    w = _expect_bit_width(w_sx.items[1])
    for etag, esx in (("src", s_sx), ("tgt", t_sx)):
        if not isinstance(esx, SList) or len(esx.items) != 2 or esx.items[0] != SAtom(etag):
            raise ValueError(f"malformed ({etag} ...)")
        if _validate_cert_expr_mirror(esx.items[1], {}) != w:
            raise ValueError(f"{etag} expression width mismatch")
    if (
        not isinstance(smt_sx, SList)
        or len(smt_sx.items) != 2
        or smt_sx.items[0] != SAtom("smt-verified")
        or smt_sx.items[1] not in (SAtom("true"), SAtom("false"))
    ):
        raise ValueError("malformed (smt-verified ...)")


# ---------------------------------------------------------------------------
# Positive & Adversarial Test Corpus (28 deterministic cases)
# ---------------------------------------------------------------------------


def build_suite_cases() -> list[SuiteCase]:
    cases: list[SuiteCase] = []

    # ---- A. Positive Acceptance Cases (returncode == 0) ----

    def prep_pos_add_zero_fold(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %t0 = add i32 %x, 0\n"
            "  %res = add i32 %t0, 42\n"
            "  ret i32 %res\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %res = add i32 %x, 42\n"
            "  ret i32 %res\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 0)) (bv 32 42))',
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 42))',
            ),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="pos_add_zero_fold",
            expect_accept=True,
            description="(x + 0) + 42 -> x + 42 algebraic identity fold",
            prepare=prep_pos_add_zero_fold,
            expect_cert_parse_ok=True,
        )
    )

    def prep_pos_reassoc_const_add(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %t0 = add i32 %x, 1\n"
            "  %res = add i32 %t0, 1\n"
            "  ret i32 %res\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %res = add i32 %x, 2\n"
            "  ret i32 %res\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1)) (bv 32 1))',
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 2))',
            ),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="pos_reassoc_const_add",
            expect_accept=True,
            description="(x + 1) + 1 -> x + 2 constant reassociation",
            prepare=prep_pos_reassoc_const_add,
            expect_cert_parse_ok=True,
        )
    )

    def prep_pos_xor_self_poison_refines_zero(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %res = xor i32 %x, %x\n"
            "  ret i32 %res\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 0\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                '(binop xor 32 (flags 0 0 0 0) (var "%x" 32) (var "%x" 32))',
                "(bv 32 0)",
            ),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="pos_xor_self_poison_refines_zero",
            expect_accept=True,
            description="xor i32 %x, %x -> 0 directional poison-to-concrete refinement",
            prepare=prep_pos_xor_self_poison_refines_zero,
            expect_cert_parse_ok=True,
        )
    )

    def prep_pos_noundef_param_assumption(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 noundef %x, i1 %c) {\n"
            "entry:\n"
            "  %fx = freeze i32 %x\n"
            "  %res = select i1 %c, i32 %fx, i32 0\n"
            "  ret i32 %res\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 noundef %x, i1 %c) {\n"
            "entry:\n"
            "  %res = select i1 %c, i32 %x, i32 0\n"
            "  ret i32 %res\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                '(select 32 (var "%c" 1) (freeze 32 (var "%x" 32)) (bv 32 0))',
                '(select 32 (var "%c" 1) (var "%x" 32) (bv 32 0))',
            ),
            ub_assumptions=('(param-noundef "%x" 32)',),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="pos_noundef_param_assumption",
            expect_accept=True,
            description="prototype noundef justifies (param-noundef \"%x\" 32) freeze elimination",
            prepare=prep_pos_noundef_param_assumption,
            expect_cert_parse_ok=True,
        )
    )

    def prep_pos_freeze_fold(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %fr = freeze i32 %x\n"
            "  %res = or i32 %fr, -1\n"
            "  ret i32 %res\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 -1\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                '(binop or 32 (flags 0 0 0 0) (freeze 32 (var "%x" 32)) (bv 32 4294967295))',
                "(bv 32 4294967295)",
            ),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="pos_freeze_fold",
            expect_accept=True,
            description="or i32 (freeze i32 %x), -1 -> -1 relational freeze fold (F-44)",
            prepare=prep_pos_freeze_fold,
            expect_cert_parse_ok=True,
        )
    )

    def prep_pos_check_merge_cert_and_safe(
        wd: pathlib.Path, vbin: pathlib.Path, fbin: pathlib.Path
    ) -> PreparedInvocation:
        f_src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %res = add i32 %x, 0\n"
            "  ret i32 %res\n"
            "}\n"
        )
        f_tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 %x\n"
            "}\n"
        )
        g_src = (
            "define i32 @g(i32 %y) {\n"
            "entry:\n"
            "  %slot = alloca i32, align 4\n"
            "  store i32 %y, ptr %slot, align 4\n"
            "  %loaded = load i32, ptr %slot, align 4\n"
            "  %sum = add i32 %loaded, 7\n"
            "  ret i32 %sum\n"
            "}\n"
        )
        f_src_p = wd / "f_src.ll"
        f_tgt_p = wd / "f_tgt.ll"
        f_cert_p = wd / "f.cert"
        g_src_p = wd / "g_src.ll"
        g_safe_p = wd / "g_safe.ll"
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"

        f_src_p.write_text(f_src, encoding="utf-8", newline="\n")
        f_tgt_p.write_text(f_tgt, encoding="utf-8", newline="\n")
        f_cert_bytes = build_cert_v1(
            "f",
            f_src,
            f_tgt,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 0))',
                '(var "%x" 32)',
            ),
        )
        f_cert_p.write_bytes(f_cert_bytes)
        g_src_p.write_text(g_src, encoding="utf-8", newline="\n")

        safe_gen = run_process(
            [str(fbin), "--pass", "pipeline", "-o", str(g_safe_p), str(g_src_p)],
            DEFAULT_TIMEOUT_SEC,
        )
        if safe_gen.timed_out or safe_gen.returncode != 0:
            raise RuntimeError(
                f"verified-opt-fallback failed on g_src.ll "
                f"(rc={safe_gen.returncode}): {safe_gen.stderr.strip()}"
            )
        g_safe = g_safe_p.read_text(encoding="utf-8")

        orig_p.write_text(f_src + "\n" + g_src, encoding="utf-8", newline="\n")
        merged_p.write_text(f_tgt + "\n" + g_safe, encoding="utf-8", newline="\n")

        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
                "--slice-cert",
                "f",
                str(f_src_p),
                str(f_tgt_p),
                str(f_cert_p),
                "--slice-safe",
                "g",
                str(g_src_p),
                str(g_safe_p),
            ],
            cert_bytes_for_grammar_check=f_cert_bytes,
        )

    cases.append(
        SuiteCase(
            name="pos_check_merge_cert_and_safe",
            expect_accept=True,
            description="2-function --check-merge combining --slice-cert (@f) and live --slice-safe (@g)",
            prepare=prep_pos_check_merge_cert_and_safe,
            expect_cert_parse_ok=True,
        )
    )

    def prep_pos_check_merge_composed_safe_cert(
        wd: pathlib.Path, vbin: pathlib.Path, fbin: pathlib.Path
    ) -> PreparedInvocation:
        g_src = (
            "define i32 @g(i32 %y) {\n"
            "entry:\n"
            "  %slot = alloca i32, align 4\n"
            "  store i32 %y, ptr %slot, align 4\n"
            "  %loaded = load i32, ptr %slot, align 4\n"
            "  %sum = add i32 %loaded, 7\n"
            "  ret i32 %sum\n"
            "}\n"
        )
        g_src_p = wd / "g_src.ll"
        g_mid_p = wd / "g_mid_safe.ll"
        g_fast_p = wd / "g_opt_fast.ll"
        g_cert_p = wd / "g.cert"
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        g_src_p.write_text(g_src, encoding="utf-8", newline="\n")

        safe_gen = run_process(
            [str(fbin), "--pass", "pipeline", "-o", str(g_mid_p), str(g_src_p)],
            DEFAULT_TIMEOUT_SEC,
        )
        if safe_gen.timed_out or safe_gen.returncode != 0:
            raise RuntimeError(
                f"verified-opt-fallback failed on g_src.ll "
                f"(rc={safe_gen.returncode}): {safe_gen.stderr.strip()}"
            )
        g_mid = g_mid_p.read_text(encoding="utf-8")
        rhs_var = "%loaded" if "add i32 %loaded, 7" in g_mid else "%y"
        g_fast = g_mid.replace(f"add i32 {rhs_var}, 7", f"add i32 7, {rhs_var}")
        if g_fast == g_mid:
            raise RuntimeError(f"unexpected verified-opt-fallback output for @g:\n{g_mid}")
        g_fast_p.write_text(g_fast, encoding="utf-8", newline="\n")
        cert_bytes = build_cert_v1(
            "g",
            g_mid,
            g_fast,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (var "%y" 32) (bv 32 7))',
                '(binop add 32 (flags 0 0 0 0) (bv 32 7) (var "%y" 32))',
            ),
        )
        g_cert_p.write_bytes(cert_bytes)
        orig_p.write_text(g_src, encoding="utf-8", newline="\n")
        merged_p.write_text(g_fast, encoding="utf-8", newline="\n")
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
                "--slice-safe-cert",
                "g",
                str(g_src_p),
                str(g_mid_p),
                str(g_fast_p),
                str(g_cert_p),
            ],
            cert_bytes_for_grammar_check=cert_bytes,
        )

    cases.append(
        SuiteCase(
            name="pos_check_merge_composed_safe_cert",
            expect_accept=True,
            description="--check-merge --slice-safe-cert composed Safe-Path -> Fast-Path acceptance",
            prepare=prep_pos_check_merge_composed_safe_cert,
            expect_cert_parse_ok=True,
        )
    )

    # ---- B. Adversarial Forged-Certificate, Soundness & DoS Rejection Cases ----

    def prep_neg_wrong_const(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %res = add i32 %x, 42\n"
            "  ret i32 %res\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %res = add i32 %x, 43\n"
            "  ret i32 %res\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 42))',
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 43))',
            ),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_wrong_const",
            expect_accept=False,
            description="forged constant miscompilation: add x, 42 -> add x, 43",
            prepare=prep_neg_wrong_const,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_target_invented_nsw(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %res = add i32 %x, 42\n"
            "  ret i32 %res\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %res = add nsw i32 %x, 42\n"
            "  ret i32 %res\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 42))',
                '(binop add 32 (flags 0 1 0 0) (var "%x" 32) (bv 32 42))',
            ),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_target_invented_nsw",
            expect_accept=False,
            description="target-invented nsw poison injection: add i32 -> add nsw i32",
            prepare=prep_neg_target_invented_nsw,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_target_invented_gep_inbounds(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(ptr %p, i64 %idx) {\n"
            "entry:\n"
            "  %q = getelementptr i8, ptr %p, i64 %idx\n"
            "  ret i32 0\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(ptr %p, i64 %idx) {\n"
            "entry:\n"
            "  %q = getelementptr inbounds i8, ptr %p, i64 %idx\n"
            "  ret i32 0\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(32, "(bv 32 0)", "(bv 32 0)"),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_target_invented_gep_inbounds",
            expect_accept=False,
            description="target-invented getelementptr inbounds poison flag (F-21)",
            prepare=prep_neg_target_invented_gep_inbounds,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_target_invented_fast_math(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define float @f(float %a, float %b) {\n"
            "entry:\n"
            "  %r = fadd float %a, %b\n"
            "  ret float %r\n"
            "}\n"
        )
        tgt = (
            "define float @f(float %a, float %b) {\n"
            "entry:\n"
            "  %r = fadd fast float %a, %b\n"
            "  ret float %r\n"
            "}\n"
        )
        cert = build_cert_v1("f", src, tgt, "(void-equiv)")
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_target_invented_fast_math",
            expect_accept=False,
            description="target-invented fast-math flag fadd float -> fadd fast float (F-17)",
            prepare=prep_neg_target_invented_fast_math,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_target_invented_fp_to_int_bitcast(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(float %x) {\n"
            "entry:\n"
            "  ret i32 0\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(float %x) {\n"
            "entry:\n"
            "  %bits = bitcast float %x to i32\n"
            "  %z = and i32 %bits, 0\n"
            "  ret i32 %z\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(32, "(bv 32 0)", "(bv 32 0)"),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_target_invented_fp_to_int_bitcast",
            expect_accept=False,
            description="target-invented bitcast float %x to i32 NaN payload leak (F-39)",
            prepare=prep_neg_target_invented_fp_to_int_bitcast,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_forged_noreturn_dc_attr(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 %x\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) noreturn {\n"
            "entry:\n"
            "  ret i32 %x\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(32, '(var "%x" 32)', '(var "%x" 32)'),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_forged_noreturn_dc_attr",
            expect_accept=False,
            description="target-invented noreturn function attribute UB escalation (F-60)",
            prepare=prep_neg_forged_noreturn_dc_attr,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_forged_nocreateundeforpoison_dc_attr(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %r = shl i32 %x, 32\n"
            "  ret i32 %r\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) nocreateundeforpoison {\n"
            "entry:\n"
            "  %r = shl i32 %x, 32\n"
            "  ret i32 %r\n"
            "}\n"
        )
        shl_expr = '(binop shl 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 32))'
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(32, shl_expr, shl_expr),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_forged_nocreateundeforpoison_dc_attr",
            expect_accept=False,
            description="target-invented nocreateundeforpoison attribute on poison return (F-60)",
            prepare=prep_neg_forged_nocreateundeforpoison_dc_attr,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_target_invented_freeze_poison(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f() {\n"
            "entry:\n"
            "  ret i32 0\n"
            "}\n"
        )
        tgt = (
            "define i32 @f() {\n"
            "entry:\n"
            "  %p = shl i32 1, 32\n"
            "  %fr = freeze i32 %p\n"
            "  ret i32 %fr\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                "(bv 32 0)",
                "(freeze 32 (binop shl 32 (flags 0 0 0 0) (bv 32 1) (bv 32 32)))",
            ),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_target_invented_freeze_poison",
            expect_accept=False,
            description="target-invented freeze(poison) claiming refinement of 0 (F-44)",
            prepare=prep_neg_target_invented_freeze_poison,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_unjustified_param_noundef(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x, i1 %c) {\n"
            "entry:\n"
            "  %fx = freeze i32 %x\n"
            "  %res = select i1 %c, i32 %fx, i32 0\n"
            "  ret i32 %res\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x, i1 %c) {\n"
            "entry:\n"
            "  %res = select i1 %c, i32 %x, i32 0\n"
            "  ret i32 %res\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(
                32,
                '(select 32 (var "%c" 1) (freeze 32 (var "%x" 32)) (bv 32 0))',
                '(select 32 (var "%c" 1) (var "%x" 32) (bv 32 0))',
            ),
            ub_assumptions=('(param-noundef "%x" 32)',),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_unjustified_param_noundef",
            expect_accept=False,
            description="forged (param-noundef \"%x\" 32) without prototype noundef on select fold",
            prepare=prep_neg_unjustified_param_noundef,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_poison_lhs_div_zero_inference(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x, i32 %d) {\n"
            "entry:\n"
            "  %p = shl i32 %x, 32\n"
            "  %q = sdiv i32 %p, %d\n"
            "  %z = and i32 %q, 0\n"
            "  ret i32 %z\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x, i32 %d) {\n"
            "entry:\n"
            "  %q = udiv i32 100, %d\n"
            "  %z = and i32 %q, 0\n"
            "  ret i32 %z\n"
            "}\n"
        )
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(32, "(bv 32 0)", "(bv 32 0)"),
            ub_assumptions=('(divisor-nonzero (var "%d" 32))',),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_poison_lhs_div_zero_inference",
            expect_accept=False,
            description="sdiv with poison LHS attempting to infer divisor != 0 (F-57)",
            prepare=prep_neg_poison_lhs_div_zero_inference,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_let_dag_30_exponential_bomb(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %z = and i32 %x, 0\n"
            "  ret i32 %z\n"
            "}\n"
        )
        tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 1\n"
            "}\n"
        )
        binds = ['("$n0" (var "%x" 32))']
        for k in range(1, 31):
            prev = f"$n{k - 1}"
            binds.append(
                f'("$n{k}" (binop xor 32 (flags 0 0 0 0) (var "{prev}" 32) (var "{prev}" 32)))'
            )
        let_dag = f'(let ({" ".join(binds)}) (var "$n30" 32))'
        cert = build_cert_v1(
            "f",
            src,
            tgt,
            scalar_refines_sexp(32, let_dag, "(bv 32 1)"),
        )
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_let_dag_30_exponential_bomb",
            expect_accept=False,
            description="30-level shared CE_Let xor DAG bomb claiming constant 1 (< 5s, F-63)",
            prepare=prep_neg_let_dag_30_exponential_bomb,
            timeout_sec=LET_DAG_BOMB_TIMEOUT_SEC,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_deep_sexp_1100_parens(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        ir = "define i32 @f(i32 %x) {\nentry:\n  ret i32 %x\n}\n"
        deep_cert = ("(" * 1100 + "cert-v1" + ")" * 1100 + "\n").encode("utf-8")
        return write_tv_files(wd, vbin, ir, ir, deep_cert)

    cases.append(
        SuiteCase(
            name="neg_deep_sexp_1100_parens",
            expect_accept=False,
            description="1,100 nested parentheses exceeding MAX_SEXP_DEPTH = 1024",
            prepare=prep_neg_deep_sexp_1100_parens,
            expect_cert_parse_ok=False,
        )
    )

    def prep_neg_large_4mib_padded_cert_no_stack_overflow(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        ir = "define i32 @f(i32 %x) {\nentry:\n  ret i32 %x\n}\n"
        padded_cert = (b" " * (4 * 1024 * 1024)) + b"(cert-v1 bad)\n"
        return write_tv_files(wd, vbin, ir, ir, padded_cert)

    cases.append(
        SuiteCase(
            name="neg_large_4mib_padded_cert_no_stack_overflow",
            expect_accept=False,
            description="4 MiB whitespace-padded invalid .cert exits in (3, 4) without Stack_overflow (F-62)",
            prepare=prep_neg_large_4mib_padded_cert_no_stack_overflow,
            allowed_reject_codes=(3, 4),
            expect_cert_parse_ok=False,
        )
    )

    def prep_neg_bare_dollar_let_name(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        ir = "define i32 @f() {\nentry:\n  ret i32 0\n}\n"
        cert = build_cert_v1(
            "f",
            ir,
            ir,
            scalar_refines_sexp(
                32,
                '(let (("$" (bv 32 0))) (var "$" 32))',
                "(bv 32 0)",
            ),
        )
        return write_tv_files(wd, vbin, ir, ir, cert)

    cases.append(
        SuiteCase(
            name="neg_bare_dollar_let_name",
            expect_accept=False,
            description='empty bare "$" let variable name rejected by is_dollar_let_name',
            prepare=prep_neg_bare_dollar_let_name,
            expect_cert_parse_ok=False,
        )
    )

    def prep_neg_nul_byte_in_cert(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        ir = "define i32 @f() {\nentry:\n  ret i32 0\n}\n"
        valid_cert = build_cert_v1(
            "f", ir, ir, scalar_refines_sexp(32, "(bv 32 0)", "(bv 32 0)")
        )
        nul_cert = valid_cert.replace(b"(blocks", b"\x00(blocks", 1)
        return write_tv_files(wd, vbin, ir, ir, nul_cert)

    cases.append(
        SuiteCase(
            name="neg_nul_byte_in_cert",
            expect_accept=False,
            description="embedded NUL (\\x00) byte in .cert rejected by S-expression lexer",
            prepare=prep_neg_nul_byte_in_cert,
            expect_cert_parse_ok=False,
        )
    )

    def prep_neg_bad_sha256_uppercase_hex(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        ir = "define i32 @f() {\nentry:\n  ret i32 0\n}\n"
        cert = build_cert_v1(
            "f",
            ir,
            ir,
            scalar_refines_sexp(32, "(bv 32 0)", "(bv 32 0)"),
            src_hash_override="A" * 64,
        )
        return write_tv_files(wd, vbin, ir, ir, cert)

    cases.append(
        SuiteCase(
            name="neg_bad_sha256_uppercase_hex",
            expect_accept=False,
            description="uppercase SHA-256 hex atom rejected by canonical lowercase gate",
            prepare=prep_neg_bad_sha256_uppercase_hex,
            expect_cert_parse_ok=False,
        )
    )

    def prep_neg_bad_sha256_short_63_hex(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        ir = "define i32 @f() {\nentry:\n  ret i32 0\n}\n"
        cert = build_cert_v1(
            "f",
            ir,
            ir,
            scalar_refines_sexp(32, "(bv 32 0)", "(bv 32 0)"),
            src_hash_override="a" * 63,
        )
        return write_tv_files(wd, vbin, ir, ir, cert)

    cases.append(
        SuiteCase(
            name="neg_bad_sha256_short_63_hex",
            expect_accept=False,
            description="truncated 63-char SHA-256 hex atom rejected by is_sha256_hex",
            prepare=prep_neg_bad_sha256_short_63_hex,
            expect_cert_parse_ok=False,
        )
    )

    def prep_neg_merge_legacy_unverified_slice_flag(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = "define i32 @f(i32 %x) {\nentry:\n  %r = add i32 %x, 0\n  ret i32 %r\n}\n"
        tgt = "define i32 @f(i32 %x) {\nentry:\n  ret i32 999\n}\n"
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        orig_p.write_text(src, encoding="utf-8", newline="\n")
        merged_p.write_text(tgt, encoding="utf-8", newline="\n")
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
                "--slice",
                "f",
                str(orig_p),
                str(merged_p),
            ]
        )

    cases.append(
        SuiteCase(
            name="neg_merge_legacy_unverified_slice_flag",
            expect_accept=False,
            description="legacy unverified --slice flag rejected in --check-merge (F-64)",
            prepare=prep_neg_merge_legacy_unverified_slice_flag,
        )
    )

    def prep_neg_merge_tampered_safe_slice(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        g_src = (
            "define i32 @g(i32 %y) {\n"
            "entry:\n"
            "  %sum = add i32 %y, 1\n"
            "  ret i32 %sum\n"
            "}\n"
        )
        g_tampered = (
            "define i32 @g(i32 %y) {\n"
            "entry:\n"
            "  ret i32 999\n"
            "}\n"
        )
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        g_src_p = wd / "g_src.ll"
        g_tampered_p = wd / "g_tampered.ll"
        orig_p.write_text(g_src, encoding="utf-8", newline="\n")
        merged_p.write_text(g_tampered, encoding="utf-8", newline="\n")
        g_src_p.write_text(g_src, encoding="utf-8", newline="\n")
        g_tampered_p.write_text(g_tampered, encoding="utf-8", newline="\n")
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
                "--slice-safe",
                "g",
                str(g_src_p),
                str(g_tampered_p),
            ]
        )

    cases.append(
        SuiteCase(
            name="neg_merge_tampered_safe_slice",
            expect_accept=False,
            description="tampered --slice-safe body (ret i32 999) rejected against verified pipeline (F-64)",
            prepare=prep_neg_merge_tampered_safe_slice,
        )
    )

    def prep_neg_merge_smuggled_prototype_attr(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        f_src = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %r = add i32 %x, 0\n"
            "  ret i32 %r\n"
            "}\n"
        )
        f_tgt = (
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 %x\n"
            "}\n"
        )
        merged_smuggled = (
            "define i32 @f(i32 noundef %x) {\n"
            "entry:\n"
            "  ret i32 %x\n"
            "}\n"
        )
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        f_src_p = wd / "f_src.ll"
        f_tgt_p = wd / "f_tgt.ll"
        f_cert_p = wd / "f.cert"
        orig_p.write_text(f_src, encoding="utf-8", newline="\n")
        merged_p.write_text(merged_smuggled, encoding="utf-8", newline="\n")
        f_src_p.write_text(f_src, encoding="utf-8", newline="\n")
        f_tgt_p.write_text(f_tgt, encoding="utf-8", newline="\n")
        cert_bytes = build_cert_v1(
            "f",
            f_src,
            f_tgt,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 0))',
                '(var "%x" 32)',
            ),
        )
        f_cert_p.write_bytes(cert_bytes)
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
                "--slice-cert",
                "f",
                str(f_src_p),
                str(f_tgt_p),
                str(f_cert_p),
            ],
            cert_bytes_for_grammar_check=cert_bytes,
        )

    cases.append(
        SuiteCase(
            name="neg_merge_smuggled_prototype_attr",
            expect_accept=False,
            description="smuggled noundef parameter attribute on merged prototype rejected (F-19)",
            prepare=prep_neg_merge_smuggled_prototype_attr,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_merge_global_initializer_tamper(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        orig = (
            "@k_table = constant i32 7, align 4\n\n"
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 %x\n"
            "}\n"
        )
        merged = (
            "@k_table = constant i32 99, align 4\n\n"
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 %x\n"
            "}\n"
        )
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        orig_p.write_text(orig, encoding="utf-8", newline="\n")
        merged_p.write_text(merged, encoding="utf-8", newline="\n")
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
            ]
        )

    cases.append(
        SuiteCase(
            name="neg_merge_global_initializer_tamper",
            expect_accept=False,
            description="mutated global constant initializer in merged.ll rejected (F-33)",
            prepare=prep_neg_merge_global_initializer_tamper,
        )
    )

    def prep_neg_merge_extern_weak_injection(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        mod_ew = (
            "@ext_probe = extern_weak global i32\n\n"
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  ret i32 %x\n"
            "}\n"
        )
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        orig_p.write_text(mod_ew, encoding="utf-8", newline="\n")
        merged_p.write_text(mod_ew, encoding="utf-8", newline="\n")
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
            ]
        )

    cases.append(
        SuiteCase(
            name="neg_merge_extern_weak_injection",
            expect_accept=False,
            description="extern_weak global linkage rejected by ModuleMerge (F-33)",
            prepare=prep_neg_merge_extern_weak_injection,
        )
    )

    def prep_neg_merge_composed_forged_mid_safe(
        wd: pathlib.Path, vbin: pathlib.Path, fbin: pathlib.Path
    ) -> PreparedInvocation:
        g_src = (
            "define i32 @g(i32 %y) {\n"
            "entry:\n"
            "  %slot = alloca i32, align 4\n"
            "  store i32 %y, ptr %slot, align 4\n"
            "  %loaded = load i32, ptr %slot, align 4\n"
            "  %sum = add i32 %loaded, 7\n"
            "  ret i32 %sum\n"
            "}\n"
        )
        g_src_p = wd / "g_src.ll"
        g_real_mid_p = wd / "g_real_mid.ll"
        g_mid_p = wd / "g_mid_tampered.ll"
        g_fast_p = wd / "g_fast.ll"
        g_cert_p = wd / "g.cert"
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        g_src_p.write_text(g_src, encoding="utf-8", newline="\n")

        safe_gen = run_process(
            [str(fbin), "--pass", "pipeline", "-o", str(g_real_mid_p), str(g_src_p)],
            DEFAULT_TIMEOUT_SEC,
        )
        if safe_gen.timed_out or safe_gen.returncode != 0:
            raise RuntimeError(f"verified-opt-fallback failed: {safe_gen.stderr.strip()}")
        g_real_mid = g_real_mid_p.read_text(encoding="utf-8")
        rhs_var = "%loaded" if "add i32 %loaded, 7" in g_real_mid else "%y"
        g_mid_tampered = g_real_mid.replace(f"add i32 {rhs_var}, 7", f"add i32 {rhs_var}, 99")
        g_fast = g_real_mid.replace(f"add i32 {rhs_var}, 7", f"add i32 99, {rhs_var}")
        g_mid_p.write_text(g_mid_tampered, encoding="utf-8", newline="\n")
        g_fast_p.write_text(g_fast, encoding="utf-8", newline="\n")
        cert_bytes = build_cert_v1(
            "g",
            g_mid_tampered,
            g_fast,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (var "%y" 32) (bv 32 99))',
                '(binop add 32 (flags 0 0 0 0) (bv 32 99) (var "%y" 32))',
            ),
        )
        g_cert_p.write_bytes(cert_bytes)
        orig_p.write_text(g_src, encoding="utf-8", newline="\n")
        merged_p.write_text(g_fast, encoding="utf-8", newline="\n")
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
                "--slice-safe-cert",
                "g",
                str(g_src_p),
                str(g_mid_p),
                str(g_fast_p),
                str(g_cert_p),
            ],
            cert_bytes_for_grammar_check=cert_bytes,
        )

    cases.append(
        SuiteCase(
            name="neg_merge_composed_forged_mid_safe",
            expect_accept=False,
            description="tampered mid_safe.ll in --slice-safe-cert rejected by Safe-Path replay",
            prepare=prep_neg_merge_composed_forged_mid_safe,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_merge_composed_forged_cert(
        wd: pathlib.Path, vbin: pathlib.Path, fbin: pathlib.Path
    ) -> PreparedInvocation:
        g_src = (
            "define i32 @g(i32 %y) {\n"
            "entry:\n"
            "  %slot = alloca i32, align 4\n"
            "  store i32 %y, ptr %slot, align 4\n"
            "  %loaded = load i32, ptr %slot, align 4\n"
            "  %sum = add i32 %loaded, 7\n"
            "  ret i32 %sum\n"
            "}\n"
        )
        g_src_p = wd / "g_src.ll"
        g_mid_p = wd / "g_mid_safe.ll"
        g_fast_p = wd / "g_fast_forged.ll"
        g_cert_p = wd / "g_forged.cert"
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        g_src_p.write_text(g_src, encoding="utf-8", newline="\n")

        safe_gen = run_process(
            [str(fbin), "--pass", "pipeline", "-o", str(g_mid_p), str(g_src_p)],
            DEFAULT_TIMEOUT_SEC,
        )
        if safe_gen.timed_out or safe_gen.returncode != 0:
            raise RuntimeError(f"verified-opt-fallback failed: {safe_gen.stderr.strip()}")
        g_mid = g_mid_p.read_text(encoding="utf-8")
        rhs_var = "%loaded" if "add i32 %loaded, 7" in g_mid else "%y"
        g_fast_forged = g_mid.replace(f"add i32 {rhs_var}, 7", f"add i32 {rhs_var}, 99")
        g_fast_p.write_text(g_fast_forged, encoding="utf-8", newline="\n")
        cert_bytes = build_cert_v1(
            "g",
            g_mid,
            g_fast_forged,
            scalar_refines_sexp(
                32,
                '(binop add 32 (flags 0 0 0 0) (var "%y" 32) (bv 32 7))',
                '(binop add 32 (flags 0 0 0 0) (var "%y" 32) (bv 32 99))',
            ),
        )
        g_cert_p.write_bytes(cert_bytes)
        orig_p.write_text(g_src, encoding="utf-8", newline="\n")
        merged_p.write_text(g_fast_forged, encoding="utf-8", newline="\n")
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
                "--slice-safe-cert",
                "g",
                str(g_src_p),
                str(g_mid_p),
                str(g_fast_p),
                str(g_cert_p),
            ],
            cert_bytes_for_grammar_check=cert_bytes,
        )

    cases.append(
        SuiteCase(
            name="neg_merge_composed_forged_cert",
            expect_accept=False,
            description="unsound Stage-2 cert in --slice-safe-cert rejected by CertValidator kernel",
            prepare=prep_neg_merge_composed_forged_cert,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_intrinsic_uadd_sat_vs_usub_sat(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "declare i32 @llvm.uadd.sat.i32(i32, i32)\n"
            "define i32 @f(i32 %x, i32 %y) {\n"
            "entry:\n"
            "  %r = call i32 @llvm.uadd.sat.i32(i32 %x, i32 %y)\n"
            "  ret i32 %r\n"
            "}\n"
        )
        tgt = (
            "declare i32 @llvm.usub.sat.i32(i32, i32)\n"
            "define i32 @f(i32 %x, i32 %y) {\n"
            "entry:\n"
            "  %r = call i32 @llvm.usub.sat.i32(i32 %x, i32 %y)\n"
            "  ret i32 %r\n"
            "}\n"
        )
        uadd_sexp = (
            '(select 32 (icmp ult 0 32 (binop add 32 (flags 0 0 0 0) (var "%x" 32) (var "%y" 32)) (var "%x" 32)) '
            '(bv 32 4294967295) '
            '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (var "%y" 32)))'
        )
        usub_sexp = (
            '(select 32 (icmp ult 0 32 (var "%x" 32) (var "%y" 32)) '
            '(bv 32 0) '
            '(binop sub 32 (flags 0 0 0 0) (var "%x" 32) (var "%y" 32)))'
        )
        cert = build_cert_v1("f", src, tgt, scalar_refines_sexp(32, uadd_sexp, usub_sexp))
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_intrinsic_uadd_sat_vs_usub_sat",
            expect_accept=False,
            description="forged uadd.sat -> usub.sat intrinsic TV claim rejected by kernel",
            prepare=prep_neg_intrinsic_uadd_sat_vs_usub_sat,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_annotated_intrinsic_call_rejected(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        src = (
            "declare i32 @llvm.abs.i32(i32, i1 immarg)\n"
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %r = call i32 @llvm.abs.i32(i32 %x, i1 false)\n"
            "  ret i32 %r\n"
            "}\n"
        )
        tgt = (
            "declare i32 @llvm.abs.i32(i32, i1 immarg)\n"
            "define i32 @f(i32 %x) {\n"
            "entry:\n"
            "  %r = call noundef i32 @llvm.abs.i32(i32 noundef %x, i1 false), !range !0\n"
            "  ret i32 %r\n"
            "}\n"
            "!0 = !{i32 0, i32 2147483647}\n"
        )
        abs_sexp = (
            '(select 32 (icmp slt 0 32 (var "%x" 32) (bv 32 0)) '
            '(binop sub 32 (flags 0 0 0 0) (bv 32 0) (var "%x" 32)) '
            '(var "%x" 32))'
        )
        cert = build_cert_v1("f", src, tgt, scalar_refines_sexp(32, abs_sexp, abs_sexp))
        return write_tv_files(wd, vbin, src, tgt, cert)

    cases.append(
        SuiteCase(
            name="neg_annotated_intrinsic_call_rejected",
            expect_accept=False,
            description="intrinsic call site carrying noundef/!range metadata rejected on fast-path",
            prepare=prep_neg_annotated_intrinsic_call_rejected,
            expect_cert_parse_ok=True,
        )
    )

    def prep_neg_merge_non_intrinsic_declare_vs_smin(
        wd: pathlib.Path, vbin: pathlib.Path, _fbin: pathlib.Path
    ) -> PreparedInvocation:
        orig_ll = (
            "declare i32 @llvm.fake.helper.i32(i32, i32)\n"
            "define i32 @f(i32 %x, i32 %y) {\n"
            "entry:\n"
            "  %r = call i32 @llvm.fake.helper.i32(i32 %x, i32 %y)\n"
            "  ret i32 %r\n"
            "}\n"
        )
        merged_ll = (
            "declare i32 @llvm.smin.i32(i32, i32)\n"
            "define i32 @f(i32 %x, i32 %y) {\n"
            "entry:\n"
            "  %r = call i32 @llvm.smin.i32(i32 %x, i32 %y)\n"
            "  ret i32 %r\n"
            "}\n"
        )
        orig_p = wd / "orig.ll"
        merged_p = wd / "merged.ll"
        orig_p.write_text(orig_ll, encoding="utf-8", newline="\n")
        merged_p.write_text(merged_ll, encoding="utf-8", newline="\n")
        return PreparedInvocation(
            argv=[
                str(vbin),
                "--check-merge",
                "--orig",
                str(orig_p),
                "--merged",
                str(merged_p),
            ],
            cert_bytes_for_grammar_check=None,
        )

    cases.append(
        SuiteCase(
            name="neg_merge_non_intrinsic_declare_vs_smin",
            expect_accept=False,
            description="forged non-intrinsic @llvm.* declaration vs @llvm.smin.i32 rejected by --check-merge",
            prepare=prep_neg_merge_non_intrinsic_declare_vs_smin,
            expect_cert_parse_ok=None,
        )
    )

    return cases


def run_suite(
    cert_validator_bin: pathlib.Path,
    verified_opt_fallback_bin: pathlib.Path,
) -> int:
    for label, binary in (
        ("cert-validator", cert_validator_bin),
        ("verified-opt-fallback", verified_opt_fallback_bin),
    ):
        if not binary.is_file():
            print(f"[FAIL] {label} binary not found: {binary}", file=sys.stderr)
            return 2

    cases = build_suite_cases()
    passed = 0
    failures: list[str] = []

    with tempfile.TemporaryDirectory(prefix="llvmcert-forged-suite-") as tmp_root_str:
        tmp_root = pathlib.Path(tmp_root_str)
        for idx, case in enumerate(cases, start=1):
            case_dir = tmp_root / f"{idx:02d}_{case.name}"
            case_dir.mkdir(parents=True, exist_ok=True)
            polarity = "ACCEPT" if case.expect_accept else "REJECT"
            try:
                prepared = case.prepare(
                    case_dir, cert_validator_bin, verified_opt_fallback_bin
                )
                outcome = run_process(prepared.argv, case.timeout_sec)
                ok, summary = evaluate_outcome(case, outcome)
            except Exception as exc:  # noqa: BLE001
                ok = False
                summary = f"preparation raised {type(exc).__name__}: {exc}"

            status = "PASS" if ok else "FAIL"
            print(f"[{status}] ({idx:02d}/{len(cases):02d}) [{polarity}] {case.name}: {summary}")
            if ok:
                passed += 1
            else:
                failures.append(f"{case.name} ({case.description}): {summary}")

    pos_count = sum(1 for c in cases if c.expect_accept)
    neg_count = len(cases) - pos_count
    if failures:
        print(
            f"\nLayer-2 Forged-Certificate Suite FAILED ({passed}/{len(cases)} passed):",
            file=sys.stderr,
        )
        for fail in failures:
            print(f"  - {fail}", file=sys.stderr)
        return 1

    print(
        f"\nLayer-2 Forged-Certificate Suite OK: {passed}/{len(cases)} passed "
        f"({pos_count} positive, {neg_count} adversarial rejections, 0 crashes/timeouts)."
    )
    return 0


def run_self_test() -> int:
    cases = build_suite_cases()
    if len(cases) < 25:
        raise AssertionError(f"expected >= 25 cases, got {len(cases)}")
    names = [c.name for c in cases]
    if len(names) != len(set(names)):
        raise AssertionError("duplicate test case names in suite")

    pos_cases = [c for c in cases if c.expect_accept]
    neg_cases = [c for c in cases if not c.expect_accept]
    if len(pos_cases) < 6 or len(neg_cases) < 20:
        raise AssertionError("insufficient positive or negative case count")

    # 1. Verify evaluate_outcome catches signal deaths, Stack_overflow, timeouts, and exit-code polarity.
    sample_pos = pos_cases[0]
    sample_neg = neg_cases[0]
    sample_4m = next(
        c for c in cases if c.name == "neg_large_4mib_padded_cert_no_stack_overflow"
    )

    assert evaluate_outcome(sample_pos, CommandOutcome(0, "", "", 0.01))[0]
    assert not evaluate_outcome(sample_pos, CommandOutcome(4, "", "rejected", 0.01))[0]
    assert not evaluate_outcome(sample_neg, CommandOutcome(0, "", "", 0.01))[0]
    assert evaluate_outcome(sample_neg, CommandOutcome(4, "", "rejected", 0.01))[0]
    assert not evaluate_outcome(sample_neg, CommandOutcome(-11, "", "", 0.01))[0]
    assert not evaluate_outcome(
        sample_neg,
        CommandOutcome(2, "", "Fatal error: exception Stack_overflow\n", 0.01),
    )[0]
    assert not evaluate_outcome(
        sample_neg, CommandOutcome(124, "", "", 10.1, timed_out=True)
    )[0]
    assert evaluate_outcome(sample_4m, CommandOutcome(4, "", "rejected", 0.05))[0]
    assert not evaluate_outcome(sample_4m, CommandOutcome(2, "", "bad exit", 0.05))[0]

    # 2. Materialize all 28 cases, validate every .cert against the CertFormat.v grammar mirror,
    #    and run an end-to-end subprocess dry-run via synthetic wrapper executables.
    with tempfile.TemporaryDirectory(prefix="llvmcert-selftest-") as tmp_str:
        tmp = pathlib.Path(tmp_str)
        mock_fallback_py = tmp / "mock_fallback.py"
        mock_validator_py = tmp / "mock_validator.py"

        mock_fallback_py.write_text(
            "import pathlib, sys\n"
            "args = sys.argv[1:]\n"
            "out_idx = args.index('-o')\n"
            "out_p = pathlib.Path(args[out_idx + 1])\n"
            "in_p = pathlib.Path(args[out_idx + 2])\n"
            "text = in_p.read_text(encoding='utf-8')\n"
            "if '@g(' in text:\n"
            "    out_p.write_text(\n"
            "        'define i32 @g(i32 %y) {\\nentry:\\n  %sum = add i32 %y, 7\\n  ret i32 %sum\\n}\\n',\n"
            "        encoding='utf-8',\n"
            "        newline='\\n',\n"
            "    )\n"
            "else:\n"
            "    out_p.write_text(text, encoding='utf-8', newline='\\n')\n",
            encoding="utf-8",
            newline="\n",
        )

        mock_validator_py.write_text(
            "import pathlib, sys\n"
            "args = sys.argv[1:]\n"
            "case_dir = pathlib.Path(args[args.index('--orig') + 1] if '--check-merge' in args else args[args.index('--src') + 1]).parent\n"
            "if case_dir.name.split('_', 1)[1].startswith('pos_'):\n"
            "    sys.exit(0)\n"
            "if '--slice' in args:\n"
            "    sys.exit(2)\n"
            "sys.exit(4)\n",
            encoding="utf-8",
            newline="\n",
        )

        if sys.platform == "win32":
            vbin = tmp / "mock-cert-validator.cmd"
            fbin = tmp / "mock-verified-opt-fallback.cmd"
            vbin.write_text(
                f'@"{sys.executable}" -B "{mock_validator_py}" %*\r\n',
                encoding="utf-8",
            )
            fbin.write_text(
                f'@"{sys.executable}" -B "{mock_fallback_py}" %*\r\n',
                encoding="utf-8",
            )
        else:
            vbin = tmp / "mock-cert-validator"
            fbin = tmp / "mock-verified-opt-fallback"
            vbin.write_text(
                f'#!/usr/bin/env bash\nexec "{sys.executable}" -B "{mock_validator_py}" "$@"\n',
                encoding="utf-8",
            )
            fbin.write_text(
                f'#!/usr/bin/env bash\nexec "{sys.executable}" -B "{mock_fallback_py}" "$@"\n',
                encoding="utf-8",
            )
            vbin.chmod(0o755)
            fbin.chmod(0o755)

        grammar_checked = 0
        for case in cases:
            cdir = tmp / f"grammar_{case.name}"
            cdir.mkdir(parents=True, exist_ok=True)
            prep = case.prepare(cdir, vbin, fbin)
            if case.expect_cert_parse_ok is None:
                continue
            assert prep.cert_bytes_for_grammar_check is not None
            grammar_checked += 1
            if case.expect_cert_parse_ok:
                validate_cert_v1_mirror(prep.cert_bytes_for_grammar_check)
            else:
                rejected = False
                try:
                    validate_cert_v1_mirror(prep.cert_bytes_for_grammar_check)
                except ValueError:
                    rejected = True
                if not rejected:
                    raise AssertionError(
                        f"expected CertFormat.v mirror to reject {case.name}"
                    )

        # Verify subprocess timeout handling on a hanging helper script.
        hang_py = tmp / "hang.py"
        hang_py.write_text("import time\ntime.sleep(5)\n", encoding="utf-8")
        hang_out = run_process([sys.executable, "-B", str(hang_py)], 0.15)
        if not hang_out.timed_out:
            raise AssertionError("expected timeout detection on sleeping subprocess")

        rc = run_suite(vbin, fbin)
        if rc != 0:
            raise AssertionError(f"mock end-to-end run_suite returned {rc}")

    print(
        f"Self-test OK: {len(cases)} cases ({len(pos_cases)} positive, {len(neg_cases)} negative), "
        f"{grammar_checked} certificates verified against CertFormat.v grammar mirror."
    )
    return 0


def parse_cli_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Validate corpus grammar, crash/timeout guards, and mock runner offline.",
    )
    parser.add_argument(
        "cert_validator",
        nargs="?",
        help="Path to compiled cert-validator executable.",
    )
    parser.add_argument(
        "verified_opt_fallback",
        nargs="?",
        help="Path to compiled verified-opt-fallback executable.",
    )
    args = parser.parse_args(argv)
    if not args.self_test and (not args.cert_validator or not args.verified_opt_fallback):
        parser.error(
            "expected <cert-validator> <verified-opt-fallback> positional arguments "
            "(or --self-test)"
        )
    return args


def main(argv: list[str] | None = None) -> int:
    args = parse_cli_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return run_self_test()
    return run_suite(
        pathlib.Path(args.cert_validator).resolve(),
        pathlib.Path(args.verified_opt_fallback).resolve(),
    )


if __name__ == "__main__":
    sys.exit(main())
