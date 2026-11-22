#!/usr/bin/env python3
"""Dual-compiler (ocamlopt native vs. ocamlc bytecode) & certificate mutation suite.

Assures the OCaml-extracted `cert-validator` and `verified-opt-fallback` binaries:
1. 28/28 native-vs.-bytecode exit-code & accept/reject parity on `run_forged_cert_suite.py`.
2. 230 deterministic malformed-format, contract-tampered, and semantically unsound
   mutations verifying 100% rejection, 0 crashes/timeouts, and 100% native-vs.-bytecode
   exit-code parity.
3. Byte-for-byte identical `--pass pipeline` IR output between native `ocamlopt` and
   bytecode `ocamlc` builds of `verified-opt-fallback` across 5 core optimization patterns.
"""

from __future__ import annotations

import argparse
import dataclasses
import pathlib
import sys
import tempfile
from dataclasses import dataclass

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from run_forged_cert_suite import (  # noqa: E402
    CRASH_STDERR_MARKERS,
    CommandOutcome,
    build_cert_v1,
    build_suite_cases,
    evaluate_outcome,
    run_process,
    scalar_refines_sexp,
    sha256_hex,
)

BYTECODE_MIN_TIMEOUT_SEC = 60.0


@dataclass(frozen=True)
class SeedProof:
    name: str
    src_ir: str
    tgt_ir: str
    cert_text: str


@dataclass(frozen=True)
class MutationCase:
    name: str
    src_ir: str
    tgt_ir: str
    cert_bytes: bytes


def _build_valid_seeds() -> list[SeedProof]:
    seeds: list[SeedProof] = []

    s1_src = (
        "define i32 @f(i32 %x) {\n"
        "entry:\n"
        "  %t0 = add i32 %x, 0\n"
        "  %res = add i32 %t0, 42\n"
        "  ret i32 %res\n"
        "}\n"
    )
    s1_tgt = (
        "define i32 @f(i32 %x) {\n"
        "entry:\n"
        "  %res = add i32 %x, 42\n"
        "  ret i32 %res\n"
        "}\n"
    )
    s1_cert = build_cert_v1(
        "f",
        s1_src,
        s1_tgt,
        scalar_refines_sexp(
            32,
            '(binop add 32 (flags 0 0 0 0) (binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 0)) (bv 32 42))',
            '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 42))',
        ),
    ).decode("utf-8")
    seeds.append(SeedProof("add_zero_fold", s1_src, s1_tgt, s1_cert))

    s2_src = (
        "define i32 @f(i32 %x) {\n"
        "entry:\n"
        "  %t0 = add i32 %x, 1\n"
        "  %res = add i32 %t0, 1\n"
        "  ret i32 %res\n"
        "}\n"
    )
    s2_tgt = (
        "define i32 @f(i32 %x) {\n"
        "entry:\n"
        "  %res = add i32 %x, 2\n"
        "  ret i32 %res\n"
        "}\n"
    )
    s2_cert = build_cert_v1(
        "f",
        s2_src,
        s2_tgt,
        scalar_refines_sexp(
            32,
            '(binop add 32 (flags 0 0 0 0) (binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1)) (bv 32 1))',
            '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 2))',
        ),
    ).decode("utf-8")
    seeds.append(SeedProof("reassoc_const_add", s2_src, s2_tgt, s2_cert))

    s3_src = (
        "define i32 @f(i32 %x) {\n"
        "entry:\n"
        "  %res = xor i32 %x, %x\n"
        "  ret i32 %res\n"
        "}\n"
    )
    s3_tgt = (
        "define i32 @f(i32 %x) {\n"
        "entry:\n"
        "  ret i32 0\n"
        "}\n"
    )
    s3_cert = build_cert_v1(
        "f",
        s3_src,
        s3_tgt,
        scalar_refines_sexp(
            32,
            '(binop xor 32 (flags 0 0 0 0) (var "%x" 32) (var "%x" 32))',
            "(bv 32 0)",
        ),
    ).decode("utf-8")
    seeds.append(SeedProof("xor_self_zero", s3_src, s3_tgt, s3_cert))

    s4_src = (
        "define i32 @f(i32 noundef %x, i1 %c) {\n"
        "entry:\n"
        "  %fx = freeze i32 %x\n"
        "  %res = select i1 %c, i32 %fx, i32 0\n"
        "  ret i32 %res\n"
        "}\n"
    )
    s4_tgt = (
        "define i32 @f(i32 noundef %x, i1 %c) {\n"
        "entry:\n"
        "  %res = select i1 %c, i32 %x, i32 0\n"
        "  ret i32 %res\n"
        "}\n"
    )
    s4_cert = build_cert_v1(
        "f",
        s4_src,
        s4_tgt,
        scalar_refines_sexp(
            32,
            '(select 32 (var "%c" 1) (freeze 32 (var "%x" 32)) (bv 32 0))',
            '(select 32 (var "%c" 1) (var "%x" 32) (bv 32 0))',
        ),
        ub_assumptions=('(param-noundef "%x" 32)',),
    ).decode("utf-8")
    seeds.append(SeedProof("noundef_freeze_elim", s4_src, s4_tgt, s4_cert))

    s5_src = (
        "define i32 @f(i32 %x) {\n"
        "entry:\n"
        "  %fr = freeze i32 %x\n"
        "  %res = or i32 %fr, -1\n"
        "  ret i32 %res\n"
        "}\n"
    )
    s5_tgt = (
        "define i32 @f(i32 %x) {\n"
        "entry:\n"
        "  ret i32 -1\n"
        "}\n"
    )
    s5_cert = build_cert_v1(
        "f",
        s5_src,
        s5_tgt,
        scalar_refines_sexp(
            32,
            '(binop or 32 (flags 0 0 0 0) (freeze 32 (var "%x" 32)) (bv 32 4294967295))',
            "(bv 32 4294967295)",
        ),
    ).decode("utf-8")
    seeds.append(SeedProof("freeze_or_minus1", s5_src, s5_tgt, s5_cert))

    return seeds


def _replace_digest_char(cert_text: str, prefix: str, offset: int, repl: str) -> str:
    idx = cert_text.find(prefix)
    assert idx >= 0, f"missing prefix {prefix}"
    pos = idx + len(prefix) + offset
    return cert_text[:pos] + repl + cert_text[pos + 1 :]


def _resize_digest(cert_text: str, prefix: str, new_len: int) -> str:
    idx = cert_text.find(prefix)
    assert idx >= 0, f"missing prefix {prefix}"
    start = idx + len(prefix)
    digest = cert_text[start : start + 64]
    if new_len < 64:
        resized = digest[:new_len]
    else:
        resized = digest + "a" * (new_len - 64)
    return cert_text[:start] + resized + cert_text[start + 64 :]


def _mk_tv_mut(
    name: str,
    src_ir: str,
    tgt_ir: str,
    width: int,
    src_sexp: str,
    tgt_sexp: str,
    *,
    ub_assumptions: tuple[str, ...] = (),
) -> MutationCase:
    return MutationCase(
        name=name,
        src_ir=src_ir,
        tgt_ir=tgt_ir,
        cert_bytes=build_cert_v1(
            "f",
            src_ir,
            tgt_ir,
            scalar_refines_sexp(width, src_sexp, tgt_sexp),
            ub_assumptions=ub_assumptions,
        ),
    )


def _mk_single_inst_mut(
    name: str,
    sig: str,
    ret_ty: str,
    src_body: str,
    tgt_body: str,
    width: int,
    src_sexp: str,
    tgt_sexp: str,
) -> MutationCase:
    src_ir = f"define {ret_ty} @f({sig}) {{\nentry:\n{src_body}}}\n"
    tgt_ir = f"define {ret_ty} @f({sig}) {{\nentry:\n{tgt_body}}}\n"
    return _mk_tv_mut(name, src_ir, tgt_ir, width, src_sexp, tgt_sexp)


def build_mutation_cases() -> list[MutationCase]:
    seeds = _build_valid_seeds()
    cases: list[MutationCase] = []

    # 1. Strictly invalid SHA-256 format corruptions (10 * 5 = 50 cases).
    for seed in seeds:
        for pos, bad_ch in ((0, "g"), (31, "z"), (63, "-")):
            cases.append(
                MutationCase(
                    f"{seed.name}_src_sha_nonhex_{pos:02d}",
                    seed.src_ir,
                    seed.tgt_ir,
                    _replace_digest_char(seed.cert_text, "(src-sha256 ", pos, bad_ch).encode("utf-8"),
                )
            )
            cases.append(
                MutationCase(
                    f"{seed.name}_tgt_sha_nonhex_{pos:02d}",
                    seed.src_ir,
                    seed.tgt_ir,
                    _replace_digest_char(seed.cert_text, "(tgt-sha256 ", pos, bad_ch).encode("utf-8"),
                )
            )
        cases.append(
            MutationCase(
                f"{seed.name}_src_sha_upper",
                seed.src_ir,
                seed.tgt_ir,
                _replace_digest_char(seed.cert_text, "(src-sha256 ", 5, "A").encode("utf-8"),
            )
        )
        cases.append(
            MutationCase(
                f"{seed.name}_tgt_sha_upper",
                seed.src_ir,
                seed.tgt_ir,
                _replace_digest_char(seed.cert_text, "(tgt-sha256 ", 17, "F").encode("utf-8"),
            )
        )
        cases.append(
            MutationCase(
                f"{seed.name}_src_sha_trunc_63",
                seed.src_ir,
                seed.tgt_ir,
                _resize_digest(seed.cert_text, "(src-sha256 ", 63).encode("utf-8"),
            )
        )
        cases.append(
            MutationCase(
                f"{seed.name}_tgt_sha_overlong_65",
                seed.src_ir,
                seed.tgt_ir,
                _resize_digest(seed.cert_text, "(tgt-sha256 ", 65).encode("utf-8"),
            )
        )

    # 2. Structural S-expression / truncation / encoding corruptions (10 * 5 = 50 cases).
    for seed in seeds:
        raw = seed.cert_text.encode("utf-8")
        for frac_pct in (10, 25, 50, 75, 90):
            cut = max(1, (len(raw) * frac_pct) // 100)
            cases.append(
                MutationCase(f"{seed.name}_trunc_{frac_pct}pct", seed.src_ir, seed.tgt_ir, raw[:cut])
            )
        cases.append(
            MutationCase(
                f"{seed.name}_drop_closing_paren",
                seed.src_ir,
                seed.tgt_ir,
                seed.cert_text.rstrip()[:-1].encode("utf-8"),
            )
        )
        cases.append(
            MutationCase(
                f"{seed.name}_extra_trailing_paren",
                seed.src_ir,
                seed.tgt_ir,
                (seed.cert_text + ")").encode("utf-8"),
            )
        )
        mid = len(raw) // 2
        cases.append(
            MutationCase(
                f"{seed.name}_embedded_nul",
                seed.src_ir,
                seed.tgt_ir,
                raw[:mid] + b"\x00" + raw[mid:],
            )
        )
        cases.append(
            MutationCase(
                f"{seed.name}_wrong_magic_version",
                seed.src_ir,
                seed.tgt_ir,
                seed.cert_text.replace("(cert-v1", "(cert-v2", 1).encode("utf-8"),
            )
        )
        cases.append(
            MutationCase(
                f"{seed.name}_bracket_mismatch",
                seed.src_ir,
                seed.tgt_ir,
                seed.cert_text.replace("(blocks", "[blocks", 1).encode("utf-8"),
            )
        )

    # 3. Certificate schema, width, variable & function-name corruptions (12 * 5 = 60 cases).
    for seed in seeds:
        schema_variants: list[tuple[str, str]] = [
            ("fn_rename_g", seed.cert_text.replace('(fn "f")', '(fn "g")', 1)),
            ("fn_empty", seed.cert_text.replace('(fn "f")', '(fn "")', 1)),
            ("width_16", seed.cert_text.replace("(width 32)", "(width 16)", 1)),
            ("width_64", seed.cert_text.replace("(width 32)", "(width 64)", 1)),
            ("width_0", seed.cert_text.replace("(width 32)", "(width 0)", 1)),
            ("var_x_to_z", seed.cert_text.replace('"%x"', '"%z"')),
            ("bad_src_bb_tag", seed.cert_text.replace("(src-bb ", "(src-b ", 1)),
            ("bad_tgt_bb_tag", seed.cert_text.replace("(tgt-bb ", "(tgt-b ", 1)),
            ("bad_block_kind", seed.cert_text.replace("(kind entry)", "(kind bogus)", 1)),
            ("bad_smt_verified_tok", seed.cert_text.replace("(smt-verified false)", "(smt-verified maybe)", 1)),
            ("missing_blocks_section", seed.cert_text.replace("(blocks", "(blks", 1)),
            ("bad_return_tag", seed.cert_text.replace("(scalar-refines", "(scalar-bad", 1)),
        ]
        for vname, vtxt in schema_variants:
            cases.append(
                MutationCase(f"{seed.name}_{vname}", seed.src_ir, seed.tgt_ir, vtxt.encode("utf-8"))
            )

    # 4. Target IR prototype / attribute tampering (4 * 5 = 20 cases).
    for seed in seeds:
        ir_mutations: list[tuple[str, str]] = [
            ("ir_tgt_ret_attr_noundef", seed.tgt_ir.replace("define i32 @f(", "define noundef i32 @f(", 1)),
            ("ir_tgt_fn_noreturn", seed.tgt_ir.replace(") {", ") noreturn {", 1)),
            ("ir_tgt_fn_nocreate", seed.tgt_ir.replace(") {", ") nocreateundeforpoison {", 1)),
            ("ir_tgt_rename_g", seed.tgt_ir.replace("@f(", "@g(", 1)),
        ]
        for mname, m_tgt in ir_mutations:
            cases.append(
                MutationCase(f"{seed.name}_{mname}", seed.src_ir, m_tgt, seed.cert_text.encode("utf-8"))
            )

    # 5. Strictly unsound semantic, poison-laundering & bitvector miscompilations (50 cases).
    s1, s2, s3, s4, s5 = seeds
    cases.extend(
        [
            _mk_tv_mut(
                "add_zero_const_43_in_tgt",
                s1.src_ir,
                s1.tgt_ir.replace("42", "43"),
                32,
                '(binop add 32 (flags 0 0 0 0) (binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 0)) (bv 32 42))',
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 43))',
            ),
            _mk_tv_mut(
                "add_zero_target_nsw",
                s1.src_ir,
                s1.tgt_ir.replace("add i32", "add nsw i32"),
                32,
                '(binop add 32 (flags 0 0 0 0) (binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 0)) (bv 32 42))',
                '(binop add 32 (flags 0 1 0 0) (var "%x" 32) (bv 32 42))',
            ),
            _mk_tv_mut(
                "reassoc_target_nuw",
                s2.src_ir,
                s2.tgt_ir.replace("add i32", "add nuw i32"),
                32,
                '(binop add 32 (flags 0 0 0 0) (binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1)) (bv 32 1))',
                '(binop add 32 (flags 1 0 0 0) (var "%x" 32) (bv 32 2))',
            ),
            _mk_tv_mut(
                "xor_self_reversed_refines",
                s3.tgt_ir,
                s3.src_ir,
                32,
                "(bv 32 0)",
                '(binop xor 32 (flags 0 0 0 0) (var "%x" 32) (var "%x" 32))',
            ),
            _mk_tv_mut(
                "noundef_drop_param_attr",
                s4.src_ir.replace("i32 noundef %x", "i32 %x"),
                s4.tgt_ir.replace("i32 noundef %x", "i32 %x"),
                32,
                '(select 32 (var "%c" 1) (freeze 32 (var "%x" 32)) (bv 32 0))',
                '(select 32 (var "%c" 1) (var "%x" 32) (bv 32 0))',
                ub_assumptions=('(param-noundef "%x" 32)',),
            ),
            _mk_tv_mut(
                "freeze_or_reversed",
                s5.tgt_ir,
                s5.src_ir,
                32,
                "(bv 32 4294967295)",
                '(binop or 32 (flags 0 0 0 0) (freeze 32 (var "%x" 32)) (bv 32 4294967295))',
            ),
            _mk_tv_mut(
                "freeze_or_const_0",
                s5.src_ir,
                s5.tgt_ir.replace("-1", "0"),
                32,
                '(binop or 32 (flags 0 0 0 0) (freeze 32 (var "%x" 32)) (bv 32 4294967295))',
                "(bv 32 0)",
            ),
        ]
    )

    # 15 target-invented poison flag injections.
    binop_poison_specs = [
        ("add_nuw", "add", "add nuw", "(flags 0 0 0 0)", "(flags 1 0 0 0)", "5"),
        ("sub_nsw", "sub", "sub nsw", "(flags 0 0 0 0)", "(flags 0 1 0 0)", "5"),
        ("sub_nuw", "sub", "sub nuw", "(flags 0 0 0 0)", "(flags 1 0 0 0)", "5"),
        ("mul_nsw", "mul", "mul nsw", "(flags 0 0 0 0)", "(flags 0 1 0 0)", "3"),
        ("mul_nuw", "mul", "mul nuw", "(flags 0 0 0 0)", "(flags 1 0 0 0)", "3"),
        ("shl_nsw", "shl", "shl nsw", "(flags 0 0 0 0)", "(flags 0 1 0 0)", "2"),
        ("shl_nuw", "shl", "shl nuw", "(flags 0 0 0 0)", "(flags 1 0 0 0)", "2"),
        ("lshr_exact", "lshr", "lshr exact", "(flags 0 0 0 0)", "(flags 0 0 1 0)", "1"),
        ("ashr_exact", "ashr", "ashr exact", "(flags 0 0 0 0)", "(flags 0 0 1 0)", "1"),
        ("udiv_exact", "udiv", "udiv exact", "(flags 0 0 0 0)", "(flags 0 0 1 0)", "2"),
        ("sdiv_exact", "sdiv", "sdiv exact", "(flags 0 0 0 0)", "(flags 0 0 1 0)", "2"),
        ("or_disjoint", "or", "or disjoint", "(flags 0 0 0 0)", "(flags 0 0 0 1)", "1"),
    ]
    for mname, op, tgt_op, s_fl, t_fl, imm in binop_poison_specs:
        cases.append(
            _mk_single_inst_mut(
                f"poison_{mname}",
                "i32 %x",
                "i32",
                f"  %r = {op} i32 %x, {imm}\n  ret i32 %r\n",
                f"  %r = {tgt_op} i32 %x, {imm}\n  ret i32 %r\n",
                32,
                f'(binop {op} 32 {s_fl} (var "%x" 32) (bv 32 {imm}))',
                f'(binop {op} 32 {t_fl} (var "%x" 32) (bv 32 {imm}))',
            )
        )
    cases.extend(
        [
            _mk_single_inst_mut(
                "poison_trunc_nuw",
                "i32 %x",
                "i8",
                "  %r = trunc i32 %x to i8\n  ret i8 %r\n",
                "  %r = trunc nuw i32 %x to i8\n  ret i8 %r\n",
                8,
                '(cast trunc 32 8 (flags 0 0 0) (var "%x" 32))',
                '(cast trunc 32 8 (flags 0 1 0) (var "%x" 32))',
            ),
            _mk_single_inst_mut(
                "poison_trunc_nsw",
                "i32 %x",
                "i8",
                "  %r = trunc i32 %x to i8\n  ret i8 %r\n",
                "  %r = trunc nsw i32 %x to i8\n  ret i8 %r\n",
                8,
                '(cast trunc 32 8 (flags 0 0 0) (var "%x" 32))',
                '(cast trunc 32 8 (flags 0 0 1) (var "%x" 32))',
            ),
            _mk_single_inst_mut(
                "poison_zext_nneg",
                "i8 %x",
                "i32",
                "  %r = zext i8 %x to i32\n  ret i32 %r\n",
                "  %r = zext nneg i8 %x to i32\n  ret i32 %r\n",
                32,
                '(cast zext 8 32 (flags 0 0 0) (var "%x" 8))',
                '(cast zext 8 32 (flags 1 0 0) (var "%x" 8))',
            ),
        ]
    )

    # 28 semantically wrong arithmetic, bitwise, shift, icmp, select & cast miscompilations.
    cases.extend(
        [
            _mk_single_inst_mut(
                "bad_add_i8_const",
                "i8 %x",
                "i8",
                "  %r = add i8 %x, 5\n  ret i8 %r\n",
                "  %r = add i8 %x, 6\n  ret i8 %r\n",
                8,
                '(binop add 8 (flags 0 0 0 0) (var "%x" 8) (bv 8 5))',
                '(binop add 8 (flags 0 0 0 0) (var "%x" 8) (bv 8 6))',
            ),
            _mk_single_inst_mut(
                "bad_add_i16_const",
                "i16 %x",
                "i16",
                "  %r = add i16 %x, 100\n  ret i16 %r\n",
                "  %r = add i16 %x, 101\n  ret i16 %r\n",
                16,
                '(binop add 16 (flags 0 0 0 0) (var "%x" 16) (bv 16 100))',
                '(binop add 16 (flags 0 0 0 0) (var "%x" 16) (bv 16 101))',
            ),
            _mk_single_inst_mut(
                "bad_add_i64_const",
                "i64 %x",
                "i64",
                "  %r = add i64 %x, 42\n  ret i64 %r\n",
                "  %r = add i64 %x, 43\n  ret i64 %r\n",
                64,
                '(binop add 64 (flags 0 0 0 0) (var "%x" 64) (bv 64 42))',
                '(binop add 64 (flags 0 0 0 0) (var "%x" 64) (bv 64 43))',
            ),
            _mk_single_inst_mut(
                "bad_sub_commuted",
                "i32 %x",
                "i32",
                "  %r = sub i32 %x, 5\n  ret i32 %r\n",
                "  %r = sub i32 5, %x\n  ret i32 %r\n",
                32,
                '(binop sub 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 5))',
                '(binop sub 32 (flags 0 0 0 0) (bv 32 5) (var "%x" 32))',
            ),
            _mk_single_inst_mut(
                "bad_sub_self_to_one",
                "i32 %x",
                "i32",
                "  %r = sub i32 %x, %x\n  ret i32 %r\n",
                "  ret i32 1\n",
                32,
                '(binop sub 32 (flags 0 0 0 0) (var "%x" 32) (var "%x" 32))',
                "(bv 32 1)",
            ),
            _mk_single_inst_mut(
                "bad_mul3_to_shl1",
                "i32 %x",
                "i32",
                "  %r = mul i32 %x, 3\n  ret i32 %r\n",
                "  %r = shl i32 %x, 1\n  ret i32 %r\n",
                32,
                '(binop mul 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 3))',
                '(binop shl 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
            ),
            _mk_single_inst_mut(
                "bad_mul2_to_add2",
                "i32 %x",
                "i32",
                "  %r = mul i32 %x, 2\n  ret i32 %r\n",
                "  %r = add i32 %x, 2\n  ret i32 %r\n",
                32,
                '(binop mul 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 2))',
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 2))',
            ),
            _mk_single_inst_mut(
                "bad_and_mask_shrink",
                "i32 %x",
                "i32",
                "  %r = and i32 %x, 7\n  ret i32 %r\n",
                "  %r = and i32 %x, 3\n  ret i32 %r\n",
                32,
                '(binop and 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 7))',
                '(binop and 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 3))',
            ),
            _mk_single_inst_mut(
                "bad_and_allones_zero",
                "i32 %x",
                "i32",
                "  %r = and i32 %x, -1\n  ret i32 %r\n",
                "  ret i32 0\n",
                32,
                '(binop and 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 4294967295))',
                "(bv 32 0)",
            ),
            _mk_single_inst_mut(
                "bad_or_to_xor",
                "i32 %x",
                "i32",
                "  %r = or i32 %x, 1\n  ret i32 %r\n",
                "  %r = xor i32 %x, 1\n  ret i32 %r\n",
                32,
                '(binop or 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
                '(binop xor 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
            ),
            _mk_single_inst_mut(
                "bad_or_zero_one",
                "i32 %x",
                "i32",
                "  %r = or i32 %x, 0\n  ret i32 %r\n",
                "  ret i32 1\n",
                32,
                '(binop or 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 0))',
                "(bv 32 1)",
            ),
            _mk_single_inst_mut(
                "bad_xor_zero_zero",
                "i32 %x",
                "i32",
                "  %r = xor i32 %x, 0\n  ret i32 %r\n",
                "  ret i32 0\n",
                32,
                '(binop xor 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 0))',
                "(bv 32 0)",
            ),
            _mk_single_inst_mut(
                "bad_not_dropped",
                "i32 %x",
                "i32",
                "  %r = xor i32 %x, -1\n  ret i32 %r\n",
                "  ret i32 %x\n",
                32,
                '(binop xor 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 4294967295))',
                '(var "%x" 32)',
            ),
            _mk_single_inst_mut(
                "bad_shl1_to_add1",
                "i32 %x",
                "i32",
                "  %r = shl i32 %x, 1\n  ret i32 %r\n",
                "  %r = add i32 %x, 1\n  ret i32 %r\n",
                32,
                '(binop shl 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
                '(binop add 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
            ),
            _mk_single_inst_mut(
                "bad_lshr_to_ashr",
                "i32 %x",
                "i32",
                "  %r = lshr i32 %x, 1\n  ret i32 %r\n",
                "  %r = ashr i32 %x, 1\n  ret i32 %r\n",
                32,
                '(binop lshr 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
                '(binop ashr 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
            ),
            _mk_single_inst_mut(
                "bad_ashr_to_lshr",
                "i32 %x",
                "i32",
                "  %r = ashr i32 %x, 1\n  ret i32 %r\n",
                "  %r = lshr i32 %x, 1\n  ret i32 %r\n",
                32,
                '(binop ashr 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
                '(binop lshr 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 1))',
            ),
            _mk_single_inst_mut(
                "bad_udiv_to_sdiv",
                "i32 %x",
                "i32",
                "  %r = udiv i32 %x, 2\n  ret i32 %r\n",
                "  %r = sdiv i32 %x, 2\n  ret i32 %r\n",
                32,
                '(binop udiv 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 2))',
                '(binop sdiv 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 2))',
            ),
            _mk_single_inst_mut(
                "bad_urem_to_srem",
                "i32 %x",
                "i32",
                "  %r = urem i32 %x, 4\n  ret i32 %r\n",
                "  %r = srem i32 %x, 4\n  ret i32 %r\n",
                32,
                '(binop urem 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 4))',
                '(binop srem 32 (flags 0 0 0 0) (var "%x" 32) (bv 32 4))',
            ),
            _mk_single_inst_mut(
                "bad_icmp_ult_to_slt",
                "i32 %x",
                "i1",
                "  %r = icmp ult i32 %x, 10\n  ret i1 %r\n",
                "  %r = icmp slt i32 %x, 10\n  ret i1 %r\n",
                1,
                '(icmp ult 0 32 (var "%x" 32) (bv 32 10))',
                '(icmp slt 0 32 (var "%x" 32) (bv 32 10))',
            ),
            _mk_single_inst_mut(
                "bad_icmp_ule_to_sle",
                "i32 %x",
                "i1",
                "  %r = icmp ule i32 %x, 10\n  ret i1 %r\n",
                "  %r = icmp sle i32 %x, 10\n  ret i1 %r\n",
                1,
                '(icmp ule 0 32 (var "%x" 32) (bv 32 10))',
                '(icmp sle 0 32 (var "%x" 32) (bv 32 10))',
            ),
            _mk_single_inst_mut(
                "bad_icmp_eq_to_ne",
                "i32 %x",
                "i1",
                "  %r = icmp eq i32 %x, 0\n  ret i1 %r\n",
                "  %r = icmp ne i32 %x, 0\n  ret i1 %r\n",
                1,
                '(icmp eq 0 32 (var "%x" 32) (bv 32 0))',
                '(icmp ne 0 32 (var "%x" 32) (bv 32 0))',
            ),
            _mk_single_inst_mut(
                "bad_icmp_ugt_to_sgt_i16",
                "i16 %x",
                "i1",
                "  %r = icmp ugt i16 %x, 7\n  ret i1 %r\n",
                "  %r = icmp sgt i16 %x, 7\n  ret i1 %r\n",
                1,
                '(icmp ugt 0 16 (var "%x" 16) (bv 16 7))',
                '(icmp sgt 0 16 (var "%x" 16) (bv 16 7))',
            ),
            _mk_single_inst_mut(
                "bad_icmp_ugt_to_uge",
                "i32 %x",
                "i1",
                "  %r = icmp ugt i32 %x, 5\n  ret i1 %r\n",
                "  %r = icmp uge i32 %x, 5\n  ret i1 %r\n",
                1,
                '(icmp ugt 0 32 (var "%x" 32) (bv 32 5))',
                '(icmp uge 0 32 (var "%x" 32) (bv 32 5))',
            ),
            _mk_single_inst_mut(
                "bad_select_swapped_arms",
                "i1 %c, i32 %x, i32 %y",
                "i32",
                "  %r = select i1 %c, i32 %x, i32 %y\n  ret i32 %r\n",
                "  %r = select i1 %c, i32 %y, i32 %x\n  ret i32 %r\n",
                32,
                '(select 32 (var "%c" 1) (var "%x" 32) (var "%y" 32))',
                '(select 32 (var "%c" 1) (var "%y" 32) (var "%x" 32))',
            ),
            _mk_single_inst_mut(
                "bad_select_dropped_then",
                "i1 %c, i32 %x",
                "i32",
                "  %r = select i1 %c, i32 %x, i32 0\n  ret i32 %r\n",
                "  ret i32 0\n",
                32,
                '(select 32 (var "%c" 1) (var "%x" 32) (bv 32 0))',
                "(bv 32 0)",
            ),
            _mk_single_inst_mut(
                "bad_zext_to_sext",
                "i8 %x",
                "i32",
                "  %r = zext i8 %x to i32\n  ret i32 %r\n",
                "  %r = sext i8 %x to i32\n  ret i32 %r\n",
                32,
                '(cast zext 8 32 (flags 0 0 0) (var "%x" 8))',
                '(cast sext 8 32 (flags 0 0 0) (var "%x" 8))',
            ),
            _mk_single_inst_mut(
                "bad_sext_to_zext",
                "i8 %x",
                "i32",
                "  %r = sext i8 %x to i32\n  ret i32 %r\n",
                "  %r = zext i8 %x to i32\n  ret i32 %r\n",
                32,
                '(cast sext 8 32 (flags 0 0 0) (var "%x" 8))',
                '(cast zext 8 32 (flags 0 0 0) (var "%x" 8))',
            ),
            _mk_single_inst_mut(
                "bad_trunc_to_zero",
                "i32 %x",
                "i8",
                "  %r = trunc i32 %x to i8\n  ret i8 %r\n",
                "  ret i8 0\n",
                8,
                '(cast trunc 32 8 (flags 0 0 0) (var "%x" 32))',
                "(bv 8 0)",
            ),
        ]
    )

    return cases


def _build_fallback_determinism_programs() -> list[tuple[str, str]]:
    return [
        (
            "mem2reg_add",
            "define i32 @smoke_add(i32 %x) {\n"
            "entry:\n"
            "  %slot = alloca i32, align 4\n"
            "  store i32 %x, ptr %slot, align 4\n"
            "  %v = load i32, ptr %slot, align 4\n"
            "  %dead = add i32 %v, 0\n"
            "  %res = add i32 %v, 42\n"
            "  ret i32 %res\n"
            "}\n",
        ),
        (
            "sccp_branch_fold",
            "define i32 @sccp_fold(i32 %x) {\n"
            "entry:\n"
            "  br i1 true, label %then, label %else\n"
            "then:\n"
            "  %a = add i32 %x, 5\n"
            "  ret i32 %a\n"
            "else:\n"
            "  ret i32 999\n"
            "}\n",
        ),
        (
            "dce_unused_alu",
            "define i32 @dce_keep(i32 %x, i32 %y) {\n"
            "entry:\n"
            "  %u0 = xor i32 %x, %y\n"
            "  %u1 = sub i32 %u0, 1\n"
            "  %res = add i32 %x, %y\n"
            "  ret i32 %res\n"
            "}\n",
        ),
        (
            "simplifycfg_chain",
            "define i32 @cfg_chain(i32 %x) {\n"
            "entry:\n"
            "  br label %b1\n"
            "b1:\n"
            "  %t = add i32 %x, 3\n"
            "  br label %b2\n"
            "b2:\n"
            "  ret i32 %t\n"
            "}\n",
        ),
        (
            "inline_helper",
            "define internal i32 @inc(i32 %v) {\n"
            "entry:\n"
            "  %r = add i32 %v, 1\n"
            "  ret i32 %r\n"
            "}\n\n"
            "define i32 @caller(i32 %x) {\n"
            "entry:\n"
            "  %y = call i32 @inc(i32 %x)\n"
            "  ret i32 %y\n"
            "}\n",
        ),
    ]


def check_dual_outcome_clean(
    label: str,
    expect_accept: bool,
    native_out: CommandOutcome,
    bc_out: CommandOutcome,
) -> tuple[bool, str]:
    for kind, out in (("native", native_out), ("bytecode", bc_out)):
        if out.timed_out:
            return False, f"{kind} timed out in {out.elapsed_sec:.2f}s"
        for marker in CRASH_STDERR_MARKERS:
            if marker in out.stderr:
                return False, f"{kind} crashed with `{marker}`"
    if expect_accept:
        if native_out.returncode != 0 or bc_out.returncode != 0:
            return (
                False,
                f"expected accept on {label}: native={native_out.returncode}, bytecode={bc_out.returncode}",
            )
    else:
        if native_out.returncode <= 0 or bc_out.returncode <= 0:
            return (
                False,
                f"mutation/forged case ESCAPED on {label}: native={native_out.returncode}, bytecode={bc_out.returncode}",
            )
    if native_out.returncode != bc_out.returncode:
        return (
            False,
            f"ocamlopt-vs-ocamlc exit mismatch on {label}: native={native_out.returncode}, bytecode={bc_out.returncode}",
        )
    return True, f"exit={native_out.returncode}"


def run_dual_suite(
    validator_native: pathlib.Path,
    validator_bc: pathlib.Path,
    fallback_native: pathlib.Path,
    fallback_bc: pathlib.Path,
) -> int:
    for label, binary in (
        ("cert-validator", validator_native),
        ("cert-validator.bc", validator_bc),
        ("verified-opt-fallback", fallback_native),
        ("verified-opt-fallback.bc", fallback_bc),
    ):
        if not binary.is_file():
            print(f"[FAIL] {label} binary not found: {binary}", file=sys.stderr)
            return 2

    failures: list[str] = []
    forged_cases = build_suite_cases()
    mutations = build_mutation_cases()
    ir_programs = _build_fallback_determinism_programs()

    with tempfile.TemporaryDirectory(prefix="llvmcert-dual-mut-") as tmp_str:
        tmp = pathlib.Path(tmp_str)

        # 1. Dual-compiler parity on all 28 forged-certificate suite cases.
        forged_passed = 0
        for idx, case in enumerate(forged_cases, start=1):
            n_dir = tmp / "forged_native" / f"{idx:02d}_{case.name}"
            b_dir = tmp / "forged_bc" / f"{idx:02d}_{case.name}"
            n_dir.mkdir(parents=True, exist_ok=True)
            b_dir.mkdir(parents=True, exist_ok=True)
            n_prep = case.prepare(n_dir, validator_native, fallback_native)
            b_prep = case.prepare(b_dir, validator_bc, fallback_bc)
            n_out = run_process(n_prep.argv, case.timeout_sec)
            bc_limit = max(case.timeout_sec, BYTECODE_MIN_TIMEOUT_SEC)
            b_out = run_process(b_prep.argv, bc_limit)

            ok_n, sum_n = evaluate_outcome(case, n_out)
            bc_case = dataclasses.replace(case, timeout_sec=bc_limit)
            ok_b, sum_b = evaluate_outcome(bc_case, b_out)
            ok_p, sum_p = check_dual_outcome_clean(case.name, case.expect_accept, n_out, b_out)
            if ok_n and ok_b and ok_p:
                forged_passed += 1
            else:
                failures.append(
                    f"forged[{case.name}]: native=({ok_n}: {sum_n}), bc=({ok_b}: {sum_b}), parity=({ok_p}: {sum_p})"
                )

        print(
            f"[1/3] Dual-compiler forged-cert parity: {forged_passed}/{len(forged_cases)} passed"
        )

        # 2. Deterministic mutation campaign (0 escaped mutations permitted).
        mut_passed = 0
        for idx, mcase in enumerate(mutations, start=1):
            mdir = tmp / "mutations" / f"{idx:03d}"
            mdir.mkdir(parents=True, exist_ok=True)
            src_p = mdir / "src.ll"
            tgt_p = mdir / "tgt.ll"
            cert_p = mdir / "fn.cert"
            src_p.write_text(mcase.src_ir, encoding="utf-8", newline="\n")
            tgt_p.write_text(mcase.tgt_ir, encoding="utf-8", newline="\n")
            cert_p.write_bytes(mcase.cert_bytes)

            n_out = run_process(
                [str(validator_native), "--src", str(src_p), "--tgt", str(tgt_p), "--cert", str(cert_p)],
                10.0,
            )
            b_out = run_process(
                [str(validator_bc), "--src", str(src_p), "--tgt", str(tgt_p), "--cert", str(cert_p)],
                30.0,
            )
            ok, detail = check_dual_outcome_clean(mcase.name, False, n_out, b_out)
            if ok:
                mut_passed += 1
            else:
                failures.append(f"mutation[{mcase.name}]: {detail}")

        print(
            f"[2/3] Deterministic mutation campaign: {mut_passed}/{len(mutations)} killed "
            f"(100% rejection + ocamlopt/ocamlc parity)"
        )

        # 3. Byte-for-byte identical IR optimization between ocamlopt and ocamlc fallback binaries.
        ir_passed = 0
        for name, ir_text in ir_programs:
            idir = tmp / "fallback_ir" / name
            idir.mkdir(parents=True, exist_ok=True)
            in_p = idir / "in.ll"
            out_n = idir / "out_native.ll"
            out_b = idir / "out_bc.ll"
            in_p.write_text(ir_text, encoding="utf-8", newline="\n")

            rn = run_process(
                [str(fallback_native), "--pass", "pipeline", "-o", str(out_n), str(in_p)],
                10.0,
            )
            rb = run_process(
                [str(fallback_bc), "--pass", "pipeline", "-o", str(out_b), str(in_p)],
                30.0,
            )
            if rn.returncode != 0 or rb.returncode != 0:
                failures.append(
                    f"fallback[{name}]: exit mismatch/failure native={rn.returncode}, bc={rb.returncode}"
                )
                continue
            bytes_n = out_n.read_bytes()
            bytes_b = out_b.read_bytes()
            if bytes_n != bytes_b or not bytes_n:
                failures.append(
                    f"fallback[{name}]: IR output divergence (native {sha256_hex(bytes_n)} != bc {sha256_hex(bytes_b)})"
                )
                continue
            ir_passed += 1

        print(
            f"[3/3] Dual-compiler verified-opt-fallback IR parity: {ir_passed}/{len(ir_programs)} byte-identical"
        )

    if failures:
        print(f"\nDual-compiler & mutation gate FAILED ({len(failures)} issue(s)):", file=sys.stderr)
        for err in failures[:50]:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print(
        f"\nDual-Compiler & Mutation Assurance OK: "
        f"{len(forged_cases)}/{len(forged_cases)} forged parity, "
        f"{len(mutations)}/{len(mutations)} mutations rejected with exact exit parity, "
        f"{len(ir_programs)}/{len(ir_programs)} verified-opt-fallback outputs byte-identical."
    )
    return 0


def run_self_test() -> int:
    mutations = build_mutation_cases()
    if len(mutations) < 220:
        raise AssertionError(f"expected >= 220 mutations, got {len(mutations)}")
    names = [m.name for m in mutations]
    if len(names) != len(set(names)):
        raise AssertionError("duplicate mutation case name generated")

    # Verify check_dual_outcome_clean catches escaped mutations and ocamlopt/ocamlc divergence.
    assert check_dual_outcome_clean(
        "killed", False, CommandOutcome(4, "", "", 0.01), CommandOutcome(4, "", "", 0.02)
    )[0]
    assert not check_dual_outcome_clean(
        "escaped", False, CommandOutcome(0, "", "", 0.01), CommandOutcome(4, "", "", 0.02)
    )[0]
    assert not check_dual_outcome_clean(
        "parity_mismatch", False, CommandOutcome(4, "", "", 0.01), CommandOutcome(3, "", "", 0.02)
    )[0]
    assert not check_dual_outcome_clean(
        "crash", False, CommandOutcome(2, "", "Fatal error: exception Failure\n", 0.01), CommandOutcome(2, "", "", 0.01)
    )[0]

    # End-to-end offline dry run using mock native + bytecode wrapper scripts.
    with tempfile.TemporaryDirectory(prefix="llvmcert-mut-selftest-") as tmp_str:
        tmp = pathlib.Path(tmp_str)
        mock_v_n = tmp / "mock_v_native.py"
        mock_v_b = tmp / "mock_v_bc.py"
        mock_f_n = tmp / "mock_f_native.py"
        mock_f_b = tmp / "mock_f_bc.py"

        v_script = (
            "import hashlib, pathlib, re, sys\n"
            "args = sys.argv[1:]\n"
            "if '--slice' in args:\n"
            "    sys.exit(2)\n"
            "if '--check-merge' in args:\n"
            "    orig = pathlib.Path(args[args.index('--orig') + 1]).read_text(encoding='utf-8')\n"
            "    merged = pathlib.Path(args[args.index('--merged') + 1]).read_text(encoding='utf-8')\n"
            "    if 'extern_weak' in orig or '999' in merged or 'noundef' in merged or '99' in merged:\n"
            "        sys.exit(4)\n"
            "    sys.exit(0)\n"
            "src = pathlib.Path(args[args.index('--src') + 1]).read_text(encoding='utf-8')\n"
            "tgt = pathlib.Path(args[args.index('--tgt') + 1]).read_text(encoding='utf-8')\n"
            "cert = pathlib.Path(args[args.index('--cert') + 1]).read_bytes().decode('utf-8', errors='replace')\n"
            "m_sh = re.search(r'\\(src-sha256 ([^)]+)\\)', cert)\n"
            "m_th = re.search(r'\\(tgt-sha256 ([^)]+)\\)', cert)\n"
            "hex_ok = lambda s: len(s) == 64 and all(c in '0123456789abcdef' for c in s)\n"
            "if ('\\x00' in cert or not m_sh or not m_th or not hex_ok(m_sh.group(1)) or not hex_ok(m_th.group(1))\n"
            "    or '(cert-v1' not in cert or '[blocks' in cert or not cert.rstrip().endswith(')')\n"
            "    or cert.count('(') != cert.count(')')):\n"
            "    sys.exit(4)\n"
            "schema_bad = (\n"
            "    '(src-b ' in cert or '(tgt-b ' in cert or '(kind bogus)' in cert\n"
            "    or '(smt-verified maybe)' in cert or '(blks' in cert or '(scalar-bad' in cert\n"
            "    or '\"%z\"' in cert\n"
            ")\n"
            "if schema_bad or '(width 32)' not in cert or '(fn \"f\")' not in cert:\n"
            "    sys.exit(4)\n"
            "pos_ok = (\n"
            "    ('  %res = add i32 %x, 42\\n' in tgt and '  %t0 = add i32 %x, 0\\n' in src and 'flags 0 0 0 0' in cert)\n"
            "    or ('  %res = add i32 %x, 2\\n' in tgt and '  %t0 = add i32 %x, 1\\n' in src and 'flags 0 0 0 0' in cert)\n"
            "    or ('  ret i32 0\\n' in tgt and 'xor i32 %x, %x' in src and 'xor 32' in cert)\n"
            "    or ('select i1 %c, i32 %x, i32 0' in tgt and 'i32 noundef %x' in src and '(param-noundef \"%x\" 32)' in cert)\n"
            "    or ('  ret i32 -1\\n' in tgt and 'freeze i32 %x' in src and '4294967295' in cert)\n"
            ") and 'define i32 @f(' in tgt and ') {' in tgt\n"
            "sys.exit(0 if pos_ok else 4)\n"
        )
        f_script = (
            "import pathlib, sys\n"
            "args = sys.argv[1:]\n"
            "out_p = pathlib.Path(args[args.index('-o') + 1])\n"
            "in_p = pathlib.Path(args[-1])\n"
            "txt = in_p.read_text(encoding='utf-8')\n"
            "if '@g(' in txt:\n"
            "    txt = 'define i32 @g(i32 %y) {\\nentry:\\n  %sum = add i32 %y, 7\\n  ret i32 %sum\\n}\\n'\n"
            "out_p.write_text(txt, encoding='utf-8', newline='\\n')\n"
        )
        mock_v_n.write_text(v_script, encoding="utf-8", newline="\n")
        mock_v_b.write_text(v_script, encoding="utf-8", newline="\n")
        mock_f_n.write_text(f_script, encoding="utf-8", newline="\n")
        mock_f_b.write_text(f_script, encoding="utf-8", newline="\n")

        wraps: list[pathlib.Path] = []
        for idx, py in enumerate((mock_v_n, mock_v_b, mock_f_n, mock_f_b)):
            if sys.platform == "win32":
                cmd = tmp / f"wrap_{idx}.cmd"
                cmd.write_text(f'@echo off\n"{sys.executable}" -B "{py}" %*\n', encoding="utf-8")
                wraps.append(cmd)
            else:
                sh = tmp / f"wrap_{idx}.sh"
                sh.write_text(f'#!/usr/bin/env sh\nexec "{sys.executable}" -B "{py}" "$@"\n', encoding="utf-8")
                sh.chmod(0o755)
                wraps.append(sh)

        rc = run_dual_suite(wraps[0], wraps[1], wraps[2], wraps[3])
        if rc != 0:
            raise AssertionError(f"mock dual-compiler self-test returned {rc}")

    print(f"Self-test OK: {len(mutations)} deterministic mutations + 28 forged cases + 5 fallback IR checks verified offline.")
    return 0


def parse_cli_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Validate mutation generator and dual-compiler parity harness offline.",
    )
    parser.add_argument("cert_validator", nargs="?")
    parser.add_argument("cert_validator_bc", nargs="?")
    parser.add_argument("verified_opt_fallback", nargs="?")
    parser.add_argument("verified_opt_fallback_bc", nargs="?")
    args = parser.parse_args(argv)
    if not args.self_test and not all(
        (
            args.cert_validator,
            args.cert_validator_bc,
            args.verified_opt_fallback,
            args.verified_opt_fallback_bc,
        )
    ):
        parser.error(
            "expected <cert-validator> <cert-validator.bc> "
            "<verified-opt-fallback> <verified-opt-fallback.bc> (or --self-test)"
        )
    return args


def main(argv: list[str] | None = None) -> int:
    args = parse_cli_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return run_self_test()
    return run_dual_suite(
        pathlib.Path(args.cert_validator).resolve(),
        pathlib.Path(args.cert_validator_bc).resolve(),
        pathlib.Path(args.verified_opt_fallback).resolve(),
        pathlib.Path(args.verified_opt_fallback_bc).resolve(),
    )


if __name__ == "__main__":
    sys.exit(main())
