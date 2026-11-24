#!/usr/bin/env python3
# Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
# Licensed under the LLVMCert Non-Commercial Evaluation & Research License
# or a separate LLVMCert Commercial Software License Agreement.
# See /LICENSE in the repository root for details.
"""Stage-2 Formal Sail ISA Reference Verification Suite (`sail-arm` & `sail-riscv`).

Combines two independent checks against official Cambridge/REMS Sail ISA models:
  Part A: Universal 2^64 / 2^128 / 2^192 per-instruction SMT equivalence
          (`A64CoreSem.a64_step_sym_oracle` vs. `rems-project/isla-snapshots`
          `armv8p5.ir`, and `Rv64Sem.rv_step_sym_oracle` vs. `riscv64.ir`)
          discharged via `isla_batch` + Z3 (`unsat` equivalence, `unsat`
          trace completeness, `sat` anti-vacuity, and mutation counterexamples).
  Part B: Concrete differential fuzzing against official compiled Sail C
          reference simulators (`armv9_sim` from `rems-project/sail-arm` 9.3
          and `sail_riscv_sim` from `riscv/sail-riscv`).
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import urllib.request
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple, Union

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if SCRIPT_DIR not in sys.path:
    sys.path.insert(0, SCRIPT_DIR)

import run_isa_oracle_suite as s1  # noqa: E402

# Pinned upstream artifact commits (BSD-3-Clause-Clear / BSD-2-Clause)
SAIL_ARM_COMMIT = "5416ef6b43e9527c38dc71fb752259c1d01a47e1"
SAIL_RISCV_TAG = "2026-11-23-71312d5"
SAIL_RISCV_ASSET = "sail-riscv-Linux-x86_64.tar.gz"
ISLA_COMMIT = "e9b5d945394277656593a0d429466d7fa0a2b4b3"
ISLA_SNAPSHOTS_COMMIT = "d8b31014643035a3b11071e56ef30001de3f52ab"

A64_PC_BASE = 0x0000000010300000
A64_UART_ADDR = 0x3C000000
A64_HALT_WORD = 0xFEE1DEAD


# ---------------------------------------------------------------------------
# Cache Bootstrap (Downloads/Compiles Pinned External Artifacts When Missing)
# ---------------------------------------------------------------------------

ARMV8P5_NOTC_TOML = """# Auto-generated Isla config for ARMv8.5-A symbolic equivalence
pc = "_PC"
branch_address = "BranchTo"
ifetch = "ReadMemory"
read_exclusives = ["AArch64.ExclusiveMonitorsPass"]
write_exclusives = ["AArch64.SetExclusiveMonitors"]
translation_table_info = "AArch64.TranslationTableWalk"
default_sizeof = 4

[[toolchain]]
name = "default"
assembler = "true"
objdump = "true"
nm = "true"
linker = "true"

[mmu]
page_table_base = "0x300000"
page_size = "4096"
s2_page_table_base = "0x300000"
s2_page_size = "4096"

[threads]
base = "0x80100000"
top = "0x80300000"
stride = "0x10000"

[symbolic_addrs]
base = "0x80310000"
top = "0x80410000"
stride = "0x10"

[registers.defaults]
"PSTATE.EL" = "#b00"
"PSTATE.nRW" = "#b0"
"PSTATE.SP" = "#b0"
"PSTATE.D" = "#b0"
"PSTATE.A" = "#b0"
"PSTATE.I" = "#b0"
"PSTATE.F" = "#b0"
"PSTATE.SS" = "#b0"
"PSTATE.IL" = "#b0"
"PSTATE.UAO" = "#b0"
"PSTATE.PAN" = "#b0"
"PSTATE.TCO" = "#b0"
"PSTATE.DIT" = "#b0"
"SCTLR_EL1" = "#x0000000000000000"
"SCTLR_EL2" = "#x0000000000000000"
"SCTLR_EL3" = "#x0000000000000000"
"TCR_EL1" = "#x0000000000000000"
"__isla_vector_gpr" = false
"__v81_implemented" = true
"__v82_implemented" = false
"__v83_implemented" = false
"__v84_implemented" = false
"__v85_implemented" = false
"__highest_el_aarch32" = false
"CFG_ID_AA64PFR0_EL1_EL0" = "#x1"
"CFG_ID_AA64PFR0_EL1_EL1" = "#x1"
"CFG_ID_AA64PFR0_EL1_EL2" = "#x1"
"CFG_ID_AA64PFR0_EL1_EL3" = "#x1"
"""


RISCV64_OLD_NOTC_TOML = """# Auto-generated Isla config for Sail RISC-V (riscv64.ir)
pc = "PC"
comment_prefixes = ["#", "//"]
zero_announce_exit = true
default_sizeof = 4

[[toolchain]]
name = "default"
assembler = "true"
objdump = "true"
nm = "true"
linker = "true"

[mmu]
page_table_base = "0x300000"
page_size = "4096"
s2_page_table_base = "0x300000"
s2_page_size = "4096"

[threads]
base = "0x80100000"
top = "0x80300000"
stride = "0x10000"

[symbolic_addrs]
base = "0x80310000"
top = "0x80410000"
stride = "0x10"

[registers.defaults]
satp = "0x0000000000000000"
misa = "{ bits = 0x0000000000000000 }"
mstatus = "{ bits = 0x0000000000000000 }"
mcountinhibit = "{ bits = 0x00000000 }"
mcyclecfg = "{ bits = 0x0000000000000000 }"
minstretcfg = "{ bits = 0x0000000000000000 }"
mtimecmp = "0x0000000000000000"
stimecmp = "0x0000000000000000"
__isla_always_aligned = "true"

[const_primops]
get_config_print_reg = false
get_config_print_instr = false
get_config_print_platform = false
get_config_print_mem = false
sys_enable_fdext = false
sys_enable_zfinx = false
sys_enable_rvc = true
sys_enable_next = false
sys_enable_vext = false
sys_enable_writable_fiom = true
sys_enable_writable_misa = true
sys_enable_bext = false
sys_pmp_count = "0 : %i64"
plat_enable_pmp = false
plat_enable_dirty_update = false
plat_enable_misaligned_access = false
plat_mtval_has_illegal_inst_bits = false
plat_insns_per_tick = 10
plat_ram_base = "0x0000000080000000"
plat_ram_size = "0x0000000004000000"
plat_rom_base = "0x0000000000001000"
plat_rom_size = "0x0000000000000100"
plat_clint_base = "0x0000000002000000"
plat_clint_size = "0x00000000000c0000"
plat_htif_tohost = "0x0000000040001000"
plat_get_16_random_bits = "undefined : %bv16"
plat_term_write = "()"
print_reg = "()"
print_platform = "()"
print_instr = "()"
print_mem_access = "()"
speculate_conditional = "undefined : %bool"
match_reservation = "true"
cancel_reservation = "()"
load_reservation = "()"
csr_full_write_callback = "()"
mem_read_callback = "()"
xreg_full_write_callback = "()"
mem_write_callback = "()"
mem_exception_callback = "()"
pc_write_callback = "()"
get_config_rvfi = "false"
plat_enable_htif = "false"
get_config_use_abi_names = "false"
"""


def download_file(url: str, dest: str) -> None:
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    tmp = dest + ".part"
    req = urllib.request.Request(url, headers={"User-Agent": "LLVMCert-SailOracle/1.0"})
    with urllib.request.urlopen(req, timeout=180) as resp, open(tmp, "wb") as out:
        shutil.copyfileobj(resp, out)
    os.replace(tmp, dest)


def ensure_cache_ready(cache_dir: str, repo_root: str, bootstrap: bool) -> Dict[str, str]:
    os.makedirs(cache_dir, exist_ok=True)
    snaps = os.path.join(cache_dir, "snapshots")
    os.makedirs(snaps, exist_ok=True)

    arm_ir = os.path.join(snaps, "armv8p5.ir")
    rv_ir = os.path.join(snaps, "riscv64.ir")
    arm_toml = os.path.join(cache_dir, "armv8p5_notc.toml")
    rv_toml = os.path.join(cache_dir, "riscv64_old_notc.toml")
    isla_batch = os.path.join(cache_dir, "isla_batch")
    armv9_sim = os.path.join(cache_dir, "sail-arm-9.3", "armv9_sim")
    rv_sim = os.path.join(cache_dir, "sail-riscv", "bin", "sail_riscv_sim")

    if not os.path.exists(arm_toml):
        with open(arm_toml, "w", encoding="utf-8", newline="\n") as f:
            f.write(ARMV8P5_NOTC_TOML)
    if not os.path.exists(rv_toml):
        with open(rv_toml, "w", encoding="utf-8", newline="\n") as f:
            f.write(RISCV64_OLD_NOTC_TOML)

    if bootstrap:
        if not os.path.exists(arm_ir):
            print("[bootstrap] Downloading armv8p5.ir...", flush=True)
            download_file(
                f"https://raw.githubusercontent.com/rems-project/isla-snapshots/{ISLA_SNAPSHOTS_COMMIT}/armv8p5.ir",
                arm_ir,
            )
        if not os.path.exists(rv_ir):
            print("[bootstrap] Downloading riscv64.ir...", flush=True)
            download_file(
                f"https://raw.githubusercontent.com/rems-project/isla-snapshots/{ISLA_SNAPSHOTS_COMMIT}/riscv64.ir",
                rv_ir,
            )
        if not os.path.exists(rv_sim):
            print("[bootstrap] Downloading sail_riscv_sim...", flush=True)
            tgz = os.path.join(cache_dir, SAIL_RISCV_ASSET)
            download_file(
                f"https://github.com/riscv/sail-riscv/releases/download/{SAIL_RISCV_TAG}/{SAIL_RISCV_ASSET}",
                tgz,
            )
            rv_dir = os.path.join(cache_dir, "sail-riscv")
            os.makedirs(rv_dir, exist_ok=True)
            subprocess.run(["tar", "-xzf", tgz, "-C", rv_dir], check=True)
            if not os.path.exists(rv_sim):
                for root, _, files in os.walk(rv_dir):
                    if "sail_riscv_sim" in files:
                        os.makedirs(os.path.dirname(rv_sim), exist_ok=True)
                        shutil.copy2(os.path.join(root, "sail_riscv_sim"), rv_sim)
                        break
            os.chmod(rv_sim, 0o755)
            if os.path.exists(tgz):
                os.remove(tgz)
        if not os.path.exists(armv9_sim):
            print("[bootstrap] Building sail-arm 9.3 armv9_sim...", flush=True)
            arm_dir = os.path.join(cache_dir, "sail-arm-9.3")
            os.makedirs(arm_dir, exist_ok=True)
            c_gz = os.path.join(arm_dir, "armv9.c.gz")
            c_src = os.path.join(arm_dir, "armv9.c")
            if not os.path.exists(c_src):
                download_file(
                    f"https://github.com/rems-project/sail-arm/raw/{SAIL_ARM_COMMIT}/arm-v9.3-a/snapshots/c/armv9.c.gz",
                    c_gz,
                )
                with gzip.open(c_gz, "rb") as gz_in, open(c_src, "wb") as f_out:
                    shutil.copyfileobj(gz_in, f_out)
            with open(c_src, "r", encoding="utf-8", errors="replace") as f:
                txt = f.read()
            if "unit z__SetConfig(sail_string" in txt:
                txt = txt.replace("unit z__SetConfig(sail_string", "unit z__SetConfig(const_sail_string")
                with open(c_src, "w", encoding="utf-8") as f:
                    f.write(txt)
            cov = os.path.join(arm_dir, "cov_stub.c")
            with open(cov, "w", encoding="utf-8") as f:
                f.write("void (*sail_rts_set_coverage_file)(const char *) = 0;\n")
            rts_dir = os.path.join(arm_dir, "sail_rts")
            if not os.path.exists(rts_dir):
                subprocess.run(
                    ["git", "clone", "--depth", "1", "https://github.com/rems-project/sail.git", rts_dir],
                    check=True,
                )
            subprocess.run(
                [
                    "gcc", "-O0", "-no-pie", "-DHAVE_SETCONFIG",
                    f"-I{os.path.join(rts_dir, 'lib')}",
                    c_src, cov,
                    os.path.join(rts_dir, "lib", "sail.c"),
                    os.path.join(rts_dir, "lib", "sail_failure.c"),
                    os.path.join(rts_dir, "lib", "rts.c"),
                    os.path.join(rts_dir, "lib", "elf.c"),
                    "-lgmp", "-lz", "-lm",
                    "-o", armv9_sim,
                ],
                check=True,
            )
            for p_rm in (c_gz, c_src, cov):
                if os.path.exists(p_rm):
                    os.remove(p_rm)
            if os.path.isdir(rts_dir):
                shutil.rmtree(rts_dir)
        if not os.path.exists(isla_batch):
            print("[bootstrap] Building isla_batch from rems-project/isla...", flush=True)
            with tempfile.TemporaryDirectory(prefix="isla_build_") as bdir:
                subprocess.run(["git", "init", bdir], check=True)
                subprocess.run(
                    ["git", "-C", bdir, "fetch", "--depth", "1", "https://github.com/rems-project/isla.git", ISLA_COMMIT],
                    check=True,
                )
                subprocess.run(["git", "-C", bdir, "checkout", "FETCH_HEAD"], check=True)
                runner_src = os.path.join(repo_root, "scripts", "isa_oracle", "isla_batch_runner.rs")
                os.makedirs(os.path.join(bdir, "src", "bin"), exist_ok=True)
                shutil.copy2(runner_src, os.path.join(bdir, "src", "bin", "isla_batch.rs"))
                cargo_toml = os.path.join(bdir, "Cargo.toml")
                with open(cargo_toml, "r", encoding="utf-8") as f:
                    ct = f.read()
                if 'name = "isla_batch"' not in ct:
                    ct += '\n[[bin]]\nname = "isla_batch"\npath = "src/bin/isla_batch.rs"\n'
                    with open(cargo_toml, "w", encoding="utf-8") as f:
                        f.write(ct)
                env = os.environ.copy()
                env.setdefault("CARGO_BUILD_JOBS", "2")
                subprocess.run(["cargo", "build", "--release", "--bin", "isla_batch"], cwd=bdir, env=env, check=True)
                shutil.copy2(os.path.join(bdir, "target", "release", "isla_batch"), isla_batch)

    paths = {
        "arm_ir": arm_ir,
        "rv_ir": rv_ir,
        "arm_toml": arm_toml,
        "rv_toml": rv_toml,
        "isla_batch": isla_batch,
        "armv9_sim": armv9_sim,
        "rv_sim": rv_sim,
    }
    return paths


# ---------------------------------------------------------------------------
# S-Expression Parser, Isla Trace Client & Persistent Z3 Client
# ---------------------------------------------------------------------------

Sexp = Union[str, List[Any]]


def tokenize_sexp(src: str) -> List[str]:
    tokens: List[str] = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c in " \t\r\n":
            i += 1
        elif c == ";":
            j = src.find("\n", i)
            i = n if j < 0 else j + 1
        elif c in "()":
            tokens.append(c)
            i += 1
        elif c == "|":
            j = src.find("|", i + 1)
            if j < 0:
                raise ValueError("unterminated pipe identifier in S-expr")
            tokens.append(src[i : j + 1])
            i = j + 1
        elif c == '"':
            j = i + 1
            while j < n:
                if src[j] == "\\" and j + 1 < n:
                    j += 2
                elif src[j] == '"':
                    break
                else:
                    j += 1
            tokens.append(src[i : j + 1])
            i = j + 1
        else:
            j = i
            while j < n and src[j] not in " \t\r\n();|\"":
                j += 1
            tokens.append(src[i:j])
            i = j
    return tokens


def parse_sexp(src: str) -> Sexp:
    toks = tokenize_sexp(src)
    stack: List[List[Any]] = [[]]
    for tok in toks:
        if tok == "(":
            lst: List[Any] = []
            stack[-1].append(lst)
            stack.append(lst)
        elif tok == ")":
            if len(stack) == 1:
                raise ValueError("unexpected ')' in S-expr")
            stack.pop()
        else:
            stack[-1].append(tok)
    if len(stack) != 1 or len(stack[0]) != 1:
        raise ValueError(f"malformed S-expr root count={len(stack[0])}")
    return stack[0][0]


def sexp_to_str(node: Sexp) -> str:
    if isinstance(node, str):
        return node
    out: List[str] = []
    stack: List[Tuple[Sexp, bool]] = [(node, False)]
    while stack:
        cur, closing = stack.pop()
        if isinstance(cur, str):
            out.append(cur)
        elif closing:
            out.append(")")
        else:
            out.append("(")
            stack.append((cur, True))
            for child in reversed(cur):
                stack.append((child, False))
    res: List[str] = []
    for k, tok in enumerate(out):
        if k > 0 and tok != ")" and out[k - 1] != "(":
            res.append(" ")
        res.append(tok)
    return "".join(res)


def rename_sexp(node: Sexp, sym_map: Dict[str, str]) -> Sexp:
    if isinstance(node, str):
        return sym_map.get(node, node)
    # Iterative deep copy + rename to avoid Python recursion limits on CLZ/REV traces
    root_out: List[Any] = []
    stack: List[Tuple[List[Any], List[Any], int]] = [(node, root_out, 0)]
    while stack:
        src_lst, dst_lst, idx = stack[-1]
        if idx >= len(src_lst):
            stack.pop()
            continue
        stack[-1] = (src_lst, dst_lst, idx + 1)
        item = src_lst[idx]
        if isinstance(item, str):
            dst_lst.append(sym_map.get(item, item))
        else:
            sub: List[Any] = []
            dst_lst.append(sub)
            stack.append((item, sub, 0))
    return root_out


def collect_sexp_atoms(node: Sexp) -> Set[str]:
    atoms: Set[str] = set()
    stack: List[Sexp] = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, str):
            atoms.add(cur)
        else:
            stack.extend(cur)
    return atoms


class Z3Client:
    def __init__(self, z3_bin: str = "z3") -> None:
        self.proc = subprocess.Popen(
            [z3_bin, "-in"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        assert self.proc.stdin is not None and self.proc.stdout is not None
        self.proc.stdin.write("(set-logic QF_BV)\n(set-option :timeout 15000)\n")
        self.proc.stdin.flush()

    def close(self) -> None:
        if self.proc.stdin:
            try:
                self.proc.stdin.write("(exit)\n")
                self.proc.stdin.flush()
            except OSError:
                pass
            self.proc.stdin.close()
        self.proc.wait(timeout=10)

    def check_script(self, smt2_body: str, label: str = "") -> str:
        assert self.proc.stdin is not None and self.proc.stdout is not None
        sentinel = "__Z3_DONE__"
        tactic = (
            "(check-sat-using (then "
            "(using-params simplify :push_ite_bv true :bv_ite2id true :ite_extra_rules true :bv_extract_prop true) "
            "solve-eqs ctx-simplify reduce-bv-size qfbv))"
        )
        script = f"(push)\n{smt2_body}\n{tactic}\n(pop)\n(echo \"{sentinel}\")\n"
        self.proc.stdin.write(script)
        self.proc.stdin.flush()
        verdict = None
        errors: List[str] = []
        while True:
            line = self.proc.stdout.readline()
            if not line:
                err = self.proc.stderr.read() if self.proc.stderr else ""
                raise RuntimeError(f"z3 EOF on {label}: {err}")
            s = line.strip()
            if s == sentinel:
                break
            if s in ("sat", "unsat", "unknown"):
                verdict = s
            elif s:
                errors.append(s)
        if errors:
            raise RuntimeError(f"z3 error on {label}: {'; '.join(errors)}")
        if verdict is None:
            raise RuntimeError(f"z3 returned no verdict on {label}")
        return verdict


class IslaBatchClient:
    def __init__(self, isla_bin: str, arch_ir: str, config_toml: str, threads: int = 2) -> None:
        self.proc = subprocess.Popen(
            [isla_bin, "-T", str(threads), "-A", arch_ir, "-C", config_toml],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        assert self.proc.stdin is not None and self.proc.stdout is not None
        self.proc.stdin.write("PING\n")
        self.proc.stdin.flush()
        while True:
            line = self.proc.stdout.readline()
            if not line:
                err = self.proc.stderr.read() if self.proc.stderr else ""
                raise RuntimeError(f"isla_batch failed startup PING: {err}")
            if line.strip() == "PONG":
                break

    def close(self) -> None:
        if self.proc.stdin:
            try:
                self.proc.stdin.write("QUIT\n")
                self.proc.stdin.flush()
            except OSError:
                pass
            self.proc.stdin.close()
        self.proc.wait(timeout=10)

    def query_many(self, hex_tokens: Sequence[str]) -> Dict[str, Tuple[List[str], List[str]]]:
        assert self.proc.stdin is not None and self.proc.stdout is not None
        out: Dict[str, Tuple[List[str], List[str]]] = {}
        chunk_sz = 32
        for i in range(0, len(hex_tokens), chunk_sz):
            chunk = hex_tokens[i : i + chunk_sz]
            self.proc.stdin.write("\n".join(chunk) + "\n")
            self.proc.stdin.flush()
            for tok in chunk:
                hdr = self.proc.stdout.readline()
                while hdr and not hdr.startswith("BEGIN "):
                    hdr = self.proc.stdout.readline()
                if not hdr:
                    err = self.proc.stderr.read() if self.proc.stderr else ""
                    raise RuntimeError(f"isla_batch EOF waiting BEGIN {tok}: {err}")
                parts = hdr.strip().split()
                if len(parts) != 4 or parts[1] != tok:
                    raise RuntimeError(f"isla_batch bad BEGIN header {hdr!r} (expected {tok})")
                n_tr = int(parts[2])
                n_err = int(parts[3])
                errors: List[str] = []
                traces: List[str] = []
                for _ in range(n_err):
                    el = self.proc.stdout.readline()
                    if not el.startswith("ERROR "):
                        raise RuntimeError(f"isla_batch expected ERROR line, got {el!r}")
                    errors.append(el[6:].strip())
                for _ in range(n_tr):
                    th = self.proc.stdout.readline()
                    if not th.startswith("TRACE "):
                        raise RuntimeError(f"isla_batch expected TRACE line, got {th!r}")
                    _, _, nbytes_s = th.strip().split()
                    nbytes = int(nbytes_s)
                    body = self.proc.stdout.read(nbytes)
                    _nl = self.proc.stdout.readline()
                    traces.append(body)
                end_line = self.proc.stdout.readline().strip()
                if end_line != f"END {tok}":
                    raise RuntimeError(f"isla_batch expected END {tok}, got {end_line!r}")
                out[tok] = (traces, errors)
        return out


# ---------------------------------------------------------------------------
# Parsed Isla Trace Model + SMT-LIB2 Builder
# ---------------------------------------------------------------------------

A64_IGNORED_REGS = {
    "|SEE|", "|__unconditional|", "|BTypeNext|", "|__PC_changed|",
    "|__isla_vector_gpr|", "|__v81_implemented|", "|__v82_implemented|",
    "|__v83_implemented|", "|__v84_implemented|", "|__v85_implemented|",
    "|__highest_el_aarch32|", "|__currentInstrLength|", "|TCR_EL1|",
    "|SCR_EL3|", "|CFG_ID_AA64PFR0_EL1_EL0|", "|CFG_ID_AA64PFR0_EL1_EL1|",
    "|CFG_ID_AA64PFR0_EL1_EL2|", "|CFG_ID_AA64PFR0_EL1_EL3|",
}

RV64_IGNORED_REGS = {
    "|nextPC|", "|misa|", "|cur_privilege|", "|mseccfg|", "|mstatus|", "|satp|",
}


class ParsedTrace:
    def __init__(self, decls: List[Tuple[str, str]], defs: List[Tuple[str, Sexp]],
                 asserts: List[Sexp], read_eqs: List[Tuple[str, str]],
                 arch_dep_vars: Set[str], write_gprs: Dict[int, Sexp],
                 write_flags: Dict[str, Sexp], write_pc: Optional[Sexp]) -> None:
        self.decls = decls
        self.defs = defs
        self.asserts = asserts
        self.read_eqs = read_eqs
        self.arch_dep_vars = arch_dep_vars
        self.write_gprs = write_gprs
        self.write_flags = write_flags
        self.write_pc = write_pc


def unwrap_pipe(tok: str) -> str:
    if len(tok) >= 2 and tok[0] == "|" and tok[-1] == "|":
        return tok[1:-1]
    return tok


def parse_isla_trace(trace_src: str, arch: str, prefix: str) -> ParsedTrace:
    root = parse_sexp(trace_src)
    if not isinstance(root, list) or not root or root[0] != "trace":
        raise ValueError("expected (trace ...) sexp")

    raw_decls: List[Tuple[str, Sexp]] = []
    raw_defs: List[Tuple[str, Sexp]] = []
    alias_map: Dict[str, Sexp] = {}
    raw_asserts: List[Sexp] = []
    read_eqs: List[Tuple[str, str]] = []
    direct_arch_vars: Set[str] = set()
    write_gprs: Dict[int, Sexp] = {}
    write_flags: Dict[str, Sexp] = {}
    write_pc: Optional[Sexp] = None

    def resolve_leaf(sym: str) -> str:
        cur = sym
        seen_r: Set[str] = set()
        while isinstance(cur, str) and cur in alias_map and cur not in seen_r:
            seen_r.add(cur)
            nxt = alias_map[cur]
            if isinstance(nxt, str):
                cur = nxt
            else:
                break
        return cur

    for stmt in root[1:]:
        if not isinstance(stmt, list) or not stmt:
            continue
        head = stmt[0]
        if head == "declare-const":
            vname, sort_node = stmt[1], stmt[2]
            if isinstance(vname, str):
                raw_decls.append((vname, sort_node))
        elif head == "define-const":
            vname, expr = stmt[1], stmt[2]
            if isinstance(vname, str):
                raw_defs.append((vname, expr))
                alias_map[vname] = expr
        elif head == "assert":
            raw_asserts.append(stmt[1])
        elif head == "read-reg":
            reg_raw = stmt[1]
            reg_name = unwrap_pipe(reg_raw) if isinstance(reg_raw, str) else ""
            if arch == "a64":
                if re.fullmatch(r"R([0-9]|[12][0-9]|30)", reg_name):
                    val = stmt[3]
                    if isinstance(val, str):
                        leaf = resolve_leaf(val)
                        read_eqs.append((leaf, reg_name))
                        direct_arch_vars.add(leaf)
                elif reg_name == "PSTATE" and isinstance(stmt[2], list) and stmt[2]:
                    fld_expr = stmt[2][0]
                    if (
                        isinstance(fld_expr, list)
                        and len(fld_expr) == 3
                        and fld_expr[0] == "_"
                        and fld_expr[1] == "field"
                        and isinstance(fld_expr[2], str)
                    ):
                        fch = unwrap_pipe(fld_expr[2])
                        if fch in ("N", "Z", "C", "V") and isinstance(stmt[3], list):
                            inner = stmt[3]
                            # (_ struct (|Z| v36))
                            if len(inner) >= 3 and inner[0] == "_" and inner[1] == "struct":
                                pair = inner[2]
                                if isinstance(pair, list) and len(pair) == 2 and isinstance(pair[1], str):
                                    leaf = resolve_leaf(pair[1])
                                    read_eqs.append((leaf, f"NZCV_{fch}"))
                                    direct_arch_vars.add(leaf)
            else:
                if re.fullmatch(r"x([1-9]|[12][0-9]|3[01])", reg_name):
                    val = stmt[3]
                    if isinstance(val, str):
                        leaf = resolve_leaf(val)
                        read_eqs.append((leaf, reg_name))
                        direct_arch_vars.add(leaf)
                elif reg_name == "PC":
                    val = stmt[3]
                    if isinstance(val, str):
                        leaf = resolve_leaf(val)
                        read_eqs.append((leaf, "PC"))
                        direct_arch_vars.add(leaf)
        elif head == "write-reg":
            reg_raw = stmt[1]
            if not isinstance(reg_raw, str):
                continue
            if (arch == "a64" and reg_raw in A64_IGNORED_REGS) or (
                arch == "rv64" and reg_raw in RV64_IGNORED_REGS
            ):
                continue
            reg_name = unwrap_pipe(reg_raw)
            if arch == "a64":
                m = re.fullmatch(r"R([0-9]|[12][0-9]|30)", reg_name)
                if m:
                    write_gprs[int(m.group(1))] = stmt[3]
                elif reg_name == "PSTATE" and isinstance(stmt[2], list) and stmt[2]:
                    fld_expr = stmt[2][0]
                    if (
                        isinstance(fld_expr, list)
                        and len(fld_expr) == 3
                        and fld_expr[0] == "_"
                        and fld_expr[1] == "field"
                        and isinstance(fld_expr[2], str)
                    ):
                        fch = unwrap_pipe(fld_expr[2])
                        if fch in ("N", "Z", "C", "V") and isinstance(stmt[3], list):
                            inner = stmt[3]
                            if len(inner) >= 3 and inner[0] == "_" and inner[1] == "struct":
                                pair = inner[2]
                                if isinstance(pair, list) and len(pair) == 2:
                                    write_flags[fch] = pair[1]
                elif reg_name == "_PC":
                    write_pc = stmt[3]
                else:
                    raise ValueError(f"unexpected A64 architectural write-reg {reg_raw!r}")
            else:
                m = re.fullmatch(r"x([1-9]|[12][0-9]|3[01])", reg_name)
                if m:
                    write_gprs[int(m.group(1))] = stmt[3]
                elif reg_name == "PC":
                    write_pc = stmt[3]
                else:
                    raise ValueError(f"unexpected RV64 architectural write-reg {reg_raw!r}")

    sym_map: Dict[str, str] = {}
    for vname, _ in raw_decls:
        sym_map[vname] = f"{prefix}{vname}"
    for vname, _ in raw_defs:
        sym_map[vname] = f"{prefix}{vname}"

    def_deps: Dict[str, Set[str]] = {}
    decl_names = {v for v, _ in raw_decls}
    # Compute dependency closure of every defined symbol back to leaf declare-consts
    for vname, expr in raw_defs:
        atoms = collect_sexp_atoms(expr)
        leaf_deps: Set[str] = set()
        for a in atoms:
            if a in def_deps:
                leaf_deps.update(def_deps[a])
            elif a in decl_names:
                leaf_deps.add(a)
        def_deps[vname] = leaf_deps

    # Prefix all symbols so multiple traces coexist cleanly inside one Z3 push/pop
    p_decls = [(sym_map[v], sexp_to_str(srt)) for v, srt in raw_decls]
    p_defs = [(sym_map[v], rename_sexp(ex, sym_map)) for v, ex in raw_defs]
    p_asserts = [rename_sexp(a, sym_map) for a in raw_asserts]
    p_read_eqs = [(sym_map.get(v, v), canon) for v, canon in read_eqs]
    p_write_gprs = {k: rename_sexp(ex, sym_map) for k, ex in write_gprs.items()}
    p_write_flags = {k: rename_sexp(ex, sym_map) for k, ex in write_flags.items()}
    p_write_pc = rename_sexp(write_pc, sym_map) if write_pc is not None else None

    # Determine which asserts are pure architectural path conditions (depend only on mapped inputs)
    # Using unprefixed leaf names against decl_names and direct_arch_vars
    arch_dep_vars: Set[str] = set()
    for a_idx, raw_a in enumerate(raw_asserts):
        atoms = collect_sexp_atoms(raw_a)
        leaves: Set[str] = set()
        for at in atoms:
            if at in def_deps:
                leaves.update(def_deps[at])
            elif at in decl_names:
                leaves.add(at)
        if leaves and leaves.issubset(direct_arch_vars):
            arch_dep_vars.add(str(a_idx))

    return ParsedTrace(
        decls=p_decls,
        defs=p_defs,
        asserts=p_asserts,
        read_eqs=p_read_eqs,
        arch_dep_vars=arch_dep_vars,
        write_gprs=p_write_gprs,
        write_flags=p_write_flags,
        write_pc=p_write_pc,
    )


def a64_canon_decls() -> str:
    lines = [f"(declare-const R{i} (_ BitVec 64))" for i in range(31)]
    for fch in ("N", "Z", "C", "V"):
        lines.append(f"(declare-const NZCV_{fch} (_ BitVec 1))")
    return "\n".join(lines) + "\n"


def rv64_canon_decls() -> str:
    lines = ["(declare-const PC (_ BitVec 64))"]
    lines.extend(f"(declare-const x{i} (_ BitVec 64))" for i in range(1, 32))
    return "\n".join(lines) + "\n"


def wrap_lets(defs: Sequence[Tuple[str, Sexp]], body_expr: str) -> str:
    """Wrap an SMT-LIB2 boolean expression inside nested sequential let-bindings."""
    if not defs:
        return body_expr
    prefix = "".join(f"(let (({vn} {sexp_to_str(ex)})) " for vn, ex in defs)
    return prefix + body_expr + (")" * len(defs))


def trace_decls_and_reads(tr: ParsedTrace) -> str:
    lines: List[str] = []
    for vn, srt in tr.decls:
        lines.append(f"(declare-const {vn} {srt})")
    for sv, cv in tr.read_eqs:
        lines.append(f"(assert (= {sv} {cv}))")
    return "\n".join(lines) + "\n"


def trace_cond_expr(tr: ParsedTrace, extra_body: Optional[str] = None, arch_only: bool = False) -> str:
    terms: List[str] = []
    for idx, ex in enumerate(tr.asserts):
        if not arch_only or str(idx) in tr.arch_dep_vars:
            terms.append(sexp_to_str(ex))
    if extra_body is not None:
        terms.append(extra_body)
    if not terms:
        return "true"
    conj = terms[0] if len(terms) == 1 else f"(and {' '.join(terms)})"
    return wrap_lets(tr.defs, conj)


def smt_bv64_signed(val: int) -> str:
    return f"(_ bv{val & s1.MASK64} 64)"


def rewrite_sexp_divrem(node: Sexp, defs_map: Dict[str, Sexp], verified_divs: Dict[Tuple[str, str, str], Sexp]) -> Sexp:
    if isinstance(node, str):
        return node
    out: List[Any] = [rewrite_sexp_divrem(ch, defs_map, verified_divs) for ch in node]
    if len(out) == 3 and out[0] in ("bvsdiv", "bvsrem"):
        key = (str(out[0]), sexp_to_str(node[1]), sexp_to_str(node[2]))
        if key in verified_divs:
            return verified_divs[key]
    return out


def apply_proven_divrem_bridge(tr: ParsedTrace, canon_decls: str, z3: Z3Client, label: str) -> None:
    """Sound Leibniz substitution justified by Rocq theorem `Rv64Sem.sail_divrem_128_width_reduce` (0 axioms).

    Whenever Isla lowers a 32/64-bit Sail division/remainder to 128-bit `(bvsdiv/bvsrem (ext a) (ext b))`,
    we first prove via Z3 on the unmodified trace that `path_cond /\\ (b == 0)` is `unsat`, then rewrite
    that node in place to its Rocq-proven equal 32/64-bit expression inside 128-bit extension.
    """
    defs_map: Dict[str, Sexp] = {vn: ex for vn, ex in tr.defs}

    def unwrap_ext(node: Sexp) -> Optional[Tuple[str, int, Sexp]]:
        cur = node
        seen: Set[str] = set()
        while isinstance(cur, str) and cur in defs_map and cur not in seen:
            seen.add(cur)
            cur = defs_map[cur]
        if (
            isinstance(cur, list)
            and len(cur) == 2
            and isinstance(cur[0], list)
            and len(cur[0]) == 3
            and cur[0][0] == "_"
            and cur[0][1] in ("zero_extend", "sign_extend")
        ):
            ext_bits = int(cur[0][2])
            if ext_bits in (64, 96):
                return cur[0][1], 128 - ext_bits, cur[1]
        return None

    verified_divs: Dict[Tuple[str, str, str], Sexp] = {}
    t_hdr = trace_decls_and_reads(tr)

    def scan(node: Sexp) -> None:
        if not isinstance(node, list):
            return
        if len(node) == 3 and node[0] in ("bvsdiv", "bvsrem"):
            op, lhs, rhs = str(node[0]), node[1], node[2]
            ul = unwrap_ext(lhs)
            ur = unwrap_ext(rhs)
            if ul and ur and ul[0] == ur[0] and ul[1] == ur[1]:
                kind, w, a_node = ul
                _, _, b_node = ur
                key = (op, sexp_to_str(lhs), sexp_to_str(rhs))
                if key not in verified_divs:
                    nz_q = canon_decls + t_hdr + f"(assert {trace_cond_expr(tr, extra_body=f'(= {sexp_to_str(b_node)} (_ bv0 {w}))')})\n"
                    if z3.check_script(nz_q, f"{label} divrem b!=0 precond") != "unsat":
                        raise AssertionError(f"{label}: trace allows divisor == 0, cannot invoke sail_divrem_128_width_reduce")
                    ext_str = str(128 - w)
                    if kind == "zero_extend":
                        op_w = "bvudiv" if op == "bvsdiv" else "bvurem"
                        verified_divs[key] = [["_", "zero_extend", ext_str], [op_w, a_node, b_node]]
                    else:
                        int_min = 1 << (w - 1)
                        all_ones = (1 << w) - 1
                        ov_cond = ["and", ["=", a_node, ["_", f"bv{int_min}", str(w)]], ["=", b_node, ["_", f"bv{all_ones}", str(w)]]]
                        ov_val = ["_", f"bv{int_min}" if op == "bvsdiv" else "bv0", "128"]
                        verified_divs[key] = ["ite", ov_cond, ov_val, [["_", "sign_extend", ext_str], [op, a_node, b_node]]]
        for ch in node:
            scan(ch)

    for _, ex in tr.defs:
        scan(ex)
    for ex in tr.asserts:
        scan(ex)
    for ex in tr.write_gprs.values():
        scan(ex)
    for ex in tr.write_flags.values():
        scan(ex)
    if tr.write_pc is not None:
        scan(tr.write_pc)

    if verified_divs:
        tr.defs = [(vn, rewrite_sexp_divrem(ex, defs_map, verified_divs)) for vn, ex in tr.defs]
        tr.asserts = [rewrite_sexp_divrem(ex, defs_map, verified_divs) for ex in tr.asserts]
        tr.write_gprs = {k: rewrite_sexp_divrem(ex, defs_map, verified_divs) for k, ex in tr.write_gprs.items()}
        tr.write_flags = {k: rewrite_sexp_divrem(ex, defs_map, verified_divs) for k, ex in tr.write_flags.items()}
        if tr.write_pc is not None:
            tr.write_pc = rewrite_sexp_divrem(tr.write_pc, defs_map, verified_divs)


def check_a64_opcode_smt(
    word: int,
    label: str,
    rocq: Dict[str, Any],
    sail_traces_raw: List[str],
    z3: Z3Client,
) -> None:
    if not sail_traces_raw:
        raise AssertionError(f"A64 {label} (0x{word:08x}): zero Sail traces")

    parsed = [parse_isla_trace(raw, "a64", f"t{idx}_") for idx, raw in enumerate(sail_traces_raw)]

    pc_fall = smt_bv64_signed(A64_PC_BASE + 4)
    pc_kind = rocq["pc_kind"]
    if pc_kind == 0:
        rocq_pc = pc_fall
    elif pc_kind == 1:
        rocq_pc = smt_bv64_signed(A64_PC_BASE + rocq["rel_bytes"])
    elif pc_kind == 2:
        pc_taken = smt_bv64_signed(A64_PC_BASE + rocq["rel_bytes"])
        rocq_pc = f"(ite (= {rocq['br_cond']} (_ bv1 1)) {pc_taken} {pc_fall})"
    elif pc_kind == 3:
        rocq_pc = "R30"
    else:
        raise ValueError(f"unknown A64 pc_kind {pc_kind}")

    base_decls = a64_canon_decls()
    arch_branch_conds: List[str] = []

    for idx, tr in enumerate(parsed):
        t_hdr = trace_decls_and_reads(tr)

        # 1. Reachability (anti-vacuity per trace)
        reach_expr = trace_cond_expr(tr)
        reach = z3.check_script(base_decls + t_hdr + f"(assert {reach_expr})\n", f"A64 {label} trace {idx} reach")
        if reach != "sat":
            raise AssertionError(f"A64 {label} trace {idx} unreachable ({reach})")

        # Apply Rocq-proven 128-bit -> 32/64-bit div/rem bridge if this trace divides
        apply_proven_divrem_bridge(tr, base_decls, z3, f"A64 {label} tr{idx}")

        # 2. Check written GPR set matches Rocq exactly
        if rocq["rd"] is None:
            if tr.write_gprs:
                raise AssertionError(
                    f"A64 {label} trace {idx}: Rocq rd=None but Sail wrote {list(tr.write_gprs.keys())}"
                )
        else:
            rd = int(rocq["rd"])
            if set(tr.write_gprs.keys()) != {rd}:
                raise AssertionError(
                    f"A64 {label} trace {idx}: Rocq rd={rd} but Sail wrote {list(tr.write_gprs.keys())}"
                )

        # 3. Check written PSTATE.NZCV matches Rocq
        if rocq["flags"] is None:
            if tr.write_flags:
                raise AssertionError(
                    f"A64 {label} trace {idx}: Rocq flags=None but Sail wrote {list(tr.write_flags.keys())}"
                )
        else:
            if set(tr.write_flags.keys()) != {"N", "Z", "C", "V"}:
                raise AssertionError(
                    f"A64 {label} trace {idx}: Sail incomplete flags {list(tr.write_flags.keys())}"
                )

        if tr.write_pc is None:
            raise AssertionError(f"A64 {label} trace {idx}: Sail did not write |_PC|")

        # 4. Universal 2^64/2^128/2^192 equivalence (path_cond /\ not(all_outputs_eq) must be unsat)
        eq_terms: List[str] = [f"(= {sexp_to_str(tr.write_pc)} {rocq_pc})"]
        if rocq["rd"] is not None:
            rd = int(rocq["rd"])
            eq_terms.append(f"(= {sexp_to_str(tr.write_gprs[rd])} {rocq['rd_expr']})")
        if rocq["flags"] is not None:
            for i, fch in enumerate(("N", "Z", "C", "V")):
                eq_terms.append(f"(= {sexp_to_str(tr.write_flags[fch])} {rocq['flags'][i]})")

        all_eq = eq_terms[0] if len(eq_terms) == 1 else f"(and {' '.join(eq_terms)})"
        mismatch_expr = trace_cond_expr(tr, extra_body=f"(not {all_eq})")
        eq_v = z3.check_script(
            base_decls + t_hdr + f"(assert {mismatch_expr})\n",
            f"A64 {label} trace {idx} equiv",
        )
        if eq_v != "unsat":
            raise AssertionError(f"A64 {label} (0x{word:08x}) trace {idx} MISMATCH: Z3={eq_v}")

        arch_branch_conds.append(trace_cond_expr(tr, arch_only=True))

    # 5. Architectural trace completeness (unsat) + global anti-vacuity (sat)
    shared_hdr = base_decls + "".join(trace_decls_and_reads(tr) for tr in parsed)
    disj = arch_branch_conds[0] if len(arch_branch_conds) == 1 else f"(or {' '.join(arch_branch_conds)})"
    if z3.check_script(shared_hdr + f"(assert (not {disj}))\n", f"A64 {label} complete") != "unsat":
        raise AssertionError(f"A64 {label} (0x{word:08x}) INCOMPLETE trace coverage!")
    if z3.check_script(shared_hdr + f"(assert {disj})\n", f"A64 {label} nonvac") != "sat":
        raise AssertionError(f"A64 {label} (0x{word:08x}) VACUOUS trace coverage!")


def check_rv64_opcode_smt(
    rvc: int,
    raw_bytes: bytes,
    label: str,
    rocq: Dict[str, Any],
    sail_traces_raw: List[str],
    z3: Z3Client,
) -> None:
    if not sail_traces_raw:
        raise AssertionError(f"RV64 {label} ({raw_bytes.hex()}): zero Sail traces")

    parsed = [parse_isla_trace(raw, "rv64", f"t{idx}_") for idx, raw in enumerate(sail_traces_raw)]
    ilen = int(rocq["len"])
    assert ilen == len(raw_bytes), f"RV64 {label}: len mismatch {ilen} vs {len(raw_bytes)}"

    pc_fall = f"(bvadd PC {smt_bv64_signed(ilen)})"
    pc_kind = rocq["pc_kind"]
    if pc_kind == 0:
        rocq_pc = pc_fall
    elif pc_kind == 1:
        rocq_pc = f"(bvadd PC {smt_bv64_signed(rocq['rel_bytes'])})"
    elif pc_kind == 2:
        pc_taken = f"(bvadd PC {smt_bv64_signed(rocq['rel_bytes'])})"
        rocq_pc = f"(ite (= {rocq['br_cond']} (_ bv1 1)) {pc_taken} {pc_fall})"
    elif pc_kind == 3:
        rocq_pc = "(bvand x1 (_ bv18446744073709551614 64))"
    else:
        raise ValueError(f"unknown RV64 pc_kind {pc_kind}")

    base_decls = rv64_canon_decls()
    arch_branch_conds: List[str] = []

    for idx, tr in enumerate(parsed):
        t_hdr = trace_decls_and_reads(tr)
        reach_expr = trace_cond_expr(tr)
        reach = z3.check_script(base_decls + t_hdr + f"(assert {reach_expr})\n", f"RV64 {label} trace {idx} reach")
        if reach != "sat":
            raise AssertionError(f"RV64 {label} trace {idx} unreachable ({reach})")

        apply_proven_divrem_bridge(tr, base_decls, z3, f"RV64 {label} tr{idx}")

        if rocq["rd"] is None:
            if tr.write_gprs:
                raise AssertionError(
                    f"RV64 {label} trace {idx}: Rocq rd=None but Sail wrote {list(tr.write_gprs.keys())}"
                )
        else:
            rd = int(rocq["rd"])
            if set(tr.write_gprs.keys()) != {rd}:
                raise AssertionError(
                    f"RV64 {label} trace {idx}: Rocq rd={rd} but Sail wrote {list(tr.write_gprs.keys())}"
                )

        if tr.write_pc is None:
            raise AssertionError(f"RV64 {label} trace {idx}: Sail did not write |PC|")

        eq_terms: List[str] = [f"(= {sexp_to_str(tr.write_pc)} {rocq_pc})"]
        if rocq["rd"] is not None:
            rd = int(rocq["rd"])
            eq_terms.append(f"(= {sexp_to_str(tr.write_gprs[rd])} {rocq['rd_expr']})")
        all_eq = eq_terms[0] if len(eq_terms) == 1 else f"(and {' '.join(eq_terms)})"
        mismatch_expr = trace_cond_expr(tr, extra_body=f"(not {all_eq})")
        eq_v = z3.check_script(
            base_decls + t_hdr + f"(assert {mismatch_expr})\n",
            f"RV64 {label} trace {idx} equiv",
        )
        if eq_v != "unsat":
            raise AssertionError(f"RV64 {label} ({raw_bytes.hex()}) trace {idx} MISMATCH: Z3={eq_v}")

        arch_branch_conds.append(trace_cond_expr(tr, arch_only=True))

    shared_hdr = base_decls + "".join(trace_decls_and_reads(tr) for tr in parsed)
    disj = arch_branch_conds[0] if len(arch_branch_conds) == 1 else f"(or {' '.join(arch_branch_conds)})"
    if z3.check_script(shared_hdr + f"(assert (not {disj}))\n", f"RV64 {label} complete") != "unsat":
        raise AssertionError(f"RV64 {label} ({raw_bytes.hex()}) INCOMPLETE trace coverage!")
    if z3.check_script(shared_hdr + f"(assert {disj})\n", f"RV64 {label} nonvac") != "sat":
        raise AssertionError(f"RV64 {label} ({raw_bytes.hex()}) VACUOUS trace coverage!")


# ---------------------------------------------------------------------------
# Comprehensive Opcode Suites (All 20 A64 Constructors & All 7 RV64 Constructors)
# ---------------------------------------------------------------------------

def collect_a64_smt_opcodes() -> List[Tuple[str, int]]:
    ops: List[Tuple[str, int]] = []
    # 1. A64_Nop
    ops.append(("nop", 0xD503201F))
    # 2. A64_AddSubImm (32/64 x sub x S x shift, plus rd=XZR when S=1)
    for sf in (0, 1):
        for sub in (0, 1):
            for s in (0, 1):
                for sh in (0, 1):
                    ops.append((f"addsub_imm sf={sf} sub={sub} s={s} sh={sh}", s1.a64_addsub_imm(sf, sub, s, sh, 0x3A5, 1, 0)))
                if s == 1:
                    ops.append((f"cmp_cmn_imm sf={sf} sub={sub}", s1.a64_addsub_imm(sf, sub, 1, 0, 17, 1, 31)))
    # 3. A64_AddSubShift
    for sf in (0, 1):
        for sub in (0, 1):
            for s in (0, 1):
                for sh in (0, 1, 2):
                    amt = 0 if sh == 0 else (31 if sf == 0 else 45)
                    ops.append((f"addsub_sh sf={sf} sub={sub} s={s} sh={sh}", s1.a64_addsub_shift(sf, sub, s, sh, 2, amt, 1, 0)))
    # 4. A64_AddSubExt
    for sf in (0, 1):
        for sub in (0, 1):
            for s in (0, 1):
                for ext in (0, 1, 2, 3, 4, 5, 6, 7):
                    if sub == 0 and s == 0 or ext in (2, 3, 6, 7):
                        ops.append((f"addsub_ext sf={sf} sub={sub} s={s} ext={ext}", s1.a64_addsub_ext(sf, sub, s, ext, 2, 3, 1, 0)))
    # 5. A64_LogicalImm
    for sf in (0, 1):
        n_b = 1 if sf == 1 else 0
        for opc in (0, 1, 2, 3):
            ops.append((f"log_imm sf={sf} opc={opc}", s1.a64_logical_imm(sf, opc, n_b, 3, 7, 1, 0)))
        ops.append((f"tst_imm sf={sf}", s1.a64_logical_imm(sf, 3, n_b, 0, 5, 1, 31)))
    # 6. A64_LogicalShift
    for sf in (0, 1):
        for opc in (0, 1, 2, 3):
            for n_inv in (0, 1):
                for sh in (0, 1, 2, 3):
                    if (opc == 3 and sh == 3) or (n_inv == 0 and sh in (0, 2)) or (n_inv == 1 and sh in (1, 3)):
                        amt = 19 if sf == 0 else 41
                        ops.append((f"log_sh sf={sf} opc={opc} inv={n_inv} sh={sh}", s1.a64_logical_shift(sf, opc, sh, n_inv, 2, amt, 1, 0)))
    # 7. A64_MoveWide
    for sf in (0, 1):
        for hw in ((0, 1) if sf == 0 else (0, 1, 2, 3)):
            ops.append((f"movn sf={sf} hw={hw}", s1.a64_movn(sf, 0, 0xA55A, hw)))
            ops.append((f"movz sf={sf} hw={hw}", s1.a64_movz(sf, 0, 0x5AA5, hw)))
            ops.append((f"movk sf={sf} hw={hw}", s1.a64_movk(sf, 0, 0x1234, hw)))
    # 8. A64_Bitfield (SBFM, BFM, UBFM with immr<=imms and immr>imms)
    for sf in (0, 1):
        for opc in (0, 1, 2):
            for (r, s_b) in ((0, 7), (4, 15), (15, 4), (31, 31) if sf == 0 else (33, 12)):
                ops.append((f"bfm sf={sf} opc={opc} r={r} s={s_b}", s1.a64_bitfield(sf, opc, sf, r, s_b, 1, 0)))
    # 9. A64_Extr
    for sf in (0, 1):
        for lsb in (0, 11, 31 if sf == 0 else 59):
            ops.append((f"extr sf={sf} lsb={lsb}", s1.a64_extr(sf, sf, 2, lsb, 1, 0)))
            ops.append((f"extr_ror sf={sf} lsb={lsb}", s1.a64_extr(sf, sf, 1, lsb, 1, 0)))
    # 10. A64_MulAddSub
    for sf in (0, 1):
        for o0 in (0, 1):
            ops.append((f"madd_sub sf={sf} o0={o0}", s1.a64_madd_sub(sf, 0, 2, o0, 3, 1, 0)))
            ops.append((f"mul_zr sf={sf} o0={o0}", s1.a64_madd_sub(sf, 0, 2, o0, 31, 1, 0)))
    # 11. A64_MulWidening
    for op31 in (1, 5):
        for o0 in (0, 1):
            ops.append((f"mulwide op31={op31} o0={o0}", s1.a64_madd_sub(1, op31, 2, o0, 3, 1, 0)))
            ops.append((f"mulwide_zr op31={op31} o0={o0}", s1.a64_madd_sub(1, op31, 2, o0, 31, 1, 0)))
    # 12. A64_DataProc2 (UDIV, SDIV, LSLV, LSRV, ASRV, RORV)
    for sf in (0, 1):
        for op6 in (2, 3, 8, 9, 10, 11):
            ops.append((f"dp2 sf={sf} op6={op6}", s1.a64_dp2(sf, op6, 2, 1, 0)))
    # 13. A64_CondSelect (CSEL, CSINC, CSINV, CSNEG across representative conds)
    for sf in (0, 1):
        for (op, o2) in ((0, 0), (0, 1), (1, 0), (1, 1)):
            for cond in (0, 1, 2, 3, 4, 8, 10, 11, 12, 14):
                if cond in (0, 10, 12) or (op == 0 and o2 == 0):
                    ops.append((f"csel sf={sf} op={op} o2={o2} c={cond}", s1.a64_csel(sf, op, o2, 2, cond, 1, 0)))
    # 14 & 15. A64_CondCompareReg & A64_CondCompareImm
    for sf in (0, 1):
        for is_sub in (0, 1):
            for cond in (0, 1, 10, 12):
                ops.append((f"ccmp_reg sf={sf} sub={is_sub} c={cond}", s1.a64_ccmp(sf, is_sub, 0, 2, cond, 1, 0b1010)))
                ops.append((f"ccmp_imm sf={sf} sub={is_sub} c={cond}", s1.a64_ccmp(sf, is_sub, 1, 19, cond, 1, 0b0101)))
    # 16. A64_B
    ops.append(("b_fwd", s1.a64_b(64)))
    ops.append(("b_bwd", s1.a64_b(-32)))
    # 17. A64_BCond (all 16 condition codes!)
    for cond in range(16):
        ops.append((f"b_cond c={cond}", s1.a64_bcond(cond, 12 if cond % 2 == 0 else -7)))
    # 18. A64_Cbz (CBZ & CBNZ, W & X)
    for sf in (0, 1):
        for op in (0, 1):
            ops.append((f"cbz sf={sf} op={op}", s1.a64_cbz(sf, op, 1, 8 if op == 0 else -5)))
    # 19. A64_Tbz (TBZ & TBNZ, low/mid/high bits)
    for op in (0, 1):
        for bit in (0, 7, 31, 32, 63):
            ops.append((f"tbz op={op} bit={bit}", s1.a64_tbz(op, 1, bit, 16)))
    # 20. A64_Ret
    ops.append(("ret", s1.a64_ret()))

    # Deduplicate by opcode word preserving order
    seen: Set[int] = set()
    uniq: List[Tuple[str, int]] = []
    for nm, w in ops:
        w32 = w & s1.MASK32
        if w32 not in seen:
            seen.add(w32)
            uniq.append((nm, w32))
    return uniq


def collect_rv64_smt_opcodes() -> List[Tuple[str, int, bytes]]:
    ops: List[Tuple[str, int, bytes]] = []
    # 1. RV_Nop
    ops.append(("nop_addi_x0", 0, s1.le32(0x00000013)))
    ops.append(("c_nop", 1, s1.le16(0x0001)))
    # 2. RV_Lui (incl. rd=x0 & C.LUI)
    for imm20 in (0, 1, 0x12345, 0x7FFFF, 0x80000, 0xFFFFF):
        ops.append((f"lui 0x{imm20:x}", 0, s1.le32(s1.rv_lui(10, imm20))))
    ops.append(("lui x0", 0, s1.le32(s1.rv_lui(0, 0xABCDE))))
    # 3. RV_AluImm (OP-IMM + OP-IMM-32, incl. rd=x0)
    for f3 in (0, 2, 3, 4, 6, 7):
        for imm12 in (0, 1, 0x5A5, 0x7FF, 0x800, 0xFFF):
            ops.append((f"opimm f3={f3} imm={imm12:x}", 0, s1.le32(s1.rv_itype(0x13, f3, 10, 11, imm12))))
    for sh6 in (0, 1, 17, 31, 32, 63):
        ops.append((f"slli {sh6}", 0, s1.le32(s1.rv_itype(0x13, 1, 10, 11, sh6))))
        ops.append((f"srli {sh6}", 0, s1.le32(s1.rv_itype(0x13, 5, 10, 11, sh6))))
        ops.append((f"srai {sh6}", 0, s1.le32(s1.rv_itype(0x13, 5, 10, 11, (16 << 6) | sh6))))
    for imm12 in (0, 1, 0x7FF, 0x800, 0xFFF):
        ops.append((f"addiw imm={imm12:x}", 0, s1.le32(s1.rv_itype(0x1B, 0, 10, 11, imm12))))
    for sh5 in (0, 1, 15, 31):
        ops.append((f"slliw {sh5}", 0, s1.le32(s1.rv_itype(0x1B, 1, 10, 11, sh5))))
        ops.append((f"srliw {sh5}", 0, s1.le32(s1.rv_itype(0x1B, 5, 10, 11, sh5))))
        ops.append((f"sraiw {sh5}", 0, s1.le32(s1.rv_itype(0x1B, 5, 10, 11, (32 << 5) | sh5))))
    ops.append(("addi x0", 0, s1.le32(s1.rv_itype(0x13, 0, 0, 11, 7))))
    # 4. RV_AluReg (all OP + OP-32 I+M)
    for f7, f3 in [(0, f) for f in range(8)] + [(32, 0), (32, 5)] + [(1, f) for f in range(8)]:
        ops.append((f"op f7={f7} f3={f3}", 0, s1.le32(s1.rv_rtype(0x33, f7, f3, 10, 11, 12))))
    for f7, f3 in [(0, 0), (0, 1), (0, 5), (32, 0), (32, 5), (1, 0), (1, 4), (1, 5), (1, 6), (1, 7)]:
        ops.append((f"op32 f7={f7} f3={f3}", 0, s1.le32(s1.rv_rtype(0x3B, f7, f3, 10, 11, 12))))
    ops.append(("add x0,x1,x2", 0, s1.le32(s1.rv_rtype(0x33, 0, 0, 0, 1, 2))))
    # 5. RV_Branch (all 6 funct3 forward & backward)
    for f3 in (0, 1, 4, 5, 6, 7):
        ops.append((f"br_fwd f3={f3}", 0, s1.le32(s1.rv_btype(f3, 10, 11, 12))))
        ops.append((f"br_bwd f3={f3}", 0, s1.le32(s1.rv_btype(f3, 10, 11, -16))))
    # 6. RV_Jal0
    ops.append(("jal x0, +8", 0, s1.le32(s1.rv_jtype(0x6F, 0, 8))))
    ops.append(("jal x0, -16", 0, s1.le32(s1.rv_jtype(0x6F, 0, -16))))
    # 7. RV_Ret
    ops.append(("ret_jalr", 0, s1.le32(0x00008067)))
    ops.append(("c_ret", 1, s1.le16(0x8082)))

    # RVC 16-bit coverage across ALU/LI/LUI/Shift/Branch/J/JR
    def rvc_ci(f3: int, rd: int, imm6: int, op: int = 1) -> int:
        return (f3 << 13) | (((imm6 >> 5) & 1) << 12) | (rd << 7) | ((imm6 & 0x1F) << 2) | op

    rvc_items = [
        ("c.addi a0, -5", s1.le16(rvc_ci(0, 10, 0x3B, 1))),
        ("c.addi a0, +31", s1.le16(rvc_ci(0, 10, 0x1F, 1))),
        ("c.addiw a0, 12", s1.le16(rvc_ci(1, 10, 12, 1))),
        ("c.addiw a0, -32", s1.le16(rvc_ci(1, 10, 0x20, 1))),
        ("c.li a0, -1", s1.le16(rvc_ci(2, 10, 0x3F, 1))),
        ("c.li a0, 15", s1.le16(rvc_ci(2, 10, 0x0F, 1))),
        ("c.lui a0, 0x1", s1.le16(rvc_ci(3, 10, 0x01, 1))),
        ("c.lui a0, -1", s1.le16(rvc_ci(3, 10, 0x3F, 1))),
        ("c.srli a0, 5", s1.le16((4 << 13) | (0 << 12) | (0 << 10) | (2 << 7) | (5 << 2) | 1)),
        ("c.srai a0, 33", s1.le16((4 << 13) | (1 << 12) | (1 << 10) | (2 << 7) | (1 << 2) | 1)),
        ("c.andi a0, -2", s1.le16((4 << 13) | (1 << 12) | (2 << 10) | (2 << 7) | (0x1E << 2) | 1)),
        ("c.sub a0, a1", s1.le16((4 << 13) | (0 << 12) | (3 << 10) | (2 << 7) | (0 << 5) | (3 << 2) | 1)),
        ("c.xor a0, a1", s1.le16((4 << 13) | (0 << 12) | (3 << 10) | (2 << 7) | (1 << 5) | (3 << 2) | 1)),
        ("c.or a0, a1", s1.le16((4 << 13) | (0 << 12) | (3 << 10) | (2 << 7) | (2 << 5) | (3 << 2) | 1)),
        ("c.and a0, a1", s1.le16((4 << 13) | (0 << 12) | (3 << 10) | (2 << 7) | (3 << 5) | (3 << 2) | 1)),
        ("c.subw a0, a1", s1.le16((4 << 13) | (1 << 12) | (3 << 10) | (2 << 7) | (0 << 5) | (3 << 2) | 1)),
        ("c.addw a0, a1", s1.le16((4 << 13) | (1 << 12) | (3 << 10) | (2 << 7) | (1 << 5) | (3 << 2) | 1)),
        ("c.slli a0, 33", s1.le16(rvc_ci(0, 10, 33, 2))),
        ("c.mv a0, a1", s1.le16((4 << 13) | (0 << 12) | (10 << 7) | (11 << 2) | 2)),
        ("c.add a0, a1", s1.le16((4 << 13) | (1 << 12) | (10 << 7) | (11 << 2) | 2)),
        ("c.beqz a0, +8", s1.le16(0xC401)),
        ("c.bnez a0, +8", s1.le16(0xE401)),
        ("c.j +8", s1.le16(0xA021)),
    ]
    for nm, b in rvc_items:
        ops.append((nm, 1, b))

    seen: Set[Tuple[int, bytes]] = set()
    uniq: List[Tuple[str, int, bytes]] = []
    for nm, rvc, b in ops:
        k = (rvc, b)
        if k not in seen:
            seen.add(k)
            uniq.append((nm, rvc, b))
    return uniq


def run_smt_mutation_tests(
    z3: Z3Client, runner: s1.IsaOracleClient, isla: IslaBatchClient, target_arch: str
) -> int:
    """Anti-vacuity self-tests: intentionally corrupted Rocq expressions MUST produce Z3 SAT counterexamples."""
    mut_specs = [
        ("A64_ADD_corrupt_rd", "a64", 0x91000C20, lambda r: {**r, "rd_expr": f"(bvadd {r['rd_expr']} (_ bv1 64))"}),
        ("A64_ADDS_corrupt_V_flag", "a64", 0xAB020020, lambda r: {**r, "flags": [r["flags"][0], r["flags"][1], r["flags"][2], f"(bvxor {r['flags'][3]} (_ bv1 1))"]}),
        ("A64_BEQ_invert_cond", "a64", 0x54000040, lambda r: {**r, "br_cond": f"(bvxor {r['br_cond']} (_ bv1 1))"}),
        ("A64_SDIV_X_corrupt_overflow", "a64", 0x9AC20C20, lambda r: {**r, "rd_expr": f"(bvadd {r['rd_expr']} (_ bv1 64))"}),
        ("RV64_MULH_corrupt_rd", "rv64", (0, bytes.fromhex("3395c502")), lambda r: {**r, "rd_expr": f"(bvxor {r['rd_expr']} (_ bv1 64))"}),
        ("RV64_BLT_invert_cond", "rv64", (0, bytes.fromhex("6344b500")), lambda r: {**r, "br_cond": f"(bvxor {r['br_cond']} (_ bv1 1))"}),
        ("RV64_DIV_corrupt_quotient", "rv64", (0, bytes.fromhex("33c5c502")), lambda r: {**r, "rd_expr": f"(bvxor {r['rd_expr']} (_ bv1 64))"}),
        ("RV64_DIVW_swap_unsigned", "rv64", (0, bytes.fromhex("3bc5c502")), lambda r: {**r, "rd_expr": f"(bvor {r['rd_expr']} (_ bv1 64))"}),
    ]
    selected = [spec for spec in mut_specs if spec[1] == target_arch]
    assert selected, f"No mutation specs for target_arch={target_arch!r}"
    for mname, arch, op_key, mutator in selected:
        if arch == "a64":
            w = op_key
            tok = s1.le32(w).hex()
            resp = runner.query(f"A64_SYM {w:08x}")
            assert resp.startswith("OK "), resp
            rocq = mutator(json.loads(resp[3:]))
            traces, errs = isla.query_many([tok])[tok]
            assert not errs and traces
            failed = False
            try:
                check_a64_opcode_smt(w, mname, rocq, traces, z3)
            except AssertionError as e:
                if "MISMATCH: Z3=sat" in str(e):
                    failed = True
                else:
                    raise
            if not failed:
                raise AssertionError(f"Mutation test {mname} unexpectedly passed instead of catching mismatch!")
        else:
            rvc, bs = op_key
            tok = bs.hex()
            resp = runner.query(f"RV64_SYM {rvc} {tok}")
            assert resp.startswith("OK "), resp
            rocq = mutator(json.loads(resp[3:]))
            traces, errs = isla.query_many([tok])[tok]
            assert not errs and traces
            failed = False
            try:
                check_rv64_opcode_smt(rvc, bs, mname, rocq, traces, z3)
            except AssertionError as e:
                if "MISMATCH: Z3=sat" in str(e):
                    failed = True
                else:
                    raise
            if not failed:
                raise AssertionError(f"Mutation test {mname} unexpectedly passed instead of catching mismatch!")
    print(f"[sail-smt] Negative mutation self-tests ({target_arch}): {len(selected)}/{len(selected)} counterexamples caught (`sat`)", flush=True)
    return len(selected)


# ---------------------------------------------------------------------------
# Part B1: Official `sail-arm` 9.3 (`armv9_sim`) Concrete Differential Harness
# ---------------------------------------------------------------------------

def run_armv9_sim_batch(
    armv9_bin: str, tmpdir: str, cases: Sequence[Tuple[bytes, Sequence[int], Tuple[int, int, int, int], bool]]
) -> List[Tuple[List[int], Tuple[int, int, int, int]]]:
    """Execute batched AArch64 cases inside official `sail-arm` 9.3 `armv9_sim`.
    Streams hex-encoded output buffer over UART (`0x3c00_0000`) and halts via `0xFEE1DEAD`."""
    if not cases:
        return []
    rec_size = 136
    n_cases = len(cases)
    out_bytes_len = n_cases * rec_size
    load_base = 0x80000000
    out_vaddr = 0x82000000
    sp_init = 0x81000000

    # Reserve X24=in_ptr, X25=out_ptr, X26=out_cur, X27=saved_sp, X28=uart_addr
    def assemble(in_vaddr: int) -> bytes:
        words: List[int] = []
        words.extend(s1.a64_load_imm32(27, sp_init))
        words.append(0x9100037F)  # mov sp, x27
        words.extend(s1.a64_load_imm32(24, in_vaddr))
        words.extend(s1.a64_load_imm32(25, out_vaddr))
        words.extend(s1.a64_load_imm32(26, out_vaddr))
        words.extend(s1.a64_load_imm32(28, A64_UART_ADDR))
        code_buf = bytearray().join(s1.le32(w) for w in words)

        for snip, _, _, is_ret in cases:
            if len(snip) % 4 != 0:
                raise ValueError(f"Unaligned A64 snippet len={len(snip)}")
            per_pre: List[int] = []
            for p in range(8):
                imm7 = (p * 2) & 0x7F
                per_pre.append(0xA9400000 | (imm7 << 15) | ((2 * p + 1) << 10) | (24 << 5) | (2 * p))
            per_pre.append(0xF9400000 | (16 << 10) | (24 << 5) | 16)  # ldr x16, [x24, #128]
            per_pre.append(0xD51B4210)                                 # msr nzcv, x16
            per_pre.append(0x91000000 | (rec_size << 10) | (24 << 5) | 24)
            for cr in (16, 17, 18, 19, 20, 21, 22, 23, 30):
                per_pre.append(0xAA1F03E0 | cr)  # mov x_cr, xzr
            code_buf.extend(b"".join(s1.le32(w) for w in per_pre))
            if is_ret:
                nwords = len(snip) // 4
                code_buf.extend(s1.le32(0x94000002))
                code_buf.extend(s1.le32(0x14000000 | ((nwords + 1) & 0x3FFFFFF)))
                code_buf.extend(snip)
            else:
                code_buf.extend(snip)
            per_post: List[int] = [
                0x9100037F,  # mov sp, x27
                0xD53B4210,  # mrs x16, nzcv
                0xF9000000 | (16 << 10) | (25 << 5) | 16,
            ]
            for p in range(8):
                imm7 = (p * 2) & 0x7F
                per_post.append(0xA9000000 | (imm7 << 15) | ((2 * p + 1) << 10) | (25 << 5) | (2 * p))
            per_post.append(0x91000000 | (rec_size << 10) | (25 << 5) | 25)
            code_buf.extend(b"".join(s1.le32(w) for w in per_post))

        # Epilogue: write "SAILBIN:" marker, stream raw output buffer over UART [X28], then ":SAILEND" + halt
        epi: List[int] = []
        for ch in b"\nSAILBIN:":
            epi.append(s1.a64_movz(1, 0, ch, 0))
            epi.append(0x39000380)  # strb w0, [x28]
        epi.extend(s1.a64_load_imm32(27, out_bytes_len))
        epi.append(0xB40000BB)  # cbz x27, +20 (skip loop if zero bytes)
        epi.append(0x38401740)  # ldrb w0, [x26], #1
        epi.append(0x39000380)  # strb w0, [x28]
        epi.append(0xD100077B)  # sub x27, x27, #1
        epi.append(0xB5FFFFBB)  # cbnz x27, -12
        for ch in b":SAILEND\n":
            epi.append(s1.a64_movz(1, 0, ch, 0))
            epi.append(0x39000380)  # strb w0, [x28]
        epi.append(A64_HALT_WORD)
        code_buf.extend(b"".join(s1.le32(w) for w in epi))
        return bytes(code_buf)

    dummy = assemble(0)
    ro_pad = (16 - (len(dummy) % 16)) % 16
    in_vaddr = load_base + len(dummy) + ro_pad
    code_final = assemble(in_vaddr)
    assert len(code_final) == len(dummy)

    rodata = bytearray()
    for _, regs16, (n, z, c, v), _ in cases:
        for r in regs16:
            rodata.extend(struct.pack("<Q", r & s1.MASK64))
        nzcv_word = ((n & 1) << 31) | ((z & 1) << 30) | ((c & 1) << 29) | ((v & 1) << 28)
        rodata.extend(struct.pack("<Q", nzcv_word))

    bin_path = os.path.join(tmpdir, "sail_a64_batch.bin")
    with open(bin_path, "wb") as f:
        f.write(code_final + (b"\x00" * ro_pad) + rodata)

    # Budget enough cycles: ~140 cycles/case setup+test+post + ~6 cycles/UART byte
    max_cycles = max(100000, n_cases * 200 + out_bytes_len * 8 + 10000)
    res = subprocess.run(
        [
            armv9_bin,
            "-b", f"0x{load_base:x},{bin_path}",
            "-C", f"cpu.cpu0.RVBAR=0x{load_base:x}",
            "-C", "cpu.has_tlb=0x0",
            "-l", str(max_cycles),
        ],
        capture_output=True,
        timeout=180,
    )
    if b"[Sail] Finished Successfully!" not in res.stdout:
        raise RuntimeError(
            f"armv9_sim did not reach halt (rc={res.returncode})\nSTDOUT tail: {res.stdout[-400:]!r}\nSTDERR: {res.stderr[-400:]!r}"
        )
    marker = b"\nSAILBIN:"
    idx_m = res.stdout.find(marker)
    if idx_m < 0:
        raise RuntimeError(f"armv9_sim missing SAILBIN payload: {res.stdout[-400:]!r}")
    start_b = idx_m + len(marker)
    end_b = start_b + out_bytes_len
    if res.stdout[end_b : end_b + 8] != b":SAILEND":
        raise RuntimeError(f"armv9_sim missing :SAILEND trailer at offset {end_b} (total len={len(res.stdout)})")
    raw_out = res.stdout[start_b:end_b]

    parsed: List[Tuple[List[int], Tuple[int, int, int, int]]] = []
    for idx in range(n_cases):
        chunk = raw_out[idx * rec_size : (idx + 1) * rec_size]
        regs = list(struct.unpack("<16Q", chunk[:128]))
        nzcv_w = struct.unpack("<Q", chunk[128:136])[0]
        fl = ((nzcv_w >> 31) & 1, (nzcv_w >> 30) & 1, (nzcv_w >> 29) & 1, (nzcv_w >> 28) & 1)
        parsed.append((regs, fl))
    return parsed


# ---------------------------------------------------------------------------
# Part B2: Official `sail-riscv` (`sail_riscv_sim`) Concrete Differential Harness
# ---------------------------------------------------------------------------

def rv_load_u32_zext(rd: int, val: int) -> List[int]:
    """Load exact unsigned 32-bit value zero-extended to 64 bits (constant 4-insn width)."""
    w = list(s1.rv_load_imm32(rd, val))
    w.append(s1.rv_itype(0x13, 1, rd, rd, 32))
    w.append(s1.rv_itype(0x13, 5, rd, rd, 32))
    return w


def build_rv64_sail_elf(
    code: bytes, rodata: bytes, rodata_vaddr: int, sig_start: int, sig_end: int
) -> bytes:
    """Minimal ELF64 LE at 0x80000000 with PT_LOAD + .symtab defining begin_signature/end_signature."""
    base_vaddr = 0x80000000
    ehdr_size = 64
    phdr_size = 56 * 2
    text_off = ehdr_size + phdr_size
    pad_ro = (16 - (len(code) % 16)) % 16
    assert base_vaddr + len(code) + pad_ro == rodata_vaddr

    payload = code + (b"\x00" * pad_ro) + rodata
    strtab = b"\x00begin_signature\x00end_signature\x00"
    sym0 = struct.pack("<IBBHQQ", 0, 0, 0, 0, 0, 0)
    sym1 = struct.pack("<IBBHQQ", 1, 0x10, 0, 1, sig_start, 0)
    sym2 = struct.pack("<IBBHQQ", 17, 0x10, 0, 1, sig_end, 0)
    symtab = sym0 + sym1 + sym2
    shstrtab = b"\x00.text\x00.strtab\x00.symtab\x00.shstrtab\x00"

    strtab_off = text_off + len(payload)
    symtab_off = strtab_off + len(strtab)
    shstrtab_off = symtab_off + len(symtab)
    sh_raw = shstrtab_off + len(shstrtab)
    pad_sh = (8 - (sh_raw % 8)) % 8
    shoff = sh_raw + pad_sh

    ehdr = struct.pack(
        "<16sHHIQQQIHHHHHH",
        b"\x7fELF\x02\x01\x01" + b"\x00" * 9,
        2, 243, 1, base_vaddr, ehdr_size, shoff,
        0, 64, 56, 2, 64, 5, 4,
    )
    ph_text = struct.pack(
        "<IIQQQQQQ", 1, 7, text_off, base_vaddr, base_vaddr, len(payload), max(len(payload), 0x1000), 0x1000
    )
    sig_memsz = max(0x1000, ((sig_end - sig_start + 0xFFF) // 0x1000) * 0x1000)
    ph_sig = struct.pack("<IIQQQQQQ", 1, 6, 0, sig_start, sig_start, 0, sig_memsz, 0x1000)

    sh0 = struct.pack("<IIQQQQIIQQ", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    sh1 = struct.pack("<IIQQQQIIQQ", 1, 1, 6, base_vaddr, text_off, len(payload), 0, 0, 4, 0)
    sh2 = struct.pack("<IIQQQQIIQQ", 7, 3, 0, 0, strtab_off, len(strtab), 0, 0, 1, 0)
    sh3 = struct.pack("<IIQQQQIIQQ", 15, 2, 0, 0, symtab_off, len(symtab), 2, 1, 8, 24)
    sh4 = struct.pack("<IIQQQQIIQQ", 23, 3, 0, 0, shstrtab_off, len(shstrtab), 0, 0, 1, 0)

    return ehdr + ph_text + ph_sig + payload + strtab + symtab + shstrtab + (b"\x00" * pad_sh) + sh0 + sh1 + sh2 + sh3 + sh4


def run_sail_riscv_sim_batch(
    rv_sim_bin: str, tmpdir: str, cases: Sequence[Tuple[bytes, Sequence[int], bool]]
) -> List[List[int]]:
    if not cases:
        return []
    n_regs = len(s1.RV64_TRACKED_REGS)  # 17
    rec_size = n_regs * 8               # 136 bytes
    n_cases = len(cases)
    out_bytes_len = n_cases * rec_size
    base_vaddr = 0x80000000
    out_vaddr = 0x80400000

    def assemble(in_vaddr: int) -> Tuple[bytes, int]:
        words: List[int] = []
        words.extend(rv_load_u32_zext(18, in_vaddr))
        words.extend(rv_load_u32_zext(19, out_vaddr))
        code_buf = bytearray().join(s1.le32(w) for w in words)

        for snip, _, is_ret in cases:
            if len(snip) % 2 != 0:
                raise ValueError(f"Unaligned RV64 snippet len={len(snip)}")
            pre: List[int] = []
            for idx, r in enumerate(s1.RV64_TRACKED_REGS):
                pre.append(s1.rv_itype(0x03, 3, r, 18, idx * 8))
            pre.append(s1.rv_itype(0x13, 0, 18, 18, rec_size))
            for cr in (1, 3, 4, 22, 23, 24, 25, 26, 27):
                pre.append(s1.rv_itype(0x13, 0, cr, 0, 0))
            code_buf.extend(b"".join(s1.le32(w) for w in pre))
            if is_ret:
                code_buf.extend(s1.le32((0x0080006F & 0xFFFFF000) | (1 << 7) | 0x6F))
                joff = len(snip) + 4
                imm20 = (
                    (((joff >> 20) & 1) << 19)
                    | (((joff >> 1) & 0x3FF) << 9)
                    | (((joff >> 11) & 1) << 8)
                    | ((joff >> 12) & 0xFF)
                )
                code_buf.extend(s1.le32((imm20 << 12) | 0x6F))
                code_buf.extend(snip)
            else:
                code_buf.extend(snip)
            post: List[int] = []
            for idx, r in enumerate(s1.RV64_TRACKED_REGS):
                post.append(s1.rv_sd(r, 19, idx * 8))
            post.append(s1.rv_itype(0x13, 0, 19, 19, rec_size))
            code_buf.extend(b"".join(s1.le32(w) for w in post))

        halt_pc = base_vaddr + len(code_buf)
        code_buf.extend(s1.le32(0x00000013))  # nop (halt target)
        return bytes(code_buf), halt_pc

    dummy_code, _ = assemble(base_vaddr)
    ro_off_raw = len(dummy_code)
    in_vaddr = base_vaddr + ro_off_raw + ((16 - (ro_off_raw % 16)) % 16)
    final_code, halt_pc = assemble(in_vaddr)
    assert len(final_code) == len(dummy_code)

    rodata = bytearray()
    for _, regs17, _ in cases:
        for r in regs17:
            rodata.extend(struct.pack("<Q", r & s1.MASK64))

    elf_bytes = build_rv64_sail_elf(final_code, bytes(rodata), in_vaddr, out_vaddr, out_vaddr + out_bytes_len)
    elf_path = os.path.join(tmpdir, "sail_rv64.elf")
    sig_path = os.path.join(tmpdir, "sail_rv64.sig")
    if os.path.exists(sig_path):
        os.remove(sig_path)
    with open(elf_path, "wb") as f:
        f.write(elf_bytes)

    r = subprocess.run(
        [
            rv_sim_bin,
            "--stop-at-pc", hex(halt_pc),
            "--test-signature", sig_path,
            "--signature-granularity", "8",
            elf_path,
        ],
        capture_output=True,
        text=True,
        timeout=120,
    )
    if r.returncode != 0 or not os.path.exists(sig_path):
        raise RuntimeError(f"sail_riscv_sim failed rc={r.returncode}\nSTDERR: {r.stderr[-400:]}\nSTDOUT: {r.stdout[-400:]}")
    words_hex = [ln.strip() for ln in open(sig_path, "r", encoding="utf-8") if ln.strip()]
    expected_words = n_cases * n_regs
    if len(words_hex) != expected_words:
        raise RuntimeError(f"sail_riscv_sim signature count {len(words_hex)} != {expected_words}")

    results: List[List[int]] = []
    for i in range(n_cases):
        results.append([int(h, 16) for h in words_hex[i * n_regs : (i + 1) * n_regs]])
    return results


# ---------------------------------------------------------------------------
# Compare Sail Simulators Against Rocq Extracted Evaluators (Chunked)
# ---------------------------------------------------------------------------

def run_armv9_sim_suite(oracle: s1.IsaOracleClient, armv9_bin: str, tmpdir: str, fuzz_count: int) -> int:
    orig_qemu = s1.run_qemu_a64_batch

    def _run_sim_adapter(_unused_bin: str, tdir: str, cases: Any) -> Any:
        out = []
        chunk_sz = 400
        for i in range(0, len(cases), chunk_sz):
            out.extend(run_armv9_sim_batch(armv9_bin, tdir, cases[i : i + chunk_sz]))
        return out

    s1.run_qemu_a64_batch = _run_sim_adapter
    try:
        # 1. All 256 (nzcv, cond) pairs across CSEL/CSINC/CSINV/CSNEG/CCMP/CCMN/B.cond
        mat_cases = []
        init_m = [0xAAAAAAAAAAAAAAAA, 0x1111111122222222, 0x9999999988888888] + [0] * 13
        for nz in range(16):
            nzcv = ((nz >> 3) & 1, (nz >> 2) & 1, (nz >> 1) & 1, nz & 1)
            for cond in range(16):
                sf = (nz + cond) & 1
                sel = (nz * 16 + cond) % 7
                if sel < 4:
                    op, o2 = sel // 2, sel % 2
                    mat_cases.append((f"csel_{sel} nz={nz} c={cond}", s1.le32(s1.a64_csel(sf, op, o2, 2, cond, 1, 0)), init_m, nzcv, False))
                elif sel == 4:
                    mat_cases.append((f"ccmp nz={nz} c={cond}", s1.le32(s1.a64_ccmp(sf, 1, cond & 1, 17 if (cond & 1) else 2, cond, 1, nz ^ 5)), init_m, nzcv, False))
                elif sel == 5:
                    mat_cases.append((f"ccmn nz={nz} c={cond}", s1.le32(s1.a64_ccmp(sf, 0, cond & 1, 31 if (cond & 1) else 2, cond, 1, nz ^ 9)), init_m, nzcv, False))
                else:
                    bc_snip = s1.le32(s1.a64_bcond(cond, 2)) + s1.le32(s1.a64_movz(1, 0, 1, 0)) + s1.le32(s1.a64_b(2)) + s1.le32(s1.a64_movz(1, 0, 2, 0))
                    mat_cases.append((f"bcond nz={nz} c={cond}", bc_snip, init_m, nzcv, False))
        n1 = s1.compare_a64_batch(oracle, armv9_bin, tmpdir, "ARMv9-Sim-NZCVxCond-256", mat_cases)

        # 2. All 20 constructors with concrete edge pairs
        con_cases = []
        def regs_ab(a: int, b: int, c: int = 0x5555555566666666) -> List[int]:
            return [0xCAFEBABEDEADBEEF, a & s1.MASK64, b & s1.MASK64, c & s1.MASK64] + [0] * 12
        edge_pairs = [
            (0, 0), (0, 1), (0x80000000, 0xFFFFFFFF),
            (0x7FFFFFFFFFFFFFFF, 1), (0x8000000000000000, 0xFFFFFFFFFFFFFFFF),
            (0x123456789ABCDEF0, 0x0FEDCBA987654321),
        ]
        for a, b in edge_pairs:
            for sf in (0, 1):
                con_cases.append((f"addsub_imm sf={sf}", s1.le32(s1.a64_addsub_imm(sf, sf, 1, 1, 0x801, 1, 0)), regs_ab(a, b), (0, 1, 0, 1), False))
                con_cases.append((f"addsub_sh sf={sf}", s1.le32(s1.a64_addsub_shift(sf, 1 - sf, 1, 2, 2, 19, 1, 0)), regs_ab(a, b), (1, 0, 1, 0), False))
                con_cases.append((f"addsub_ext sf={sf}", s1.le32(s1.a64_addsub_ext(sf, 0, 1, 6, 2, 3, 1, 0)), regs_ab(a, b), (0, 0, 1, 1), False))
                con_cases.append((f"cmp_xzr sf={sf}", s1.le32(s1.a64_addsub_shift(sf, 1, 1, 0, 2, 0, 1, 31)), regs_ab(a, b), (0, 0, 0, 0), False))
                con_cases.append((f"log_sh sf={sf}", s1.le32(s1.a64_logical_shift(sf, 3, 2, 1, 2, 13, 1, 0)), regs_ab(a, b), (1, 1, 1, 1), False))
                con_cases.append((f"madd sf={sf}", s1.le32(s1.a64_madd_sub(sf, 0, 2, sf, 3, 1, 0)), regs_ab(a, b, 0x12345), (0, 0, 0, 0), False))
                for op6 in (2, 3, 8, 9, 10, 11):
                    con_cases.append((f"dp2 sf={sf} op={op6}", s1.le32(s1.a64_dp2(sf, op6, 2, 1, 0)), regs_ab(a, b), (0, 0, 0, 0), False))
            con_cases.append(("smaddl", s1.le32(s1.a64_madd_sub(1, 1, 2, 0, 3, 1, 0)), regs_ab(a, b, 0x100000002), (0, 0, 0, 0), False))
            con_cases.append(("umsubl", s1.le32(s1.a64_madd_sub(1, 5, 2, 1, 3, 1, 0)), regs_ab(a, b, 0x100000002), (0, 0, 0, 0), False))
        for sf in (0, 1):
            for hw in ((0, 1) if sf == 0 else (0, 2)):
                con_cases.append((f"movz sf={sf} hw={hw}", s1.le32(s1.a64_movz(sf, 0, 0xA55A, hw)), regs_ab(0, 0), (0, 0, 0, 0), False))
                con_cases.append((f"movk sf={sf} hw={hw}", s1.le32(s1.a64_movk(sf, 0, 0x1234, hw)), regs_ab(0, 0), (0, 0, 0, 0), False))
            for opc in (0, 1, 2):
                con_cases.append((f"bfm sf={sf} opc={opc}", s1.le32(s1.a64_bitfield(sf, opc, sf, 7, 3, 1, 0)), regs_ab(0xFEDCBA9876543210, 0), (0, 0, 0, 0), False))
            con_cases.append((f"extr sf={sf}", s1.le32(s1.a64_extr(sf, sf, 2, 15, 1, 0)), regs_ab(0x1122334455667788, 0x99AABBCCDDEEFF01), (0, 0, 0, 0), False))
            for tv in (0, 0x100000000, 1):
                for op in (0, 1):
                    snip = s1.le32(s1.a64_cbz(sf, op, 1, 2)) + s1.le32(s1.a64_movz(1, 0, 0x11, 0)) + s1.le32(s1.a64_b(2)) + s1.le32(s1.a64_movz(1, 0, 0x22, 0))
                    con_cases.append((f"cbz sf={sf} op={op}", snip, regs_ab(tv, 0), (0, 0, 0, 0), False))
        for bit in (0, 31, 63):
            for op in (0, 1):
                snip = s1.le32(s1.a64_tbz(op, 1, bit, 2)) + s1.le32(s1.a64_movz(1, 0, 0x33, 0)) + s1.le32(s1.a64_b(2)) + s1.le32(s1.a64_movz(1, 0, 0x44, 0))
                con_cases.append((f"tbz bit={bit} op={op}", snip, regs_ab(1 << bit, 0), (0, 0, 0, 0), False))
        con_cases.append(("nop_add_ret", s1.le32(0xD503201F) + s1.le32(s1.a64_addsub_imm(1, 0, 0, 0, 77, 1, 0)) + s1.le32(s1.a64_ret()), regs_ab(100, 0), (0, 0, 0, 0), True))
        n2 = s1.compare_a64_batch(oracle, armv9_bin, tmpdir, "ARMv9-Sim-Constructors-Edges", con_cases)

        n3 = s1.run_a64_random_diff_fuzz(oracle, armv9_bin, tmpdir, fuzz_count, seed=424242) if fuzz_count > 0 else 0
    finally:
        s1.run_qemu_a64_batch = orig_qemu
    return n1 + n2 + n3


def run_sail_riscv_sim_suite(oracle: s1.IsaOracleClient, rv_sim_bin: str, tmpdir: str, fuzz_count: int) -> int:
    orig_qemu = s1.run_qemu_rv64_batch

    def _run_sim_adapter(_unused_bin: str, tdir: str, cases: Any) -> Any:
        out = []
        chunk_sz = 450
        for i in range(0, len(cases), chunk_sz):
            out.extend(run_sail_riscv_sim_batch(rv_sim_bin, tdir, cases[i : i + chunk_sz]))
        return out

    s1.run_qemu_rv64_batch = _run_sim_adapter
    try:
        n1 = s1.run_rv64_constructors_and_edges(oracle, rv_sim_bin, tmpdir)
        n2 = s1.run_rv64_random_diff_fuzz(oracle, rv_sim_bin, tmpdir, fuzz_count, seed=778899) if fuzz_count > 0 else 0
    finally:
        s1.run_qemu_rv64_batch = orig_qemu
    return n1 + n2


# ---------------------------------------------------------------------------
# Entrypoint
# ---------------------------------------------------------------------------

def main(argv: Sequence[str]) -> int:
    ap = argparse.ArgumentParser(description="Stage-2 Official Sail Reference Oracle Verification Suite")
    ap.add_argument("--cache-dir", default="/sail-cache", help="Directory containing Sail/Isla cache")
    ap.add_argument("--bootstrap", action="store_true", help="Download/build missing pinned Sail & Isla artifacts")
    ap.add_argument("--bootstrap-only", action="store_true", help="Only populate missing Sail/Isla cache artifacts and exit")
    ap.add_argument("--runner", default=None, help="Pre-built isa_oracle_runner binary")
    ap.add_argument("--skip-smt", action="store_true", help="Skip Part A Isla+Z3 SMT equivalence proofs")
    ap.add_argument("--skip-sim", action="store_true", help="Skip Part B Sail C-simulator concrete differential fuzzing")
    ap.add_argument("--threads", type=int, default=2, help="Worker threads for isla_batch")
    ap.add_argument("--a64-sim-cases", type=int, default=1000, help="Additional random fuzz cases on armv9_sim")
    ap.add_argument("--rv64-sim-cases", type=int, default=2200, help="Additional random fuzz cases on sail_riscv_sim")
    args = ap.parse_args(argv)

    repo_root = os.path.abspath(os.path.join(SCRIPT_DIR, ".."))
    paths = ensure_cache_ready(args.cache_dir, repo_root, args.bootstrap)
    if args.bootstrap_only:
        print(f"[bootstrap] Cache ready at {args.cache_dir}", flush=True)
        return 0

    with tempfile.TemporaryDirectory(prefix="sail_oracle_") as tmpdir:
        runner_bin = args.runner if args.runner else s1.build_runner(repo_root, tmpdir)
        oracle = s1.IsaOracleClient(runner_bin)
        try:
            a64_smt_n = 0
            rv64_smt_n = 0
            a64_sim_n = 0
            rv64_sim_n = 0

            if not args.skip_smt:
                for req in ("arm_ir", "arm_toml", "rv_ir", "rv_toml", "isla_batch"):
                    if not os.path.exists(paths[req]):
                        raise RuntimeError(f"Missing cache artifact {paths[req]} (pass --bootstrap?)")

                # Phase 1: AArch64 2^64 / 2^128 / 2^192 per-instruction SMT equivalence
                a64_ops = collect_a64_smt_opcodes()
                a64_toks = [s1.le32(w).hex() for _, w in a64_ops]
                print(f"[sail-smt] Extracting A64 Isla symbolic traces ({len(a64_ops)} opcodes)...", flush=True)
                z3 = Z3Client()
                isla_a64 = IslaBatchClient(paths["isla_batch"], paths["arm_ir"], paths["arm_toml"], args.threads)
                try:
                    a64_traces = isla_a64.query_many(a64_toks)
                    print("[sail-smt] Verifying A64 SMT equivalence via Z3...", flush=True)
                    for (nm, w), tok in zip(a64_ops, a64_toks):
                        traces, errs = a64_traces[tok]
                        if errs:
                            raise RuntimeError(f"isla_batch A64 error on {nm} (0x{w:08x}): {errs}")
                        resp = oracle.query(f"A64_SYM {w:08x}")
                        if not resp.startswith("OK "):
                            raise AssertionError(f"A64_SYM rejected {nm} (0x{w:08x}): {resp}")
                        check_a64_opcode_smt(w, nm, json.loads(resp[3:]), traces, z3)
                        a64_smt_n += 1
                    print(f"[sail-smt] A64: {a64_smt_n} opcodes across all 20 constructors proven equivalent over 2^64/2^128/2^192 (unsat)", flush=True)
                    run_smt_mutation_tests(z3, oracle, isla_a64, "a64")
                finally:
                    isla_a64.close()
                    z3.close()

                # Phase 2: RISC-V RV64IM + 16-bit RVC per-instruction SMT equivalence
                rv_ops = collect_rv64_smt_opcodes()
                rv_toks = [bs.hex() for _, _, bs in rv_ops]
                print(f"[sail-smt] Extracting RV64/RVC Isla symbolic traces ({len(rv_ops)} opcodes)...", flush=True)
                z3 = Z3Client()
                isla_rv = IslaBatchClient(paths["isla_batch"], paths["rv_ir"], paths["rv_toml"], args.threads)
                try:
                    rv_traces = isla_rv.query_many(rv_toks)
                    print("[sail-smt] Verifying RV64/RVC SMT equivalence via Z3...", flush=True)
                    for (nm, rvc, bs), tok in zip(rv_ops, rv_toks):
                        traces, errs = rv_traces[tok]
                        if errs:
                            raise RuntimeError(f"isla_batch RV64 error on {nm} ({tok}): {errs}")
                        resp = oracle.query(f"RV64_SYM {rvc} {tok}")
                        if not resp.startswith("OK "):
                            raise AssertionError(f"RV64_SYM rejected {nm} ({tok}): {resp}")
                        check_rv64_opcode_smt(rvc, bs, nm, json.loads(resp[3:]), traces, z3)
                        rv64_smt_n += 1
                    print(f"[sail-smt] RV64/RVC: {rv64_smt_n} opcodes across all 7 constructors proven equivalent over 2^64/2^128 (unsat)", flush=True)
                    run_smt_mutation_tests(z3, oracle, isla_rv, "rv64")
                finally:
                    isla_rv.close()
                    z3.close()

            if not args.skip_sim:
                for req in ("armv9_sim", "rv_sim"):
                    if not os.path.exists(paths[req]):
                        raise RuntimeError(f"Missing simulator binary {paths[req]} (pass --bootstrap?)")
                print("[sail-sim] Starting ARMv9_Sim & SailRV64_Sim concrete differential fuzzing...", flush=True)
                a64_sim_n = run_armv9_sim_suite(oracle, paths["armv9_sim"], tmpdir, args.a64_sim_cases)
                rv64_sim_n = run_sail_riscv_sim_suite(oracle, paths["rv_sim"], tmpdir, args.rv64_sim_cases)

            print(
                f"\nALL STAGE-2 SAIL ORACLE CHECKS PASSED: "
                f"A64_SMT={a64_smt_n} RV64_SMT={rv64_smt_n} "
                f"ARMv9_Sim={a64_sim_n} SailRV64_Sim={rv64_sim_n}",
                flush=True,
            )
        finally:
            oracle.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
