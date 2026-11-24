#!/usr/bin/env python3
# Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
# Licensed under the LLVMCert Non-Commercial Evaluation & Research License
# or a separate LLVMCert Commercial Software License Agreement.
# See /LICENSE in the repository root for details.
"""Self-contained Layer-2 positive and adversarial forged-ELF / forged-MC test suite
for cert-validator --check-mc and --emit-mc-cnf (Phase 8.3a Milestone M1: RV64IM + RVC)."""

from __future__ import annotations

import argparse
import os
import re
import struct
import subprocess
import sys
import tempfile
import time
from typing import Dict, List, Optional, Tuple


# Ground-truth LLVM IR emitted by clang-22 (--target=riscv64-unknown-none-elf
# -march=rv64imc -mno-relax -mabi=lp64 -O2 -fno-builtin -S -emit-llvm) for all 8
# functions in e2e_corpus_mc.c.
CORPUS_IR = """\
target datalayout = "e-m:e-p:64:64-i64:64-i128:128-n32:64-S128"
target triple = "riscv64-unknown-none-elf"

define dso_local noundef signext i32 @pid_clamp_i32(i32 noundef signext %0, i32 noundef signext %1, i32 noundef signext %2) local_unnamed_addr {
  %4 = icmp sgt i32 %1, %2
  %5 = icmp slt i32 %0, %1
  %6 = or i1 %5, %4
  %7 = tail call i32 @llvm.smin.i32(i32 %0, i32 %2)
  %8 = select i1 %6, i32 %1, i32 %7
  ret i32 %8
}

define dso_local signext i32 @deadband_i32(i32 noundef signext %0, i32 noundef signext %1) local_unnamed_addr {
  %3 = tail call i32 @llvm.smax.i32(i32 %1, i32 0)
  %4 = icmp sgt i32 %0, %3
  br i1 %4, label %5, label %7

5:
  %6 = sub nsw i32 %0, %3
  br label %12

7:
  %8 = sub nsw i32 0, %3
  %9 = icmp slt i32 %0, %8
  %10 = add i32 %3, %0
  %11 = select i1 %9, i32 %10, i32 0
  br label %12

12:
  %13 = phi i32 [ %6, %5 ], [ %11, %7 ]
  ret i32 %13
}

define dso_local signext i32 @linear_interp_i32(i32 noundef signext %0, i32 noundef signext %1, i32 noundef signext %2) local_unnamed_addr {
  %4 = sext i32 %1 to i64
  %5 = sext i32 %0 to i64
  %6 = sub nsw i64 %4, %5
  %7 = sext i32 %2 to i64
  %8 = mul nsw i64 %6, %7
  %9 = sdiv i64 %8, 256
  %10 = trunc i64 %9 to i32
  %11 = add i32 %0, %10
  ret i32 %11
}

define dso_local signext i32 @crc_step_u32(i32 noundef signext %0, i32 noundef signext %1) local_unnamed_addr {
  %3 = and i32 %1, 255
  %4 = xor i32 %3, %0
  %5 = and i32 %4, 1
  %6 = icmp eq i32 %5, 0
  %7 = lshr i32 %4, 1
  %8 = xor i32 %7, -306674912
  %9 = select i1 %6, i32 %7, i32 %8
  %10 = and i32 %9, 1
  %11 = icmp eq i32 %10, 0
  %12 = lshr i32 %9, 1
  %13 = xor i32 %12, -306674912
  %14 = select i1 %11, i32 %12, i32 %13
  ret i32 %14
}

define dso_local i64 @pack_sensor_u64(i32 noundef signext %0, i32 noundef signext %1) local_unnamed_addr {
  %3 = zext i32 %0 to i64
  %4 = shl nuw i64 %3, 32
  %5 = zext i32 %1 to i64
  %6 = or disjoint i64 %4, %5
  ret i64 %6
}

define dso_local noundef signext i32 @voter_median3_i32(i32 noundef signext %0, i32 noundef signext %1, i32 noundef signext %2) local_unnamed_addr {
  %4 = tail call i32 @llvm.smax.i32(i32 %0, i32 %1)
  %5 = tail call i32 @llvm.smin.i32(i32 %0, i32 %1)
  %6 = icmp sgt i32 %4, %2
  %7 = tail call i32 @llvm.smax.i32(i32 %5, i32 %2)
  %8 = select i1 %6, i32 %7, i32 %4
  ret i32 %8
}

define dso_local noundef signext i32 @saturating_add_u32(i32 noundef signext %0, i32 noundef signext %1) local_unnamed_addr {
  %3 = tail call i32 @llvm.uadd.sat.i32(i32 %0, i32 %1)
  ret i32 %3
}

define dso_local noundef i64 @abs_diff_i64(i64 noundef %0, i64 noundef %1) local_unnamed_addr {
  %3 = icmp slt i64 %0, %1
  %4 = sub i64 %0, %1
  %5 = sub i64 %1, %0
  %6 = select i1 %3, i64 %5, i64 %4
  ret i64 %6
}

declare i32 @llvm.smax.i32(i32, i32)
declare i32 @llvm.uadd.sat.i32(i32, i32)
declare i32 @llvm.smin.i32(i32, i32)
"""

CORPUS_FUNCS = [
    ("pid_clamp_i32", 32, [("%0", 32, "signext"), ("%1", 32, "signext"), ("%2", 32, "signext")],
     "b326b6003327b500d98e6355c50089c62e8582803285edfe8280"),
    ("deadband_i32", 32, [("%0", 32, "signext"), ("%1", 32, "signext")],
     "3326b0003306c040f18d63d4a5000d9d82803b06b0403326c5002d9db305c0406d8d8280"),
    ("linear_interp_i32", 32, [("%0", 32, "signext"), ("%1", 32, "signext"), ("%2", 32, "signext")],
     "898db385c50213d6f5436192b295a1812d9d8280"),
    ("crc_step_u32", 32, [("%0", 32, "signext"), ("%1", 32, "signext")],
     "93f5f50f3786b8ed2d8d930506321316f5031b5515007d966d8e318d1316f5037d961b551500f18d2d8d8280"),
    ("pack_sensor_u64", 64, [("%0", 32, "signext"), ("%1", 32, "signext")],
     "0215821581914d8d8280"),
    ("voter_median3_i32", 32, [("%0", 32, "signext"), ("%1", 32, "signext"), ("%2", 32, "signext")],
     "aa8663d9a500635ab500635ba600635cd6008280ae86e34ab5fe2e85e349b6fe3285e348d6fe36858280"),
    ("saturating_add_u32", 32, [("%0", 32, "signext"), ("%1", 32, "signext")],
     "a99d33b5a5003305a0404d8d8280"),
    ("abs_diff_i64", 64, [("%0", 64, "none"), ("%1", 64, "none")],
     "63c5a5003385a54082800d8d8280"),
]


def solve_cdcl_lrat(cnf_text: str) -> List[Tuple[int, List[int], List[int]]]:
    """Minimal self-contained 1-UIP CDCL solver emitting trimmed LRAT UNSAT steps."""
    nvars = 0
    orig_clauses: List[List[int]] = []
    for line in cnf_text.splitlines():
        s = line.strip()
        if not s or s.startswith("c"):
            continue
        if s.startswith("p cnf"):
            nvars = int(s.split()[2])
            continue
        orig_clauses.append([int(x) for x in s.split()[:-1]])

    clauses: List[Optional[List[int]]] = [None] + list(orig_clauses)
    val = [0] * (nvars + 1)
    phase = [1] * (nvars + 1)
    level = [0] * (nvars + 1)
    reason = [0] * (nvars + 1)
    trail_pos = [-1] * (nvars + 1)
    trail: List[int] = []
    unit0_cid: Dict[int, int] = {}
    lrat_steps: List[Tuple[int, List[int], List[int]]] = []
    watches: Dict[int, List[int]] = {l: [] for v in range(1, nvars + 1) for l in (v, -v)}

    def lit_val(l: int) -> int:
        v = val[abs(l)]
        return v if l > 0 else -v

    def add_watch(cid: int, cl: List[int]) -> None:
        watches[cl[0]].append(cid)
        watches[cl[1]].append(cid)

    for cid in range(1, len(clauses)):
        u = list(dict.fromkeys(clauses[cid]))  # type: ignore[arg-type]
        if not u:
            return [(len(clauses), [], [cid])]
        if len(u) == 1:
            l = u[0]
            if lit_val(l) == -1:
                return [(len(clauses), [], [unit0_cid[-l], cid])]
            if lit_val(l) == 0:
                val[abs(l)] = 1 if l > 0 else -1
                phase[abs(l)] = val[abs(l)]
                level[abs(l)] = 0
                reason[abs(l)] = cid
                trail_pos[abs(l)] = len(trail)
                trail.append(l)
                unit0_cid[l] = cid
        else:
            clauses[cid] = u
            add_watch(cid, u)

    activity = [0.0] * (nvars + 1)
    bump = 1.0

    def bump_var(v: int) -> None:
        nonlocal bump
        activity[v] += bump
        if activity[v] > 1e100:
            for i in range(1, nvars + 1):
                activity[i] *= 1e-100
            bump *= 1e-100

    def emit_unit0(l: int, rc: int) -> int:
        if l in unit0_cid:
            return unit0_cid[l]
        cl = clauses[rc]
        assert cl is not None
        hints = list(dict.fromkeys([unit0_cid[-x] for x in cl if x != l])) + [rc]
        new_cid = len(clauses)
        clauses.append([l])
        lrat_steps.append((new_cid, [l], hints))
        unit0_cid[l] = new_cid
        return new_cid

    qhead = 0
    dl = 0
    lim: List[int] = []

    def propagate() -> int:
        nonlocal qhead
        while qhead < len(trail):
            p = trail[qhead]
            qhead += 1
            falsified = -p
            wl = watches[falsified]
            i = 0
            while i < len(wl):
                cid = wl[i]
                cl = clauses[cid]
                assert cl is not None
                if cl[0] == falsified:
                    cl[0], cl[1] = cl[1], cl[0]
                if lit_val(cl[0]) == 1:
                    i += 1
                    continue
                found = False
                for j in range(2, len(cl)):
                    if lit_val(cl[j]) != -1:
                        cl[1], cl[j] = cl[j], cl[1]
                        watches[cl[1]].append(cid)
                        wl[i] = wl[-1]
                        wl.pop()
                        found = True
                        break
                if found:
                    continue
                if lit_val(cl[0]) == -1:
                    return cid
                l = cl[0]
                val[abs(l)] = 1 if l > 0 else -1
                phase[abs(l)] = val[abs(l)]
                level[abs(l)] = dl
                reason[abs(l)] = cid
                trail_pos[abs(l)] = len(trail)
                trail.append(l)
                if dl == 0:
                    emit_unit0(l, cid)
                i += 1
        return 0

    def analyze(conf_cid: int) -> Tuple[List[int], int, List[int]]:
        seen = set()
        learned: List[int] = []
        used_cids: List[Tuple[int, int]] = []
        u0_needed: List[int] = []
        path_c = 0
        idx = len(trail) - 1
        p = 0
        c = conf_cid
        while True:
            cl = clauses[c]
            assert cl is not None
            for l in cl:
                v = abs(l)
                if l == p or v in seen:
                    continue
                if level[v] == 0:
                    u0_needed.append(unit0_cid[-l])
                    seen.add(v)
                    continue
                seen.add(v)
                bump_var(v)
                if level[v] == dl:
                    path_c += 1
                else:
                    learned.append(l)
            while abs(trail[idx]) not in seen:
                idx -= 1
            p = trail[idx]
            v = abs(p)
            c = reason[v]
            seen.remove(v)
            path_c -= 1
            if path_c == 0:
                learned.insert(0, -p)
                break
            used_cids.append((trail_pos[v], c))
        res_cids = [rc for _, rc in sorted(used_cids, key=lambda x: x[0])]
        hints = list(dict.fromkeys(u0_needed)) + res_cids + [conf_cid]
        if len(learned) == 1:
            bt_lvl = 0
        else:
            best_i, best_l = 1, level[abs(learned[1])]
            for k in range(2, len(learned)):
                lk = level[abs(learned[k])]
                if lk > best_l:
                    best_l, best_i = lk, k
            learned[1], learned[best_i] = learned[best_i], learned[1]
            bt_lvl = best_l
        return learned, bt_lvl, hints

    def backtrack(bt_lvl: int) -> None:
        nonlocal dl, qhead
        while len(trail) > lim[bt_lvl]:
            l = trail.pop()
            v = abs(l)
            val[v] = 0
            reason[v] = 0
            trail_pos[v] = -1
        del lim[bt_lvl:]
        dl = bt_lvl
        qhead = len(trail)

    def trim_lrat(num_orig: int) -> List[Tuple[int, List[int], List[int]]]:
        step_map = {cid: (cl, hints) for cid, cl, hints in lrat_steps}
        empty_cid = lrat_steps[-1][0]
        needed = {empty_cid}
        q = [empty_cid]
        while q:
            cid = q.pop()
            if cid <= num_orig:
                continue
            for h in step_map[cid][1]:
                if h > num_orig and h not in needed:
                    needed.add(h)
                    q.append(h)
        kept = [(cid, cl, hints) for cid, cl, hints in lrat_steps if cid in needed]
        remap = {old: num_orig + 1 + i for i, (old, _, _) in enumerate(kept)}
        return [
            (remap[old], cl, [remap[h] if h > num_orig else h for h in hints])
            for old, cl, hints in kept
        ]

    conflicts = 0
    next_restart = 100
    while True:
        conf = propagate()
        if conf != 0:
            conflicts += 1
            if dl == 0:
                cl = clauses[conf]
                assert cl is not None
                hints = list(dict.fromkeys([unit0_cid[-l] for l in cl])) + [conf]
                empty_cid = len(clauses)
                clauses.append([])
                lrat_steps.append((empty_cid, [], hints))
                return trim_lrat(len(orig_clauses))
            learned, bt_lvl, hints = analyze(conf)
            new_cid = len(clauses)
            clauses.append(learned)
            lrat_steps.append((new_cid, learned, hints))
            backtrack(bt_lvl)
            l = learned[0]
            val[abs(l)] = 1 if l > 0 else -1
            phase[abs(l)] = val[abs(l)]
            level[abs(l)] = 0 if len(learned) == 1 else dl
            reason[abs(l)] = new_cid
            trail_pos[abs(l)] = len(trail)
            trail.append(l)
            if len(learned) == 1:
                unit0_cid[l] = new_cid
            else:
                add_watch(new_cid, learned)
            bump /= 0.95
            if conflicts >= next_restart and dl > 0:
                backtrack(0)
                next_restart = int(next_restart * 1.5) + 50
        else:
            if conflicts >= next_restart and dl > 0:
                backtrack(0)
                next_restart = int(next_restart * 1.5) + 50
            best_v, best_a = 0, -1.0
            for v in range(1, nvars + 1):
                if val[v] == 0 and activity[v] > best_a:
                    best_a, best_v = activity[v], v
            if best_v == 0:
                raise RuntimeError("Unexpected SAT instance while generating UNSAT LRAT proof")
            dl += 1
            lim.append(len(trail))
            lit = best_v if phase[best_v] > 0 else -best_v
            val[best_v] = 1 if lit > 0 else -1
            level[best_v] = dl
            reason[best_v] = 0
            trail_pos[best_v] = len(trail)
            trail.append(lit)


def format_lrat_sexp(steps: List[Tuple[int, List[int], List[int]]]) -> str:
    return " ".join(
        f"(add {cid} ({' '.join(map(str, cl))}) ({' '.join(map(str, hs))}))"
        for cid, cl, hs in steps
    )


def format_mc_cert(
    kind: str,
    fn: str,
    rvc: int,
    ret_width: int,
    args: List[Tuple[str, int, str]],
    lrat_s: Optional[str] = None,
) -> str:
    args_s = " ".join(f'(arg "{r}" {w} {a})' for r, w, a in args)
    tail = f" (lrat {lrat_s})" if lrat_s is not None else ""
    return f'(mc-cert-v1 (arch rv64) (elf-kind {kind}) (fn "{fn}") (rvc {rvc}) (ret-width {ret_width}) (args {args_s}){tail})'


def build_elf64(
    fn_name: str,
    text_bytes: bytes,
    *,
    e_type: int = 1,          # 1=ET_REL, 2=ET_EXEC, 3=ET_DYN
    ei_class: int = 2,        # 2=ELFCLASS64
    ei_data: int = 1,         # 1=ELFDATA2LSB
    e_machine: int = 243,     # 243=EM_RISCV
    e_flags: int = 0x1,       # EF_RISCV_RVC
    magic: bytes = b"\x7fELF",
    sym_name: Optional[str] = None,
    sym_value_override: Optional[int] = None,
    sym_size_override: Optional[int] = None,
    relas: Optional[List[Tuple[int, int, int]]] = None,
    truncate_to: Optional[int] = None,
) -> bytes:
    """Build a minimal valid (or deliberately malformed) little-endian ELF64 RISC-V binary."""
    actual_sym = fn_name if sym_name is None else sym_name
    text_vaddr = 0x10000 if e_type in (2, 3) else 0x0
    sym_val = text_vaddr if sym_value_override is None else sym_value_override
    sym_sz = len(text_bytes) if sym_size_override is None else sym_size_override

    strtab = b"\x00" + actual_sym.encode("ascii") + b"\x00"
    sym_entry0 = b"\x00" * 24
    # Elf64_Sym: st_name(I), st_info(B), st_other(B), st_shndx(H), st_value(Q), st_size(Q)
    # STB_GLOBAL=1, STT_FUNC=2 -> st_info = 0x12
    sym_entry1 = struct.pack("<IBBHQQ", 1, 0x12, 0, 1, sym_val, sym_sz)
    symtab = sym_entry0 + sym_entry1

    shstr_parts = [b"", b".text", b".symtab", b".strtab", b".shstrtab"]
    if relas is not None:
        shstr_parts.append(b".rela.text")
    shstr_offsets: List[int] = []
    shstrtab = bytearray()
    for p in shstr_parts:
        shstr_offsets.append(len(shstrtab))
        shstrtab.extend(p + b"\x00")
    shstrtab_bytes = bytes(shstrtab)

    rela_bytes = b""
    if relas is not None:
        rela_bytes = b"".join(struct.pack("<QQq", r_off, r_info, r_add) for r_off, r_info, r_add in relas)

    off = 64  # sizeof(Elf64_Ehdr)
    text_off = off
    off += len(text_bytes)
    pad = (8 - (off % 8)) % 8
    sym_off = off + pad
    off = sym_off + len(symtab)
    str_off = off
    off += len(strtab)
    shstr_off = off
    off += len(shstrtab_bytes)
    rela_pad = 0
    rela_off = off
    if relas is not None:
        rela_pad = (8 - (off % 8)) % 8
        rela_off = off + rela_pad
        off = rela_off + len(rela_bytes)
    sh_pad = (8 - (off % 8)) % 8
    shoff = off + sh_pad

    # Elf64_Shdr: sh_name(I), sh_type(I), sh_flags(Q), sh_addr(Q), sh_offset(Q),
    #             sh_size(Q), sh_link(I), sh_info(I), sh_addralign(Q), sh_entsize(Q)
    sh0 = struct.pack("<IIQQQQIIQQ", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    sh1 = struct.pack("<IIQQQQIIQQ", shstr_offsets[1], 1, 6, text_vaddr, text_off, len(text_bytes), 0, 0, 2, 0)
    sh2 = struct.pack("<IIQQQQIIQQ", shstr_offsets[2], 2, 0, 0, sym_off, len(symtab), 3, 1, 8, 24)
    sh3 = struct.pack("<IIQQQQIIQQ", shstr_offsets[3], 3, 0, 0, str_off, len(strtab), 0, 0, 1, 0)
    sh4 = struct.pack("<IIQQQQIIQQ", shstr_offsets[4], 3, 0, 0, shstr_off, len(shstrtab_bytes), 0, 0, 1, 0)
    shdrs = [sh0, sh1, sh2, sh3, sh4]
    if relas is not None:
        sh5 = struct.pack("<IIQQQQIIQQ", shstr_offsets[5], 4, 0, 0, rela_off, len(rela_bytes), 2, 1, 8, 24)
        shdrs.append(sh5)

    e_ident = bytearray(16)
    e_ident[0:4] = magic
    e_ident[4] = ei_class
    e_ident[5] = ei_data
    e_ident[6] = 1  # EV_CURRENT
    ehdr = struct.pack(
        "<16sHHIQQQIHHHHHH",
        bytes(e_ident), e_type, e_machine, 1, 0, 0, shoff, e_flags, 64, 56, 0, 64, len(shdrs), 4
    )

    out = bytearray(ehdr)
    out.extend(text_bytes)
    out.extend(b"\x00" * pad)
    out.extend(symtab)
    out.extend(strtab)
    out.extend(shstrtab_bytes)
    if relas is not None:
        out.extend(b"\x00" * rela_pad)
        out.extend(rela_bytes)
    out.extend(b"\x00" * sh_pad)
    out.extend(b"".join(shdrs))
    assert len(out) == shoff + len(shdrs) * 64

    raw = bytes(out)
    return raw[:truncate_to] if truncate_to is not None else raw


def run_cmd(cmd: List[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, text=True, capture_output=True)


def run_live_corpus(
    bins: List[str],
    c_path: str,
    tmpdir: str,
    lrat_cache: Dict[str, str],
) -> int:
    clang = "/usr/lib/llvm-22/bin/clang"
    lld = "/usr/lib/llvm-22/bin/ld.lld"
    ll = os.path.join(tmpdir, "live.ll")
    o_file = os.path.join(tmpdir, "live.o")
    elf_file = os.path.join(tmpdir, "live.elf")
    relax_o = os.path.join(tmpdir, "live_relax.o")
    subprocess.run(
        [clang, "--target=riscv64-unknown-none-elf", "-march=rv64imc", "-mno-relax", "-mabi=lp64",
         "-O2", "-fno-builtin", "-S", "-emit-llvm", c_path, "-o", ll],
        check=True,
    )
    subprocess.run(
        [clang, "--target=riscv64-unknown-none-elf", "-march=rv64imc", "-mno-relax", "-mabi=lp64",
         "-O2", "-fno-builtin", "-c", c_path, "-o", o_file],
        check=True,
    )
    subprocess.run([lld, "-m", "elf64lriscv", "--no-relax", "-e", "pid_clamp_i32", o_file, "-o", elf_file], check=True)
    subprocess.run(
        [clang, "--target=riscv64-unknown-none-elf", "-march=rv64imc", "-mabi=lp64",
         "-O2", "-fno-builtin", "-c", c_path, "-o", relax_o],
        check=True,
    )

    count = 0
    for fn, rw, args, _ in CORPUS_FUNCS:
        if fn not in lrat_cache:
            bare_cert = os.path.join(tmpdir, f"live_{fn}.bare.cert")
            with open(bare_cert, "w", encoding="utf-8") as f:
                f.write(format_mc_cert("rel", fn, 1, rw, args))
            em = run_cmd([bins[0], "--emit-mc-cnf", "--ir", ll, "--elf", o_file, "--cert", bare_cert])
            if em.returncode != 0:
                raise RuntimeError(f"live --emit-mc-cnf failed for {fn}: {em.stderr}")
            lrat_cache[fn] = format_lrat_sexp(solve_cdcl_lrat(em.stdout))
        for kind, elf_path in [("rel", o_file), ("exec", elf_file)]:
            cert_path = os.path.join(tmpdir, f"live_{fn}.{kind}.mc.cert")
            with open(cert_path, "w", encoding="utf-8") as f:
                f.write(format_mc_cert(kind, fn, 1, rw, args, lrat_cache[fn]))
            for b in bins:
                res = run_cmd([b, "--check-mc", "--ir", ll, "--elf", elf_path, "--cert", cert_path])
                if res.returncode != 0:
                    raise RuntimeError(f"live --check-mc failed ({b}, {fn}, {kind}): rc={res.returncode} {res.stderr}")
            count += 1
    # Ensure branched functions in live_relax.o are rejected with rc=4
    rel_cert_pid = os.path.join(tmpdir, "live_pid_clamp_i32.rel.mc.cert")
    for b in bins:
        rej = run_cmd([b, "--check-mc", "--ir", ll, "--elf", relax_o, "--cert", rel_cert_pid])
        if rej.returncode != 4:
            raise RuntimeError(f"expected relax rejection rc=4 on live_relax.o ({b}), got {rej.returncode}")
    return count


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    default_native = os.path.join(repo_root, "vellvm", "src", "_build", "default", "ml", "bin", "cert-validator")
    default_bc = os.path.join(repo_root, "vellvm", "src", "_build", "default", "ml", "bin", "cert-validator.bc")
    parser.add_argument("cert_validator", nargs="?", default=default_native, help="Path to native cert-validator.")
    parser.add_argument("cert_validator_bc", nargs="?", default=default_bc, help="Path to bytecode cert-validator.bc.")
    parser.add_argument("--live-corpus", metavar="C_FILE", help="Also compile and verify a live C corpus with clang-22/ld.lld.")
    ns = parser.parse_args(argv)

    bins = [ns.cert_validator, ns.cert_validator_bc]
    for b in bins:
        if not os.path.isfile(b):
            print(f"error: validator binary not found: {b}", file=sys.stderr)
            return 2

    t_start = time.time()
    with tempfile.TemporaryDirectory(prefix="forged_mc_") as tmpdir:
        ir_path = os.path.join(tmpdir, "corpus.ll")
        with open(ir_path, "w", encoding="utf-8") as f:
            f.write(CORPUS_IR)

        lrat_cache: Dict[str, str] = {}
        pos_passed = 0

        # 16 positive checks: 8 functions x (ET_REL + ET_EXEC), dual-verified native vs bytecode.
        for fn, rw, args, hex_bytes in CORPUS_FUNCS:
            code = bytes.fromhex(hex_bytes)
            rel_elf = build_elf64(fn, code, e_type=1, e_flags=0x1)
            exec_elf = build_elf64(fn, code, e_type=2, e_flags=0x1)
            rel_path = os.path.join(tmpdir, f"{fn}.o")
            exec_path = os.path.join(tmpdir, f"{fn}.elf")
            with open(rel_path, "wb") as f:
                f.write(rel_elf)
            with open(exec_path, "wb") as f:
                f.write(exec_elf)

            bare_cert = os.path.join(tmpdir, f"{fn}.bare.mc.cert")
            with open(bare_cert, "w", encoding="utf-8") as f:
                f.write(format_mc_cert("rel", fn, 1, rw, args))

            em = run_cmd([bins[0], "--emit-mc-cnf", "--ir", ir_path, "--elf", rel_path, "--cert", bare_cert])
            if em.returncode != 0:
                print(f"FAIL --emit-mc-cnf {fn}: rc={em.returncode} err={em.stderr}", file=sys.stderr)
                return 1

            t0 = time.time()
            if em.stdout.strip().startswith("c ALGEBRAIC_OK"):
                lrat_cache[fn] = ""
            else:
                lrat_cache[fn] = format_lrat_sexp(solve_cdcl_lrat(em.stdout))
            solve_dt = time.time() - t0

            for kind, epath in [("rel", rel_path), ("exec", exec_path)]:
                cert_path = os.path.join(tmpdir, f"{fn}.{kind}.mc.cert")
                with open(cert_path, "w", encoding="utf-8") as f:
                    f.write(format_mc_cert(kind, fn, 1, rw, args, lrat_cache[fn]))
                rcs = []
                for b in bins:
                    r = run_cmd([b, "--check-mc", "--ir", ir_path, "--elf", epath, "--cert", cert_path])
                    rcs.append((b, r.returncode, r.stderr.strip()))
                if any(rc != 0 for _, rc, _ in rcs):
                    print(f"FAIL positive {fn} ({kind}): {rcs}", file=sys.stderr)
                    return 1
                pos_passed += 1
            print(f"PASS {fn} (rel+exec, native+bc, lrat solve {solve_dt:.2f}s)")

        # Adversarial forged-ELF / forged-MC rejection suite (all parity-checked native vs bytecode).
        pack_fn, pack_rw, pack_args, pack_hex = CORPUS_FUNCS[4]
        pack_code = bytes.fromhex(pack_hex)
        pack_lrat = lrat_cache[pack_fn]
        pack_cert_rel = format_mc_cert("rel", pack_fn, 1, pack_rw, pack_args, pack_lrat)
        pack_cert_exec = format_mc_cert("exec", pack_fn, 1, pack_rw, pack_args, pack_lrat)

        pid_fn, pid_rw, pid_args, pid_hex = CORPUS_FUNCS[0]
        pid_code = bytes.fromhex(pid_hex)
        pid_lrat = lrat_cache[pid_fn]
        pid_cert_rel = format_mc_cert("rel", pid_fn, 1, pid_rw, pid_args, pid_lrat)

        # Flip 1 bit in pack_sensor_u64 (slli a0, a0, 32 -> wrong code)
        flipped_pack = bytes([pack_code[0] ^ 0x01]) + pack_code[1:]
        # Single RV64 jalr ra, 0(zero) = 0x000080e7 followed by c.ret (0x8082)
        call_inst = bytes.fromhex("e78000008280")
        bad_call_ir = (
            'target datalayout = "e-m:e-p:64:64-i64:64-i128:128-n32:64-S128"\n'
            'target triple = "riscv64-unknown-none-elf"\n'
            'declare i32 @ext_helper(i32)\n'
            'define i32 @ext_caller(i32 signext %0) {\n'
            '  %2 = call i32 @ext_helper(i32 %0)\n'
            '  ret i32 %2\n'
            '}\n'
        )
        bad_call_ir_path = os.path.join(tmpdir, "bad_call.ll")
        with open(bad_call_ir_path, "w", encoding="utf-8") as f:
            f.write(bad_call_ir)

        adv_cases = [
            ("bad_elf_magic", build_elf64(pack_fn, pack_code, magic=b"\x00ELF"), pack_cert_rel, ir_path),
            ("bad_elf_class_32", build_elf64(pack_fn, pack_code, ei_class=1), pack_cert_rel, ir_path),
            ("bad_elf_endian_be", build_elf64(pack_fn, pack_code, ei_data=2), pack_cert_rel, ir_path),
            ("bad_elf_machine_x86", build_elf64(pack_fn, pack_code, e_machine=62), pack_cert_rel, ir_path),
            ("et_rel_with_rela_relax", build_elf64(pack_fn, pack_code, relas=[(0, 51, 0)]), pack_cert_rel, ir_path),
            ("et_rel_with_rela_branch", build_elf64(pack_fn, pack_code, relas=[(2, 16, 0)]), pack_cert_rel, ir_path),
            ("truncated_elf_header", build_elf64(pack_fn, pack_code, truncate_to=48), pack_cert_rel, ir_path),
            ("oob_symbol_slice", build_elf64(pack_fn, pack_code, sym_size_override=len(pack_code) + 4), pack_cert_rel, ir_path),
            ("zero_size_symbol", build_elf64(pack_fn, pack_code, sym_size_override=0), pack_cert_rel, ir_path),
            ("missing_symbol", build_elf64(pack_fn, pack_code, sym_name="other_fn"), pack_cert_rel, ir_path),
            ("forged_elf_kind_exec_on_rel", build_elf64(pack_fn, pack_code, e_type=1), pack_cert_exec, ir_path),
            ("forged_rvc0_on_rvc1_bytes",
             build_elf64(pack_fn, pack_code, e_flags=0),
             format_mc_cert("rel", pack_fn, 0, pack_rw, pack_args, pack_lrat), ir_path),
            ("forged_rvc_flag_mismatch",
             build_elf64(pack_fn, pack_code, e_flags=1),
             format_mc_cert("rel", pack_fn, 0, pack_rw, pack_args, pack_lrat), ir_path),
            ("wrong_abi_signext_vs_zeroext",
             build_elf64(pid_fn, pid_code),
             format_mc_cert("rel", pid_fn, 1, pid_rw, [("%0", 32, "zeroext"), ("%1", 32, "signext"), ("%2", 32, "signext")], pid_lrat), ir_path),
            ("wrong_abi_missing_attr",
             build_elf64(pid_fn, pid_code),
             format_mc_cert("rel", pid_fn, 1, pid_rw, [("%0", 32, "none"), ("%1", 32, "signext"), ("%2", 32, "signext")], pid_lrat), ir_path),
            ("wrong_ret_width",
             build_elf64(pid_fn, pid_code),
             format_mc_cert("rel", pid_fn, 1, 64, pid_args, pid_lrat), ir_path),
            ("single_bit_inst_flip", build_elf64(pack_fn, flipped_pack), pack_cert_rel, ir_path),
            ("corrupted_lrat_empty_proof",
             build_elf64(pack_fn, pack_code),
             format_mc_cert("rel", pack_fn, 1, pack_rw, pack_args, ""), ir_path),
            ("corrupted_lrat_bad_hint",
             build_elf64(pack_fn, pack_code),
             format_mc_cert("rel", pack_fn, 1, pack_rw, pack_args, "(add 999999 () (999998))"), ir_path),
            ("unapproved_jalr_call_inst", build_elf64(pack_fn, call_inst), pack_cert_rel, ir_path),
            ("unsupported_ir_ext_call",
             build_elf64("ext_caller", call_inst),
             format_mc_cert("rel", "ext_caller", 1, 32, [("%0", 32, "signext")], ""), bad_call_ir_path),
        ]

        for name, elf_bytes, cert_str, case_ir in adv_cases:
            ep = os.path.join(tmpdir, f"adv_{name}.elf")
            cp = os.path.join(tmpdir, f"adv_{name}.mc.cert")
            with open(ep, "wb") as f:
                f.write(elf_bytes)
            with open(cp, "w", encoding="utf-8") as f:
                f.write(cert_str)
            rcs = [run_cmd([b, "--check-mc", "--ir", case_ir, "--elf", ep, "--cert", cp]).returncode for b in bins]
            if rcs[0] == 0 or rcs[0] != rcs[1]:
                print(f"FAIL adversarial {name}: rcs={rcs}", file=sys.stderr)
                return 1
        print(f"PASS {len(adv_cases)} adversarial forged-ELF/forged-MC rejection cases (native == bytecode parity)")

        live_count = 0
        if ns.live_corpus:
            live_count = run_live_corpus(bins, ns.live_corpus, tmpdir, lrat_cache)
            print(f"PASS live corpus: {live_count} positive + relax rejection checks")

    dt = time.time() - t_start
    print(f"MC FORGED SUITE OK: {pos_passed} positive, {len(adv_cases)} adversarial ({dt:.2f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
