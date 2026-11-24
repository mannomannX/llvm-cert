#!/usr/bin/env python3
# Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
# Licensed under the LLVMCert Non-Commercial Evaluation & Research License
# or a separate LLVMCert Commercial Software License Agreement.
# See /LICENSE in the repository root for details.
"""Stage-1 Extracted Rocq Concrete ISA Semantics Differential Oracle
(`A64CoreSem` vs. `qemu-aarch64` & `Rv64Sem` vs. `qemu-riscv64`).

Executes Rocq-extracted `A64CoreSem.a64_eval_bytes_concrete` / `a64_decode_word_ok` /
`a64_decode_bitmasks` and `Rv64Sem.rv_eval_bytes_concrete` / `rv_decode_bytes_ok`
directly against static ELF64 batches running under `qemu-aarch64` / `qemu-riscv64`
and instruction disassembly via `llvm-objdump`. Zero OCaml TCB impact.
"""

from __future__ import annotations

import argparse
import os
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from typing import Dict, List, Optional, Sequence, Tuple

MASK64 = (1 << 64) - 1
MASK32 = (1 << 32) - 1

A64_TRACKED_REGS = list(range(16))  # x0..x15
RV64_TRACKED_REGS = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

EDGE_VALS_64 = [
    0,
    1,
    2,
    3,
    7,
    8,
    15,
    16,
    31,
    32,
    33,
    63,
    64,
    0xFF,
    0x100,
    0x7FFF,
    0x8000,
    0xFFFF,
    0x7FFFFFFF,
    0x80000000,
    0x80000001,
    0xFFFFFFFF,
    0x100000000,
    0x123456789ABCDEF0,
    0xFEDCBA9876543210,
    0x7FFFFFFFFFFFFFFF,
    0x8000000000000000,
    0x8000000000000001,
    0xFFFFFFFFFFFFFFFF,
]


def u32(x: int) -> int:
    return x & MASK32


def u64(x: int) -> int:
    return x & MASK64


def le32(w: int) -> bytes:
    return struct.pack("<I", w & MASK32)


def le16(h: int) -> bytes:
    return struct.pack("<H", h & 0xFFFF)


def find_tool(candidates: Sequence[str]) -> Optional[str]:
    for c in candidates:
        if os.path.isabs(c) and os.path.isfile(c):
            return c
        p = shutil.which(c)
        if p:
            return p
    return None


def build_runner(repo_root: str, build_dir: str) -> str:
    runner_ml = os.path.join(repo_root, "scripts", "isa_oracle", "isa_oracle_runner.ml")
    extracted_dir = os.path.join(repo_root, "vellvm", "src", "_build", "default", "ml", "extracted")
    cmxa = os.path.join(extracted_dir, "extracted.cmxa")
    byte_objs = os.path.join(extracted_dir, ".extracted.objs", "byte")
    native_objs = os.path.join(extracted_dir, ".extracted.objs", "native")
    if not os.path.isfile(cmxa):
        raise FileNotFoundError(f"extracted.cmxa not found: {cmxa}")
    out_bin = os.path.join(build_dir, "isa_oracle_runner")
    need_build = (
        not os.path.isfile(out_bin)
        or os.path.getmtime(runner_ml) > os.path.getmtime(out_bin)
        or os.path.getmtime(cmxa) > os.path.getmtime(out_bin)
    )
    if need_build:
        os.makedirs(build_dir, exist_ok=True)
        cmd = [
            "ocamlfind",
            "ocamlopt",
            "-package",
            "zarith",
            "-linkpkg",
            "-I",
            byte_objs,
            "-I",
            native_objs,
            cmxa,
            runner_ml,
            "-o",
            out_bin,
        ]
        res = subprocess.run(cmd, text=True, capture_output=True)
        if res.returncode != 0:
            raise RuntimeError(f"Failed building isa_oracle_runner:\n{res.stderr}")
    return out_bin


class IsaOracleClient:
    def __init__(self, runner_bin: str) -> None:
        self.proc = subprocess.Popen(
            [runner_bin],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        assert self.proc.stdin is not None and self.proc.stdout is not None
        resp = self.query("PING")
        if resp != "PONG":
            raise RuntimeError(f"isa_oracle_runner failed PING: {resp!r}")

    def close(self) -> None:
        if self.proc.stdin:
            self.proc.stdin.close()
        self.proc.wait(timeout=10)

    def query(self, line: str) -> str:
        assert self.proc.stdin is not None and self.proc.stdout is not None
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()
        out = self.proc.stdout.readline()
        if not out:
            err = self.proc.stderr.read() if self.proc.stderr else ""
            raise RuntimeError(f"isa_oracle_runner EOF on {line!r}: {err}")
        return out.rstrip("\r\n")

    def query_many(self, lines: Sequence[str]) -> List[str]:
        assert self.proc.stdin is not None and self.proc.stdout is not None
        out: List[str] = []
        chunk_sz = 64
        for i in range(0, len(lines), chunk_sz):
            chunk = lines[i : i + chunk_sz]
            self.proc.stdin.write("\n".join(chunk) + "\n")
            self.proc.stdin.flush()
            for _ in chunk:
                resp = self.proc.stdout.readline()
                if not resp:
                    err = self.proc.stderr.read() if self.proc.stderr else ""
                    raise RuntimeError(f"isa_oracle_runner EOF in query_many: {err}")
                out.append(resp.rstrip("\r\n"))
        return out

    def a64_bitmask(self, sf: int, n: int, imms: int, immr: int) -> Optional[int]:
        resp = self.query(f"A64_BITMASK {sf} {n} {imms} {immr}")
        if resp == "NONE":
            return None
        if resp.startswith("OK "):
            return int(resp[3:], 16)
        raise RuntimeError(f"Unexpected A64_BITMASK response: {resp!r}")

    def a64_decode_batch(self, words: Sequence[int]) -> List[bool]:
        resps = self.query_many([f"A64_DECODE {w:08x}" for w in words])
        return [r == "OK" for r in resps]

    def a64_exec(
        self, fuel: int, code: bytes, regs31: Sequence[int], nzcv: Tuple[int, int, int, int]
    ) -> Tuple[List[int], Tuple[int, int, int, int]]:
        n, z, c, v = nzcv
        rhex = " ".join(f"{r & MASK64:016x}" for r in regs31)
        resp = self.query(f"A64_EXEC {fuel} {code.hex()} {n} {z} {c} {v} {rhex}")
        if not resp.startswith("OK "):
            raise RuntimeError(f"A64_EXEC error for {code.hex()}: {resp}")
        parts = resp.split()[1:]
        fl = (int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3]))
        out_regs = [int(h, 16) for h in parts[4:]]
        return out_regs, fl

    def rv64_decode_batch(self, rvc: int, codes: Sequence[bytes]) -> List[bool]:
        resps = self.query_many([f"RV64_DECODE {rvc} {c.hex()}" for c in codes])
        return [r == "OK" for r in resps]

    def rv64_exec(self, rvc: int, fuel: int, code: bytes, regs32: Sequence[int]) -> List[int]:
        rhex = " ".join(f"{r & MASK64:016x}" for r in regs32)
        resp = self.query(f"RV64_EXEC {rvc} {fuel} {code.hex()} {rhex}")
        if not resp.startswith("OK "):
            raise RuntimeError(f"RV64_EXEC error for {code.hex()}: {resp}")
        return [int(h, 16) for h in resp.split()[1:]]


# ---------------------------------------------------------------------------
# Pure-Python Static ELF64 Harness (AArch64 & RISC-V64, zero assembler needed)
# ---------------------------------------------------------------------------

def build_static_elf64(
    e_machine: int, e_flags: int, text_code: bytes, rodata: bytes, out_buf_size: int
) -> Tuple[bytes, int, int]:
    """Build a static Linux ELF64 executable with RX segment (0x400000) and RW BSS (0x800000).
    Returns (elf_bytes, rodata_vaddr, out_vaddr)."""
    base_vaddr = 0x400000
    out_vaddr = 0x800000
    ehdr_size = 64
    phdr_size = 56
    hdr_total = ehdr_size + 2 * phdr_size  # 176 bytes (16B aligned)
    code_off = hdr_total
    entry_vaddr = base_vaddr + code_off
    rodata_off_raw = code_off + len(text_code)
    pad = (16 - (rodata_off_raw % 16)) % 16
    rodata_off = rodata_off_raw + pad
    rodata_vaddr = base_vaddr + rodata_off
    file_size = rodata_off + len(rodata)

    e_ident = bytearray(16)
    e_ident[0:4] = b"\x7fELF"
    e_ident[4] = 2  # ELFCLASS64
    e_ident[5] = 1  # ELFDATA2LSB
    e_ident[6] = 1  # EV_CURRENT
    ehdr = struct.pack(
        "<16sHHIQQQIHHHHHH",
        bytes(e_ident),
        2,              # ET_EXEC
        e_machine,
        1,              # EV_CURRENT
        entry_vaddr,
        ehdr_size,      # e_phoff
        0,              # e_shoff
        e_flags,
        ehdr_size,
        phdr_size,
        2,              # e_phnum
        64,             # e_shentsize
        0,              # e_shnum
        0,              # e_shstrndx
    )
    # PT_LOAD = 1, PF_X=1, PF_W=2, PF_R=4
    ph0 = struct.pack(
        "<IIQQQQQQ", 1, 5, 0, base_vaddr, base_vaddr, file_size, file_size, 0x1000
    )
    out_memsz = max(0x1000, ((out_buf_size + 0xFFF) // 0x1000) * 0x1000)
    ph1 = struct.pack(
        "<IIQQQQQQ", 1, 6, 0, out_vaddr, out_vaddr, 0, out_memsz, 0x1000
    )
    blob = bytearray(ehdr + ph0 + ph1 + text_code + (b"\x00" * pad) + rodata)
    assert len(blob) == file_size
    return bytes(blob), rodata_vaddr, out_vaddr


def a64_movz(sf: int, rd: int, imm16: int, hw: int) -> int:
    return (sf << 31) | (0b10 << 29) | (0b100101 << 23) | (hw << 21) | ((imm16 & 0xFFFF) << 5) | rd


def a64_movn(sf: int, rd: int, imm16: int, hw: int) -> int:
    return (sf << 31) | (0b00 << 29) | (0b100101 << 23) | (hw << 21) | ((imm16 & 0xFFFF) << 5) | rd


def a64_movk(sf: int, rd: int, imm16: int, hw: int) -> int:
    return (sf << 31) | (0b11 << 29) | (0b100101 << 23) | (hw << 21) | ((imm16 & 0xFFFF) << 5) | rd


def a64_load_imm32(rd: int, val: int) -> List[int]:
    return [a64_movz(1, rd, val & 0xFFFF, 0), a64_movk(1, rd, (val >> 16) & 0xFFFF, 1)]


def run_qemu_a64_batch(
    qemu_bin: str, tmpdir: str, cases: Sequence[Tuple[bytes, Sequence[int], Tuple[int, int, int, int], bool]]
) -> List[Tuple[List[int], Tuple[int, int, int, int]]]:
    """Execute batched AArch64 cases in one `qemu-aarch64` call.
    Each case is (code_bytes, regs_0_15, (n, z, c, v), is_ret_wrapped)."""
    if not cases:
        return []
    rec_size = 136  # 16*8 + 8 (nzcv)
    n_cases = len(cases)
    out_bytes_len = n_cases * rec_size
    base_vaddr = 0x400000
    out_vaddr = 0x800000

    # Placeholder prologue loads x24=in_vaddr, x25=out_vaddr, x26=out_vaddr, x27=sp
    # First measure code length with dummy in_vaddr=0, then patch!
    def assemble(in_vaddr: int) -> bytes:
        words: List[int] = []
        words.extend(a64_load_imm32(24, in_vaddr))
        words.extend(a64_load_imm32(25, out_vaddr))
        words.extend(a64_load_imm32(26, out_vaddr))
        words.append(0x910003FB)  # add x27, sp, #0
        code_buf = bytearray().join(le32(w) for w in words)

        for snip, _, _, is_ret in cases:
            if len(snip) % 4 != 0:
                raise ValueError(f"Unaligned A64 snippet len={len(snip)}")
            per_pre: List[int] = []
            for p in range(8):
                # ldp x(2p), x(2p+1), [x24, #(p*16)]
                imm7 = (p * 2) & 0x7F
                per_pre.append(0xA9400000 | (imm7 << 15) | ((2 * p + 1) << 10) | (24 << 5) | (2 * p))
            per_pre.append(0xF9400000 | (16 << 10) | (24 << 5) | 16)  # ldr x16, [x24, #128]
            per_pre.append(0xD51B4210)                                 # msr nzcv, x16
            per_pre.append(0x91000000 | (rec_size << 10) | (24 << 5) | 24)  # add x24, x24, #136
            for cr in (16, 17, 18, 19, 20, 21, 22, 23, 30):
                per_pre.append(0xAA1F03E0 | cr)  # mov x_cr, xzr
            code_buf.extend(b"".join(le32(w) for w in per_pre))
            if is_ret:
                nwords = len(snip) // 4
                code_buf.extend(le32(0x94000002))              # bl +8
                code_buf.extend(le32(0x14000000 | ((nwords + 1) & 0x3FFFFFF)))  # b after_ret
                code_buf.extend(snip)
            else:
                code_buf.extend(snip)
            per_post: List[int] = [
                0x9100037F,  # add sp, x27, #0  (restore sp if touched)
                0xD53B4210,  # mrs x16, nzcv
                0xF9000000 | (16 << 10) | (25 << 5) | 16,  # str x16, [x25, #128]
            ]
            for p in range(8):
                imm7 = (p * 2) & 0x7F
                per_post.append(0xA9000000 | (imm7 << 15) | ((2 * p + 1) << 10) | (25 << 5) | (2 * p))
            per_post.append(0x91000000 | (rec_size << 10) | (25 << 5) | 25)  # add x25, x25, #136
            code_buf.extend(b"".join(le32(w) for w in per_post))

        # Write full out_bytes_len looping on write(1, ptr, rem)
        # x26 = cur_ptr, x27 = rem
        epi: List[int] = []
        epi.extend(a64_load_imm32(27, out_bytes_len))
        # loop_hdr:
        # cbz x27, exit (offset +9*4 = +36 -> imm19=9)
        epi.append(0xB400013B)                 # cbz x27, +36
        epi.append(a64_movz(1, 0, 1, 0))       # mov x0, #1
        epi.append(0xAA1A03E1)                 # mov x1, x26
        epi.append(0xAA1B03E2)                 # mov x2, x27
        epi.append(a64_movz(1, 8, 64, 0))      # mov x8, #64 (__NR_write)
        epi.append(0xD4000001)                 # svc #0
        epi.append(0x8B00035A)                 # add x26, x26, x0
        epi.append(0xCB00037B)                 # sub x27, x27, x0
        epi.append(0x17FFFFF8)                 # b -32 (loop_hdr)
        # exit:
        epi.append(a64_movz(1, 0, 0, 0))       # mov x0, #0
        epi.append(a64_movz(1, 8, 94, 0))      # mov x8, #94 (__NR_exit_group)
        epi.append(0xD4000001)                 # svc #0
        code_buf.extend(b"".join(le32(w) for w in epi))
        return bytes(code_buf)

    dummy_code = assemble(0)
    ro_off_raw = 176 + len(dummy_code)
    in_vaddr = base_vaddr + ro_off_raw + ((16 - (ro_off_raw % 16)) % 16)
    final_code = assemble(in_vaddr)
    assert len(final_code) == len(dummy_code)

    rodata = bytearray()
    for _, regs16, (n, z, c, v), _ in cases:
        for r in regs16:
            rodata.extend(struct.pack("<Q", r & MASK64))
        nzcv_word = ((n & 1) << 31) | ((z & 1) << 30) | ((c & 1) << 29) | ((v & 1) << 28)
        rodata.extend(struct.pack("<Q", nzcv_word))

    elf_bytes, actual_ro, _ = build_static_elf64(183, 0, final_code, bytes(rodata), out_bytes_len)
    assert actual_ro == in_vaddr

    ep = os.path.join(tmpdir, "batch_a64.elf")
    with open(ep, "wb") as f:
        f.write(elf_bytes)
    os.chmod(ep, 0o755)
    proc = subprocess.run([qemu_bin, ep], capture_output=True, timeout=60)
    if proc.returncode != 0 or len(proc.stdout) != out_bytes_len:
        raise RuntimeError(
            f"qemu-aarch64 batch failed: rc={proc.returncode} stdout={len(proc.stdout)}/{out_bytes_len} stderr={proc.stderr!r}"
        )

    out: List[Tuple[List[int], Tuple[int, int, int, int]]] = []
    for i in range(n_cases):
        chunk = proc.stdout[i * rec_size : (i + 1) * rec_size]
        vals = struct.unpack("<17Q", chunk)
        nzcv_w = vals[16]
        fl = ((nzcv_w >> 31) & 1, (nzcv_w >> 30) & 1, (nzcv_w >> 29) & 1, (nzcv_w >> 28) & 1)
        out.append((list(vals[:16]), fl))
    return out


def rv_lui(rd: int, imm20: int) -> int:
    return ((imm20 & 0xFFFFF) << 12) | (rd << 7) | 0x37


def rv_itype(opcode: int, funct3: int, rd: int, rs1: int, imm12: int) -> int:
    return ((imm12 & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode


def rv_rtype(opcode: int, funct7: int, funct3: int, rd: int, rs1: int, rs2: int) -> int:
    return (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode


def rv_sd(rs2: int, rs1: int, imm12: int) -> int:
    return (((imm12 >> 5) & 0x7F) << 25) | (rs2 << 20) | (rs1 << 15) | (3 << 12) | ((imm12 & 0x1F) << 7) | 0x23


def rv_load_imm32(rd: int, val: int) -> List[int]:
    val32 = val & 0xFFFFFFFF
    hi = ((val32 + 0x800) >> 12) & 0xFFFFF
    lo = val32 & 0xFFF
    return [rv_lui(rd, hi), rv_itype(0x1B, 0, rd, rd, lo)]


def run_qemu_rv64_batch(
    qemu_bin: str, tmpdir: str, cases: Sequence[Tuple[bytes, Sequence[int], bool]]
) -> List[List[int]]:
    """Execute batched RV64/RVC cases in one `qemu-riscv64` call.
    Each case is (code_bytes, regs_17_tracked, is_ret_wrapped).
    Returns list of 17 tracked register values corresponding to RV64_TRACKED_REGS."""
    if not cases:
        return []
    n_regs = len(RV64_TRACKED_REGS)  # 17
    rec_size = n_regs * 8             # 136 bytes
    n_cases = len(cases)
    out_bytes_len = n_cases * rec_size
    base_vaddr = 0x400000
    out_vaddr = 0x800000

    # Reserve x18=in_ptr, x19=out_ptr, x20=out_cur, x21=rem
    def assemble(in_vaddr: int) -> bytes:
        words: List[int] = []
        words.extend(rv_load_imm32(18, in_vaddr))
        words.extend(rv_load_imm32(19, out_vaddr))
        words.extend(rv_load_imm32(20, out_vaddr))
        code_buf = bytearray().join(le32(w) for w in words)

        for snip, _, is_ret in cases:
            if len(snip) % 2 != 0:
                raise ValueError(f"Unaligned RV64 snippet len={len(snip)}")
            pre: List[int] = []
            for idx, r in enumerate(RV64_TRACKED_REGS):
                pre.append(rv_itype(0x03, 3, r, 18, idx * 8))  # ld r, off(x18)
            pre.append(rv_itype(0x13, 0, 18, 18, rec_size))     # addi x18, x18, 136
            for cr in (1, 3, 4, 22, 23, 24, 25, 26, 27):
                pre.append(rv_itype(0x13, 0, cr, 0, 0))         # addi cr, x0, 0
            code_buf.extend(b"".join(le32(w) for w in pre))
            if is_ret:
                # jal x1, +8; jal x0, +(len(snip)+4); snip
                code_buf.extend(le32((0x0080006F & 0xFFFFF000) | (1 << 7) | 0x6F))
                joff = len(snip) + 4
                imm20 = (
                    (((joff >> 20) & 1) << 19)
                    | (((joff >> 1) & 0x3FF) << 9)
                    | (((joff >> 11) & 1) << 8)
                    | ((joff >> 12) & 0xFF)
                )
                code_buf.extend(le32((imm20 << 12) | 0x6F))
                code_buf.extend(snip)
            else:
                code_buf.extend(snip)
            # Align back to 4B? Not strictly needed on RVC-enabled RV64, all subsequent are 4B.
            post: List[int] = []
            for idx, r in enumerate(RV64_TRACKED_REGS):
                post.append(rv_sd(r, 19, idx * 8))              # sd r, off(x19)
            post.append(rv_itype(0x13, 0, 19, 19, rec_size))    # addi x19, x19, 136
            code_buf.extend(b"".join(le32(w) for w in post))

        # Write loop using x20 (cur_ptr), x21 (rem)
        epi: List[int] = []
        epi.extend(rv_load_imm32(21, out_bytes_len))
        # loop_hdr: beq x21, x0, +36 (9*4)
        off_b = 36
        beq_done = (
            (((off_b >> 12) & 1) << 31)
            | (((off_b >> 5) & 0x3F) << 25)
            | (0 << 20)
            | (21 << 15)
            | (0 << 12)
            | (((off_b >> 1) & 0xF) << 8)
            | (((off_b >> 11) & 1) << 7)
            | 0x63
        )
        epi.append(beq_done)
        epi.append(rv_itype(0x13, 0, 10, 0, 1))                 # addi a0, x0, 1
        epi.append(rv_rtype(0x33, 0, 0, 11, 20, 0))             # add a1, x20, x0
        epi.append(rv_rtype(0x33, 0, 0, 12, 21, 0))             # add a2, x21, x0
        epi.append(rv_itype(0x13, 0, 17, 0, 64))                # addi a7, x0, 64 (__NR_write)
        epi.append(0x00000073)                                  # ecall
        epi.append(rv_rtype(0x33, 0, 0, 20, 20, 10))            # add x20, x20, a0
        epi.append(rv_rtype(0x33, 32, 0, 21, 21, 10))           # sub x21, x21, a0
        # jal x0, -32
        back = (-32) & 0x1FFFFF
        bimm = (
            (((back >> 20) & 1) << 19)
            | (((back >> 1) & 0x3FF) << 9)
            | (((back >> 11) & 1) << 8)
            | ((back >> 12) & 0xFF)
        )
        epi.append((bimm << 12) | 0x6F)
        epi.append(rv_itype(0x13, 0, 10, 0, 0))                 # addi a0, x0, 0
        epi.append(rv_itype(0x13, 0, 17, 0, 94))                # addi a7, x0, 94 (__NR_exit_group)
        epi.append(0x00000073)                                  # ecall
        code_buf.extend(b"".join(le32(w) for w in epi))
        return bytes(code_buf)

    dummy_code = assemble(0)
    ro_off_raw = 176 + len(dummy_code)
    in_vaddr = base_vaddr + ro_off_raw + ((16 - (ro_off_raw % 16)) % 16)
    final_code = assemble(in_vaddr)
    assert len(final_code) == len(dummy_code)

    rodata = bytearray()
    for _, regs17, _ in cases:
        for r in regs17:
            rodata.extend(struct.pack("<Q", r & MASK64))

    elf_bytes, actual_ro, _ = build_static_elf64(243, 0x1, final_code, bytes(rodata), out_bytes_len)
    assert actual_ro == in_vaddr

    ep = os.path.join(tmpdir, "batch_rv64.elf")
    with open(ep, "wb") as f:
        f.write(elf_bytes)
    os.chmod(ep, 0o755)
    proc = subprocess.run([qemu_bin, ep], capture_output=True, timeout=60)
    if proc.returncode != 0 or len(proc.stdout) != out_bytes_len:
        raise RuntimeError(
            f"qemu-riscv64 batch failed: rc={proc.returncode} stdout={len(proc.stdout)}/{out_bytes_len} stderr={proc.stderr!r}"
        )

    out: List[List[int]] = []
    for i in range(n_cases):
        chunk = proc.stdout[i * rec_size : (i + 1) * rec_size]
        out.append(list(struct.unpack(f"<{n_regs}Q", chunk)))
    return out


# ---------------------------------------------------------------------------
# AArch64 Instruction Encoders (covering all 20 a64_inst constructors)
# ---------------------------------------------------------------------------

def a64_ret() -> int:
    return 0xD65F03C0


def a64_b(imm26_words: int) -> int:
    return (0b000101 << 26) | (imm26_words & 0x3FFFFFF)


def a64_bcond(cond: int, imm19_words: int) -> int:
    return (0b01010100 << 24) | ((imm19_words & 0x7FFFF) << 5) | (cond & 0xF)


def a64_cbz(sf: int, op: int, rt: int, imm19_words: int) -> int:
    return (sf << 31) | (0b011010 << 25) | (op << 24) | ((imm19_words & 0x7FFFF) << 5) | rt


def a64_tbz(op: int, rt: int, bit: int, imm14_words: int) -> int:
    b5 = (bit >> 5) & 1
    b40 = bit & 0x1F
    return (b5 << 31) | (0b011011 << 25) | (op << 24) | (b40 << 19) | ((imm14_words & 0x3FFF) << 5) | rt


def a64_addsub_imm(sf: int, sub: int, s: int, sh: int, imm12: int, rn: int, rd: int) -> int:
    return (sf << 31) | (sub << 30) | (s << 29) | (0b100010 << 23) | (sh << 22) | ((imm12 & 0xFFF) << 10) | (rn << 5) | rd


def a64_addsub_shift(sf: int, sub: int, s: int, sh: int, rm: int, amt: int, rn: int, rd: int) -> int:
    return (sf << 31) | (sub << 30) | (s << 29) | (0b01011 << 24) | (sh << 22) | (rm << 16) | ((amt & 0x3F) << 10) | (rn << 5) | rd


def a64_addsub_ext(sf: int, sub: int, s: int, opt: int, rm: int, amt: int, rn: int, rd: int) -> int:
    return (sf << 31) | (sub << 30) | (s << 29) | (0b01011 << 24) | (1 << 21) | (rm << 16) | ((opt & 7) << 13) | ((amt & 7) << 10) | (rn << 5) | rd


def a64_logical_imm(sf: int, opc: int, n_bit: int, immr: int, imms: int, rn: int, rd: int) -> int:
    return (sf << 31) | (opc << 29) | (0b100100 << 23) | (n_bit << 22) | ((immr & 0x3F) << 16) | ((imms & 0x3F) << 10) | (rn << 5) | rd


def a64_logical_shift(sf: int, opc: int, sh: int, n_inv: int, rm: int, amt: int, rn: int, rd: int) -> int:
    return (sf << 31) | (opc << 29) | (0b01010 << 24) | (sh << 22) | (n_inv << 21) | (rm << 16) | ((amt & 0x3F) << 10) | (rn << 5) | rd


def a64_bitfield(sf: int, opc: int, n_bit: int, immr: int, imms: int, rn: int, rd: int) -> int:
    return (sf << 31) | (opc << 29) | (0b100110 << 23) | (n_bit << 22) | ((immr & 0x3F) << 16) | ((imms & 0x3F) << 10) | (rn << 5) | rd


def a64_extr(sf: int, n_bit: int, rm: int, lsb: int, rn: int, rd: int) -> int:
    return (sf << 31) | (0b100111 << 23) | (n_bit << 22) | (rm << 16) | ((lsb & 0x3F) << 10) | (rn << 5) | rd


def a64_dp2(sf: int, op6: int, rm: int, rn: int, rd: int) -> int:
    return (sf << 31) | (0b0011010110 << 21) | (rm << 16) | ((op6 & 0x3F) << 10) | (rn << 5) | rd


def a64_madd_sub(sf: int, op31: int, rm: int, o0: int, ra: int, rn: int, rd: int) -> int:
    return (sf << 31) | (0b0011011 << 24) | ((op31 & 7) << 21) | (rm << 16) | (o0 << 15) | (ra << 10) | (rn << 5) | rd


def a64_csel(sf: int, op: int, o2: int, rm: int, cond: int, rn: int, rd: int) -> int:
    return (sf << 31) | (op << 30) | (0b11010100 << 21) | (rm << 16) | ((cond & 0xF) << 12) | (o2 << 10) | (rn << 5) | rd


def a64_ccmp(sf: int, op: int, is_imm: int, rm_or_imm5: int, cond: int, rn: int, nzcv: int) -> int:
    return (sf << 31) | (op << 30) | (0b1111010010 << 21) | ((rm_or_imm5 & 0x1F) << 16) | ((cond & 0xF) << 12) | (is_imm << 11) | (rn << 5) | (nzcv & 0xF)


# ---------------------------------------------------------------------------
# Verification & Differential Comparison Helpers
# ---------------------------------------------------------------------------

def compare_a64_batch(
    oracle: IsaOracleClient,
    qemu_bin: str,
    tmpdir: str,
    label: str,
    cases: Sequence[Tuple[str, bytes, Sequence[int], Tuple[int, int, int, int], bool]],
) -> int:
    """Run cases in batches against both qemu-aarch64 and extracted A64CoreSem."""
    batch_sz = 200
    checked = 0
    for start in range(0, len(cases), batch_sz):
        sub = cases[start : start + batch_sz]
        q_in_full = [(code, regs16, nzcv, is_ret) for _, code, regs16, nzcv, is_ret in sub]
        q_res = run_qemu_a64_batch(qemu_bin, tmpdir, q_in_full)
        # Prepare batch for Rocq runner
        cmds: List[str] = []
        for _, code, regs16, nzcv, is_ret in sub:
            rc_code = code if is_ret else (code + le32(a64_ret()))
            fuel = max(4, (len(rc_code) // 4) * 3 + 2)
            full31 = list(regs16) + [0] * 15
            n, z, c, v = nzcv
            rhex = " ".join(f"{r & MASK64:016x}" for r in full31)
            cmds.append(f"A64_EXEC {fuel} {rc_code.hex()} {n} {z} {c} {v} {rhex}")
        r_resps = oracle.query_many(cmds)
        for idx, ((desc, code, regs16, nzcv, is_ret), (q_regs, q_fl), r_resp) in enumerate(zip(sub, q_res, r_resps)):
            if not r_resp.startswith("OK "):
                raise AssertionError(
                    f"[{label}] case {start + idx} ({desc}) Rocq A64_EXEC failed: {r_resp}\n"
                    f"  code={code.hex()} init_x0_3={[hex(x) for x in regs16[:4]]} nzcv={nzcv}"
                )
            parts = r_resp.split()[1:]
            r_fl = (int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3]))
            r_regs = [int(h, 16) for h in parts[4:20]]  # x0..x15
            if r_regs != q_regs or r_fl != q_fl:
                diffs = []
                for ri in range(16):
                    if r_regs[ri] != q_regs[ri]:
                        diffs.append(f"x{ri}: rocq=0x{r_regs[ri]:016x} qemu=0x{q_regs[ri]:016x}")
                if r_fl != q_fl:
                    diffs.append(f"nzcv: rocq={r_fl} qemu={q_fl}")
                raise AssertionError(
                    f"ISA MISMATCH [{label}] case {start + idx} ({desc}):\n"
                    f"  code={code.hex()} (ret={is_ret})\n"
                    f"  init_nzcv={nzcv} init_regs={[f'x{i}=0x{v:x}' for i, v in enumerate(regs16[:6])]}\n"
                    f"  diffs: {'; '.join(diffs)}"
                )
            checked += 1
    print(f"PASS [AArch64/{label}]: {checked} cases bit-exact vs qemu-aarch64", flush=True)
    return checked


def compare_rv64_batch(
    oracle: IsaOracleClient,
    qemu_bin: str,
    tmpdir: str,
    label: str,
    cases: Sequence[Tuple[str, int, bytes, Sequence[int], bool]],
) -> int:
    """Run cases in batches against both qemu-riscv64 and extracted Rv64Sem.
    regs17 corresponds to RV64_TRACKED_REGS."""
    batch_sz = 200
    checked = 0
    rv_ret = le32(0x00008067)  # jalr x0, 0(x1)
    for start in range(0, len(cases), batch_sz):
        sub = cases[start : start + batch_sz]
        q_in = [(code, regs17, is_ret) for _, _, code, regs17, is_ret in sub]
        q_res = run_qemu_rv64_batch(qemu_bin, tmpdir, q_in)
        cmds: List[str] = []
        for _, rvc, code, regs17, is_ret in sub:
            rc_code = code if is_ret else (code + rv_ret)
            fuel = max(4, (len(rc_code) // 2) * 3 + 2)
            full32 = [0] * 32
            for idx, r in enumerate(RV64_TRACKED_REGS):
                full32[r] = regs17[idx] & MASK64
            rhex = " ".join(f"{v:016x}" for v in full32)
            cmds.append(f"RV64_EXEC {rvc} {fuel} {rc_code.hex()} {rhex}")
        r_resps = oracle.query_many(cmds)
        for idx, ((desc, rvc, code, regs17, is_ret), q_regs, r_resp) in enumerate(zip(sub, q_res, r_resps)):
            if not r_resp.startswith("OK "):
                raise AssertionError(
                    f"[{label}] case {start + idx} ({desc}) Rocq RV64_EXEC failed: {r_resp}\n"
                    f"  rvc={rvc} code={code.hex()}"
                )
            all_r_regs = [int(h, 16) for h in r_resp.split()[1:]]
            r_tracked = [all_r_regs[r] for r in RV64_TRACKED_REGS]
            if r_tracked != q_regs:
                diffs = []
                for pos, rnum in enumerate(RV64_TRACKED_REGS):
                    if r_tracked[pos] != q_regs[pos]:
                        diffs.append(f"x{rnum}: rocq=0x{r_tracked[pos]:016x} qemu=0x{q_regs[pos]:016x}")
                raise AssertionError(
                    f"ISA MISMATCH [{label}] case {start + idx} ({desc}):\n"
                    f"  rvc={rvc} code={code.hex()} (ret={is_ret})\n"
                    f"  diffs: {'; '.join(diffs)}"
                )
            checked += 1
    print(f"PASS [RV64/{label}]: {checked} cases bit-exact vs qemu-riscv64", flush=True)
    return checked


# ---------------------------------------------------------------------------
# AArch64 Test Batteries
# ---------------------------------------------------------------------------

def run_a64_decode_bitmasks_exhaustive(
    oracle: IsaOracleClient, qemu_bin: str, tmpdir: str
) -> int:
    # Check ALL 16,384 (sf, n, imms, immr) combinations!
    cmds = []
    tuples = []
    for sf in (0, 1):
        for n in (0, 1):
            for imms in range(64):
                for immr in range(64):
                    cmds.append(f"A64_BITMASK {sf} {n} {imms} {immr}")
                    tuples.append((sf, n, imms, immr))
    resps = oracle.query_many(cmds)
    valid_cases = []
    invalid_words = []
    for (sf, n, imms, immr), resp in zip(tuples, resps):
        # ORR Rd, XZR, #imm (opc=1, rn=31, rd=0)
        w = a64_logical_imm(sf, 1, n, immr, imms, 31, 0)
        if resp == "NONE":
            invalid_words.append(w)
        else:
            assert resp.startswith("OK ")
            # Verify via ORR x0/w0, xzr/wzr, #imm (plus x1=dirty upper bits)
            init = [0xDEADBEEFCAFEBABE] + [0] * 15
            valid_cases.append((f"bitmask sf={sf} n={n} imms={imms} immr={immr}", le32(w), init, (0, 0, 0, 0), False))
    # Assert all invalid bitmasks are rejected by decode_a64_word
    dec_res = oracle.a64_decode_batch(invalid_words)
    if any(dec_res):
        bad_idx = dec_res.index(True)
        raise AssertionError(f"Invalid bitmask word accepted by decoder: 0x{invalid_words[bad_idx]:08x}")
    # Execute ALL valid DecodeBitMasks encodings on QEMU (note ORR-imm with sf=0, n=1 is excluded -> invalid -> tested!)
    n_exec = compare_a64_batch(oracle, qemu_bin, tmpdir, "DecodeBitMasks-100%-ORR", valid_cases)
    print(f"PASS [AArch64/DecodeBitMasks-All]: 16384 tuples checked ({n_exec} valid executed, {len(invalid_words)} invalid rejected)")
    return 16384


def run_a64_nzcv_cond_matrix(
    oracle: IsaOracleClient, qemu_bin: str, tmpdir: str
) -> int:
    cases = []
    for nz in range(16):
        nzcv = ((nz >> 3) & 1, (nz >> 2) & 1, (nz >> 1) & 1, nz & 1)
        init = [0xAAAAAAAAAAAAAAAA, 0x1111111122222222, 0x9999999988888888] + [0] * 13
        for cond in range(16):
            for sf in (0, 1):
                for (op, o2, name) in [(0, 0, "csel"), (0, 1, "csinc"), (1, 0, "csinv"), (1, 1, "csneg")]:
                    w = a64_csel(sf, op, o2, 2, cond, 1, 0)
                    cases.append((f"{name} sf={sf} c={cond} nzcv={nzcv}", le32(w), init, nzcv, False))
                w_ccmp_r = a64_ccmp(sf, 1, 0, 2, cond, 1, nz ^ 5)
                w_ccmp_i = a64_ccmp(sf, 1, 1, 17, cond, 1, nz ^ 3)
                w_ccmn_r = a64_ccmp(sf, 0, 0, 2, cond, 1, nz ^ 9)
                w_ccmn_i = a64_ccmp(sf, 0, 1, 31, cond, 1, nz ^ 6)
                cases.append((f"ccmp_reg sf={sf} c={cond} nzcv={nzcv}", le32(w_ccmp_r), init, nzcv, False))
                cases.append((f"ccmp_imm sf={sf} c={cond} nzcv={nzcv}", le32(w_ccmp_i), init, nzcv, False))
                cases.append((f"ccmn_reg sf={sf} c={cond} nzcv={nzcv}", le32(w_ccmn_r), init, nzcv, False))
                cases.append((f"ccmn_imm sf={sf} c={cond} nzcv={nzcv}", le32(w_ccmn_i), init, nzcv, False))
            # B.cond +8; movz x0, #1; b +8; movz x0, #2
            bc_snip = le32(a64_bcond(cond, 2)) + le32(a64_movz(1, 0, 1, 0)) + le32(a64_b(2)) + le32(a64_movz(1, 0, 2, 0))
            cases.append((f"b.cond c={cond} nzcv={nzcv}", bc_snip, init, nzcv, False))
    return compare_a64_batch(oracle, qemu_bin, tmpdir, "NZCVxCond-100%-Matrix", cases)


def run_a64_constructors_and_edges(
    oracle: IsaOracleClient, qemu_bin: str, tmpdir: str
) -> int:
    cases = []
    def regs_ab(a: int, b: int, c: int = 0x5555555566666666) -> List[int]:
        return [0xCAFEBABEDEADBEEF, a & MASK64, b & MASK64, c & MASK64] + [0] * 12

    pairs = [
        (0, 0), (0, 1), (1, 0), (1, 1),
        (0x7FFFFFFF, 1), (0x80000000, 1), (0x80000000, 0xFFFFFFFF), (0xFFFFFFFF, 1),
        (0x7FFFFFFFFFFFFFFF, 1), (0x8000000000000000, 1),
        (0x8000000000000000, 0xFFFFFFFFFFFFFFFF), (0xFFFFFFFFFFFFFFFF, 1),
        (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF), (0x123456789ABCDEF0, 0x0FEDCBA987654321),
    ]
    # AddSubImm + AddSubShift + AddSubExt + XZR tests
    for a, b in pairs:
        for sf in (0, 1):
            for sub in (0, 1):
                for s in (0, 1):
                    for sh_i, imm12 in [(0, 0), (0, 1), (0, 0xFFF), (1, 0x801)]:
                        w = a64_addsub_imm(sf, sub, s, sh_i, imm12, 1, 0)
                        cases.append((f"addsub_imm sf={sf} sub={sub} s={s} sh={sh_i}", le32(w), regs_ab(a, b), (0, 1, 0, 1), False))
                    for sh in (0, 1, 2):
                        for amt in (0, 1, 31 if sf == 0 else 63):
                            w = a64_addsub_shift(sf, sub, s, sh, 2, amt, 1, 0)
                            cases.append((f"addsub_sh sf={sf} sub={sub} s={s} sh={sh} amt={amt}", le32(w), regs_ab(a, b), (1, 0, 1, 0), False))
                    for opt in range(8):
                        for amt in (0, 1, 4):
                            w = a64_addsub_ext(sf, sub, s, opt, 2, amt, 1, 0)
                            cases.append((f"addsub_ext sf={sf} sub={sub} s={s} opt={opt} amt={amt}", le32(w), regs_ab(a, b), (0, 0, 1, 1), False))
            # XZR checks on non-SP instructions (sets flags or logical shift)
            w_xzr = a64_addsub_shift(sf, 1, 1, 0, 2, 0, 1, 31)  # cmp x1, x2
            cases.append((f"cmp_xzr sf={sf}", le32(w_xzr), regs_ab(a, b), (0, 0, 0, 0), False))
            w_rd31_imm = a64_addsub_imm(sf, 0, 1, 0, 1, 1, 31)  # cmn imm (rd=xzr)
            cases.append((f"cmn_imm sf={sf}", le32(w_rd31_imm), regs_ab(a, b), (0, 0, 0, 0), False))

    # LogicalShift (all opc, n_inv, sh, amt)
    for sf in (0, 1):
        max_a = 31 if sf == 0 else 63
        for opc in (0, 1, 2, 3):
            for n_inv in (0, 1):
                for sh in (0, 1, 2, 3):
                    for amt in (0, 1, 17, max_a):
                        w = a64_logical_shift(sf, opc, sh, n_inv, 2, amt, 1, 0)
                        cases.append((f"log_sh sf={sf} opc={opc} inv={n_inv} sh={sh} amt={amt}", le32(w), regs_ab(0xF0F000FF80000001, 0x80000000FFFFFFFF), (1, 1, 1, 1), False))

    # MoveWide (MOVN, MOVZ, MOVK)
    for sf in (0, 1):
        hws = (0, 1) if sf == 0 else (0, 1, 2, 3)
        for hw in hws:
            for imm16 in (0, 1, 0x8000, 0xFFFF):
                for fn in (a64_movn, a64_movz, a64_movk):
                    w = fn(sf, 0, imm16, hw)
                    cases.append((f"movw sf={sf} hw={hw} imm={imm16:x}", le32(w), regs_ab(0, 0), (0, 0, 0, 0), False))

    # Bitfield (SBFM, BFM, UBFM) & EXTR
    for sf in (0, 1):
        wb = 32 if sf == 0 else 64
        bf_pairs = [(0, 0), (0, 7), (0, wb - 1), (1, 1), (1, wb - 1), (7, 3), (wb - 1, 0), (wb - 1, wb - 1), (16, 15)]
        for immr, imms in bf_pairs:
            for opc in (0, 1, 2):
                w = a64_bitfield(sf, opc, sf, immr, imms, 1, 0)
                cases.append((f"bfm opc={opc} sf={sf} r={immr} s={imms}", le32(w), regs_ab(0xFEDCBA9876543210, 0), (0, 0, 0, 0), False))
        for lsb in (0, 1, 15, 31, wb - 1):
            cases.append((f"extr sf={sf} lsb={lsb}", le32(a64_extr(sf, sf, 2, lsb, 1, 0)), regs_ab(0x1122334455667788, 0x99AABBCCDDEEFF01), (0, 0, 0, 0), False))
            cases.append((f"extr_same sf={sf} lsb={lsb}", le32(a64_extr(sf, sf, 1, lsb, 1, 0)), regs_ab(0x1122334455667788, 0), (0, 0, 0, 0), False))

    # MADD / MSUB / SMADDL / SMSUBL / UMADDL / UMSUBL / UDIV / SDIV / LSLV / LSRV / ASRV / RORV
    for a, b in pairs:
        for sf in (0, 1):
            for o0 in (0, 1):
                cases.append((f"madd_sub sf={sf} o0={o0}", le32(a64_madd_sub(sf, 0, 2, o0, 3, 1, 0)), regs_ab(a, b, 0x123456789ABCDEF1), (0, 0, 0, 0), False))
            for op6 in (2, 3, 8, 9, 10, 11):
                cases.append((f"dp2 sf={sf} op={op6}", le32(a64_dp2(sf, op6, 2, 1, 0)), regs_ab(a, b), (0, 0, 0, 0), False))
        for op31 in (1, 5):
            for o0 in (0, 1):
                cases.append((f"mulw op31={op31} o0={o0}", le32(a64_madd_sub(1, op31, 2, o0, 3, 1, 0)), regs_ab(a, b, 0x100000002), (0, 0, 0, 0), False))

    # Branches: CBZ/CBNZ (sf=0 dirty upper bits!), TBZ/TBNZ (all bit groups), B, Ret
    for sf in (0, 1):
        for tv in (0, 1, 0xFFFFFFFF00000000, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF):
            for op in (0, 1):
                snip = le32(a64_cbz(sf, op, 1, 2)) + le32(a64_movz(1, 0, 0x11, 0)) + le32(a64_b(2)) + le32(a64_movz(1, 0, 0x22, 0))
                cases.append((f"cbz sf={sf} op={op} x1={tv:x}", snip, regs_ab(tv, 0), (0, 0, 0, 0), False))
    for bit in (0, 1, 15, 31, 32, 62, 63):
        for tv in (0, 1 << bit, MASK64 ^ (1 << bit)):
            for op in (0, 1):
                snip = le32(a64_tbz(op, 1, bit, 2)) + le32(a64_movz(1, 0, 0x33, 0)) + le32(a64_b(2)) + le32(a64_movz(1, 0, 0x44, 0))
                cases.append((f"tbz bit={bit} op={op}", snip, regs_ab(tv, 0), (0, 0, 0, 0), False))
    # NOP + RET
    ret_snip = le32(0xD503201F) + le32(a64_addsub_imm(1, 0, 0, 0, 77, 1, 0)) + le32(a64_ret())
    cases.append(("nop_add_ret", ret_snip, regs_ab(100, 0), (0, 0, 0, 0), True))

    # Reject SP (r=31 where hardware reads/writes SP instead of XZR); allow XZR on S=1/TST
    sp_checks = [
        (a64_addsub_imm(1, 0, 0, 0, 16, 31, 0), False),  # add x0, sp, #16
        (a64_addsub_imm(1, 1, 0, 0, 16, 1, 31), False),  # sub sp, x1, #16
        (a64_addsub_ext(1, 0, 0, 3, 2, 0, 31, 0), False),# add x0, sp, w2, uxtw
        (a64_addsub_ext(1, 0, 0, 3, 2, 0, 1, 31), False),# add sp, x1, w2, uxtw
        (a64_logical_imm(1, 1, 1, 0, 0, 1, 31), False),  # orr sp, x1, #1
        (a64_addsub_imm(1, 1, 1, 0, 16, 31, 0), False),  # cmp sp, #16
        (a64_addsub_imm(1, 1, 1, 0, 16, 1, 31), True),   # cmp x1, #16 (rd=xzr)
        (a64_logical_imm(1, 3, 1, 0, 0, 1, 31), True),   # tst x1, #1 (rd=xzr)
    ]
    sp_dec = oracle.a64_decode_batch([w for w, _ in sp_checks])
    for (w, want), got in zip(sp_checks, sp_dec):
        if got != want:
            raise AssertionError(f"A64 SP/XZR decode mismatch for 0x{w:08x}: expected {want}, got {got}")

    return compare_a64_batch(oracle, qemu_bin, tmpdir, "All-20-Constructors-Edges", cases)


def rand_val64(rng: random.Random) -> int:
    choice = rng.randrange(5)
    if choice == 0:
        return rng.choice(EDGE_VALS_64)
    if choice == 1:
        return rng.getrandbits(32) | (rng.getrandbits(32) << 32)
    if choice == 2:
        return (rng.getrandbits(32) & MASK32) | ((rng.choice(EDGE_VALS_64) & MASK32) << 32)
    return rng.getrandbits(64)


def run_a64_random_diff_fuzz(
    oracle: IsaOracleClient, qemu_bin: str, tmpdir: str, count: int, seed: int = 20260401
) -> int:
    rng = random.Random(seed)
    # Precompute valid bitmasks split by sf
    valid_bm = {0: [], 1: []}
    cmds = []
    b_meta = []
    for sf in (0, 1):
        for n in (0, 1):
            if sf == 0 and n == 1:
                continue
            for imms in range(64):
                for immr in range(64):
                    cmds.append(f"A64_BITMASK {sf} {n} {imms} {immr}")
                    b_meta.append((sf, n, imms, immr))
    for meta, resp in zip(b_meta, oracle.query_many(cmds)):
        if resp.startswith("OK "):
            valid_bm[meta[0]].append(meta)

    cases = []
    for i in range(count):
        seq_len = rng.choice([1, 1, 2, 3, 4])
        code = bytearray()
        for _ in range(seq_len):
            kind = rng.randrange(11)
            sf = rng.randrange(2)
            rd = rng.randrange(16)
            rn = rng.randrange(16)
            rm = rng.randrange(16)
            ra = rng.randrange(16)
            wb = 32 if sf == 0 else 64
            if kind == 0:
                w = a64_addsub_imm(sf, rng.randrange(2), rng.randrange(2), rng.randrange(2), rng.randrange(4096), rn, rd)
            elif kind == 1:
                w = a64_addsub_shift(sf, rng.randrange(2), rng.randrange(2), rng.randrange(3), rm, rng.randrange(wb), rn, rd)
            elif kind == 2:
                w = a64_addsub_ext(sf, rng.randrange(2), rng.randrange(2), rng.randrange(8), rm, rng.randrange(5), rn, rd)
            elif kind == 3:
                _, n_b, imms, immr = rng.choice(valid_bm[sf])
                # Note: opc=0,1,2 with rd=31 is SP; rd is 0..15 here so safe
                w = a64_logical_imm(sf, rng.randrange(4), n_b, immr, imms, rn, rd)
            elif kind == 4:
                w = a64_logical_shift(sf, rng.randrange(4), rng.randrange(4), rng.randrange(2), rm, rng.randrange(wb), rn, rd)
            elif kind == 5:
                hw = rng.randrange(2 if sf == 0 else 4)
                fn = rng.choice([a64_movn, a64_movz, a64_movk])
                w = fn(sf, rd, rng.getrandbits(16), hw)
            elif kind == 6:
                w = a64_bitfield(sf, rng.randrange(3), sf, rng.randrange(wb), rng.randrange(wb), rn, rd)
            elif kind == 7:
                w = a64_extr(sf, sf, rm, rng.randrange(wb), rn, rd)
            elif kind == 8:
                op6 = rng.choice([2, 3, 8, 9, 10, 11])
                w = a64_dp2(sf, op6, rm, rn, rd)
            elif kind == 9:
                if sf == 1 and rng.randrange(2) == 0:
                    op31 = rng.choice([1, 5])
                else:
                    op31 = 0
                w = a64_madd_sub(sf, op31, rm, rng.randrange(2), ra, rn, rd)
            else:
                if rng.randrange(2) == 0:
                    w = a64_csel(sf, rng.randrange(2), rng.randrange(2), rm, rng.randrange(16), rn, rd)
                else:
                    w = a64_ccmp(sf, rng.randrange(2), rng.randrange(2), rm, rng.randrange(16), rn, rng.randrange(16))
            code.extend(le32(w))
        init = [rand_val64(rng) for _ in range(16)]
        nzcv = (rng.randrange(2), rng.randrange(2), rng.randrange(2), rng.randrange(2))
        cases.append((f"fuzz#{i}", bytes(code), init, nzcv, False))
    return compare_a64_batch(oracle, qemu_bin, tmpdir, f"RandomDiffFuzz-{count}", cases)


def run_a64_decoder_fuzz(
    oracle: IsaOracleClient, qemu_bin: str, objdump_bin: Optional[str], tmpdir: str, count: int, seed: int = 8301
) -> Tuple[int, int]:
    rng = random.Random(seed)
    words = [rng.getrandbits(32) for _ in range(count)]
    # Mix in random words biased to 0..15/31 registers & interesting opcode top bits
    for _ in range(min(5000, count // 5)):
        w = rng.getrandbits(32)
        # Clear bit 4,9,20? Keep realistic distribution + bitflips of valid opcodes
        w = (w & ~0x001F03FF) | (rng.randrange(16)) | (rng.randrange(16) << 5)
        words.append(w)

    acc_flags = oracle.a64_decode_batch(words)
    accepted = [w for w, ok in zip(words, acc_flags) if ok]
    if not accepted:
        raise AssertionError("No accepted words found during A64 decoder fuzz")

    # 1. Verify EVERY accepted word with llvm-objdump (zero <unknown>/udf/.word/.inst)
    if objdump_bin:
        blob = b"".join(le32(w) for w in accepted)
        elf_bytes, _, _ = build_static_elf64(183, 0, blob, b"", 0x1000)
        ep = os.path.join(tmpdir, "dec_a64.elf")
        with open(ep, "wb") as f:
            f.write(elf_bytes)
        stop_addr = 0x4000B0 + len(blob)
        res = subprocess.run([objdump_bin, "-d", "--start-address=0x4000b0", f"--stop-address=0x{stop_addr:x}", ep], text=True, capture_output=True)
        if res.returncode != 0:
            raise RuntimeError(f"llvm-objdump failed on A64 decoder fuzz ELF: {res.stderr}")
        bad_lines = []
        for ln in res.stdout.splitlines():
            lo = ln.lower()
            if re.search(r"^\s*[0-9a-f]+:\s+[0-9a-f]{8}\s+", lo):
                if any(tok in lo for tok in ("<unknown>", ".word", ".inst", "\tudf")):
                    bad_lines.append(ln.strip())
        if bad_lines:
            raise AssertionError(f"A64 decoder false-accept detected by llvm-objdump ({len(bad_lines)}):\n" + "\n".join(bad_lines[:10]))

    # 2. Execute accepted non-control-flow instructions whose register fields fall in x0..x15 / x31 on QEMU
    exec_cases = []
    for w in accepted:
        top6 = (w >> 26) & 0x3F
        op24_8 = (w >> 24) & 0xFF
        op25_6 = (w >> 25) & 0x3F
        # Skip branches & ret (PC-relative / link-reg control flow) and system hints
        if top6 == 5 or (op24_8 == 84 and ((w >> 4) & 1) == 0) or op25_6 in (26, 27):
            continue
        if ((w >> 10) & 0x3FFFFF) == 3512256:  # ret
            continue
        rd, rn, rm, ra = w & 31, (w >> 5) & 31, (w >> 16) & 31, (w >> 10) & 31
        # Mask non-31 register slots cleanly to 0..15 by rebuilding safe subset OR test if safe
        op24_5 = (w >> 24) & 0x1F
        uses_rm = op24_5 in (10, 11, 27) or ((w >> 21) & 0xFF) in (210, 212, 214) or ((w >> 23) & 0x3F) == 39
        uses_ra = op24_5 == 27
        if (rd >= 16 and rd != 31) or (rn >= 16 and rn != 31):
            continue
        if uses_rm and rm >= 16 and rm != 31:
            continue
        if uses_ra and ra >= 16 and ra != 31:
            continue
        init = [rand_val64(rng) for _ in range(16)]
        nzcv = (rng.randrange(2), rng.randrange(2), rng.randrange(2), rng.randrange(2))
        exec_cases.append((f"dec_fuzz_0x{w:08x}", le32(w), init, nzcv, False))
        if len(exec_cases) >= 2000:
            break

    n_exec = compare_a64_batch(oracle, qemu_bin, tmpdir, "DecoderFuzzExec", exec_cases) if exec_cases else 0
    print(f"PASS [AArch64/DecoderFuzz]: {len(words)} words tested, {len(accepted)} accepted (0 unallocated), {n_exec} executed vs QEMU")
    return len(words), len(accepted)


# ---------------------------------------------------------------------------
# RISC-V64 Test Batteries
# ---------------------------------------------------------------------------

def rv_jtype(opcode: int, rd: int, off: int) -> int:
    u = off & 0x1FFFFF
    imm20 = (((u >> 20) & 1) << 19) | (((u >> 1) & 0x3FF) << 9) | (((u >> 11) & 1) << 8) | ((u >> 12) & 0xFF)
    return (imm20 << 12) | (rd << 7) | opcode


def rv_btype(funct3: int, rs1: int, rs2: int, off: int) -> int:
    u = off & 0x1FFF
    return (
        (((u >> 12) & 1) << 31)
        | (((u >> 5) & 0x3F) << 25)
        | (rs2 << 20)
        | (rs1 << 15)
        | (funct3 << 12)
        | (((u >> 1) & 0xF) << 8)
        | (((u >> 11) & 1) << 7)
        | 0x63
    )


def run_rv64_constructors_and_edges(
    oracle: IsaOracleClient, qemu_bin: str, tmpdir: str
) -> int:
    cases = []
    # RV64_TRACKED_REGS = [5..17, 28..31]; a0=x10 (idx 5), a1=x11 (idx 6), a2=x12 (idx 7)
    def mk_regs(a0: int, a1: int = 0, a2: int = 0) -> List[int]:
        out = [0] * len(RV64_TRACKED_REGS)
        out[RV64_TRACKED_REGS.index(10)] = a0 & MASK64
        out[RV64_TRACKED_REGS.index(11)] = a1 & MASK64
        out[RV64_TRACKED_REGS.index(12)] = a2 & MASK64
        return out

    # LUI
    for imm20 in (0, 1, 0x7FFFF, 0x80000, 0xFFFFF):
        cases.append((f"lui 0x{imm20:x}", 0, le32(rv_lui(10, imm20)), mk_regs(0), False))
        cases.append((f"lui x0 0x{imm20:x}", 0, le32(rv_lui(0, imm20)), mk_regs(0x123), False))

    # OP-IMM & OP-IMM-32
    for v in (0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0x123456789ABCDEF0):
        for f3 in (0, 2, 3, 4, 6, 7):
            for imm12 in (0, 1, 0x7FF, 0x800, 0xFFF):
                cases.append((f"opimm f3={f3} imm={imm12}", 0, le32(rv_itype(0x13, f3, 10, 11, imm12)), mk_regs(0, v), False))
        for sh6 in (0, 1, 31, 32, 63):
            cases.append((f"slli {sh6}", 0, le32(rv_itype(0x13, 1, 10, 11, sh6)), mk_regs(0, v), False))
            cases.append((f"srli {sh6}", 0, le32(rv_itype(0x13, 5, 10, 11, sh6)), mk_regs(0, v), False))
            cases.append((f"srai {sh6}", 0, le32(rv_itype(0x13, 5, 10, 11, (16 << 6) | sh6)), mk_regs(0, v), False))
        for imm12 in (0, 1, 0x7FF, 0x800, 0xFFF):
            cases.append((f"addiw imm={imm12}", 0, le32(rv_itype(0x1B, 0, 10, 11, imm12)), mk_regs(0, v), False))
        for sh5 in (0, 1, 17, 31):
            cases.append((f"slliw {sh5}", 0, le32(rv_itype(0x1B, 1, 10, 11, sh5)), mk_regs(0, v), False))
            cases.append((f"srliw {sh5}", 0, le32(rv_itype(0x1B, 5, 10, 11, sh5)), mk_regs(0, v), False))
            cases.append((f"sraiw {sh5}", 0, le32(rv_itype(0x1B, 5, 10, 11, (32 << 5) | sh5)), mk_regs(0, v), False))

    # OP & OP-32 (I + M extensions including div/rem by 0 and INT_MIN / -1)
    op_pairs = [
        (0, 0), (1, 0), (0, 1), (-1, -1), (0x8000000000000000, -1),
        (0x80000000, 0xFFFFFFFF), (0x1000000080000000, 0x20000000FFFFFFFF),
        (0x7FFFFFFFFFFFFFFF, 0x8000000000000001), (0x123456789ABCDEF0, 0xFEDCBA9876543210),
    ]
    for a, b in op_pairs:
        for f7, f3 in [(0, f) for f in range(8)] + [(32, 0), (32, 5)] + [(1, f) for f in range(8)]:
            cases.append((f"op f7={f7} f3={f3}", 0, le32(rv_rtype(0x33, f7, f3, 10, 11, 12)), mk_regs(0, a, b), False))
        for f7, f3 in [(0, 0), (0, 1), (0, 5), (32, 0), (32, 5), (1, 0), (1, 4), (1, 5), (1, 6), (1, 7)]:
            cases.append((f"op32 f7={f7} f3={f3}", 0, le32(rv_rtype(0x3B, f7, f3, 10, 11, 12)), mk_regs(0, a, b), False))

    # BRANCH (all 6 funct3) & JAL x0
    for f3 in (0, 1, 4, 5, 6, 7):
        for a, b in [(5, 5), (5, 7), (-5, 7), (0x8000000000000000, 1)]:
            snip = le32(rv_btype(f3, 11, 12, 12)) + le32(rv_itype(0x13, 0, 10, 0, 11)) + le32(rv_jtype(0x6F, 0, 8)) + le32(rv_itype(0x13, 0, 10, 0, 22))
            cases.append((f"br f3={f3}", 0, snip, mk_regs(0, a, b), False))

    # RVC 16-bit instructions: c.nop, c.addi, c.addiw, c.li, c.lui, c.srli, c.srai, c.andi, c.sub, c.xor, c.or, c.and, c.subw, c.addw, c.slli, c.mv, c.add, c.beqz, c.bnez, c.j, c.ret
    def rvc_ci(f3: int, rd: int, imm6: int, op: int = 1) -> int:
        return (f3 << 13) | (((imm6 >> 5) & 1) << 12) | (rd << 7) | ((imm6 & 0x1F) << 2) | op
    rvc_snips = [
        ("c.nop", le16(0x0001), mk_regs(42)),
        ("c.addi a0, -5", le16(rvc_ci(0, 10, 0x3B, 1)), mk_regs(100)),
        ("c.addiw a0, 12", le16(rvc_ci(1, 10, 12, 1)), mk_regs(0xFFFFFFFF)),
        ("c.li a0, -1", le16(rvc_ci(2, 10, 0x3F, 1)), mk_regs(123)),
        ("c.lui a0, 0x20", le16(rvc_ci(3, 10, 0x20, 1)), mk_regs(0)),
        ("c.srli a0, 5", le16((4 << 13) | (0 << 12) | (0 << 10) | (2 << 7) | (5 << 2) | 1), mk_regs(0x8000000000000040)),
        ("c.srai a0, 5", le16((4 << 13) | (1 << 12) | (1 << 10) | (2 << 7) | (5 << 2) | 1), mk_regs(0x8000000000000040)),
        ("c.andi a0, -2", le16((4 << 13) | (1 << 12) | (2 << 10) | (2 << 7) | (0x1E << 2) | 1), mk_regs(0xFFFFFFFF)),
        ("c.sub a0, a1", le16((4 << 13) | (0 << 12) | (3 << 10) | (2 << 7) | (0 << 5) | (3 << 2) | 1), mk_regs(10, 3)),
        ("c.xor a0, a1", le16((4 << 13) | (0 << 12) | (3 << 10) | (2 << 7) | (1 << 5) | (3 << 2) | 1), mk_regs(0xAA, 0x55)),
        ("c.or a0, a1", le16((4 << 13) | (0 << 12) | (3 << 10) | (2 << 7) | (2 << 5) | (3 << 2) | 1), mk_regs(0xA0, 0x05)),
        ("c.and a0, a1", le16((4 << 13) | (0 << 12) | (3 << 10) | (2 << 7) | (3 << 5) | (3 << 2) | 1), mk_regs(0xFF, 0x0F)),
        ("c.subw a0, a1", le16((4 << 13) | (1 << 12) | (3 << 10) | (2 << 7) | (0 << 5) | (3 << 2) | 1), mk_regs(0x100000000, 1)),
        ("c.addw a0, a1", le16((4 << 13) | (1 << 12) | (3 << 10) | (2 << 7) | (1 << 5) | (3 << 2) | 1), mk_regs(0x7FFFFFFF, 1)),
        ("c.slli a0, 33", le16(rvc_ci(0, 10, 33, 2)), mk_regs(1)),
        ("c.mv a0, a1", le16((4 << 13) | (0 << 12) | (10 << 7) | (11 << 2) | 2), mk_regs(0, 0x999)),
        ("c.add a0, a1", le16((4 << 13) | (1 << 12) | (10 << 7) | (11 << 2) | 2), mk_regs(100, 200)),
    ]
    for nm, bcode, regs in rvc_snips:
        cases.append((nm, 1, bcode, regs, False))
    # c.beqz a0, +4; c.li a0, 1; c.j +4; c.li a0, 2 (note c.j +4 -> bit4=1 => 0xA011)
    cases.append(("c.j_pair", 1, le16(0xA011) + le16(rvc_ci(2, 10, 9, 1)) + le16(rvc_ci(2, 10, 5, 1)), mk_regs(0), False))
    cases.append(("c.beqz_taken", 1, le16(0xC111) + le16(rvc_ci(2, 10, 9, 1)) + le16(0xA011) + le16(rvc_ci(2, 10, 5, 1)), mk_regs(0), False))
    cases.append(("c.beqz_not", 1, le16(0xC111) + le16(rvc_ci(2, 10, 9, 1)) + le16(0xA011) + le16(rvc_ci(2, 10, 5, 1)), mk_regs(1), False))
    cases.append(("c.ret", 1, le16(rvc_ci(2, 10, 19, 1)) + le16(0x8082), mk_regs(0), True))

    return compare_rv64_batch(oracle, qemu_bin, tmpdir, "RV64-All-Constructors-Edges", cases)


def run_rv64_random_diff_fuzz(
    oracle: IsaOracleClient, qemu_bin: str, tmpdir: str, count: int, seed: int = 99100
) -> int:
    rng = random.Random(seed)
    cases = []
    for i in range(count):
        seq_len = rng.choice([1, 1, 2, 3, 4])
        rvc = 1 if rng.randrange(3) == 0 else 0
        code = bytearray()
        for _ in range(seq_len):
            rd = rng.choice(RV64_TRACKED_REGS)
            rs1 = rng.choice(RV64_TRACKED_REGS)
            rs2 = rng.choice(RV64_TRACKED_REGS)
            if rvc == 1 and rng.randrange(2) == 0:
                rdp = rng.randrange(8)
                rs2p = rng.randrange(8)
                c_kind = rng.randrange(6)
                if c_kind == 0:
                    code.extend(le16((0 << 13) | (((rng.randrange(64) >> 5) & 1) << 12) | (rd << 7) | ((rng.randrange(32)) << 2) | 1))
                elif c_kind == 1:
                    code.extend(le16((1 << 13) | (((rng.randrange(64) >> 5) & 1) << 12) | (rd << 7) | ((rng.randrange(32)) << 2) | 1))
                elif c_kind == 2:
                    code.extend(le16((2 << 13) | (((rng.randrange(64) >> 5) & 1) << 12) | (rd << 7) | ((rng.randrange(32)) << 2) | 1))
                elif c_kind == 3:
                    code.extend(le16((4 << 13) | (rng.randrange(2) << 12) | (rng.randrange(3) << 10) | (rdp << 7) | (rng.randrange(32) << 2) | 1))
                elif c_kind == 4:
                    b12 = rng.randrange(2)
                    subop = rng.randrange(4 if b12 == 0 else 2)
                    code.extend(le16((4 << 13) | (b12 << 12) | (3 << 10) | (rdp << 7) | (subop << 5) | (rs2p << 2) | 1))
                else:
                    code.extend(le16((4 << 13) | (rng.randrange(2) << 12) | (rd << 7) | (rs2 << 2) | 2))
            else:
                k = rng.randrange(5)
                if k == 0:
                    w = rv_lui(rd, rng.getrandbits(20))
                elif k == 1:
                    f3 = rng.choice([0, 2, 3, 4, 6, 7])
                    w = rv_itype(0x13, f3, rd, rs1, rng.getrandbits(12))
                elif k == 2:
                    sh = rng.randrange(64)
                    f3, top = rng.choice([(1, 0), (5, 0), (5, 16)])
                    w = rv_itype(0x13, f3, rd, rs1, (top << 6) | sh)
                elif k == 3:
                    w = rv_itype(0x1B, 0, rd, rs1, rng.getrandbits(12))
                else:
                    f7, f3 = rng.choice(
                        [(0, f) for f in range(8)] + [(32, 0), (32, 5)] + [(1, f) for f in range(8)]
                    )
                    opc = 0x33 if rng.randrange(2) == 0 else 0x3B
                    if opc == 0x3B and (f7, f3) not in [(0, 0), (0, 1), (0, 5), (32, 0), (32, 5), (1, 0), (1, 4), (1, 5), (1, 6), (1, 7)]:
                        f7, f3 = 0, 0
                    w = rv_rtype(opc, f7, f3, rd, rs1, rs2)
                code.extend(le32(w))
        init = [rand_val64(rng) for _ in RV64_TRACKED_REGS]
        cases.append((f"rv_fuzz#{i}", rvc, bytes(code), init, False))
    return compare_rv64_batch(oracle, qemu_bin, tmpdir, f"RV64-RandomDiffFuzz-{count}", cases)


def run_rv64_decoder_fuzz(
    oracle: IsaOracleClient, qemu_bin: str, objdump_bin: Optional[str], tmpdir: str, count: int, seed: int = 8401
) -> Tuple[int, int]:
    rng = random.Random(seed)
    w32 = [rng.getrandbits(32) for _ in range(count // 2)]
    w16 = [rng.getrandbits(16) for _ in range(count // 2)]
    c32 = [le32(w) for w in w32]
    c16 = [le16(h) for h in w16]

    acc32 = [c for c, ok in zip(c32, oracle.rv64_decode_batch(0, c32)) if ok]
    acc16 = [c for c, ok in zip(c16, oracle.rv64_decode_batch(1, c16)) if ok]

    if objdump_bin:
        for tag, acc, e_flags in [("rv32", acc32, 0), ("rv16", acc16, 1)]:
            if not acc:
                continue
            blob = b"".join(acc)
            elf_bytes, _, _ = build_static_elf64(243, e_flags, blob, b"", 0x1000)
            ep = os.path.join(tmpdir, f"dec_{tag}.elf")
            with open(ep, "wb") as f:
                f.write(elf_bytes)
            stop_addr = 0x4000B0 + len(blob)
            res = subprocess.run([objdump_bin, "-d", "--mattr=+m,+c", "--start-address=0x4000b0", f"--stop-address=0x{stop_addr:x}", ep], text=True, capture_output=True)
            if res.returncode != 0:
                raise RuntimeError(f"llvm-objdump failed on RV64 {tag} decoder fuzz ELF: {res.stderr}")
            bad = []
            for ln in res.stdout.splitlines():
                lo = ln.lower()
                if re.search(r"^\s*[0-9a-f]+:\s+[0-9a-f]+\s+", lo):
                    if any(tok in lo for tok in ("<unknown>", ".word", ".4byte", ".2byte", "unimp")):
                        bad.append(ln.strip())
            if bad:
                raise AssertionError(f"RV64 {tag} decoder false-accept via llvm-objdump ({len(bad)}):\n" + "\n".join(bad[:10]))

    # Execute safe subset on QEMU
    tracked_set = set(RV64_TRACKED_REGS) | {0}
    exec_cases = []
    for c in acc32:
        w = struct.unpack("<I", c)[0]
        opc = w & 0x7F
        if opc in (0x63, 0x6F, 0x67):  # branches / jal / jalr
            continue
        rd, rs1, rs2 = (w >> 7) & 31, (w >> 15) & 31, (w >> 20) & 31
        if rd not in tracked_set:
            continue
        if opc != 0x37 and rs1 not in tracked_set:
            continue
        if opc in (0x33, 0x3B) and rs2 not in tracked_set:
            continue
        init = [rand_val64(rng) for _ in RV64_TRACKED_REGS]
        exec_cases.append((f"rv32_dec_0x{w:08x}", 0, c, init, False))
        if len(exec_cases) >= 1000:
            break
    n_ex = compare_rv64_batch(oracle, qemu_bin, tmpdir, "RV64-DecoderFuzzExec", exec_cases) if exec_cases else 0
    total = len(w32) + len(w16)
    print(f"PASS [RV64/DecoderFuzz]: {total} words tested ({len(acc32)} RV32 + {len(acc16)} RVC accepted, 0 unallocated), {n_ex} executed vs QEMU")
    return total, len(acc32) + len(acc16)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--a64-fuzz", type=int, default=10000, help="Random valid A64 sequences (default 10000)")
    parser.add_argument("--a64-decode-fuzz", type=int, default=50000, help="Random raw 32-bit A64 words (default 50000)")
    parser.add_argument("--rv64-fuzz", type=int, default=5000, help="Random valid RV64/RVC sequences (default 5000)")
    parser.add_argument("--rv64-decode-fuzz", type=int, default=50000, help="Random raw 16/32-bit RV64 words (default 50000)")
    parser.add_argument("--runner", default="", help="Optional pre-built isa_oracle_runner binary path")
    ns = parser.parse_args(argv)

    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    qemu_a64 = find_tool(["qemu-aarch64", "qemu-aarch64-static"])
    qemu_rv64 = find_tool(["qemu-riscv64", "qemu-riscv64-static"])
    objdump = find_tool(["llvm-objdump-22", "llvm-objdump", "/usr/lib/llvm-22/bin/llvm-objdump"])
    if not qemu_a64 or not qemu_rv64:
        print(f"error: missing QEMU binaries (qemu-aarch64={qemu_a64}, qemu-riscv64={qemu_rv64})", file=sys.stderr)
        return 2

    t0 = time.time()
    with tempfile.TemporaryDirectory(prefix="isa_oracle_") as tmpdir:
        runner_bin = ns.runner if ns.runner else build_runner(repo_root, tmpdir)
        oracle = IsaOracleClient(runner_bin)
        try:
            a64_bm = run_a64_decode_bitmasks_exhaustive(oracle, qemu_a64, tmpdir)
            a64_nzcv = run_a64_nzcv_cond_matrix(oracle, qemu_a64, tmpdir)
            a64_edges = run_a64_constructors_and_edges(oracle, qemu_a64, tmpdir)
            a64_fuzz = run_a64_random_diff_fuzz(oracle, qemu_a64, tmpdir, ns.a64_fuzz)
            a64_dec, _ = run_a64_decoder_fuzz(oracle, qemu_a64, objdump, tmpdir, ns.a64_decode_fuzz)

            rv_edges = run_rv64_constructors_and_edges(oracle, qemu_rv64, tmpdir)
            rv_fuzz = run_rv64_random_diff_fuzz(oracle, qemu_rv64, tmpdir, ns.rv64_fuzz)
            rv_dec, _ = run_rv64_decoder_fuzz(oracle, qemu_rv64, objdump, tmpdir, ns.rv64_decode_fuzz)
        finally:
            oracle.close()

    dt = time.time() - t0
    print(
        f"ISA ORACLE SUITE OK ({dt:.2f}s): "
        f"A64(bitmasks={a64_bm}, nzcv_cond={a64_nzcv}, edges={a64_edges}, fuzz={a64_fuzz}, dec={a64_dec}) "
        f"RV64(edges={rv_edges}, fuzz={rv_fuzz}, dec={rv_dec})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
