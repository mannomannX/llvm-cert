/* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
 * Licensed under the LLVMCert Non-Commercial Evaluation & Research License
 * or a separate LLVMCert Commercial Software License Agreement.
 * See /LICENSE in the repository root for details. */

#ifndef CERT_RUNTIME_H
#define CERT_RUNTIME_H

#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

#if defined(__cplusplus)
#define CERT_RUNTIME_RESTRICT
#elif defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901L)
#define CERT_RUNTIME_RESTRICT restrict
#else
#define CERT_RUNTIME_RESTRICT
#endif

/* Portable little-endian two-limb 128-bit unsigned integer matching AAPCS64 (x0, x1)
 * and RISC-V64 LP64 (a0, a1) register-pair layout. */
typedef struct cert_u128 {
  uint64_t low;
  uint64_t high;
} cert_u128_t;

/* Portable little-endian two's-complement two-limb 128-bit signed integer.
 * Stored as unsigned 64-bit limbs (bit 63 of `high` is the sign bit) so all arithmetic
 * executes without C11 signed-overflow or signed-shift undefined behavior (CERT C INT32-C). */
typedef struct cert_i128 {
  uint64_t low;
  uint64_t high;
} cert_i128_t;

/* Freestanding deterministic memory primitives.
 * - Zero-length (`count == 0U`) operations return immediately without dereferencing pointers.
 * - `cert_memmove` compares addresses in `uintptr_t` domain (CERT C ARR36-C).
 * - `cert_memcmp` compares bytes strictly as `unsigned char` (C11 7.24.4.1).
 * - `cert_memzero_explicit` writes through `volatile unsigned char *` (CERT C MSC06-C). */
void *cert_memcpy(void *CERT_RUNTIME_RESTRICT dst, const void *CERT_RUNTIME_RESTRICT src,
                  size_t count);
void *cert_memmove(void *dst, const void *src, size_t count);
void *cert_memset(void *dst, int byte_value, size_t count);
int cert_memcmp(const void *lhs, const void *rhs, size_t count);
void *cert_memzero_explicit(void *dst, size_t count);

/* Portable 128-bit bitwise, shift, additive, multiplicative, and bit-count primitives.
 * Shift counts >= 128 deterministically saturate (`0` for `shl`/`lshr`; sign fill for `ashr`).
 * `cert_u128_clz` and `cert_u128_ctz` deterministically return `128U` when `value == 0`. */
cert_u128_t cert_u128_add(cert_u128_t lhs, cert_u128_t rhs);
cert_u128_t cert_u128_sub(cert_u128_t lhs, cert_u128_t rhs);
cert_u128_t cert_u128_neg(cert_u128_t value);
int cert_u128_cmp(cert_u128_t lhs, cert_u128_t rhs);
int cert_i128_cmp(cert_i128_t lhs, cert_i128_t rhs);

cert_u128_t cert_u128_shl(cert_u128_t value, uint32_t shift);
cert_u128_t cert_u128_lshr(cert_u128_t value, uint32_t shift);
cert_i128_t cert_i128_ashr(cert_i128_t value, uint32_t shift);

cert_u128_t cert_u128_mul(cert_u128_t lhs, cert_u128_t rhs);
cert_i128_t cert_i128_mul(cert_i128_t lhs, cert_i128_t rhs);

uint32_t cert_u128_clz(cert_u128_t value);
uint32_t cert_u128_ctz(cert_u128_t value);
uint32_t cert_u128_popcount(cert_u128_t value);

/* Portable 128-bit unsigned and signed division/modulo primitives (max 128 loop iterations).
 * Total deterministic edge-case semantics (matching RISC-V M-extension architecture table):
 * - Unsigned division by 0: quotient = UINT128_MAX (`{UINT64_MAX, UINT64_MAX}`), remainder = lhs.
 * - Signed division by 0:   quotient = -1 (`{UINT64_MAX, UINT64_MAX}`), remainder = lhs.
 * - Signed `INT128_MIN / -1`: quotient = `INT128_MIN` (two's-complement wrap), remainder = 0,
 *   computed purely in unsigned magnitude domain with zero signed overflow UB (CERT C INT32-C). */
cert_u128_t cert_udivmod128(cert_u128_t lhs, cert_u128_t rhs, cert_u128_t *remainder);
cert_u128_t cert_u128_udiv(cert_u128_t lhs, cert_u128_t rhs);
cert_u128_t cert_u128_umod(cert_u128_t lhs, cert_u128_t rhs);
cert_i128_t cert_div128(cert_i128_t lhs, cert_i128_t rhs);
cert_i128_t cert_mod128(cert_i128_t lhs, cert_i128_t rhs);
cert_i128_t cert_i128_sdiv(cert_i128_t lhs, cert_i128_t rhs);
cert_i128_t cert_i128_srem(cert_i128_t lhs, cert_i128_t rhs);

#if defined(CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES)

#if !defined(CERT_RUNTIME_HOSTED_TEST)
void *memcpy(void *CERT_RUNTIME_RESTRICT dst, const void *CERT_RUNTIME_RESTRICT src, size_t count);
void *memmove(void *dst, const void *src, size_t count);
void *memset(void *dst, int byte_value, size_t count);
int memcmp(const void *lhs, const void *rhs, size_t count);
#endif

#if defined(__SIZEOF_INT128__) && !defined(CERT_RUNTIME_NO_ABI_WRAPPERS)
__extension__ typedef __int128 cert_abi_i128_t;
__extension__ typedef unsigned __int128 cert_abi_u128_t;

/* MISRA C:2023 Rule 21.2 / CERT C DCL37-C ABI-provider deviation: these symbols implement the
 * target compiler-rt 128-bit integer ABI required by LLVM backend lowering. */
/* NOLINTBEGIN(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp) */
cert_abi_i128_t __ashlti3(cert_abi_i128_t value, int shift);
cert_abi_i128_t __lshrti3(cert_abi_i128_t value, int shift);
cert_abi_i128_t __ashrti3(cert_abi_i128_t value, int shift);
cert_abi_i128_t __multi3(cert_abi_i128_t lhs, cert_abi_i128_t rhs);
cert_abi_u128_t __udivmodti4(cert_abi_u128_t lhs, cert_abi_u128_t rhs, cert_abi_u128_t *remainder);
cert_abi_u128_t __udivti3(cert_abi_u128_t lhs, cert_abi_u128_t rhs);
cert_abi_u128_t __umodti3(cert_abi_u128_t lhs, cert_abi_u128_t rhs);
cert_abi_i128_t __divti3(cert_abi_i128_t lhs, cert_abi_i128_t rhs);
cert_abi_i128_t __modti3(cert_abi_i128_t lhs, cert_abi_i128_t rhs);
int __clzti2(cert_abi_i128_t value);
int __ctzti2(cert_abi_i128_t value);
int __popcountti2(cert_abi_i128_t value);
/* NOLINTEND(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp) */
#endif

#endif /* CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES */

#if defined(__cplusplus)
}
#endif

#endif /* CERT_RUNTIME_H */
