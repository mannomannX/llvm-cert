/* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
 * Licensed under the LLVMCert Non-Commercial Evaluation & Research License
 * or a separate LLVMCert Commercial Software License Agreement.
 * See /LICENSE in the repository root for details. */

#if !defined(CERT_RUNTIME_HOSTED_TEST)
#define CERT_RUNTIME_HOSTED_TEST 1
#endif
#if !defined(CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES)
#define CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES 1
#endif

#include "../include/cert_runtime.h"

static int check_memory_primitives(void) {
  unsigned char src[32];
  unsigned char dst[32];
  for (size_t i = 0U; i < 32U; ++i) {
    src[i] = (unsigned char)(0xA0U + (unsigned int)i);
    dst[i] = 0U;
  }

  /* Zero-length calls with NULL pointers must never dereference pointers (CERT C EXP34-C). */
  if (cert_memcpy(NULL, NULL, 0U) != NULL) {
    return 1;
  }
  if (cert_memmove(NULL, NULL, 0U) != NULL) {
    return 2;
  }
  if (cert_memset(NULL, 0x5A, 0U) != NULL) {
    return 3;
  }
  if (cert_memcmp(NULL, NULL, 0U) != 0) {
    return 4;
  }
  if (cert_memzero_explicit(NULL, 0U) != NULL) {
    return 5;
  }

  /* Basic copy and comparison. */
  if (cert_memcpy(dst, src, 32U) != dst) {
    return 6;
  }
  if (cert_memcmp(dst, src, 32U) != 0) {
    return 7;
  }

  /* C11 7.24.4.1 unsigned byte ordering: 0x80 > 0x7F must compare positive. */
  const unsigned char high_bit_buf[2] = {0x42U, 0x80U};
  const unsigned char low_bit_buf[2] = {0x42U, 0x7FU};
  if (cert_memcmp(high_bit_buf, low_bit_buf, 2U) <= 0) {
    return 8;
  }
  if (cert_memcmp(low_bit_buf, high_bit_buf, 2U) >= 0) {
    return 9;
  }

  /* Overlapping backward-copy memmove (`dst > src`). */
  unsigned char overlap_back[16];
  for (size_t i = 0U; i < 16U; ++i) {
    overlap_back[i] = (unsigned char)i;
  }
  if (cert_memmove(&overlap_back[4], &overlap_back[0], 10U) != &overlap_back[4]) {
    return 10;
  }
  for (size_t i = 0U; i < 10U; ++i) {
    if (overlap_back[i + 4U] != (unsigned char)i) {
      return 11;
    }
  }

  /* Overlapping forward-copy memmove (`dst < src`). */
  unsigned char overlap_fwd[16];
  for (size_t i = 0U; i < 16U; ++i) {
    overlap_fwd[i] = (unsigned char)(100U + (unsigned int)i);
  }
  if (cert_memmove(&overlap_fwd[0], &overlap_fwd[4], 10U) != &overlap_fwd[0]) {
    return 12;
  }
  for (size_t i = 0U; i < 10U; ++i) {
    if (overlap_fwd[i] != (unsigned char)(104U + (unsigned int)i)) {
      return 13;
    }
  }

  /* Fill and explicit zeroize (`MSC06-C`). */
  if (cert_memset(dst, 0xAB, 32U) != dst) {
    return 14;
  }
  for (size_t i = 0U; i < 32U; ++i) {
    if (dst[i] != 0xABU) {
      return 15;
    }
  }
  if (cert_memzero_explicit(dst, 32U) != dst) {
    return 16;
  }
  for (size_t i = 0U; i < 32U; ++i) {
    if (dst[i] != 0U) {
      return 17;
    }
  }

  return 0;
}

static int check_int128_shifts_and_counts(void) {
  const cert_u128_t zero = {.low = 0U, .high = 0U};
  const cert_u128_t one = {.low = 1U, .high = 0U};
  const cert_u128_t pattern = {
      .low = UINT64_C(0x0123456789ABCDEF),
      .high = UINT64_C(0xFEDCBA9876543210),
  };

  /* Shift boundary counts: 0, 1, 63, 64, 65, 127, 128. */
  if (cert_u128_cmp(cert_u128_shl(pattern, 0U), pattern) != 0) {
    return 20;
  }
  if (cert_u128_cmp(cert_u128_lshr(pattern, 0U), pattern) != 0) {
    return 21;
  }

  const cert_u128_t shl1 = cert_u128_shl(one, 1U);
  if ((shl1.low != 2U) || (shl1.high != 0U)) {
    return 22;
  }
  const cert_u128_t shl63 = cert_u128_shl(one, 63U);
  if ((shl63.low != UINT64_C(0x8000000000000000)) || (shl63.high != 0U)) {
    return 23;
  }
  const cert_u128_t shl64 = cert_u128_shl(one, 64U);
  if ((shl64.low != 0U) || (shl64.high != 1U)) {
    return 24;
  }
  const cert_u128_t shl65 = cert_u128_shl(one, 65U);
  if ((shl65.low != 0U) || (shl65.high != 2U)) {
    return 25;
  }
  const cert_u128_t shl127 = cert_u128_shl(one, 127U);
  if ((shl127.low != 0U) || (shl127.high != UINT64_C(0x8000000000000000))) {
    return 26;
  }
  if (cert_u128_cmp(cert_u128_shl(pattern, 128U), zero) != 0) {
    return 27;
  }

  /* Cross-limb inverse check on `shl` / `lshr`. */
  const cert_u128_t lshr63 = cert_u128_lshr(shl127, 63U);
  if (cert_u128_cmp(lshr63, shl64) != 0) {
    return 28;
  }
  const cert_u128_t lshr64 = cert_u128_lshr(shl64, 64U);
  if (cert_u128_cmp(lshr64, one) != 0) {
    return 29;
  }
  const cert_u128_t lshr65 = cert_u128_lshr(shl127, 65U);
  if ((lshr65.low != UINT64_C(0x4000000000000000)) || (lshr65.high != 0U)) {
    return 30;
  }
  const cert_u128_t lshr127 = cert_u128_lshr(shl127, 127U);
  if (cert_u128_cmp(lshr127, one) != 0) {
    return 31;
  }

  /* Arithmetic right shift sign propagation at 0, 1, 63, 64, 65, 127, 128. */
  const cert_i128_t i128_min = {.low = 0U, .high = UINT64_C(0x8000000000000000)};
  const cert_i128_t ashr0 = cert_i128_ashr(i128_min, 0U);
  if ((ashr0.low != 0U) || (ashr0.high != UINT64_C(0x8000000000000000))) {
    return 32;
  }
  const cert_i128_t ashr1 = cert_i128_ashr(i128_min, 1U);
  if ((ashr1.low != 0U) || (ashr1.high != UINT64_C(0xC000000000000000))) {
    return 33;
  }
  const cert_i128_t ashr63 = cert_i128_ashr(i128_min, 63U);
  if ((ashr63.low != 0U) || (ashr63.high != UINT64_MAX)) {
    return 34;
  }
  const cert_i128_t ashr64 = cert_i128_ashr(i128_min, 64U);
  if ((ashr64.low != UINT64_C(0x8000000000000000)) || (ashr64.high != UINT64_MAX)) {
    return 35;
  }
  const cert_i128_t ashr65 = cert_i128_ashr(i128_min, 65U);
  if ((ashr65.low != UINT64_C(0xC000000000000000)) || (ashr65.high != UINT64_MAX)) {
    return 36;
  }
  const cert_i128_t ashr127 = cert_i128_ashr(i128_min, 127U);
  if ((ashr127.low != UINT64_MAX) || (ashr127.high != UINT64_MAX)) {
    return 37;
  }

  /* Leading/trailing zero count and popcount edge cases. */
  if ((cert_u128_clz(zero) != 128U) || (cert_u128_ctz(zero) != 128U) ||
      (cert_u128_popcount(zero) != 0U)) {
    return 38;
  }
  if ((cert_u128_clz(one) != 127U) || (cert_u128_ctz(one) != 0U) ||
      (cert_u128_popcount(one) != 1U)) {
    return 39;
  }
  if ((cert_u128_clz(shl127) != 0U) || (cert_u128_ctz(shl127) != 127U) ||
      (cert_u128_popcount(shl127) != 1U)) {
    return 40;
  }
  const cert_u128_t u128_max = {.low = UINT64_MAX, .high = UINT64_MAX};
  if (cert_u128_popcount(u128_max) != 128U) {
    return 41;
  }

  return 0;
}

static int check_int128_mul_div_mod(void) {
  const cert_u128_t zero = {.low = 0U, .high = 0U};
  const cert_u128_t one = {.low = 1U, .high = 0U};
  const cert_u128_t u128_max = {.low = UINT64_MAX, .high = UINT64_MAX};

  /* `(2^64 - 1) * (2^64 - 1) = 2^128 - 2^65 + 1 = { 1, 0xFFFFFFFFFFFFFFFE }`. */
  const cert_u128_t u64_max_128 = {.low = UINT64_MAX, .high = 0U};
  const cert_u128_t sq = cert_u128_mul(u64_max_128, u64_max_128);
  if ((sq.low != 1U) || (sq.high != UINT64_C(0xFFFFFFFFFFFFFFFE))) {
    return 50;
  }

  /* `UINT128_MAX * UINT128_MAX mod 2^128 == (-1) * (-1) == 1`. */
  if (cert_u128_cmp(cert_u128_mul(u128_max, u128_max), one) != 0) {
    return 51;
  }

  /* Unsigned division/modulo edge cases: `UINT128_MAX / 1`, `UINT128_MAX / UINT128_MAX`, `/ 0`. */
  cert_u128_t u_rem = zero;
  const cert_u128_t u_quot_one = cert_udivmod128(u128_max, one, &u_rem);
  if ((cert_u128_cmp(u_quot_one, u128_max) != 0) || (cert_u128_cmp(u_rem, zero) != 0)) {
    return 52;
  }
  const cert_u128_t u_quot_self = cert_udivmod128(u128_max, u128_max, &u_rem);
  if ((cert_u128_cmp(u_quot_self, one) != 0) || (cert_u128_cmp(u_rem, zero) != 0)) {
    return 53;
  }
  const cert_u128_t sample_dividend = {.low = UINT64_C(0xCAFEBABE12345678), .high = 42U};
  const cert_u128_t u_quot_zero = cert_udivmod128(sample_dividend, zero, &u_rem);
  if ((cert_u128_cmp(u_quot_zero, u128_max) != 0) || (cert_u128_cmp(u_rem, sample_dividend) != 0)) {
    return 54;
  }

  /* Euclidean identity `lhs == quot * rhs + rem` with `rem < rhs` on non-trivial 128-bit pair. */
  const cert_u128_t big_lhs = {
      .low = UINT64_C(0xFEDCBA9876543211),
      .high = UINT64_C(0x9ABCDEF012345678),
  };
  const cert_u128_t big_rhs = {
      .low = UINT64_C(0x13579BDF2468ACE1),
      .high = UINT64_C(0x0000000100000003),
  };
  const cert_u128_t big_quot = cert_udivmod128(big_lhs, big_rhs, &u_rem);
  const cert_u128_t reconstructed = cert_u128_add(cert_u128_mul(big_quot, big_rhs), u_rem);
  if ((cert_u128_cmp(reconstructed, big_lhs) != 0) || (cert_u128_cmp(u_rem, big_rhs) >= 0)) {
    return 55;
  }

  /* Signed `INT128_MIN / -1` and `INT128_MIN % -1` (CERT C INT32-C overflow-free check). */
  const cert_i128_t i128_min = {.low = 0U, .high = UINT64_C(0x8000000000000000)};
  const cert_i128_t minus_one = {.low = UINT64_MAX, .high = UINT64_MAX};
  const cert_i128_t plus_one = {.low = 1U, .high = 0U};
  const cert_i128_t s_zero = {.low = 0U, .high = 0U};

  if (cert_i128_cmp(cert_div128(i128_min, minus_one), i128_min) != 0) {
    return 56;
  }
  if (cert_i128_cmp(cert_mod128(i128_min, minus_one), s_zero) != 0) {
    return 57;
  }
  if (cert_i128_cmp(cert_div128(i128_min, plus_one), i128_min) != 0) {
    return 58;
  }

  /* Signed division by zero determinism (`quot == -1`, `rem == lhs`). */
  if (cert_i128_cmp(cert_div128(i128_min, s_zero), minus_one) != 0) {
    return 59;
  }
  if (cert_i128_cmp(cert_mod128(i128_min, s_zero), i128_min) != 0) {
    return 60;
  }

  /* Signed truncation-toward-zero check: `INT128_MIN` divided by `+3` and `-3`. */
  const cert_i128_t plus_three = {.low = 3U, .high = 0U};
  const cert_i128_t minus_three = {.low = UINT64_MAX - 2U, .high = UINT64_MAX};
  const cert_i128_t q_pos = cert_div128(i128_min, plus_three);
  const cert_i128_t r_pos = cert_mod128(i128_min, plus_three);
  const cert_i128_t minus_two = {.low = UINT64_MAX - 1U, .high = UINT64_MAX};
  if (cert_i128_cmp(r_pos, minus_two) != 0) {
    return 61;
  }
  const cert_u128_t u_q_pos = {.low = q_pos.low, .high = q_pos.high};
  const cert_u128_t u_plus_three = {.low = plus_three.low, .high = plus_three.high};
  const cert_u128_t u_r_pos = {.low = r_pos.low, .high = r_pos.high};
  const cert_u128_t check_pos = cert_u128_add(cert_u128_mul(u_q_pos, u_plus_three), u_r_pos);
  if ((check_pos.low != i128_min.low) || (check_pos.high != i128_min.high)) {
    return 62;
  }
  const cert_i128_t r_neg = cert_mod128(i128_min, minus_three);
  if (cert_i128_cmp(r_neg, minus_two) != 0) {
    return 63;
  }

#if defined(__SIZEOF_INT128__) && !defined(CERT_RUNTIME_NO_ABI_WRAPPERS)
  /* Differential check of compiler-rt ABI wrappers against native 128-bit operations. */
  const cert_abi_u128_t native_a =
      ((cert_abi_u128_t)UINT64_C(0x9ABCDEF012345678) << 64U) | UINT64_C(0xFEDCBA9876543211);
  const cert_abi_u128_t native_b =
      ((cert_abi_u128_t)UINT64_C(0x0000000100000003) << 64U) | UINT64_C(0x13579BDF2468ACE1);
  cert_abi_u128_t abi_rem = 0U;
  const cert_abi_u128_t abi_quot = __udivmodti4(native_a, native_b, &abi_rem);
  if ((abi_quot * native_b + abi_rem != native_a) || (abi_rem >= native_b)) {
    return 64;
  }
  if ((__udivti3(native_a, native_b) != abi_quot) || (__umodti3(native_a, native_b) != abi_rem)) {
    return 65;
  }
  if (__multi3((cert_abi_i128_t)native_a, (cert_abi_i128_t)native_b) !=
      (cert_abi_i128_t)(native_a * native_b)) {
    return 66;
  }
  if ((__ashlti3((cert_abi_i128_t)1, 65) != ((cert_abi_i128_t)1 << 65)) ||
      (__lshrti3((cert_abi_i128_t)((cert_abi_u128_t)1 << 127U), 65) !=
       (cert_abi_i128_t)((cert_abi_u128_t)1 << 62U)) ||
      (__ashrti3((cert_abi_i128_t)((cert_abi_u128_t)1 << 127U), 127) != (cert_abi_i128_t)-1)) {
    return 67;
  }
  if ((__clzti2((cert_abi_i128_t)1) != 127) || (__ctzti2((cert_abi_i128_t)8) != 3) ||
      (__popcountti2((cert_abi_i128_t)-1) != 128)) {
    return 68;
  }
  const cert_abi_i128_t abi_min = (cert_abi_i128_t)((cert_abi_u128_t)1 << 127U);
  if ((__divti3(abi_min, (cert_abi_i128_t)-1) != abi_min) ||
      (__modti3(abi_min, (cert_abi_i128_t)-1) != 0)) {
    return 69;
  }
#endif

  return 0;
}

int main(void) {
  const int mem_rc = check_memory_primitives();
  if (mem_rc != 0) {
    return mem_rc;
  }
  const int shift_rc = check_int128_shifts_and_counts();
  if (shift_rc != 0) {
    return shift_rc;
  }
  return check_int128_mul_div_mod();
}
