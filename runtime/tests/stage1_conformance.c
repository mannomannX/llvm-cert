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

#include <stddef.h>
#include <stdint.h>

#include "../include/cert_runtime.h"

#if defined(__GNUC__) || defined(__clang__)
#define STAGE1_NOINLINE __attribute__((noinline))
#define STAGE1_PACKED __attribute__((packed))
#else
#define STAGE1_NOINLINE
#define STAGE1_PACKED
#endif

typedef struct stage1_padded_agg {
  uint8_t tag;
  uint64_t payload;
  uint16_t tail;
} stage1_padded_agg_t;

typedef struct STAGE1_PACKED stage1_packed_agg {
  uint8_t tag;
  uint64_t payload;
  uint16_t tail;
} stage1_packed_agg_t;

typedef struct stage1_sret_box {
  uint64_t w0;
  uint64_t w1;
  uint64_t w2;
  uint64_t w3;
} stage1_sret_box_t;

typedef union stage1_f64_bits {
  double f;
  uint64_t u;
} stage1_f64_bits_t;

_Static_assert(offsetof(stage1_padded_agg_t, tag) == 0U, "unexpected tag offset");
_Static_assert(offsetof(stage1_padded_agg_t, payload) == 8U, "unexpected payload offset");
_Static_assert(offsetof(stage1_padded_agg_t, tail) == 16U, "unexpected tail offset");
_Static_assert(sizeof(stage1_padded_agg_t) == 24U, "unexpected padded struct size");

_Static_assert(offsetof(stage1_packed_agg_t, tag) == 0U, "unexpected packed tag offset");
_Static_assert(offsetof(stage1_packed_agg_t, payload) == 1U, "unexpected packed payload offset");
_Static_assert(offsetof(stage1_packed_agg_t, tail) == 9U, "unexpected packed tail offset");
_Static_assert(sizeof(stage1_packed_agg_t) == 11U, "unexpected packed struct size");

_Static_assert(sizeof(stage1_sret_box_t) == 32U, "sret struct must exceed 16-byte register pair");

#if defined(__SIZEOF_INT128__)
_Static_assert(sizeof(cert_abi_u128_t) == 16U, "cert_abi_u128_t must be 16 bytes");
_Static_assert(_Alignof(cert_abi_u128_t) == 16U, "cert_abi_u128_t must be 16-byte aligned");
#endif

static STAGE1_NOINLINE uint32_t pun_store_half_and_reload_word(uint32_t *word_ptr,
                                                               uint16_t *half_ptr, uint16_t patch) {
  *word_ptr = UINT32_C(0x11223344);
  *half_ptr = patch;
  return *word_ptr;
}

static STAGE1_NOINLINE stage1_sret_box_t build_sret_box(uint64_t seed) {
  const stage1_sret_box_t out = {
      .w0 = seed ^ UINT64_C(0xA5A5A5A5A5A5A5A5),
      .w1 = seed + UINT64_C(0x0101010101010101),
      .w2 = (seed << 8U) | (seed >> 56U),
      .w3 = ~seed,
  };
  return out;
}

/* 1. `-fwrapv`: signed two's-complement addition, subtraction, and negation wraparound. */
static int check_wrapv_signed_overflow(void) {
  volatile int32_t v_i32_max = INT32_MAX;
  volatile int32_t v_i32_min = INT32_MIN;
  volatile int32_t v_i32_one = 1;
  volatile int32_t v_i32_zero = 0;

  const int32_t add32 = v_i32_max + v_i32_one;
  if (add32 != INT32_MIN) {
    return 10;
  }
  const int32_t sub32 = v_i32_min - v_i32_one;
  if (sub32 != INT32_MAX) {
    return 11;
  }
  const int32_t zero_sub_min32 = v_i32_zero - v_i32_min;
  if (zero_sub_min32 != INT32_MIN) {
    return 12;
  }
  const int32_t neg_min32 = -v_i32_min;
  if (neg_min32 != INT32_MIN) {
    return 13;
  }

  volatile int64_t v_i64_max = INT64_MAX;
  volatile int64_t v_i64_min = INT64_MIN;
  volatile int64_t v_i64_one = INT64_C(1);
  volatile int64_t v_i64_zero = INT64_C(0);

  const int64_t add64 = v_i64_max + v_i64_one;
  if (add64 != INT64_MIN) {
    return 14;
  }
  const int64_t sub64 = v_i64_min - v_i64_one;
  if (sub64 != INT64_MAX) {
    return 15;
  }
  const int64_t zero_sub_min64 = v_i64_zero - v_i64_min;
  if (zero_sub_min64 != INT64_MIN) {
    return 16;
  }

  return 0;
}

/* 2. `-fno-strict-aliasing`: type-punned halfword and byte accesses alias integer storage. */
static int check_no_strict_aliasing(void) {
  const uint16_t endian_probe = UINT16_C(0x0102);
  const unsigned char *const probe_bytes = (const unsigned char *)&endian_probe;
  const int is_little_endian = (probe_bytes[0] == 0x02U) ? 1 : 0;

  uint32_t word_slot = 0U;
  uint16_t *const half_view = (uint16_t *)&word_slot;
  const uint32_t reloaded = pun_store_half_and_reload_word(&word_slot, half_view, UINT16_C(0xAABB));
  const uint32_t expected_word =
      (is_little_endian != 0) ? UINT32_C(0x1122AABB) : UINT32_C(0xAABB3344);
  if (reloaded != expected_word) {
    return 20;
  }

  unsigned char *const byte_view = (unsigned char *)&word_slot;
  byte_view[0] = 0xEFU;
  const uint32_t expected_after_byte =
      (is_little_endian != 0) ? UINT32_C(0x1122AAEF) : UINT32_C(0xEFBB3344);
  if (word_slot != expected_after_byte) {
    return 21;
  }

  return 0;
}

/* 3. Aggregate zero-init / layout & 16-byte `__int128` ABI alignment. */
static int check_aggregate_layout_and_int128_abi(void) {
  const stage1_padded_agg_t padded = {.tag = 0x5AU};
  if ((padded.tag != 0x5AU) || (padded.payload != 0U) || (padded.tail != 0U)) {
    return 30;
  }

  const stage1_packed_agg_t packed = {
      .tag = 0x12U,
      .payload = UINT64_C(0x0102030405060708),
      .tail = UINT16_C(0xBEEF),
  };
  if ((packed.tag != 0x12U) || (packed.payload != UINT64_C(0x0102030405060708)) ||
      (packed.tail != UINT16_C(0xBEEF))) {
    return 31;
  }

  const uint32_t partial_arr[4] = {9U};
  if ((partial_arr[0] != 9U) || (partial_arr[1] != 0U) || (partial_arr[2] != 0U) ||
      (partial_arr[3] != 0U)) {
    return 32;
  }

#if defined(__SIZEOF_INT128__)
  volatile cert_abi_u128_t abi_slot = (cert_abi_u128_t)1U << 96U;
  const uintptr_t slot_addr = (uintptr_t)&abi_slot;
  if ((slot_addr & (uintptr_t)15U) != 0U) {
    return 33;
  }
  if ((uint64_t)(abi_slot >> 96U) != 1U) {
    return 34;
  }
#endif

  return 0;
}

/* 4. `-ffp-contract=off` & `-fno-fast-math`: non-contracted rounding, `-0.0`, and quiet NaN. */
static int check_ieee754_fp_semantics(void) {
  /* `(1 + 2^-27) * (1 - 2^-27) = 1 - 2^-54`, which rounds to `1.0` in binary64 round-to-even,
   * so uncontracted `(a * b) + (-1.0)` MUST equal `0.0`, whereas fused FMA yields `-2^-54`. */
  volatile double va = 1.0 + 0x1.0p-27;
  volatile double vb = 1.0 - 0x1.0p-27;
  volatile double vc = -1.0;
  const double uncontracted = (va * vb) + vc;
  if (uncontracted != 0.0) {
    return 40;
  }

  /* Preserve signed zero `-0.0` sign bit and reciprocal sign (`1.0 / -0.0 == -inf < 0.0`). */
  volatile double v_pos_zero = 0.0;
  volatile double v_neg_one = -1.0;
  volatile double v_pos_one = 1.0;
  const stage1_f64_bits_t neg_zero_bits = {.f = v_pos_zero * v_neg_one};
  if (neg_zero_bits.u != UINT64_C(0x8000000000000000)) {
    return 41;
  }
  const double neg_inf = v_pos_one / neg_zero_bits.f;
  if (!(neg_inf < 0.0)) {
    return 42;
  }

  /* Preserve IEEE-754 unordered quiet-NaN comparisons (`NaN != NaN` and `!(NaN == NaN)`). */
  const stage1_f64_bits_t qnan_bits = {.u = UINT64_C(0x7FF8000000000000)};
  volatile double v_nan_lhs = qnan_bits.f;
  volatile double v_nan_rhs = qnan_bits.f;
  const double nan_lhs = v_nan_lhs;
  const double nan_rhs = v_nan_rhs;
  if (nan_lhs == nan_rhs) {
    return 43;
  }
  if (!(nan_lhs != nan_rhs)) {
    return 44;
  }

  return 0;
}

/* 5. `-fno-finite-loops`: pure state-machine loop without memory/I/O side effects. */
static int check_side_effect_free_state_machine_loop(void) {
  volatile uint32_t v_seed = UINT32_C(0xACE1);
  volatile uint32_t v_target = UINT32_C(0xC2C4);
  uint32_t lfsr = v_seed;
  const uint32_t target = v_target;
  uint32_t steps = 0U;

  while (lfsr != target) {
    const uint32_t lsb = lfsr & 1U;
    const uint32_t mask = (lsb != 0U) ? UINT32_C(0xB400) : 0U;
    lfsr = (lfsr >> 1U) ^ mask;
    steps += 1U;
  }

  if ((steps != 8U) || (lfsr != UINT32_C(0xC2C4))) {
    return 50;
  }
  return 0;
}

/* 6. Multi-word `> 16B` struct return (`sret` ABI lowering path). */
static int check_sret_large_struct_return(void) {
  volatile uint64_t v_seed = UINT64_C(0x0123456789ABCDEF);
  const uint64_t seed = v_seed;
  const stage1_sret_box_t box = build_sret_box(seed);

  if (box.w0 != (seed ^ UINT64_C(0xA5A5A5A5A5A5A5A5))) {
    return 60;
  }
  if (box.w1 != (seed + UINT64_C(0x0101010101010101))) {
    return 61;
  }
  if (box.w2 != ((seed << 8U) | (seed >> 56U))) {
    return 62;
  }
  if (box.w3 != (~seed)) {
    return 63;
  }
  return 0;
}

int main(void) {
  const int rc_wrapv = check_wrapv_signed_overflow();
  if (rc_wrapv != 0) {
    return rc_wrapv;
  }

  const int rc_alias = check_no_strict_aliasing();
  if (rc_alias != 0) {
    return rc_alias;
  }

  const int rc_layout = check_aggregate_layout_and_int128_abi();
  if (rc_layout != 0) {
    return rc_layout;
  }

  const int rc_fp = check_ieee754_fp_semantics();
  if (rc_fp != 0) {
    return rc_fp;
  }

  const int rc_loop = check_side_effect_free_state_machine_loop();
  if (rc_loop != 0) {
    return rc_loop;
  }

  const int rc_sret = check_sret_large_struct_return();
  if (rc_sret != 0) {
    return rc_sret;
  }

  return 0;
}
