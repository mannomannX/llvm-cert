/* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
 * Licensed under the LLVMCert Non-Commercial Evaluation & Research License
 * or a separate LLVMCert Commercial Software License Agreement.
 * See /LICENSE in the repository root for details. */

#if !defined(CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES)
#define CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES 1
#endif

#include "../include/cert_runtime.h"

static uint32_t cert_clz64_nonzero(uint64_t value) {
  uint32_t count = 0U;
  if ((value & UINT64_C(0xFFFFFFFF00000000)) == 0U) {
    count += 32U;
    value <<= 32U;
  }
  if ((value & UINT64_C(0xFFFF000000000000)) == 0U) {
    count += 16U;
    value <<= 16U;
  }
  if ((value & UINT64_C(0xFF00000000000000)) == 0U) {
    count += 8U;
    value <<= 8U;
  }
  if ((value & UINT64_C(0xF000000000000000)) == 0U) {
    count += 4U;
    value <<= 4U;
  }
  if ((value & UINT64_C(0xC000000000000000)) == 0U) {
    count += 2U;
    value <<= 2U;
  }
  if ((value & UINT64_C(0x8000000000000000)) == 0U) {
    count += 1U;
  }
  return count;
}

static uint32_t cert_ctz64_nonzero(uint64_t value) {
  uint32_t count = 0U;
  if ((value & UINT64_C(0x00000000FFFFFFFF)) == 0U) {
    count += 32U;
    value >>= 32U;
  }
  if ((value & UINT64_C(0x000000000000FFFF)) == 0U) {
    count += 16U;
    value >>= 16U;
  }
  if ((value & UINT64_C(0x00000000000000FF)) == 0U) {
    count += 8U;
    value >>= 8U;
  }
  if ((value & UINT64_C(0x000000000000000F)) == 0U) {
    count += 4U;
    value >>= 4U;
  }
  if ((value & UINT64_C(0x0000000000000003)) == 0U) {
    count += 2U;
    value >>= 2U;
  }
  if ((value & UINT64_C(0x0000000000000001)) == 0U) {
    count += 1U;
  }
  return count;
}

static uint32_t cert_popcount64(uint64_t value) {
  value = value - ((value >> 1U) & UINT64_C(0x5555555555555555));
  value = (value & UINT64_C(0x3333333333333333)) + ((value >> 2U) & UINT64_C(0x3333333333333333));
  value = (value + (value >> 4U)) & UINT64_C(0x0F0F0F0F0F0F0F0F);
  return (uint32_t)((value * UINT64_C(0x0101010101010101)) >> 56U);
}

cert_u128_t cert_u128_add(cert_u128_t lhs, cert_u128_t rhs) {
  cert_u128_t result;
  result.low = lhs.low + rhs.low;
  const uint64_t carry = (result.low < lhs.low) ? 1U : 0U;
  result.high = lhs.high + rhs.high + carry;
  return result;
}

cert_u128_t cert_u128_sub(cert_u128_t lhs, cert_u128_t rhs) {
  cert_u128_t result;
  const uint64_t borrow = (lhs.low < rhs.low) ? 1U : 0U;
  result.low = lhs.low - rhs.low;
  result.high = lhs.high - rhs.high - borrow;
  return result;
}

cert_u128_t cert_u128_neg(cert_u128_t value) {
  const cert_u128_t inverted = {.low = ~value.low, .high = ~value.high};
  const cert_u128_t one = {.low = 1U, .high = 0U};
  return cert_u128_add(inverted, one);
}

int cert_u128_cmp(cert_u128_t lhs, cert_u128_t rhs) {
  if (lhs.high != rhs.high) {
    return (lhs.high < rhs.high) ? -1 : 1;
  }
  if (lhs.low != rhs.low) {
    return (lhs.low < rhs.low) ? -1 : 1;
  }
  return 0;
}

int cert_i128_cmp(cert_i128_t lhs, cert_i128_t rhs) {
  const uint64_t lhs_neg = lhs.high >> 63U;
  const uint64_t rhs_neg = rhs.high >> 63U;
  if (lhs_neg != rhs_neg) {
    return (lhs_neg != 0U) ? -1 : 1;
  }
  const cert_u128_t u_lhs = {.low = lhs.low, .high = lhs.high};
  const cert_u128_t u_rhs = {.low = rhs.low, .high = rhs.high};
  return cert_u128_cmp(u_lhs, u_rhs);
}

cert_u128_t cert_u128_shl(cert_u128_t value, uint32_t shift) {
  if (shift == 0U) {
    return value;
  }
  if (shift >= 128U) {
    const cert_u128_t zero = {.low = 0U, .high = 0U};
    return zero;
  }
  if (shift == 64U) {
    const cert_u128_t moved = {.low = 0U, .high = value.low};
    return moved;
  }
  if (shift > 64U) {
    const uint32_t limb_shift = shift - 64U;
    const cert_u128_t upper = {.low = 0U, .high = value.low << limb_shift};
    return upper;
  }
  const cert_u128_t shifted = {
      .low = value.low << shift,
      .high = (value.high << shift) | (value.low >> (64U - shift)),
  };
  return shifted;
}

cert_u128_t cert_u128_lshr(cert_u128_t value, uint32_t shift) {
  if (shift == 0U) {
    return value;
  }
  if (shift >= 128U) {
    const cert_u128_t zero = {.low = 0U, .high = 0U};
    return zero;
  }
  if (shift == 64U) {
    const cert_u128_t moved = {.low = value.high, .high = 0U};
    return moved;
  }
  if (shift > 64U) {
    const uint32_t limb_shift = shift - 64U;
    const cert_u128_t lower = {.low = value.high >> limb_shift, .high = 0U};
    return lower;
  }
  const cert_u128_t shifted = {
      .low = (value.low >> shift) | (value.high << (64U - shift)),
      .high = value.high >> shift,
  };
  return shifted;
}

cert_i128_t cert_i128_ashr(cert_i128_t value, uint32_t shift) {
  if (shift == 0U) {
    return value;
  }
  const uint64_t sign_fill = ((value.high >> 63U) != 0U) ? UINT64_MAX : 0U;
  if (shift >= 128U) {
    const cert_i128_t saturated = {.low = sign_fill, .high = sign_fill};
    return saturated;
  }
  if (shift == 64U) {
    const cert_i128_t moved = {.low = value.high, .high = sign_fill};
    return moved;
  }
  if (shift > 64U) {
    const uint32_t limb_shift = shift - 64U;
    const cert_i128_t lower = {
        .low = (value.high >> limb_shift) | (sign_fill << (64U - limb_shift)),
        .high = sign_fill,
    };
    return lower;
  }
  const cert_i128_t shifted = {
      .low = (value.low >> shift) | (value.high << (64U - shift)),
      .high = (value.high >> shift) | (sign_fill << (64U - shift)),
  };
  return shifted;
}

cert_u128_t cert_u128_mul(cert_u128_t lhs, cert_u128_t rhs) {
  const uint64_t a0 = lhs.low & UINT64_C(0xFFFFFFFF);
  const uint64_t a1 = lhs.low >> 32U;
  const uint64_t b0 = rhs.low & UINT64_C(0xFFFFFFFF);
  const uint64_t b1 = rhs.low >> 32U;

  const uint64_t p00 = a0 * b0;
  const uint64_t p01 = a0 * b1;
  const uint64_t p10 = a1 * b0;
  const uint64_t p11 = a1 * b1;

  const uint64_t mid = (p00 >> 32U) + (p01 & UINT64_C(0xFFFFFFFF)) + (p10 & UINT64_C(0xFFFFFFFF));
  const uint64_t prod_low = (p00 & UINT64_C(0xFFFFFFFF)) | (mid << 32U);
  const uint64_t prod_high_base = p11 + (p01 >> 32U) + (p10 >> 32U) + (mid >> 32U);
  const uint64_t prod_high = prod_high_base + (lhs.low * rhs.high) + (lhs.high * rhs.low);

  const cert_u128_t product = {.low = prod_low, .high = prod_high};
  return product;
}

cert_i128_t cert_i128_mul(cert_i128_t lhs, cert_i128_t rhs) {
  const cert_u128_t u_lhs = {.low = lhs.low, .high = lhs.high};
  const cert_u128_t u_rhs = {.low = rhs.low, .high = rhs.high};
  const cert_u128_t u_prod = cert_u128_mul(u_lhs, u_rhs);
  const cert_i128_t prod = {.low = u_prod.low, .high = u_prod.high};
  return prod;
}

uint32_t cert_u128_clz(cert_u128_t value) {
  if (value.high != 0U) {
    return cert_clz64_nonzero(value.high);
  }
  if (value.low != 0U) {
    return 64U + cert_clz64_nonzero(value.low);
  }
  return 128U;
}

uint32_t cert_u128_ctz(cert_u128_t value) {
  if (value.low != 0U) {
    return cert_ctz64_nonzero(value.low);
  }
  if (value.high != 0U) {
    return 64U + cert_ctz64_nonzero(value.high);
  }
  return 128U;
}

uint32_t cert_u128_popcount(cert_u128_t value) {
  return cert_popcount64(value.low) + cert_popcount64(value.high);
}

cert_u128_t cert_udivmod128(cert_u128_t lhs, cert_u128_t rhs, cert_u128_t *remainder) {
  if ((rhs.low == 0U) && (rhs.high == 0U)) {
    if (remainder != NULL) {
      *remainder = lhs;
    }
    const cert_u128_t all_ones = {.low = UINT64_MAX, .high = UINT64_MAX};
    return all_ones;
  }

  cert_u128_t quot = {.low = 0U, .high = 0U};
  cert_u128_t rem = {.low = 0U, .high = 0U};

  for (uint32_t step = 0U; step < 128U; ++step) {
    const uint32_t bit_index = 127U - step;
    uint64_t dividend_bit = 0U;
    if (bit_index >= 64U) {
      dividend_bit = (lhs.high >> (bit_index - 64U)) & 1U;
    } else {
      dividend_bit = (lhs.low >> bit_index) & 1U;
    }

    const uint64_t carry = rem.high >> 63U;
    rem = cert_u128_shl(rem, 1U);
    rem.low |= dividend_bit;

    if ((carry != 0U) || (cert_u128_cmp(rem, rhs) >= 0)) {
      rem = cert_u128_sub(rem, rhs);
      if (bit_index >= 64U) {
        quot.high |= UINT64_C(1) << (bit_index - 64U);
      } else {
        quot.low |= UINT64_C(1) << bit_index;
      }
    }
  }

  if (remainder != NULL) {
    *remainder = rem;
  }
  return quot;
}

cert_u128_t cert_u128_udiv(cert_u128_t lhs, cert_u128_t rhs) {
  return cert_udivmod128(lhs, rhs, NULL);
}

cert_u128_t cert_u128_umod(cert_u128_t lhs, cert_u128_t rhs) {
  cert_u128_t rem = {.low = 0U, .high = 0U};
  (void)cert_udivmod128(lhs, rhs, &rem);
  return rem;
}

static cert_i128_t cert_sdivmod128_internal(cert_i128_t lhs, cert_i128_t rhs,
                                            cert_i128_t *remainder) {
  if ((rhs.low == 0U) && (rhs.high == 0U)) {
    if (remainder != NULL) {
      *remainder = lhs;
    }
    const cert_i128_t minus_one = {.low = UINT64_MAX, .high = UINT64_MAX};
    return minus_one;
  }

  const uint64_t lhs_neg = lhs.high >> 63U;
  const uint64_t rhs_neg = rhs.high >> 63U;

  const cert_u128_t u_lhs = {.low = lhs.low, .high = lhs.high};
  const cert_u128_t u_rhs = {.low = rhs.low, .high = rhs.high};
  const cert_u128_t mag_lhs = (lhs_neg != 0U) ? cert_u128_neg(u_lhs) : u_lhs;
  const cert_u128_t mag_rhs = (rhs_neg != 0U) ? cert_u128_neg(u_rhs) : u_rhs;

  cert_u128_t mag_rem = {.low = 0U, .high = 0U};
  const cert_u128_t mag_quot = cert_udivmod128(mag_lhs, mag_rhs, &mag_rem);

  const cert_u128_t signed_quot = (lhs_neg != rhs_neg) ? cert_u128_neg(mag_quot) : mag_quot;
  if (remainder != NULL) {
    const cert_u128_t signed_rem = (lhs_neg != 0U) ? cert_u128_neg(mag_rem) : mag_rem;
    remainder->low = signed_rem.low;
    remainder->high = signed_rem.high;
  }

  const cert_i128_t quot = {.low = signed_quot.low, .high = signed_quot.high};
  return quot;
}

cert_i128_t cert_div128(cert_i128_t lhs, cert_i128_t rhs) {
  return cert_sdivmod128_internal(lhs, rhs, NULL);
}

cert_i128_t cert_mod128(cert_i128_t lhs, cert_i128_t rhs) {
  cert_i128_t rem = {.low = 0U, .high = 0U};
  (void)cert_sdivmod128_internal(lhs, rhs, &rem);
  return rem;
}

cert_i128_t cert_i128_sdiv(cert_i128_t lhs, cert_i128_t rhs) { return cert_div128(lhs, rhs); }

cert_i128_t cert_i128_srem(cert_i128_t lhs, cert_i128_t rhs) { return cert_mod128(lhs, rhs); }

#if defined(__SIZEOF_INT128__) && !defined(CERT_RUNTIME_NO_ABI_WRAPPERS)

static cert_u128_t cert_u128_from_abi(cert_abi_u128_t value) {
  const cert_u128_t limbs = {
      .low = (uint64_t)value,
      .high = (uint64_t)(value >> 64U),
  };
  return limbs;
}

static cert_abi_u128_t cert_u128_to_abi(cert_u128_t value) {
  return ((cert_abi_u128_t)value.high << 64U) | (cert_abi_u128_t)value.low;
}

static cert_i128_t cert_i128_from_abi(cert_abi_i128_t value) {
  const cert_abi_u128_t bits = (cert_abi_u128_t)value;
  const cert_i128_t limbs = {
      .low = (uint64_t)bits,
      .high = (uint64_t)(bits >> 64U),
  };
  return limbs;
}

static cert_abi_i128_t cert_abi_i128_from_u128_bits(cert_abi_u128_t bits) {
  const union {
    cert_abi_u128_t u;
    cert_abi_i128_t s;
  } pun = {.u = bits};
  return pun.s;
}

static cert_abi_i128_t cert_i128_to_abi(cert_i128_t value) {
  const cert_abi_u128_t bits = ((cert_abi_u128_t)value.high << 64U) | (cert_abi_u128_t)value.low;
  return cert_abi_i128_from_u128_bits(bits);
}

static uint32_t cert_normalize_abi_shift(int shift) { return (uint32_t)shift; }

/* NOLINTBEGIN(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp) */
cert_abi_i128_t __ashlti3(cert_abi_i128_t value, int shift) {
  const cert_u128_t res =
      cert_u128_shl(cert_u128_from_abi((cert_abi_u128_t)value), cert_normalize_abi_shift(shift));
  return cert_abi_i128_from_u128_bits(cert_u128_to_abi(res));
}

cert_abi_i128_t __lshrti3(cert_abi_i128_t value, int shift) {
  const cert_u128_t res =
      cert_u128_lshr(cert_u128_from_abi((cert_abi_u128_t)value), cert_normalize_abi_shift(shift));
  return cert_abi_i128_from_u128_bits(cert_u128_to_abi(res));
}

cert_abi_i128_t __ashrti3(cert_abi_i128_t value, int shift) {
  const cert_i128_t res =
      cert_i128_ashr(cert_i128_from_abi(value), cert_normalize_abi_shift(shift));
  return cert_i128_to_abi(res);
}

cert_abi_i128_t __multi3(cert_abi_i128_t lhs, cert_abi_i128_t rhs) {
  return cert_i128_to_abi(cert_i128_mul(cert_i128_from_abi(lhs), cert_i128_from_abi(rhs)));
}

cert_abi_u128_t __udivmodti4(cert_abi_u128_t lhs, cert_abi_u128_t rhs, cert_abi_u128_t *remainder) {
  cert_u128_t rem_limbs = {.low = 0U, .high = 0U};
  const cert_u128_t quot_limbs =
      cert_udivmod128(cert_u128_from_abi(lhs), cert_u128_from_abi(rhs), &rem_limbs);
  if (remainder != NULL) {
    *remainder = cert_u128_to_abi(rem_limbs);
  }
  return cert_u128_to_abi(quot_limbs);
}

cert_abi_u128_t __udivti3(cert_abi_u128_t lhs, cert_abi_u128_t rhs) {
  return cert_u128_to_abi(cert_u128_udiv(cert_u128_from_abi(lhs), cert_u128_from_abi(rhs)));
}

cert_abi_u128_t __umodti3(cert_abi_u128_t lhs, cert_abi_u128_t rhs) {
  return cert_u128_to_abi(cert_u128_umod(cert_u128_from_abi(lhs), cert_u128_from_abi(rhs)));
}

cert_abi_i128_t __divti3(cert_abi_i128_t lhs, cert_abi_i128_t rhs) {
  return cert_i128_to_abi(cert_div128(cert_i128_from_abi(lhs), cert_i128_from_abi(rhs)));
}

cert_abi_i128_t __modti3(cert_abi_i128_t lhs, cert_abi_i128_t rhs) {
  return cert_i128_to_abi(cert_mod128(cert_i128_from_abi(lhs), cert_i128_from_abi(rhs)));
}

int __clzti2(cert_abi_i128_t value) {
  return (int)cert_u128_clz(cert_u128_from_abi((cert_abi_u128_t)value));
}

int __ctzti2(cert_abi_i128_t value) {
  return (int)cert_u128_ctz(cert_u128_from_abi((cert_abi_u128_t)value));
}

int __popcountti2(cert_abi_i128_t value) {
  return (int)cert_u128_popcount(cert_u128_from_abi((cert_abi_u128_t)value));
}
/* NOLINTEND(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp) */

#endif /* defined(__SIZEOF_INT128__) && !defined(CERT_RUNTIME_NO_ABI_WRAPPERS) */
