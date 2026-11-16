/* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
 * Licensed under the LLVMCert Non-Commercial Evaluation & Research License
 * or a separate LLVMCert Commercial Software License Agreement.
 * See /LICENSE in the repository root for details. */

#if !defined(CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES)
#define CERT_RUNTIME_EXPORT_COMPILER_RT_ALIASES 1
#endif
#if !defined(CERT_RUNTIME_NO_ABI_WRAPPERS)
#define CERT_RUNTIME_NO_ABI_WRAPPERS 1
#endif

#include "../include/cert_runtime.h"

void *cert_memcpy(void *CERT_RUNTIME_RESTRICT dst, const void *CERT_RUNTIME_RESTRICT src,
                  size_t count) {
  if ((count == 0U) || (dst == src) || (dst == NULL) || (src == NULL)) {
    return dst;
  }

  unsigned char *const dst_bytes = (unsigned char *)dst;
  const unsigned char *const src_bytes = (const unsigned char *)src;
  for (size_t i = 0U; i < count; ++i) {
    dst_bytes[i] = src_bytes[i];
  }
  return dst;
}

void *cert_memmove(void *dst, const void *src, size_t count) {
  if ((count == 0U) || (dst == src) || (dst == NULL) || (src == NULL)) {
    return dst;
  }

  unsigned char *const dst_bytes = (unsigned char *)dst;
  const unsigned char *const src_bytes = (const unsigned char *)src;
  const uintptr_t dst_addr = (uintptr_t)dst_bytes;
  const uintptr_t src_addr = (uintptr_t)src_bytes;

  if (dst_addr < src_addr) {
    for (size_t i = 0U; i < count; ++i) {
      dst_bytes[i] = src_bytes[i];
    }
  } else {
    for (size_t i = count; i > 0U; --i) {
      dst_bytes[i - 1U] = src_bytes[i - 1U];
    }
  }
  return dst;
}

/* NOLINTNEXTLINE(bugprone-easily-swappable-parameters): ISO C11 7.24.6.1 memset signature. */
void *cert_memset(void *dst, int byte_value, size_t count) {
  if ((count == 0U) || (dst == NULL)) {
    return dst;
  }

  unsigned char *const dst_bytes = (unsigned char *)dst;
  const unsigned char fill = (unsigned char)((unsigned int)byte_value & 0xFFU);
  for (size_t i = 0U; i < count; ++i) {
    dst_bytes[i] = fill;
  }
  return dst;
}

int cert_memcmp(const void *lhs, const void *rhs, size_t count) {
  if ((count == 0U) || (lhs == rhs)) {
    return 0;
  }
  if ((lhs == NULL) || (rhs == NULL)) {
    return (lhs == NULL) ? -1 : 1;
  }

  const unsigned char *const lhs_bytes = (const unsigned char *)lhs;
  const unsigned char *const rhs_bytes = (const unsigned char *)rhs;
  for (size_t i = 0U; i < count; ++i) {
    const unsigned char lhs_byte = lhs_bytes[i];
    const unsigned char rhs_byte = rhs_bytes[i];
    if (lhs_byte != rhs_byte) {
      return (lhs_byte < rhs_byte) ? -1 : 1;
    }
  }
  return 0;
}

void *cert_memzero_explicit(void *dst, size_t count) {
  if ((count == 0U) || (dst == NULL)) {
    return dst;
  }

  volatile unsigned char *const dst_bytes = (volatile unsigned char *)dst;
  for (size_t i = 0U; i < count; ++i) {
    dst_bytes[i] = 0U;
  }
  return dst;
}

#if !defined(CERT_RUNTIME_HOSTED_TEST)
void *memcpy(void *CERT_RUNTIME_RESTRICT dst, const void *CERT_RUNTIME_RESTRICT src, size_t count) {
  return cert_memcpy(dst, src, count);
}

void *memmove(void *dst, const void *src, size_t count) { return cert_memmove(dst, src, count); }

void *memset(void *dst, int byte_value, size_t count) {
  return cert_memset(dst, byte_value, count);
}

int memcmp(const void *lhs, const void *rhs, size_t count) { return cert_memcmp(lhs, rhs, count); }
#endif
