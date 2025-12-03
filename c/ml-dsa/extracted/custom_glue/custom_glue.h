/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 */

#ifndef internal_libcrux_iot_custom_glue_H
#define internal_libcrux_iot_custom_glue_H

#if defined(__cplusplus)
extern "C" {
#endif

// The following needed for SHA3
static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1) {
  return (x0 << x1) | (x0 >> ((-x1) & 31));
}

// The following needed for ML-DSA
#define core_option__core__option__Option_T__TraitClause_0___is_some(X, _0, \
                                                                     _1)    \
  ((X)->tag == 1)

// This is needed for ML-DSA
static inline uint8_t
core_ops_bit__core__ops__bit__BitAnd_u8__u8__for__0__u8___bitand(
    const uint8_t *x0, uint8_t x1) {
  return Eurydice_bitand_pv_u8(x0, x1);
}

// This is needed for ML-DSA
static inline uint8_t
core_ops_bit__core__ops__bit__Shr_i32__u8__for__0__u8___shr(const uint8_t *x0,
                                                            int32_t x1) {
  return Eurydice_shr_pv_u8(x0, x1);
}

#ifndef KRML_HOST_EPRINTF
#define KRML_HOST_EPRINTF(...) fprintf(stderr, __VA_ARGS__)
#elif !(defined KRML_HOST_EPRINTF) && defined(_MSC_VER)
#define KRML_HOST_EPRINTF(...) fprintf(stderr, __VA_ARGS__)
#endif

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_custom_glue_H_DEFINED
#endif /* internal_libcrux_iot_custom_glue_H */
