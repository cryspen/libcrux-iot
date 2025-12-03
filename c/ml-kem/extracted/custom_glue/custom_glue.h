/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 */

#ifndef internal_libcrux_iot_custom_glue_H
#define internal_libcrux_iot_custom_glue_H

#include "../eurydice-include/eurydice/base.h"

#if defined(__cplusplus)
extern "C" {
#endif

// The following needed for SHA3
static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1) {
  return (x0 << x1) | (x0 >> ((-x1) & 31));
}

// The following needed for ML-KEM
#define core_array___Array_T__N___as_mut_slice(len_, ptr_, t, ret_t) \
  (KRML_CLITERAL(ret_t){EURYDICE_CFIELD(.ptr =)(ptr_)->data,         \
                        EURYDICE_CFIELD(.meta =) len_})

#define Eurydice_slice_eq_shared(s1, s2, t, _) \
  ((s1)->meta == (s2)->meta &&                 \
   memcmp((s1)->ptr, (s2)->ptr, (s1)->meta * sizeof(t)) == 0)

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_custom_glue_H_DEFINED
#endif /* internal_libcrux_iot_custom_glue_H */
