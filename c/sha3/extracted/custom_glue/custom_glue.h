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

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_custom_glue_H_DEFINED
#endif /* internal_libcrux_iot_custom_glue_H */
