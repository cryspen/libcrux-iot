/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 2381cbc416ef2ad0b561c362c500bc84f36b6785
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: d9eca8f974e7674039ae93714a8d3123efc52846
 */

#ifndef internal_librux_iot_core_H
#define internal_librux_iot_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../librux_iot_core.h"

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_10;

static inline uint32_t core_num__u32__from_le_bytes(uint8_t x0[4U]);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline void core_num__u32__to_le_bytes(uint32_t x0, uint8_t x1[4U]);

extern uint64_t
libcrux_secrets_int__libcrux_secrets__int__CastOps_for_u32__as_u64(uint32_t x0);

extern uint32_t
libcrux_secrets_int__libcrux_secrets__int__CastOps_for_u64__as_u32(uint64_t x0);

/**
A monomorphic instance of core.result.Result
with types uint8_t[4size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_12_s {
  core_result_Result_10 tag;
  union {
    uint8_t case_Ok[4U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_12;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[4size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_0a(core_result_Result_12 self, uint8_t ret[4U]);

#if defined(__cplusplus)
}
#endif

#define internal_librux_iot_core_H_DEFINED
#endif /* internal_librux_iot_core_H */
