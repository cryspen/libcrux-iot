/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon:
 * Eurydice:
 * Karamel:
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: ded8c0f46a4ee8f93a6474c5aec0b9f13c3501c5
 */

#include "internal/libcrux_mlkem_iot.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_iot_sha3.h"
#include "libcrux_core.h"
#include "libcrux_iot_sha3.h"

KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_G(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_iot_sha3_portable_sha512(output, input);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_H(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_iot_sha3_portable_sha256(output, input);
}

inline void libcrux_iot_ml_kem_hash_functions_portable_PRFxN(
    Eurydice_slice input, Eurydice_slice outputs, size_t out_len) {
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(input, uint8_t[33U]);
       i++) {
    size_t i0 = i;
    libcrux_iot_sha3_portable_shake256(
        Eurydice_slice_subslice3(outputs, i0 * out_len,
                                 (i0 + (size_t)1U) * out_len, uint8_t *),
        Eurydice_array_to_slice(
            (size_t)33U,
            Eurydice_slice_index(input, i0, uint8_t[33U], uint8_t(*)[33U]),
            uint8_t));
  }
}

KRML_MUSTINLINE libcrux_iot_ml_kem_hash_functions_portable_PortableHash
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final(
    Eurydice_slice input) {
  libcrux_iot_sha3_state_KeccakState shake128_state[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  shake128_state[i] =
                      libcrux_iot_sha3_portable_incremental_shake128_init(););
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(input, uint8_t[34U]);
       i++) {
    size_t i0 = i;
    libcrux_iot_sha3_portable_incremental_shake128_absorb_final(
        &shake128_state[i0],
        Eurydice_array_to_slice(
            (size_t)34U,
            Eurydice_slice_index(input, i0, uint8_t[34U], uint8_t(*)[34U]),
            uint8_t));
  }
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_iot_sha3_state_KeccakState copy_of_shake128_state[4U];
  memcpy(copy_of_shake128_state, shake128_state,
         (size_t)4U * sizeof(libcrux_iot_sha3_state_KeccakState));
  libcrux_iot_ml_kem_hash_functions_portable_PortableHash lit;
  memcpy(lit.shake128_state, copy_of_shake128_state,
         (size_t)4U * sizeof(libcrux_iot_sha3_state_KeccakState));
  return lit;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
    libcrux_iot_ml_kem_hash_functions_portable_PortableHash *st,
    Eurydice_slice outputs) {
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(outputs, uint8_t[504U]);
       i++) {
    size_t i0 = i;
    libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
        &st->shake128_state[i0],
        Eurydice_array_to_slice(
            (size_t)504U,
            Eurydice_slice_index(outputs, i0, uint8_t[504U], uint8_t(*)[504U]),
            uint8_t));
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
    libcrux_iot_ml_kem_hash_functions_portable_PortableHash *st,
    Eurydice_slice outputs) {
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(outputs, uint8_t[168U]);
       i++) {
    size_t i0 = i;
    libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
        &st->shake128_state[i0],
        Eurydice_array_to_slice(
            (size_t)168U,
            Eurydice_slice_index(outputs, i0, uint8_t[168U], uint8_t(*)[168U]),
            uint8_t));
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_G_07(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_iot_ml_kem_hash_functions_portable_G(input, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_H_07(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_iot_ml_kem_hash_functions_portable_H(input, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
inline void libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
    Eurydice_slice input, Eurydice_slice outputs, size_t out_len) {
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN(input, outputs, out_len);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE libcrux_iot_ml_kem_hash_functions_portable_PortableHash
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
    Eurydice_slice input) {
  return libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final(
      input);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
    libcrux_iot_ml_kem_hash_functions_portable_PortableHash *self,
    Eurydice_slice output) {
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
      self, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
    libcrux_iot_ml_kem_hash_functions_portable_PortableHash *self,
    Eurydice_slice output) {
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
      self, output);
}

static const int16_t ZETAS_TIMES_MONTGOMERY_R[128U] = {
    (int16_t)-1044, (int16_t)-758,  (int16_t)-359,  (int16_t)-1517,
    (int16_t)1493,  (int16_t)1422,  (int16_t)287,   (int16_t)202,
    (int16_t)-171,  (int16_t)622,   (int16_t)1577,  (int16_t)182,
    (int16_t)962,   (int16_t)-1202, (int16_t)-1474, (int16_t)1468,
    (int16_t)573,   (int16_t)-1325, (int16_t)264,   (int16_t)383,
    (int16_t)-829,  (int16_t)1458,  (int16_t)-1602, (int16_t)-130,
    (int16_t)-681,  (int16_t)1017,  (int16_t)732,   (int16_t)608,
    (int16_t)-1542, (int16_t)411,   (int16_t)-205,  (int16_t)-1571,
    (int16_t)1223,  (int16_t)652,   (int16_t)-552,  (int16_t)1015,
    (int16_t)-1293, (int16_t)1491,  (int16_t)-282,  (int16_t)-1544,
    (int16_t)516,   (int16_t)-8,    (int16_t)-320,  (int16_t)-666,
    (int16_t)-1618, (int16_t)-1162, (int16_t)126,   (int16_t)1469,
    (int16_t)-853,  (int16_t)-90,   (int16_t)-271,  (int16_t)830,
    (int16_t)107,   (int16_t)-1421, (int16_t)-247,  (int16_t)-951,
    (int16_t)-398,  (int16_t)961,   (int16_t)-1508, (int16_t)-725,
    (int16_t)448,   (int16_t)-1065, (int16_t)677,   (int16_t)-1275,
    (int16_t)-1103, (int16_t)430,   (int16_t)555,   (int16_t)843,
    (int16_t)-1251, (int16_t)871,   (int16_t)1550,  (int16_t)105,
    (int16_t)422,   (int16_t)587,   (int16_t)177,   (int16_t)-235,
    (int16_t)-291,  (int16_t)-460,  (int16_t)1574,  (int16_t)1653,
    (int16_t)-246,  (int16_t)778,   (int16_t)1159,  (int16_t)-147,
    (int16_t)-777,  (int16_t)1483,  (int16_t)-602,  (int16_t)1119,
    (int16_t)-1590, (int16_t)644,   (int16_t)-872,  (int16_t)349,
    (int16_t)418,   (int16_t)329,   (int16_t)-156,  (int16_t)-75,
    (int16_t)817,   (int16_t)1097,  (int16_t)603,   (int16_t)610,
    (int16_t)1322,  (int16_t)-1285, (int16_t)-1465, (int16_t)384,
    (int16_t)-1215, (int16_t)-136,  (int16_t)1218,  (int16_t)-1335,
    (int16_t)-874,  (int16_t)220,   (int16_t)-1187, (int16_t)-1659,
    (int16_t)-1185, (int16_t)-1530, (int16_t)-1278, (int16_t)794,
    (int16_t)-1510, (int16_t)-854,  (int16_t)-870,  (int16_t)478,
    (int16_t)-108,  (int16_t)-308,  (int16_t)996,   (int16_t)991,
    (int16_t)958,   (int16_t)-1460, (int16_t)1522,  (int16_t)1628};

static KRML_MUSTINLINE int16_t zeta(size_t i) {
  return ZETAS_TIMES_MONTGOMERY_R[i];
}

#define VECTORS_IN_RING_ELEMENT                                \
  (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / \
   LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR)

KRML_MUSTINLINE libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
libcrux_iot_ml_kem_vector_portable_vector_type_zero(void) {
  return (KRML_CLITERAL(
      libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector){
      .elements = {0U}});
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
libcrux_iot_ml_kem_vector_portable_ZERO_4e(void) {
  return libcrux_iot_ml_kem_vector_portable_vector_type_zero();
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t uu____0[16U];
  core_result_Result_0a dst;
  Eurydice_slice_to_array2(
      &dst, Eurydice_slice_subslice3(array, (size_t)0U, (size_t)16U, int16_t *),
      Eurydice_slice, int16_t[16U], core_array_TryFromSliceError);
  core_result_unwrap_26_00(dst, uu____0);
  memcpy(out->elements, uu____0, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_from_i16_array_4e(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_vector_type_from_i16_array(array, out);
}

/**
 Signed Montgomery Reduction

 Given an input `value`, `montgomery_reduce` outputs a representative `o`
 such that:

 - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
 - the absolute value of `o` is bound as follows:

 `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665

 In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <=
 FIELD_MODULUS-1`. And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <=
 FIELD_MODULUS + 1664

*/
int16_t libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
    int32_t value) {
  int32_t k =
      (int32_t)(int16_t)value *
      (int32_t)
          LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
  int32_t k_times_modulus =
      (int32_t)(int16_t)k *
      (int32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
  int16_t c =
      (int16_t)(k_times_modulus >>
                (uint32_t)
                    LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int16_t value_high =
      (int16_t)(value >>
                (uint32_t)
                    LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  return value_high - c;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_vector_type_reducing_from_i32_array(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      out->elements[i0] =
          libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
              Eurydice_slice_index(array, i0, int32_t, int32_t *)););
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_reducing_from_i32_array_4e(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_vector_type_reducing_from_i32_array(array,
                                                                         out);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_vector_type_to_i16_array(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *x,
    Eurydice_slice out) {
  Eurydice_slice uu____0 = out;
  Eurydice_slice_copy(uu____0,
                      core_array___Array_T__N___as_slice(
                          (size_t)16U, x->elements, int16_t, Eurydice_slice),
                      int16_t);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_to_i16_array_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *x,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_vector_type_to_i16_array(x, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_vector_type_from_bytes(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    out->elements[i0] =
        (int16_t)Eurydice_slice_index(array, (size_t)2U * i0, uint8_t,
                                      uint8_t *)
            << 8U |
        (int16_t)Eurydice_slice_index(array, (size_t)2U * i0 + (size_t)1U,
                                      uint8_t, uint8_t *);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_from_bytes_4e(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_vector_type_from_bytes(array, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_vector_type_to_bytes(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector x,
    Eurydice_slice bytes) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    Eurydice_slice_index(bytes, (size_t)2U * i0, uint8_t, uint8_t *) =
        (uint8_t)(x.elements[i0] >> 8U);
    Eurydice_slice_index(bytes, (size_t)2U * i0 + (size_t)1U, uint8_t,
                         uint8_t *) = (uint8_t)x.elements[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_to_bytes_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector x,
    Eurydice_slice bytes) {
  libcrux_iot_ml_kem_vector_portable_vector_type_to_bytes(x, bytes);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_add(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->elements[uu____0] = lhs->elements[uu____0] + rhs->elements[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_add_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_sub(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->elements[uu____0] = lhs->elements[uu____0] - rhs->elements[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_sub_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_sub(lhs, rhs);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_negate(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec->elements[i0] = -vec->elements[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_negate_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_negate(vec);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->elements[uu____0] = vec->elements[uu____0] * c;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_multiply_by_constant_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_multiply_by_constant(vec, c);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->elements[uu____0] = vec->elements[uu____0] & c;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(vec,
                                                                          c);
}

/**
 Note: This function is not secret independent
 Only use with public values.
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    if (vec->elements[i0] >= (int16_t)3329) {
      size_t uu____0 = i0;
      vec->elements[uu____0] = vec->elements[uu____0] - (int16_t)3329;
    }
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_cond_subtract_3329_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_cond_subtract_3329(vec);
}

/**
 Signed Barrett Reduction

 Given an input `value`, `barrett_reduce` outputs a representative `result`
 such that:

 - result ≡ value (mod FIELD_MODULUS)
 - the absolute value of `result` is bound as follows:

 `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)

 Note: The input bound is 28296 to prevent overflow in the multiplication of
 quotient by FIELD_MODULUS

*/
KRML_MUSTINLINE int16_t
libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
    int16_t value) {
  int32_t t =
      (int32_t)value *
          LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER +
      (LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_R >> 1U);
  int16_t quotient =
      (int16_t)(t >> (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT);
  return value - quotient * LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t vi =
        libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
            vec->elements[i0]);
    vec->elements[i0] = vi;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce(vec);
}

/**
 If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
 `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
 `x · y`, as follows:

    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`

 `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a
 representative `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod
 FIELD_MODULUS)`.
*/
KRML_MUSTINLINE int16_t
libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int16_t fe, int16_t fer) {
  int32_t product = (int32_t)fe * (int32_t)fer;
  return libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
      product);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec->elements[i0] =
        libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
            vec->elements[i0], c);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t r) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
      vec, r);
}

/**
 The `compress_*` functions implement the `Compress` function specified in the
 NIST FIPS 203 standard (Page 18, Expression 4.5), which is defined as:

 ```plaintext
 Compress_d: ℤq -> ℤ_{2ᵈ}
 Compress_d(x) = ⌈(2ᵈ/q)·x⌋
 ```

 Since `⌈x⌋ = ⌊x + 1/2⌋` we have:

 ```plaintext
 Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
               = ⌊(2^{d+1}·x + q) / 2q⌋
 ```

 For further information about the function implementations, consult the
 `implementation_notes.pdf` document in this directory.

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
KRML_MUSTINLINE uint8_t
libcrux_iot_ml_kem_vector_portable_compress_compress_message_coefficient(
    uint16_t fe) {
  int16_t shifted = (int16_t)1664 - (int16_t)fe;
  int16_t mask = shifted >> 15U;
  int16_t shifted_to_positive = mask ^ shifted;
  int16_t shifted_positive_in_range = shifted_to_positive - (int16_t)832;
  int16_t r0 = shifted_positive_in_range >> 15U;
  int16_t r1 = r0 & (int16_t)1;
  return (uint8_t)r1;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_compress_compress_1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    a->elements[i0] = (int16_t)
        libcrux_iot_ml_kem_vector_portable_compress_compress_message_coefficient(
            (uint16_t)a->elements[i0]);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_compress_1_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  libcrux_iot_ml_kem_vector_portable_compress_compress_1(a);
}

KRML_MUSTINLINE uint32_t
libcrux_iot_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value) {
  return value & ((1U << (uint32_t)n) - 1U);
}

KRML_MUSTINLINE int16_t
libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe) {
  uint64_t compressed = (uint64_t)fe << (uint32_t)coefficient_bits;
  compressed = compressed + 1664ULL;
  compressed = compressed * 10321340ULL;
  compressed = compressed >> 35U;
  return (int16_t)
      libcrux_iot_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
          coefficient_bits, (uint32_t)compressed);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j) {
  int16_t t =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          vec->elements[j], zeta);
  int16_t a_minus_t = vec->elements[i] - t;
  int16_t a_plus_t = vec->elements[i] + t;
  vec->elements[j] = a_minus_t;
  vec->elements[i] = a_plus_t;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)0U,
                                                  (size_t)2U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)1U,
                                                  (size_t)3U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)4U,
                                                  (size_t)6U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)5U,
                                                  (size_t)7U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta2, (size_t)8U,
                                                  (size_t)10U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta2, (size_t)9U,
                                                  (size_t)11U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta3, (size_t)12U,
                                                  (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta3, (size_t)13U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_layer_1_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_1_step(a, zeta0, zeta1,
                                                          zeta2, zeta3);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)0U,
                                                  (size_t)4U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)1U,
                                                  (size_t)5U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)2U,
                                                  (size_t)6U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)3U,
                                                  (size_t)7U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)8U,
                                                  (size_t)12U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)9U,
                                                  (size_t)13U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)10U,
                                                  (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)11U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_layer_2_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_2_step(a, zeta0, zeta1);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)0U,
                                                  (size_t)8U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)1U,
                                                  (size_t)9U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)2U,
                                                  (size_t)10U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)3U,
                                                  (size_t)11U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)4U,
                                                  (size_t)12U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)5U,
                                                  (size_t)13U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)6U,
                                                  (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)7U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_layer_3_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j) {
  int16_t a_minus_b = vec->elements[j] - vec->elements[i];
  int16_t a_plus_b = vec->elements[j] + vec->elements[i];
  int16_t o0 =
      libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
          a_plus_b);
  int16_t o1 =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta);
  vec->elements[i] = o0;
  vec->elements[j] = o1;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)0U,
                                                      (size_t)2U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)1U,
                                                      (size_t)3U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)4U,
                                                      (size_t)6U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)5U,
                                                      (size_t)7U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta2, (size_t)8U,
                                                      (size_t)10U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta2, (size_t)9U,
                                                      (size_t)11U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta3, (size_t)12U,
                                                      (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta3, (size_t)13U,
                                                      (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_1_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(a, zeta0, zeta1,
                                                              zeta2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)0U,
                                                      (size_t)4U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)1U,
                                                      (size_t)5U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)2U,
                                                      (size_t)6U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)3U,
                                                      (size_t)7U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)8U,
                                                      (size_t)12U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)9U,
                                                      (size_t)13U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)10U,
                                                      (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)11U,
                                                      (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_2_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(a, zeta0, zeta1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)0U,
                                                      (size_t)8U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)1U,
                                                      (size_t)9U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)2U,
                                                      (size_t)10U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)3U,
                                                      (size_t)11U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)4U,
                                                      (size_t)12U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)5U,
                                                      (size_t)13U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)6U,
                                                      (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)7U,
                                                      (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_3_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *b,
    int16_t zeta, size_t i, Eurydice_slice out) {
  int16_t ai = a->elements[(size_t)2U * i];
  int16_t bi = b->elements[(size_t)2U * i];
  int16_t aj = a->elements[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->elements[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = (int32_t)ai * (int32_t)bi;
  int32_t bj_zeta_ = (int32_t)bj * (int32_t)zeta;
  int16_t bj_zeta =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          bj_zeta_);
  int32_t aj_bj_zeta = (int32_t)aj * (int32_t)bj_zeta;
  int32_t ai_bi_aj_bj = ai_bi + aj_bj_zeta;
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = (int32_t)ai * (int32_t)bj;
  int32_t aj_bi = (int32_t)aj * (int32_t)bi;
  int32_t ai_bj_aj_bi = ai_bj + aj_bi;
  int32_t o1 = ai_bj_aj_bi;
  size_t uu____0 = (size_t)2U * i;
  Eurydice_slice_index(out, uu____0, int32_t, int32_t *) =
      Eurydice_slice_index(out, uu____0, int32_t, int32_t *) + o0;
  size_t uu____1 = (size_t)2U * i + (size_t)1U;
  Eurydice_slice_index(out, uu____1, int32_t, int32_t *) =
      Eurydice_slice_index(out, uu____1, int32_t, int32_t *) + o1;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  int16_t nzeta0 = -zeta0;
  int16_t nzeta1 = -zeta1;
  int16_t nzeta2 = -zeta2;
  int16_t nzeta3 = -zeta3;
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, zeta0, (size_t)0U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, nzeta0, (size_t)1U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, zeta1, (size_t)2U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, nzeta1, (size_t)3U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, zeta2, (size_t)4U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, nzeta2, (size_t)5U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, zeta3, (size_t)6U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, nzeta3, (size_t)7U, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply(
      lhs, rhs, out, zeta0, zeta1, zeta2, zeta3);
}

/**
 Compute the product of two Kyber binomials with respect to the
 modulus `X² - zeta`.

 This function almost implements <strong>Algorithm 11</strong> of the
 NIST FIPS 203 standard, which is reproduced below:

 ```plaintext
 Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
 Input: γ ∈ ℤq.
 Output: c₀, c₁ ∈ ℤq.

 c₀ ← a₀·b₀ + a₁·b₁·γ
 c₁ ← a₀·b₁ + a₁·b₀
 return c₀, c₁
 ```
 We say "almost" because the coefficients output by this function are in
 the Montgomery domain (unlike in the specification).

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *b,
    int16_t zeta, size_t i, Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache) {
  int16_t ai = a->elements[(size_t)2U * i];
  int16_t bi = b->elements[(size_t)2U * i];
  int16_t aj = a->elements[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->elements[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = (int32_t)ai * (int32_t)bi;
  int32_t bj_zeta_ = (int32_t)bj * (int32_t)zeta;
  int16_t bj_zeta =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          bj_zeta_);
  cache->elements[i] = bj_zeta;
  int32_t aj_bj_zeta = (int32_t)aj * (int32_t)bj_zeta;
  int32_t ai_bi_aj_bj = ai_bi + aj_bj_zeta;
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = (int32_t)ai * (int32_t)bj;
  int32_t aj_bi = (int32_t)aj * (int32_t)bi;
  int32_t ai_bj_aj_bi = ai_bj + aj_bi;
  int32_t o1 = ai_bj_aj_bi;
  size_t uu____0 = (size_t)2U * i;
  Eurydice_slice_index(out, uu____0, int32_t, int32_t *) =
      Eurydice_slice_index(out, uu____0, int32_t, int32_t *) + o0;
  size_t uu____1 = (size_t)2U * i + (size_t)1U;
  Eurydice_slice_index(out, uu____1, int32_t, int32_t *) =
      Eurydice_slice_index(out, uu____1, int32_t, int32_t *) + o1;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_fill_cache(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  int16_t nzeta0 = -zeta0;
  int16_t nzeta1 = -zeta1;
  int16_t nzeta2 = -zeta2;
  int16_t nzeta3 = -zeta3;
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, zeta0, (size_t)0U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, nzeta0, (size_t)1U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, zeta1, (size_t)2U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, nzeta1, (size_t)3U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, zeta2, (size_t)4U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, nzeta2, (size_t)5U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, zeta3, (size_t)6U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, nzeta3, (size_t)7U, out, cache);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_fill_cache_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_fill_cache(
      lhs, rhs, out, cache, zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *b, size_t i,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache) {
  int16_t ai = a->elements[(size_t)2U * i];
  int16_t bi = b->elements[(size_t)2U * i];
  int16_t aj = a->elements[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->elements[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = (int32_t)ai * (int32_t)bi;
  int32_t aj_bj_zeta = (int32_t)aj * (int32_t)cache->elements[i];
  int32_t ai_bi_aj_bj = ai_bi + aj_bj_zeta;
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = (int32_t)ai * (int32_t)bj;
  int32_t aj_bi = (int32_t)aj * (int32_t)bi;
  int32_t ai_bj_aj_bi = ai_bj + aj_bi;
  int32_t o1 = ai_bj_aj_bi;
  size_t uu____0 = (size_t)2U * i;
  Eurydice_slice_index(out, uu____0, int32_t, int32_t *) =
      Eurydice_slice_index(out, uu____0, int32_t, int32_t *) + o0;
  size_t uu____1 = (size_t)2U * i + (size_t)1U;
  Eurydice_slice_index(out, uu____1, int32_t, int32_t *) =
      Eurydice_slice_index(out, uu____1, int32_t, int32_t *) + o1;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_use_cache(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)0U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)1U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)2U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)3U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)4U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)5U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)6U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)7U, out, cache);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_use_cache_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_use_cache(
      lhs, rhs, out, cache);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) =
      (((((((uint32_t)(uint8_t)v->elements[0U] |
            (uint32_t)(uint8_t)v->elements[1U] << 1U) |
           (uint32_t)(uint8_t)v->elements[2U] << 2U) |
          (uint32_t)(uint8_t)v->elements[3U] << 3U) |
         (uint32_t)(uint8_t)v->elements[4U] << 4U) |
        (uint32_t)(uint8_t)v->elements[5U] << 5U) |
       (uint32_t)(uint8_t)v->elements[6U] << 6U) |
      (uint32_t)(uint8_t)v->elements[7U] << 7U;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) =
      (((((((uint32_t)(uint8_t)v->elements[8U] |
            (uint32_t)(uint8_t)v->elements[9U] << 1U) |
           (uint32_t)(uint8_t)v->elements[10U] << 2U) |
          (uint32_t)(uint8_t)v->elements[11U] << 3U) |
         (uint32_t)(uint8_t)v->elements[12U] << 4U) |
        (uint32_t)(uint8_t)v->elements[13U] << 5U) |
       (uint32_t)(uint8_t)v->elements[14U] << 6U) |
      (uint32_t)(uint8_t)v->elements[15U] << 7U;
}

void libcrux_iot_ml_kem_vector_portable_serialize_1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_1(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_1_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_1(a, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_1(
    Eurydice_slice v,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  out->elements[0U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)0U, uint8_t, uint8_t *) &
                                1U);
  out->elements[1U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)0U, uint8_t, uint8_t *) >>
                                    1U &
                                1U);
  out->elements[2U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)0U, uint8_t, uint8_t *) >>
                                    2U &
                                1U);
  out->elements[3U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)0U, uint8_t, uint8_t *) >>
                                    3U &
                                1U);
  out->elements[4U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)0U, uint8_t, uint8_t *) >>
                                    4U &
                                1U);
  out->elements[5U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)0U, uint8_t, uint8_t *) >>
                                    5U &
                                1U);
  out->elements[6U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)0U, uint8_t, uint8_t *) >>
                                    6U &
                                1U);
  out->elements[7U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)0U, uint8_t, uint8_t *) >>
                                    7U &
                                1U);
  out->elements[8U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)1U, uint8_t, uint8_t *) &
                                1U);
  out->elements[9U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                    v, (size_t)1U, uint8_t, uint8_t *) >>
                                    1U &
                                1U);
  out->elements[10U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                     v, (size_t)1U, uint8_t, uint8_t *) >>
                                     2U &
                                 1U);
  out->elements[11U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                     v, (size_t)1U, uint8_t, uint8_t *) >>
                                     3U &
                                 1U);
  out->elements[12U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                     v, (size_t)1U, uint8_t, uint8_t *) >>
                                     4U &
                                 1U);
  out->elements[13U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                     v, (size_t)1U, uint8_t, uint8_t *) >>
                                     5U &
                                 1U);
  out->elements[14U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                     v, (size_t)1U, uint8_t, uint8_t *) >>
                                     6U &
                                 1U);
  out->elements[15U] = (int16_t)((uint32_t)Eurydice_slice_index(
                                     v, (size_t)1U, uint8_t, uint8_t *) >>
                                     7U &
                                 1U);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_1(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_1(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_1_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_deserialize_1(a, out);
}

KRML_MUSTINLINE uint8_t_x4
libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(Eurydice_slice v) {
  uint8_t result0 =
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *)
          << 4U |
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)0U, int16_t,
                                              int16_t *);
  uint8_t result1 =
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *)
          << 4U |
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)2U, int16_t,
                                              int16_t *);
  uint8_t result2 =
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *)
          << 4U |
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)4U, int16_t,
                                              int16_t *);
  uint8_t result3 =
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *)
          << 4U |
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)6U, int16_t,
                                              int16_t *);
  return (KRML_CLITERAL(uint8_t_x4){
      .fst = result0, .snd = result1, .thd = result2, .f3 = result3});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  uint8_t_x4 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)0U, (size_t)8U,
                                      int16_t *));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) = uu____0.fst;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) = uu____1;
  Eurydice_slice_index(out, (size_t)2U, uint8_t, uint8_t *) = uu____2;
  Eurydice_slice_index(out, (size_t)3U, uint8_t, uint8_t *) = uu____3;
  uint8_t_x4 uu____4 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)8U, (size_t)16U,
                                      int16_t *));
  uint8_t uu____5 = uu____4.snd;
  uint8_t uu____6 = uu____4.thd;
  uint8_t uu____7 = uu____4.f3;
  Eurydice_slice_index(out, (size_t)4U, uint8_t, uint8_t *) = uu____4.fst;
  Eurydice_slice_index(out, (size_t)5U, uint8_t, uint8_t *) = uu____5;
  Eurydice_slice_index(out, (size_t)6U, uint8_t, uint8_t *) = uu____6;
  Eurydice_slice_index(out, (size_t)7U, uint8_t, uint8_t *) = uu____7;
}

void libcrux_iot_ml_kem_vector_portable_serialize_4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_4(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_4_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_4(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_slice bytes) {
  int16_t v0 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)0U,
                                                        uint8_t, uint8_t *) &
                         15U);
  int16_t v1 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)0U,
                                                        uint8_t, uint8_t *) >>
                             4U &
                         15U);
  int16_t v2 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)1U,
                                                        uint8_t, uint8_t *) &
                         15U);
  int16_t v3 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)1U,
                                                        uint8_t, uint8_t *) >>
                             4U &
                         15U);
  int16_t v4 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)2U,
                                                        uint8_t, uint8_t *) &
                         15U);
  int16_t v5 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)2U,
                                                        uint8_t, uint8_t *) >>
                             4U &
                         15U);
  int16_t v6 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)3U,
                                                        uint8_t, uint8_t *) &
                         15U);
  int16_t v7 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)3U,
                                                        uint8_t, uint8_t *) >>
                             4U &
                         15U);
  return (KRML_CLITERAL(int16_t_x8){.fst = v0,
                                    .snd = v1,
                                    .thd = v2,
                                    .f3 = v3,
                                    .f4 = v4,
                                    .f5 = v5,
                                    .f6 = v6,
                                    .f7 = v7});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
          Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)4U, uint8_t *));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->elements[0U] = uu____0.fst;
  out->elements[1U] = uu____1;
  out->elements[2U] = uu____2;
  out->elements[3U] = uu____3;
  out->elements[4U] = uu____4;
  out->elements[5U] = uu____5;
  out->elements[6U] = uu____6;
  out->elements[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
          Eurydice_slice_subslice3(bytes, (size_t)4U, (size_t)8U, uint8_t *));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->elements[8U] = uu____8.fst;
  out->elements[9U] = uu____9;
  out->elements[10U] = uu____10;
  out->elements[11U] = uu____11;
  out->elements[12U] = uu____12;
  out->elements[13U] = uu____13;
  out->elements[14U] = uu____14;
  out->elements[15U] = uu____15;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_4(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_4_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_deserialize_4(a, out);
}

KRML_MUSTINLINE uint8_t_x5
libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(Eurydice_slice v) {
  uint8_t r0 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) |
                Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) << 5U);
  uint8_t r1 =
      (uint8_t)((Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 3U |
                 Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *)
                     << 2U) |
                Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) << 7U);
  uint8_t r2 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) >> 1U |
                Eurydice_slice_index(v, (size_t)4U, int16_t, int16_t *) << 4U);
  uint8_t r3 =
      (uint8_t)((Eurydice_slice_index(v, (size_t)4U, int16_t, int16_t *) >> 4U |
                 Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *)
                     << 1U) |
                Eurydice_slice_index(v, (size_t)6U, int16_t, int16_t *) << 6U);
  uint8_t r4 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)6U, int16_t, int16_t *) >> 2U |
                Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *) << 3U);
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = r0, .snd = r1, .thd = r2, .f3 = r3, .f4 = r4});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_5(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  uint8_t_x5 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)0U, (size_t)8U,
                                      int16_t *));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) = uu____0.fst;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) = uu____1;
  Eurydice_slice_index(out, (size_t)2U, uint8_t, uint8_t *) = uu____2;
  Eurydice_slice_index(out, (size_t)3U, uint8_t, uint8_t *) = uu____3;
  Eurydice_slice_index(out, (size_t)4U, uint8_t, uint8_t *) = uu____4;
  uint8_t_x5 uu____5 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)8U, (size_t)16U,
                                      int16_t *));
  uint8_t uu____6 = uu____5.snd;
  uint8_t uu____7 = uu____5.thd;
  uint8_t uu____8 = uu____5.f3;
  uint8_t uu____9 = uu____5.f4;
  Eurydice_slice_index(out, (size_t)5U, uint8_t, uint8_t *) = uu____5.fst;
  Eurydice_slice_index(out, (size_t)6U, uint8_t, uint8_t *) = uu____6;
  Eurydice_slice_index(out, (size_t)7U, uint8_t, uint8_t *) = uu____7;
  Eurydice_slice_index(out, (size_t)8U, uint8_t, uint8_t *) = uu____8;
  Eurydice_slice_index(out, (size_t)9U, uint8_t, uint8_t *) = uu____9;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_5(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_5(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_5_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_5(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
    Eurydice_slice bytes) {
  int16_t v0 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)0U,
                                                        uint8_t, uint8_t *) &
                         31U);
  int16_t v1 = (int16_t)(((uint32_t)Eurydice_slice_index(bytes, (size_t)1U,
                                                         uint8_t, uint8_t *) &
                          3U) << 3U |
                         (uint32_t)Eurydice_slice_index(bytes, (size_t)0U,
                                                        uint8_t, uint8_t *) >>
                             5U);
  int16_t v2 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)1U,
                                                        uint8_t, uint8_t *) >>
                             2U &
                         31U);
  int16_t v3 = (int16_t)(((uint32_t)Eurydice_slice_index(bytes, (size_t)2U,
                                                         uint8_t, uint8_t *) &
                          15U)
                             << 1U |
                         (uint32_t)Eurydice_slice_index(bytes, (size_t)1U,
                                                        uint8_t, uint8_t *) >>
                             7U);
  int16_t v4 = (int16_t)(((uint32_t)Eurydice_slice_index(bytes, (size_t)3U,
                                                         uint8_t, uint8_t *) &
                          1U) << 4U |
                         (uint32_t)Eurydice_slice_index(bytes, (size_t)2U,
                                                        uint8_t, uint8_t *) >>
                             4U);
  int16_t v5 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)3U,
                                                        uint8_t, uint8_t *) >>
                             1U &
                         31U);
  int16_t v6 = (int16_t)(((uint32_t)Eurydice_slice_index(bytes, (size_t)4U,
                                                         uint8_t, uint8_t *) &
                          7U) << 2U |
                         (uint32_t)Eurydice_slice_index(bytes, (size_t)3U,
                                                        uint8_t, uint8_t *) >>
                             6U);
  int16_t v7 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)4U,
                                                        uint8_t, uint8_t *) >>
                         3U);
  return (KRML_CLITERAL(int16_t_x8){.fst = v0,
                                    .snd = v1,
                                    .thd = v2,
                                    .f3 = v3,
                                    .f4 = v4,
                                    .f5 = v5,
                                    .f6 = v6,
                                    .f7 = v7});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
          Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)5U, uint8_t *));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->elements[0U] = uu____0.fst;
  out->elements[1U] = uu____1;
  out->elements[2U] = uu____2;
  out->elements[3U] = uu____3;
  out->elements[4U] = uu____4;
  out->elements[5U] = uu____5;
  out->elements[6U] = uu____6;
  out->elements[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
          Eurydice_slice_subslice3(bytes, (size_t)5U, (size_t)10U, uint8_t *));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->elements[8U] = uu____8.fst;
  out->elements[9U] = uu____9;
  out->elements[10U] = uu____10;
  out->elements[11U] = uu____11;
  out->elements[12U] = uu____12;
  out->elements[13U] = uu____13;
  out->elements[14U] = uu____14;
  out->elements[15U] = uu____15;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_5(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_5_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_deserialize_5(a, out);
}

KRML_MUSTINLINE uint8_t_x5
libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
    Eurydice_slice v) {
  uint8_t r0 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) &
                (int16_t)255);
  uint8_t r1 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)1U, int16_t,
                                                        int16_t *) &
                                   (int16_t)63)
                   << 2U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t,
                                                        int16_t *) >>
                                       8U &
                                   (int16_t)3);
  uint8_t r2 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)2U, int16_t,
                                                        int16_t *) &
                                   (int16_t)15)
                   << 4U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)1U, int16_t,
                                                        int16_t *) >>
                                       6U &
                                   (int16_t)15);
  uint8_t r3 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)3U, int16_t,
                                                        int16_t *) &
                                   (int16_t)3)
                   << 6U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)2U, int16_t,
                                                        int16_t *) >>
                                       4U &
                                   (int16_t)63);
  uint8_t r4 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) >> 2U &
                (int16_t)255);
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = r0, .snd = r1, .thd = r2, .f3 = r3, .f4 = r4});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_10(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  uint8_t_x5 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)0U, (size_t)4U,
                                      int16_t *));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) = uu____0.fst;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) = uu____1;
  Eurydice_slice_index(out, (size_t)2U, uint8_t, uint8_t *) = uu____2;
  Eurydice_slice_index(out, (size_t)3U, uint8_t, uint8_t *) = uu____3;
  Eurydice_slice_index(out, (size_t)4U, uint8_t, uint8_t *) = uu____4;
  uint8_t_x5 uu____5 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)4U, (size_t)8U,
                                      int16_t *));
  uint8_t uu____6 = uu____5.snd;
  uint8_t uu____7 = uu____5.thd;
  uint8_t uu____8 = uu____5.f3;
  uint8_t uu____9 = uu____5.f4;
  Eurydice_slice_index(out, (size_t)5U, uint8_t, uint8_t *) = uu____5.fst;
  Eurydice_slice_index(out, (size_t)6U, uint8_t, uint8_t *) = uu____6;
  Eurydice_slice_index(out, (size_t)7U, uint8_t, uint8_t *) = uu____7;
  Eurydice_slice_index(out, (size_t)8U, uint8_t, uint8_t *) = uu____8;
  Eurydice_slice_index(out, (size_t)9U, uint8_t, uint8_t *) = uu____9;
  uint8_t_x5 uu____10 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)8U, (size_t)12U,
                                      int16_t *));
  uint8_t uu____11 = uu____10.snd;
  uint8_t uu____12 = uu____10.thd;
  uint8_t uu____13 = uu____10.f3;
  uint8_t uu____14 = uu____10.f4;
  Eurydice_slice_index(out, (size_t)10U, uint8_t, uint8_t *) = uu____10.fst;
  Eurydice_slice_index(out, (size_t)11U, uint8_t, uint8_t *) = uu____11;
  Eurydice_slice_index(out, (size_t)12U, uint8_t, uint8_t *) = uu____12;
  Eurydice_slice_index(out, (size_t)13U, uint8_t, uint8_t *) = uu____13;
  Eurydice_slice_index(out, (size_t)14U, uint8_t, uint8_t *) = uu____14;
  uint8_t_x5 uu____15 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)12U, (size_t)16U,
                                      int16_t *));
  uint8_t uu____16 = uu____15.snd;
  uint8_t uu____17 = uu____15.thd;
  uint8_t uu____18 = uu____15.f3;
  uint8_t uu____19 = uu____15.f4;
  Eurydice_slice_index(out, (size_t)15U, uint8_t, uint8_t *) = uu____15.fst;
  Eurydice_slice_index(out, (size_t)16U, uint8_t, uint8_t *) = uu____16;
  Eurydice_slice_index(out, (size_t)17U, uint8_t, uint8_t *) = uu____17;
  Eurydice_slice_index(out, (size_t)18U, uint8_t, uint8_t *) = uu____18;
  Eurydice_slice_index(out, (size_t)19U, uint8_t, uint8_t *) = uu____19;
}

void libcrux_iot_ml_kem_vector_portable_serialize_10(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_10(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_10_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_10(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_slice bytes) {
  int16_t r0 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) &
       (int16_t)3)
          << 8U |
      ((int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *) &
       (int16_t)255);
  int16_t r1 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) &
       (int16_t)15)
          << 6U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) >>
          2U;
  int16_t r2 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) &
       (int16_t)63)
          << 4U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) >>
          4U;
  int16_t r3 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *)
          << 2U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) >>
          6U;
  int16_t r4 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *) &
       (int16_t)3)
          << 8U |
      ((int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *) &
       (int16_t)255);
  int16_t r5 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *) &
       (int16_t)15)
          << 6U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *) >>
          2U;
  int16_t r6 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *) &
       (int16_t)63)
          << 4U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *) >>
          4U;
  int16_t r7 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *)
          << 2U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *) >>
          6U;
  return (KRML_CLITERAL(int16_t_x8){.fst = r0,
                                    .snd = r1,
                                    .thd = r2,
                                    .f3 = r3,
                                    .f4 = r4,
                                    .f5 = r5,
                                    .f6 = r6,
                                    .f7 = r7});
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)10U, uint8_t *));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->elements[0U] = uu____0.fst;
  out->elements[1U] = uu____1;
  out->elements[2U] = uu____2;
  out->elements[3U] = uu____3;
  out->elements[4U] = uu____4;
  out->elements[5U] = uu____5;
  out->elements[6U] = uu____6;
  out->elements[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice3(bytes, (size_t)10U, (size_t)20U, uint8_t *));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->elements[8U] = uu____8.fst;
  out->elements[9U] = uu____9;
  out->elements[10U] = uu____10;
  out->elements[11U] = uu____11;
  out->elements[12U] = uu____12;
  out->elements[13U] = uu____13;
  out->elements[14U] = uu____14;
  out->elements[15U] = uu____15;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_10(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_10_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_deserialize_10(a, out);
}

KRML_MUSTINLINE uint8_t_x11
libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
    Eurydice_slice v) {
  uint8_t r0 = (uint8_t)Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *);
  uint8_t r1 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)1U, int16_t,
                                                        int16_t *) &
                                   (int16_t)31)
                   << 3U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t,
                                                        int16_t *) >>
                                   8U);
  uint8_t r2 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)2U, int16_t,
                                                        int16_t *) &
                                   (int16_t)3)
                   << 6U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)1U, int16_t,
                                                        int16_t *) >>
                                   5U);
  uint8_t r3 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) >> 2U &
                (int16_t)255);
  uint8_t r4 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)3U, int16_t,
                                                        int16_t *) &
                                   (int16_t)127)
                   << 1U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)2U, int16_t,
                                                        int16_t *) >>
                                   10U);
  uint8_t r5 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)4U, int16_t,
                                                        int16_t *) &
                                   (int16_t)15)
                   << 4U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)3U, int16_t,
                                                        int16_t *) >>
                                   7U);
  uint8_t r6 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)5U, int16_t,
                                                        int16_t *) &
                                   (int16_t)1)
                   << 7U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)4U, int16_t,
                                                        int16_t *) >>
                                   4U);
  uint8_t r7 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *) >> 1U &
                (int16_t)255);
  uint8_t r8 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)6U, int16_t,
                                                        int16_t *) &
                                   (int16_t)63)
                   << 2U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)5U, int16_t,
                                                        int16_t *) >>
                                   9U);
  uint8_t r9 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)7U, int16_t,
                                                        int16_t *) &
                                   (int16_t)7)
                   << 5U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)6U, int16_t,
                                                        int16_t *) >>
                                   6U);
  uint8_t r10 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *) >> 3U);
  return (KRML_CLITERAL(uint8_t_x11){.fst = r0,
                                     .snd = r1,
                                     .thd = r2,
                                     .f3 = r3,
                                     .f4 = r4,
                                     .f5 = r5,
                                     .f6 = r6,
                                     .f7 = r7,
                                     .f8 = r8,
                                     .f9 = r9,
                                     .f10 = r10});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_11(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  uint8_t_x11 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)0U, (size_t)8U,
                                      int16_t *));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  uint8_t uu____5 = uu____0.f5;
  uint8_t uu____6 = uu____0.f6;
  uint8_t uu____7 = uu____0.f7;
  uint8_t uu____8 = uu____0.f8;
  uint8_t uu____9 = uu____0.f9;
  uint8_t uu____10 = uu____0.f10;
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) = uu____0.fst;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) = uu____1;
  Eurydice_slice_index(out, (size_t)2U, uint8_t, uint8_t *) = uu____2;
  Eurydice_slice_index(out, (size_t)3U, uint8_t, uint8_t *) = uu____3;
  Eurydice_slice_index(out, (size_t)4U, uint8_t, uint8_t *) = uu____4;
  Eurydice_slice_index(out, (size_t)5U, uint8_t, uint8_t *) = uu____5;
  Eurydice_slice_index(out, (size_t)6U, uint8_t, uint8_t *) = uu____6;
  Eurydice_slice_index(out, (size_t)7U, uint8_t, uint8_t *) = uu____7;
  Eurydice_slice_index(out, (size_t)8U, uint8_t, uint8_t *) = uu____8;
  Eurydice_slice_index(out, (size_t)9U, uint8_t, uint8_t *) = uu____9;
  Eurydice_slice_index(out, (size_t)10U, uint8_t, uint8_t *) = uu____10;
  uint8_t_x11 uu____11 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)8U, (size_t)16U,
                                      int16_t *));
  uint8_t uu____12 = uu____11.snd;
  uint8_t uu____13 = uu____11.thd;
  uint8_t uu____14 = uu____11.f3;
  uint8_t uu____15 = uu____11.f4;
  uint8_t uu____16 = uu____11.f5;
  uint8_t uu____17 = uu____11.f6;
  uint8_t uu____18 = uu____11.f7;
  uint8_t uu____19 = uu____11.f8;
  uint8_t uu____20 = uu____11.f9;
  uint8_t uu____21 = uu____11.f10;
  Eurydice_slice_index(out, (size_t)11U, uint8_t, uint8_t *) = uu____11.fst;
  Eurydice_slice_index(out, (size_t)12U, uint8_t, uint8_t *) = uu____12;
  Eurydice_slice_index(out, (size_t)13U, uint8_t, uint8_t *) = uu____13;
  Eurydice_slice_index(out, (size_t)14U, uint8_t, uint8_t *) = uu____14;
  Eurydice_slice_index(out, (size_t)15U, uint8_t, uint8_t *) = uu____15;
  Eurydice_slice_index(out, (size_t)16U, uint8_t, uint8_t *) = uu____16;
  Eurydice_slice_index(out, (size_t)17U, uint8_t, uint8_t *) = uu____17;
  Eurydice_slice_index(out, (size_t)18U, uint8_t, uint8_t *) = uu____18;
  Eurydice_slice_index(out, (size_t)19U, uint8_t, uint8_t *) = uu____19;
  Eurydice_slice_index(out, (size_t)20U, uint8_t, uint8_t *) = uu____20;
  Eurydice_slice_index(out, (size_t)21U, uint8_t, uint8_t *) = uu____21;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_11(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_11(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_11_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_11(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
    Eurydice_slice bytes) {
  int16_t r0 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) &
       (int16_t)7)
          << 8U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
  int16_t r1 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) &
       (int16_t)63)
          << 5U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) >>
          3U;
  int16_t r2 =
      (((int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *) &
        (int16_t)1)
           << 10U |
       (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *)
           << 2U) |
      (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) >>
          6U;
  int16_t r3 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *) &
       (int16_t)15)
          << 7U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *) >>
          1U;
  int16_t r4 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *) &
       (int16_t)127)
          << 4U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *) >>
          4U;
  int16_t r5 =
      (((int16_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *) &
        (int16_t)3)
           << 9U |
       (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *)
           << 1U) |
      (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *) >>
          7U;
  int16_t r6 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *) &
       (int16_t)31)
          << 6U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *) >>
          2U;
  int16_t r7 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)10U, uint8_t, uint8_t *)
          << 3U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *) >>
          5U;
  return (KRML_CLITERAL(int16_t_x8){.fst = r0,
                                    .snd = r1,
                                    .thd = r2,
                                    .f3 = r3,
                                    .f4 = r4,
                                    .f5 = r5,
                                    .f6 = r6,
                                    .f7 = r7});
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
          Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)11U, uint8_t *));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->elements[0U] = uu____0.fst;
  out->elements[1U] = uu____1;
  out->elements[2U] = uu____2;
  out->elements[3U] = uu____3;
  out->elements[4U] = uu____4;
  out->elements[5U] = uu____5;
  out->elements[6U] = uu____6;
  out->elements[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
          Eurydice_slice_subslice3(bytes, (size_t)11U, (size_t)22U, uint8_t *));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->elements[8U] = uu____8.fst;
  out->elements[9U] = uu____9;
  out->elements[10U] = uu____10;
  out->elements[11U] = uu____11;
  out->elements[12U] = uu____12;
  out->elements[13U] = uu____13;
  out->elements[14U] = uu____14;
  out->elements[15U] = uu____15;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_11(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_11_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_deserialize_11(a, out);
}

KRML_MUSTINLINE uint8_t_x3
libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
    Eurydice_slice v) {
  uint8_t r0 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) &
                (int16_t)255);
  uint8_t r1 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) >> 8U |
                (Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) &
                 (int16_t)15)
                    << 4U);
  uint8_t r2 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 4U &
                (int16_t)255);
  return (KRML_CLITERAL(uint8_t_x3){.fst = r0, .snd = r1, .thd = r2});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_12(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  uint8_t_x3 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)0U, (size_t)2U,
                                      int16_t *));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) = uu____0.fst;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) = uu____1;
  Eurydice_slice_index(out, (size_t)2U, uint8_t, uint8_t *) = uu____2;
  uint8_t_x3 uu____3 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)2U, (size_t)4U,
                                      int16_t *));
  uint8_t uu____4 = uu____3.snd;
  uint8_t uu____5 = uu____3.thd;
  Eurydice_slice_index(out, (size_t)3U, uint8_t, uint8_t *) = uu____3.fst;
  Eurydice_slice_index(out, (size_t)4U, uint8_t, uint8_t *) = uu____4;
  Eurydice_slice_index(out, (size_t)5U, uint8_t, uint8_t *) = uu____5;
  uint8_t_x3 uu____6 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)4U, (size_t)6U,
                                      int16_t *));
  uint8_t uu____7 = uu____6.snd;
  uint8_t uu____8 = uu____6.thd;
  Eurydice_slice_index(out, (size_t)6U, uint8_t, uint8_t *) = uu____6.fst;
  Eurydice_slice_index(out, (size_t)7U, uint8_t, uint8_t *) = uu____7;
  Eurydice_slice_index(out, (size_t)8U, uint8_t, uint8_t *) = uu____8;
  uint8_t_x3 uu____9 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)6U, (size_t)8U,
                                      int16_t *));
  uint8_t uu____10 = uu____9.snd;
  uint8_t uu____11 = uu____9.thd;
  Eurydice_slice_index(out, (size_t)9U, uint8_t, uint8_t *) = uu____9.fst;
  Eurydice_slice_index(out, (size_t)10U, uint8_t, uint8_t *) = uu____10;
  Eurydice_slice_index(out, (size_t)11U, uint8_t, uint8_t *) = uu____11;
  uint8_t_x3 uu____12 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)8U, (size_t)10U,
                                      int16_t *));
  uint8_t uu____13 = uu____12.snd;
  uint8_t uu____14 = uu____12.thd;
  Eurydice_slice_index(out, (size_t)12U, uint8_t, uint8_t *) = uu____12.fst;
  Eurydice_slice_index(out, (size_t)13U, uint8_t, uint8_t *) = uu____13;
  Eurydice_slice_index(out, (size_t)14U, uint8_t, uint8_t *) = uu____14;
  uint8_t_x3 uu____15 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)10U, (size_t)12U,
                                      int16_t *));
  uint8_t uu____16 = uu____15.snd;
  uint8_t uu____17 = uu____15.thd;
  Eurydice_slice_index(out, (size_t)15U, uint8_t, uint8_t *) = uu____15.fst;
  Eurydice_slice_index(out, (size_t)16U, uint8_t, uint8_t *) = uu____16;
  Eurydice_slice_index(out, (size_t)17U, uint8_t, uint8_t *) = uu____17;
  uint8_t_x3 uu____18 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)12U, (size_t)14U,
                                      int16_t *));
  uint8_t uu____19 = uu____18.snd;
  uint8_t uu____20 = uu____18.thd;
  Eurydice_slice_index(out, (size_t)18U, uint8_t, uint8_t *) = uu____18.fst;
  Eurydice_slice_index(out, (size_t)19U, uint8_t, uint8_t *) = uu____19;
  Eurydice_slice_index(out, (size_t)20U, uint8_t, uint8_t *) = uu____20;
  uint8_t_x3 uu____21 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)14U, (size_t)16U,
                                      int16_t *));
  uint8_t uu____22 = uu____21.snd;
  uint8_t uu____23 = uu____21.thd;
  Eurydice_slice_index(out, (size_t)21U, uint8_t, uint8_t *) = uu____21.fst;
  Eurydice_slice_index(out, (size_t)22U, uint8_t, uint8_t *) = uu____22;
  Eurydice_slice_index(out, (size_t)23U, uint8_t, uint8_t *) = uu____23;
}

void libcrux_iot_ml_kem_vector_portable_serialize_12(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_12(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_12_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_vector_portable_serialize_12(a, out);
}

KRML_MUSTINLINE int16_t_x2
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_slice bytes) {
  int16_t byte0 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
  int16_t byte1 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *);
  int16_t byte2 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *);
  int16_t r0 = (byte1 & (int16_t)15) << 8U | (byte0 & (int16_t)255);
  int16_t r1 = byte2 << 4U | (byte1 >> 4U & (int16_t)15);
  return (KRML_CLITERAL(int16_t_x2){.fst = r0, .snd = r1});
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t_x2 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)3U, uint8_t *));
  int16_t uu____1 = uu____0.snd;
  out->elements[0U] = uu____0.fst;
  out->elements[1U] = uu____1;
  int16_t_x2 uu____2 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)3U, (size_t)6U, uint8_t *));
  int16_t uu____3 = uu____2.snd;
  out->elements[2U] = uu____2.fst;
  out->elements[3U] = uu____3;
  int16_t_x2 uu____4 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)6U, (size_t)9U, uint8_t *));
  int16_t uu____5 = uu____4.snd;
  out->elements[4U] = uu____4.fst;
  out->elements[5U] = uu____5;
  int16_t_x2 uu____6 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)9U, (size_t)12U, uint8_t *));
  int16_t uu____7 = uu____6.snd;
  out->elements[6U] = uu____6.fst;
  out->elements[7U] = uu____7;
  int16_t_x2 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)12U, (size_t)15U, uint8_t *));
  int16_t uu____9 = uu____8.snd;
  out->elements[8U] = uu____8.fst;
  out->elements[9U] = uu____9;
  int16_t_x2 uu____10 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)15U, (size_t)18U, uint8_t *));
  int16_t uu____11 = uu____10.snd;
  out->elements[10U] = uu____10.fst;
  out->elements[11U] = uu____11;
  int16_t_x2 uu____12 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)18U, (size_t)21U, uint8_t *));
  int16_t uu____13 = uu____12.snd;
  out->elements[12U] = uu____12.fst;
  out->elements[13U] = uu____13;
  int16_t_x2 uu____14 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)21U, (size_t)24U, uint8_t *));
  int16_t uu____15 = uu____14.snd;
  out->elements[14U] = uu____14.fst;
  out->elements[15U] = uu____15;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_12(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12(a, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_iot_ml_kem_vector_portable_deserialize_12(a, out);
}

KRML_MUSTINLINE size_t libcrux_iot_ml_kem_vector_portable_sampling_rej_sample(
    Eurydice_slice a, Eurydice_slice result) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(a, uint8_t) / (size_t)3U;
       i++) {
    size_t i0 = i;
    int16_t b1 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)0U,
                                               uint8_t, uint8_t *);
    int16_t b2 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)1U,
                                               uint8_t, uint8_t *);
    int16_t b3 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)2U,
                                               uint8_t, uint8_t *);
    int16_t d1 = (b2 & (int16_t)15) << 8U | b1;
    int16_t d2 = b3 << 4U | b2 >> 4U;
    if (d1 < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
      if (sampled < (size_t)16U) {
        Eurydice_slice_index(result, sampled, int16_t, int16_t *) = d1;
        sampled++;
      }
    }
    if (d2 < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
      if (sampled < (size_t)16U) {
        Eurydice_slice_index(result, sampled, int16_t, int16_t *) = d2;
        sampled++;
      }
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE size_t libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
    Eurydice_slice a, Eurydice_slice out) {
  return libcrux_iot_ml_kem_vector_portable_sampling_rej_sample(a, out);
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
inline libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
libcrux_iot_ml_kem_vector_portable_vector_type_clone_9c(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *self) {
  return self[0U];
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.ZERO_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 ZERO_64_a7(void) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 lit;
  libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
      repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_iot_ml_kem_vector_portable_ZERO_4e(););
  memcpy(
      lit.coefficients, repeat_expression,
      (size_t)16U *
          sizeof(
              libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_iot_ml_kem::ind_cca::validate_public_key::closure<Vector, K,
PUBLIC_KEY_SIZE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.validate_public_key.call_mut_42 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_42_c5(
    void **_) {
  return ZERO_64_a7();
}

/**
 Only use with public values.

 This MUST NOT be used with secret inputs, like its caller
 `deserialize_ring_elements_reduced`.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_to_reduced_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_to_reduced_ring_element_a7(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(bytes,
                                                         &re->coefficients[i0]);
    libcrux_iot_ml_kem_vector_portable_cond_subtract_3329_4e(
        &re->coefficients[i0]);
  }
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_e1(
    Eurydice_slice public_key, Eurydice_slice deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    deserialize_to_reduced_ring_element_a7(
        ring_element,
        &Eurydice_slice_index(
            deserialized_pk, i0,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE void shift_right_ef(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec->elements[i0] = vec->elements[i0] >> (uint32_t)(int32_t)15;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.shift_right_4e
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE void shift_right_4e_ef(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  shift_right_ef(vec);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void to_unsigned_representative_a7(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  out[0U] = a[0U];
  shift_right_4e_ef(out);
  libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(
      out, LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  libcrux_iot_ml_kem_vector_portable_add_4e(out, a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void to_unsigned_field_modulus_a7(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out) {
  to_unsigned_representative_a7(a, out);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re->coefficients[i0], scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_12_4e(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)24U * i0,
                                 (size_t)24U * i0 + (size_t)24U, uint8_t *));
  }
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.serialize_vector
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void serialize_vector_e1(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *key,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, key,
                   libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
               libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 re = key[i0];
    serialize_uncompressed_ring_element_a7(
        &re, scratch,
        Eurydice_slice_subslice3(
            out, i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            uint8_t *));
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_mut_c5(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *t_as_ntt,
    Eurydice_slice seed_for_a, Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  serialize_vector_e1(
      t_as_ntt,
      Eurydice_slice_subslice3(
          serialized, (size_t)0U,
          libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)4U),
          uint8_t *),
      scratch);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_from(
          serialized,
          libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)4U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_public_key
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_iot_ml_kem_ind_cca_validate_public_key_c5(uint8_t *public_key) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  deserialized_pk[i] = call_mut_42_c5(&lvalue););
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1568U, public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
      uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_e1(
      uu____0, Eurydice_array_to_slice(
                   (size_t)4U, deserialized_pk,
                   libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  uint8_t public_key_serialized[1568U] = {0U};
  libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *uu____1 =
      deserialized_pk;
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1568U, public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
      uint8_t, size_t, uint8_t[]);
  serialize_public_key_mut_c5(
      uu____1, uu____2,
      Eurydice_array_to_slice((size_t)1568U, public_key_serialized, uint8_t),
      &scratch);
  return Eurydice_array_eq((size_t)1568U, public_key, public_key_serialized,
                           uint8_t);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key_only
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_only_8a(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key) {
  uint8_t t[32U] = {0U};
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      Eurydice_array_to_subslice3(private_key->value, (size_t)384U * (size_t)4U,
                                  (size_t)768U * (size_t)4U + (size_t)32U,
                                  uint8_t *),
      Eurydice_array_to_slice((size_t)32U, t, uint8_t));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key->value, (size_t)768U * (size_t)4U + (size_t)32U,
      (size_t)768U * (size_t)4U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, t, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_7b(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext *_ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_8a(private_key);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $4size_t
*/
typedef struct IndCpaPrivateKeyUnpacked_4f_s {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 secret_as_ntt[4U];
} IndCpaPrivateKeyUnpacked_4f;

/**
This function found in impl {core::default::Default for
libcrux_iot_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.unpacked.default_1e
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE IndCpaPrivateKeyUnpacked_4f default_1e_e1(void) {
  IndCpaPrivateKeyUnpacked_4f lit;
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] = ZERO_64_a7(););
  memcpy(lit.secret_as_ntt, repeat_expression,
         (size_t)4U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  return lit;
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $4size_t
- $16size_t
*/
typedef struct IndCpaPublicKeyUnpacked_81_s {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 t_as_ntt[4U];
  uint8_t seed_for_A[32U];
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 A[16U];
} IndCpaPublicKeyUnpacked_81;

/**
This function found in impl {core::default::Default for
libcrux_iot_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.unpacked.default_1f
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- K_SQUARED= 16
*/
static KRML_MUSTINLINE IndCpaPublicKeyUnpacked_81 default_1f_c5(void) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 uu____0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  uu____0[i] = ZERO_64_a7(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_81 lit;
  memcpy(lit.t_as_ntt, uu____0,
         (size_t)4U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 repeat_expression[16U];
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U,
                   repeat_expression[i] = ZERO_64_a7(););
  memcpy(lit.A, repeat_expression,
         (size_t)16U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  return lit;
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.cpa_keygen_seed_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
*/
static KRML_MUSTINLINE void cpa_keygen_seed_cc_22(
    Eurydice_slice key_generation_seed, Eurydice_slice out) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          seed, (size_t)0U,
          LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE,
          uint8_t *),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)4U;
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice((size_t)33U, seed, uint8_t), out);
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_c5(
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *) <
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          uint8_t *randomness_i = Eurydice_slice_index(
              randomness, i1, uint8_t[504U], uint8_t(*)[504U]);
          int16_t *out_i =
              Eurydice_slice_index(out, i1, int16_t[272U], int16_t(*)[272U]);
          size_t sampled_coefficients_i =
              Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *);
          size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
              Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                          sampled_coefficients_i + (size_t)16U,
                                          int16_t *));
          size_t uu____0 = i1;
          Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                               size_t *) =
              Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                   size_t *) +
              sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) >=
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) =
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_c50(
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *) <
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          uint8_t *randomness_i = Eurydice_slice_index(
              randomness, i1, uint8_t[168U], uint8_t(*)[168U]);
          int16_t *out_i =
              Eurydice_slice_index(out, i1, int16_t[272U], int16_t(*)[272U]);
          size_t sampled_coefficients_i =
              Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *);
          size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
              Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                          sampled_coefficients_i + (size_t)16U,
                                          int16_t *));
          size_t uu____0 = i1;
          Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                               size_t *) =
              Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                   size_t *) +
              sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) >=
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) =
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.sampling.sample_from_xof
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_from_xof_c92(
    Eurydice_slice seeds, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_hash_functions_portable_PortableHash xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  uint8_t randomness[4U][504U] = {{0U}};
  uint8_t randomness_blocksize[4U][168U] = {{0U}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state,
      Eurydice_array_to_slice((size_t)4U, randomness, uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_c5(
      Eurydice_array_to_slice((size_t)4U, randomness, uint8_t[504U]),
      sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice((size_t)4U, randomness_blocksize,
                                              uint8_t[168U]));
      done = sample_from_uniform_distribution_next_c50(
          Eurydice_array_to_slice((size_t)4U, randomness_blocksize,
                                  uint8_t[168U]),
          sampled_coefficients, out);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.from_i16_array
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void from_i16_array_a7(
    Eurydice_slice a,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *result) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_from_i16_array_4e(
        Eurydice_slice_subslice3(a, i0 * (size_t)16U,
                                 (i0 + (size_t)1U) * (size_t)16U, int16_t *),
        &result->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.from_i16_array_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void from_i16_array_64_a7(
    Eurydice_slice a,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *out) {
  from_i16_array_a7(a, out);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.sample_matrix_A
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_c91(Eurydice_slice A_transpose,
                                                uint8_t *seed, bool transpose) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_seed[34U];
      memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
      uint8_t seeds[4U][34U]; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          memcpy(seeds[i], copy_of_seed, (size_t)34U * sizeof(uint8_t)););
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      size_t sampled_coefficients[4U] = {0U}; int16_t out[4U][272U] = {{0U}};
      sample_from_xof_c92(
          Eurydice_array_to_slice((size_t)4U, seeds, uint8_t[34U]),
          Eurydice_array_to_slice((size_t)4U, sampled_coefficients, size_t),
          Eurydice_array_to_slice((size_t)4U, out, int16_t[272U]));
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice((size_t)4U, out, int16_t[272U]),
                   int16_t[272U]);
           i++) {
        size_t j = i;
        int16_t sample[272U];
        memcpy(sample, out[j], (size_t)272U * sizeof(int16_t));
        if (transpose) {
          Eurydice_slice uu____1 = Eurydice_array_to_subslice_to(
              (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
          from_i16_array_64_a7(
              uu____1,
              &Eurydice_slice_index(
                  A_transpose, j * (size_t)4U + i1,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
        } else {
          Eurydice_slice uu____2 = Eurydice_array_to_subslice_to(
              (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
          from_i16_array_64_a7(
              uu____2,
              &Eurydice_slice_index(
                  A_transpose, i1 * (size_t)4U + j,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
        }
      });
}

/**
 Given a series of uniformly random bytes in `randomness`, for some number
 `eta`, the `sample_from_binomial_distribution_{eta}` functions sample a ring
 element from a binomial distribution centered at 0 that uses two sets of `eta`
 coin flips. If, for example, `eta = ETA`, each ring coefficient is a value `v`
 such such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:

 ```plaintext
 - If v < 0, Pr[v] = Pr[-v]
 - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
 ```

 The values `v < 0` are mapped to the appropriate `KyberFieldElement`.

 The expected value is:

 ```plaintext
 E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1]
 + (ETA)Pr[ETA] = 0 since Pr[-v] = Pr[v] when v < 0.
 ```

 And the variance is:

 ```plaintext
 Var(X) = E[(X - E[X])^2]
        = E[X^2]
        = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) /
 2^(2 * ETA)) = ETA / 2
 ```

 This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203
 standard, which is reproduced below:

 ```plaintext
 Input: byte array B ∈ 𝔹^{64η}.
 Output: array f ∈ ℤ₂₅₆.

 b ← BytesToBits(B)
 for (i ← 0; i < 256; i++)
     x ← ∑(j=0 to η - 1) b[2iη + j]
     y ← ∑(j=0 to η - 1) b[2iη + η + j]
     f[i] ← x−y mod q
 end for
 return f
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_binomial_distribution_2 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void sample_from_binomial_distribution_2_a7(
    Eurydice_slice randomness, Eurydice_slice sampled_i16s) {
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice3(
        randomness, chunk_number * (size_t)4U,
        chunk_number * (size_t)4U + (size_t)4U, uint8_t *);
    uint32_t random_bits_as_u32 =
        (((uint32_t)Eurydice_slice_index(byte_chunk, (size_t)0U, uint8_t,
                                         uint8_t *) |
          (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U, uint8_t,
                                         uint8_t *)
              << 8U) |
         (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U, uint8_t,
                                        uint8_t *)
             << 16U) |
        (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)3U, uint8_t,
                                       uint8_t *)
            << 24U;
    uint32_t even_bits = random_bits_as_u32 & 1431655765U;
    uint32_t odd_bits = random_bits_as_u32 >> 1U & 1431655765U;
    uint32_t coin_toss_outcomes = even_bits + odd_bits;
    for (uint32_t i = 0U; i < 32U / 4U; i++) {
      uint32_t outcome_set = i;
      uint32_t outcome_set0 = outcome_set * 4U;
      int16_t outcome_1 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)outcome_set0 & 3U);
      int16_t outcome_2 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)(outcome_set0 + 2U) & 3U);
      size_t offset = (size_t)(outcome_set0 >> 2U);
      Eurydice_slice_index(sampled_i16s, (size_t)8U * chunk_number + offset,
                           int16_t, int16_t *) = outcome_1 - outcome_2;
    }
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- ETA= 2
*/
static KRML_MUSTINLINE void sample_from_binomial_distribution_0b(
    Eurydice_slice randomness, int16_t *output) {
  sample_from_binomial_distribution_2_a7(
      randomness, Eurydice_array_to_slice((size_t)256U, output, int16_t));
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_7
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t step = VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    scratch[0U] = re->coefficients[j + step];
    libcrux_iot_ml_kem_vector_portable_multiply_by_constant_4e(scratch,
                                                               (int16_t)-1600);
    re->coefficients[j + step] = re->coefficients[j];
    libcrux_iot_ml_kem_vector_portable_add_4e(&re->coefficients[j], scratch);
    libcrux_iot_ml_kem_vector_portable_sub_4e(&re->coefficients[j + step],
                                              scratch);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.traits.montgomery_multiply_fe with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void montgomery_multiply_fe_a7(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    int16_t fer) {
  libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(v, fer);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_layer_int_vec_step_a7(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *coefficients,
    size_t a, size_t b,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int16_t zeta_r) {
  scratch[0U] = coefficients[b];
  montgomery_multiply_fe_a7(scratch, zeta_r);
  coefficients[b] = coefficients[a];
  libcrux_iot_ml_kem_vector_portable_add_4e(&coefficients[a], scratch);
  libcrux_iot_ml_kem_vector_portable_sub_4e(&coefficients[b], scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_a7(
    size_t *zeta_i, libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    size_t layer,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec = step / (size_t)16U;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      ntt_layer_int_vec_step_a7(re->coefficients, a_offset + j, b_offset + j,
                                scratch, zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_3
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_3_a7(
    size_t *zeta_i,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
                   zeta_i[0U] = zeta_i[0U] + (size_t)1U;
                   libcrux_iot_ml_kem_vector_portable_ntt_layer_3_step_4e(
                       &re->coefficients[round], zeta(zeta_i[0U])););
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_a7(
    size_t *zeta_i,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
                   zeta_i[0U] = zeta_i[0U] + (size_t)1U;
                   libcrux_iot_ml_kem_vector_portable_ntt_layer_2_step_4e(
                       &re->coefficients[round], zeta(zeta_i[0U]),
                       zeta(zeta_i[0U] + (size_t)1U));
                   zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_a7(
    size_t *zeta_i,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      libcrux_iot_ml_kem_vector_portable_ntt_layer_1_step_4e(
          &re->coefficients[round], zeta(zeta_i[0U]),
          zeta(zeta_i[0U] + (size_t)1U), zeta(zeta_i[0U] + (size_t)2U),
          zeta(zeta_i[0U] + (size_t)3U));
      zeta_i[0U] = zeta_i[0U] + (size_t)3U;);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.poly_barrett_reduce
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *myself) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(
        &myself->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.poly_barrett_reduce_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_64_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *self) {
  poly_barrett_reduce_a7(self);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  ntt_at_layer_7_a7(re, scratch);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  ntt_at_layer_3_a7(&zeta_i, re);
  ntt_at_layer_2_a7(&zeta_i, re);
  ntt_at_layer_1_a7(&zeta_i, re);
  poly_barrett_reduce_64_a7(re);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE= 512
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_141(
    Eurydice_slice re_as_ntt, uint8_t *prf_input, uint8_t domain_separator,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_ac(prf_inputs, domain_separator);
  uint8_t prf_outputs[512U] = {0U};
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      Eurydice_array_to_slice((size_t)4U, prf_inputs, uint8_t[33U]),
      Eurydice_array_to_slice((size_t)512U, prf_outputs, uint8_t),
      (size_t)128U);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_slice randomness = Eurydice_array_to_subslice3(
          prf_outputs, i0 * (size_t)128U, (i0 + (size_t)1U) * (size_t)128U,
          uint8_t *);
      int16_t sample_buffer[256U] = {0U};
      sample_from_binomial_distribution_0b(randomness, sample_buffer);
      from_i16_array_64_a7(
          Eurydice_array_to_slice((size_t)256U, sample_buffer, int16_t),
          &Eurydice_slice_index(
              re_as_ntt, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
      ntt_binomially_sampled_ring_element_a7(
          &Eurydice_slice_index(
              re_as_ntt, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
          scratch););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_iot_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, K_SQUARED, ETA1, ETA1_RANDOMNESS_SIZE,
PRF_OUTPUT_SIZE1>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3,
TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_58 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_58_161(
    void **_) {
  return ZERO_64_a7();
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.entry
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *entry_e1(
    Eurydice_slice matrix, size_t i, size_t j) {
  return &Eurydice_slice_index(
      matrix, i * (size_t)4U + j,
      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply_fill_cache with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_fill_cache_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *myself,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *rhs,
    int32_t *accumulator,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *cache) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_fill_cache_4e(
        &myself->coefficients[i0], &rhs->coefficients[i0],
        Eurydice_array_to_subslice3(accumulator, i0 * (size_t)16U,
                                    (i0 + (size_t)1U) * (size_t)16U, int32_t *),
        &cache->coefficients[i0], zeta((size_t)64U + (size_t)4U * i0),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)1U),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)2U),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)3U));
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply_fill_cache_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_fill_cache_64_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *self,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *rhs,
    int32_t *accumulator,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *cache) {
  accumulating_ntt_multiply_fill_cache_a7(self, rhs, accumulator, cache);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.reducing_from_i32_array
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static void reducing_from_i32_array_a7(
    Eurydice_slice a,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *result) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_reducing_from_i32_array_4e(
        Eurydice_slice_subslice3(a, i0 * (size_t)16U,
                                 (i0 + (size_t)1U) * (size_t)16U, int32_t *),
        &result->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.reducing_from_i32_array_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void reducing_from_i32_array_64_a7(
    Eurydice_slice a,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *out) {
  reducing_from_i32_array_a7(a, out);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.traits.to_standard_domain
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void to_standard_domain_a7(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v) {
  libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
      v,
      LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.add_standard_error_reduce with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *myself,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    to_standard_domain_a7(&myself->coefficients[j]);
    libcrux_iot_ml_kem_vector_portable_add_4e(&myself->coefficients[j],
                                              &error->coefficients[j]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(
        &myself->coefficients[j]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.add_standard_error_reduce_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_64_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *self,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error) {
  add_standard_error_reduce_a7(self, error);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply_use_cache with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_use_cache_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *myself,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *rhs,
    int32_t *accumulator,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *cache) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_use_cache_4e(
        &myself->coefficients[i0], &rhs->coefficients[i0],
        Eurydice_array_to_subslice3(accumulator, i0 * (size_t)16U,
                                    (i0 + (size_t)1U) * (size_t)16U, int32_t *),
        &cache->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply_use_cache_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_use_cache_64_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *self,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *rhs,
    int32_t *accumulator,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *cache) {
  accumulating_ntt_multiply_use_cache_a7(self, rhs, accumulator, cache);
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_As_plus_e
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_As_plus_e_e1(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *t_as_ntt,
    Eurydice_slice matrix_A,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *s_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *s_cache,
    int32_t *accumulator) {
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *uu____0 =
          entry_e1(matrix_A, (size_t)0U, j);
      accumulating_ntt_multiply_fill_cache_64_a7(uu____0, &s_as_ntt[j],
                                                 accumulator, &s_cache[j]););
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, accumulator, int32_t), t_as_ntt);
  add_standard_error_reduce_64_a7(t_as_ntt, error_as_ntt);
  KRML_MAYBE_FOR3(
      i, (size_t)1U, (size_t)4U, (size_t)1U, size_t i0 = i;
      int32_t buf[256U] = {0U}; accumulator = buf; KRML_MAYBE_FOR4(
          i1, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i1;
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *uu____1 =
              entry_e1(matrix_A, i0, j);
          accumulating_ntt_multiply_use_cache_64_a7(uu____1, &s_as_ntt[j],
                                                    accumulator, &s_cache[j]););
      reducing_from_i32_array_64_a7(
          Eurydice_array_to_slice((size_t)256U, accumulator, int32_t),
          &t_as_ntt[i0]);
      add_standard_error_reduce_64_a7(&t_as_ntt[i0], &error_as_ntt[i0]););
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_161(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_4f *private_key,
    IndCpaPublicKeyUnpacked_81 *public_key,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *scratch,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *s_cache,
    int32_t *accumulator) {
  uint8_t hashed[64U] = {0U};
  cpa_keygen_seed_cc_22(key_generation_seed,
                        Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_slice uu____1 = Eurydice_array_to_slice(
      (size_t)16U, public_key->A,
      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12);
  uint8_t ret[34U];
  libcrux_iot_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  sample_matrix_A_c91(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_iot_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                                prf_input);
  uint8_t domain_separator = sample_vector_cbd_then_ntt_141(
      Eurydice_array_to_slice(
          (size_t)4U, private_key->secret_as_ntt,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      prf_input, 0U, scratch->coefficients);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 error_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_as_ntt[i] = call_mut_58_161(&lvalue););
  sample_vector_cbd_then_ntt_141(
      Eurydice_array_to_slice(
          (size_t)4U, error_as_ntt,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      prf_input, domain_separator, scratch->coefficients);
  compute_As_plus_e_e1(
      public_key->t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)16U, public_key->A,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      private_key->secret_as_ntt, error_as_ntt, s_cache, accumulator);
  uint8_t uu____2[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U],
                           core_array_TryFromSliceError);
  core_result_unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.serialize_unpacked_secret_key with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- K_SQUARED= 16
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static void serialize_unpacked_secret_key_00(
    IndCpaPublicKeyUnpacked_81 *public_key,
    IndCpaPrivateKeyUnpacked_4f *private_key,
    Eurydice_slice serialized_private_key, Eurydice_slice serialized_public_key,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  serialize_public_key_mut_c5(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      serialized_public_key, scratch);
  serialize_vector_e1(private_key->secret_as_ntt, serialized_private_key,
                      scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
static KRML_MUSTINLINE void generate_keypair_641(
    Eurydice_slice key_generation_seed,
    Eurydice_slice serialized_ind_cpa_private_key,
    Eurydice_slice serialized_public_key,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *scratch,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *s_cache,
    int32_t *accumulator) {
  IndCpaPrivateKeyUnpacked_4f private_key = default_1e_e1();
  IndCpaPublicKeyUnpacked_81 public_key = default_1f_c5();
  generate_keypair_unpacked_161(key_generation_seed, &private_key, &public_key,
                                scratch, s_cache, accumulator);
  serialize_unpacked_secret_key_00(
      &public_key, &private_key, serialized_ind_cpa_private_key,
      serialized_public_key, scratch->coefficients);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.serialize_kem_secret_key_mut with types
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_8a(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      public_key,
      Eurydice_array_to_subslice3(
          serialized, pointer,
          pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t *));
  pointer = pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____6 = serialized;
  size_t uu____7 = pointer;
  size_t uu____8 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____6, uu____7,
          uu____8 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
libcrux_iot_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_iot_ml_kem_ind_cca_generate_keypair_b71(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  uint8_t public_key[1568U] = {0U};
  uint8_t secret_key_serialized[3168U] = {0U};
  uint8_t ind_cpa_private_key[1536U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 scratch = ZERO_64_a7();
  int32_t accumulator[256U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 s_cache[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  s_cache[i] = ZERO_64_a7(););
  generate_keypair_641(
      ind_cpa_keypair_randomness,
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t), &scratch,
      s_cache, accumulator);
  serialize_kem_secret_key_mut_8a(
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[3168U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)3168U * sizeof(uint8_t));
  libcrux_iot_ml_kem_types_MlKemPrivateKey_83 private_key =
      libcrux_iot_ml_kem_types_from_56_39(copy_of_secret_key_serialized);
  libcrux_iot_ml_kem_types_MlKemPrivateKey_83 uu____1 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1568U];
  memcpy(copy_of_public_key, public_key, (size_t)1568U * sizeof(uint8_t));
  return libcrux_iot_ml_kem_types_from_d9_94(
      uu____1, libcrux_iot_ml_kem_types_from_18_af(copy_of_public_key));
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.entropy_preprocess_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
*/
static KRML_MUSTINLINE void entropy_preprocess_cc_22(Eurydice_slice randomness,
                                                     Eurydice_slice out) {
  Eurydice_slice_copy(out, randomness, uint8_t);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_iot_ml_kem::ind_cca::encapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE,
T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE, VECTOR_U_COMPRESSION_FACTOR,
VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1, PRF_OUTPUT_SIZE2>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate.call_mut_92
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_92_351(
    void **_) {
  return ZERO_64_a7();
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_iot_ml_kem::ind_cpa::encrypt_c1::closure<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1.call_mut_6f
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- K_SQUARED= 16
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_6f_921(
    void **_) {
  return ZERO_64_a7();
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
- PRF_OUTPUT_SIZE= 512
*/
static KRML_MUSTINLINE uint8_t
sample_ring_element_cbd_141(uint8_t *prf_input, uint8_t domain_separator,
                            Eurydice_slice error_1, int16_t *sample_buffer) {
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_ac(prf_inputs, domain_separator);
  uint8_t prf_outputs[512U] = {0U};
  Eurydice_slice uu____0 = core_array___Array_T__N___as_slice(
      (size_t)4U, prf_inputs, uint8_t[33U], Eurydice_slice);
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      uu____0, Eurydice_array_to_slice((size_t)512U, prf_outputs, uint8_t),
      (size_t)128U);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_slice randomness = Eurydice_array_to_subslice3(
          prf_outputs, i0 * (size_t)128U, (i0 + (size_t)1U) * (size_t)128U,
          uint8_t *);
      sample_from_binomial_distribution_0b(randomness, sample_buffer);
      from_i16_array_64_a7(
          Eurydice_array_to_slice((size_t)256U, sample_buffer, int16_t),
          &Eurydice_slice_index(
              error_1, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
  return domain_separator;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_a6(Eurydice_slice input, Eurydice_slice out) {
  libcrux_iot_sha3_portable_shake256(out, input);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF_07
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_07_a6(Eurydice_slice input,
                                      Eurydice_slice out) {
  PRF_a6(input, out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_iot_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1.call_mut_33
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- K_SQUARED= 16
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_33_921(
    void **_) {
  return ZERO_64_a7();
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 1
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_1b(
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  {
    size_t i0 = (size_t)0U;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        uint8_t *randomness_i = Eurydice_slice_index(
            randomness, i0, uint8_t[504U], uint8_t(*)[504U]);
        int16_t *out_i =
            Eurydice_slice_index(out, i0, int16_t[272U], int16_t(*)[272U]);
        size_t sampled_coefficients_i =
            Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *);
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                        r * (size_t)24U + (size_t)24U,
                                        uint8_t *),
            Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                        sampled_coefficients_i + (size_t)16U,
                                        int16_t *));
        size_t uu____0 = i0;
        Eurydice_slice_index(sampled_coefficients, uu____0, size_t, size_t *) =
            Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                 size_t *) +
            sampled;
      }
    }
  }
  bool done = true;
  {
    size_t i = (size_t)0U;
    if (Eurydice_slice_index(sampled_coefficients, i, size_t, size_t *) >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index(sampled_coefficients, i, size_t, size_t *) =
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 1
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_1b0(
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  {
    size_t i0 = (size_t)0U;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        uint8_t *randomness_i = Eurydice_slice_index(
            randomness, i0, uint8_t[168U], uint8_t(*)[168U]);
        int16_t *out_i =
            Eurydice_slice_index(out, i0, int16_t[272U], int16_t(*)[272U]);
        size_t sampled_coefficients_i =
            Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *);
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                        r * (size_t)24U + (size_t)24U,
                                        uint8_t *),
            Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                        sampled_coefficients_i + (size_t)16U,
                                        int16_t *));
        size_t uu____0 = i0;
        Eurydice_slice_index(sampled_coefficients, uu____0, size_t, size_t *) =
            Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                 size_t *) +
            sampled;
      }
    }
  }
  bool done = true;
  {
    size_t i = (size_t)0U;
    if (Eurydice_slice_index(sampled_coefficients, i, size_t, size_t *) >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index(sampled_coefficients, i, size_t, size_t *) =
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.sampling.sample_from_xof
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 1
*/
static KRML_MUSTINLINE void sample_from_xof_c9(
    Eurydice_slice seeds, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_hash_functions_portable_PortableHash xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  uint8_t randomness[1U][504U] = {{0U}};
  uint8_t randomness_blocksize[1U][168U] = {{0U}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state,
      Eurydice_array_to_slice((size_t)1U, randomness, uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_1b(
      Eurydice_array_to_slice((size_t)1U, randomness, uint8_t[504U]),
      sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice((size_t)1U, randomness_blocksize,
                                              uint8_t[168U]));
      done = sample_from_uniform_distribution_next_1b0(
          Eurydice_array_to_slice((size_t)1U, randomness_blocksize,
                                  uint8_t[168U]),
          sampled_coefficients, out);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.sample_matrix_entry
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics

*/
static KRML_MUSTINLINE void sample_matrix_entry_36(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *out,
    Eurydice_slice seed, size_t i, size_t j) {
  uint8_t seed_ij[34U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(seed_ij, (size_t)0U, (size_t)32U, uint8_t *),
      seed, uint8_t);
  seed_ij[32U] = (uint8_t)i;
  seed_ij[33U] = (uint8_t)j;
  size_t sampled_coefficients[1U] = {0U};
  int16_t out_raw[1U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_ij[34U];
  memcpy(copy_of_seed_ij, seed_ij, (size_t)34U * sizeof(uint8_t));
  uint8_t uu____1[1U][34U];
  memcpy(uu____1[0U], copy_of_seed_ij, (size_t)34U * sizeof(uint8_t));
  sample_from_xof_c9(
      Eurydice_array_to_slice((size_t)1U, uu____1, uint8_t[34U]),
      Eurydice_array_to_slice((size_t)1U, sampled_coefficients, size_t),
      Eurydice_array_to_slice((size_t)1U, out_raw, int16_t[272U]));
  from_i16_array_64_a7(
      Eurydice_array_to_slice((size_t)272U, out_raw[0U], int16_t), out);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_a7(
    size_t *zeta_i,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_1_step_4e(
          &re->coefficients[round], zeta(zeta_i[0U]),
          zeta(zeta_i[0U] - (size_t)1U), zeta(zeta_i[0U] - (size_t)2U),
          zeta(zeta_i[0U] - (size_t)3U));
      zeta_i[0U] = zeta_i[0U] - (size_t)3U;);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_2_a7(
    size_t *zeta_i,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
                   zeta_i[0U] = zeta_i[0U] - (size_t)1U;
                   libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_2_step_4e(
                       &re->coefficients[round], zeta(zeta_i[0U]),
                       zeta(zeta_i[0U] - (size_t)1U));
                   zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_a7(
    size_t *zeta_i,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
                   zeta_i[0U] = zeta_i[0U] - (size_t)1U;
                   libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_3_step_4e(
                       &re->coefficients[round], zeta(zeta_i[0U])););
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void inv_ntt_layer_int_vec_step_reduce_a7(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *coefficients,
    size_t a, size_t b,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int16_t zeta_r) {
  scratch[0U] = coefficients[a];
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients[b]);
  libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(scratch);
  coefficients[a] = scratch[0U];
  libcrux_iot_ml_kem_vector_portable_negate_4e(scratch);
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients[b]);
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients[b]);
  montgomery_multiply_fe_a7(scratch, zeta_r);
  coefficients[b] = scratch[0U];
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_a7(
    size_t *zeta_i, libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    size_t layer,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec =
      step / LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      inv_ntt_layer_int_vec_step_reduce_a7(re->coefficients, a_offset + j,
                                           b_offset + j, scratch,
                                           zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_e1(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t zeta_i =
      LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_a7(&zeta_i, re);
  invert_ntt_at_layer_2_a7(&zeta_i, re);
  invert_ntt_at_layer_3_a7(&zeta_i, re);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)7U, scratch);
  poly_barrett_reduce_64_a7(re);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.add_error_reduce
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *myself,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &myself->coefficients[j], (int16_t)1441);
    libcrux_iot_ml_kem_vector_portable_add_4e(&myself->coefficients[j],
                                              &error->coefficients[j]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(
        &myself->coefficients[j]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.add_error_reduce_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_64_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *self,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error) {
  add_error_reduce_a7(self, error);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_vector_u_c91(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *matrix_entry,
    Eurydice_slice seed, Eurydice_slice r_as_ntt, Eurydice_slice error_1,
    Eurydice_slice result,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  int32_t buf0[256U] = {0U};
  accumulator = buf0;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
      sample_matrix_entry_36(matrix_entry, seed, (size_t)0U, j);
      accumulating_ntt_multiply_fill_cache_64_a7(
          matrix_entry,
          &Eurydice_slice_index(
              r_as_ntt, j,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
          accumulator,
          &Eurydice_slice_index(
              cache, j, libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, accumulator, int32_t),
      &Eurydice_slice_index(
          result, (size_t)0U,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
  invert_ntt_montgomery_e1(
      &Eurydice_slice_index(
          result, (size_t)0U,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
      scratch);
  add_error_reduce_64_a7(
      &Eurydice_slice_index(
          result, (size_t)0U,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
      &Eurydice_slice_index(
          error_1, (size_t)0U,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
  KRML_MAYBE_FOR3(
      i, (size_t)1U, (size_t)4U, (size_t)1U, size_t i0 = i;
      int32_t buf[256U] = {0U}; accumulator = buf; KRML_MAYBE_FOR4(
          i1, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i1;
          sample_matrix_entry_36(matrix_entry, seed, i0, j);
          accumulating_ntt_multiply_use_cache_64_a7(
              matrix_entry,
              &Eurydice_slice_index(
                  r_as_ntt, j,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
              accumulator,
              &Eurydice_slice_index(
                  cache, j,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
      reducing_from_i32_array_64_a7(
          Eurydice_array_to_slice((size_t)256U, accumulator, int32_t),
          &Eurydice_slice_index(
              result, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
      invert_ntt_montgomery_e1(
          &Eurydice_slice_index(
              result, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
          scratch);
      add_error_reduce_64_a7(
          &Eurydice_slice_index(
              result, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
          &Eurydice_slice_index(
              error_1, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void compress_ef(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)10, (uint16_t)a->elements[i0]);
    a->elements[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress_4e
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void compress_4e_ef(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  compress_ef(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void compress_c4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)11, (uint16_t)a->elements[i0]);
    a->elements[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress_4e
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void compress_4e_c4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  compress_c4(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_11 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_11_c7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_representative_a7(&re->coefficients[i0], scratch);
    compress_4e_c4(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_11_4e(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)22U * i0,
                                 (size_t)22U * i0 + (size_t)22U, uint8_t *));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- COMPRESSION_FACTOR= 11
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_d2(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  compress_then_serialize_11_c7(re, serialized, scratch);
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- OUT_LEN= 1408
- COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_u_00(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 input[4U],
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, input,
                   libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
               libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 re = input[i0];
    compress_then_serialize_ring_element_u_d2(
        &re,
        Eurydice_slice_subslice3(
            out, i0 * ((size_t)1408U / (size_t)4U),
            (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t *),
        scratch);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- K_SQUARED= 16
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static KRML_MUSTINLINE void encrypt_c1_921(
    Eurydice_slice randomness,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *matrix_entry,
    Eurydice_slice seed_for_a, Eurydice_slice ciphertext,
    Eurydice_slice r_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_2,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  uint8_t prf_input[33U];
  libcrux_iot_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_141(r_as_ntt, prf_input, 0U, scratch);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 error_1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_1[i] = call_mut_6f_921(&lvalue););
  int16_t sampling_buffer[256U] = {0U};
  uint8_t domain_separator = sample_ring_element_cbd_141(
      prf_input, domain_separator0,
      Eurydice_array_to_slice(
          (size_t)4U, error_1,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      sampling_buffer);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U] = {0U};
  PRF_07_a6(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
            Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  sample_from_binomial_distribution_0b(
      Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t),
      sampling_buffer);
  from_i16_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, sampling_buffer, int16_t), error_2);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 u[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  u[i] = call_mut_33_921(&lvalue););
  compute_vector_u_c91(
      matrix_entry, seed_for_a, r_as_ntt,
      Eurydice_array_to_slice(
          (size_t)4U, error_1,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      Eurydice_array_to_slice(
          (size_t)4U, u,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      scratch, cache, accumulator);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 copy_of_u[4U];
  memcpy(copy_of_u, u,
         (size_t)4U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  compress_then_serialize_u_00(copy_of_u, ciphertext, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.traits.decompress_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void decompress_1_a7(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  libcrux_iot_ml_kem_vector_portable_negate_4e(vec);
  libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(
      vec, (int16_t)1665);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_message_a7(
    uint8_t *serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      libcrux_iot_ml_kem_vector_portable_deserialize_1_4e(
          Eurydice_array_to_subslice3(serialized, (size_t)2U * i0,
                                      (size_t)2U * i0 + (size_t)2U, uint8_t *),
          &re->coefficients[i0]);
      decompress_1_a7(&re->coefficients[i0]););
}

/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.add_message_error_reduce
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void add_message_error_reduce_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *myself,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *message,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *result,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &result->coefficients[i0], (int16_t)1441);
    scratch[0U] = myself->coefficients[i0];
    libcrux_iot_ml_kem_vector_portable_add_4e(scratch,
                                              &message->coefficients[i0]);
    libcrux_iot_ml_kem_vector_portable_add_4e(&result->coefficients[i0],
                                              scratch);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(
        &result->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.add_message_error_reduce_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void add_message_error_reduce_64_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *self,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *message,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *result,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  add_message_error_reduce_a7(self, message, result, scratch);
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_ring_element_v
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_ring_element_v_e1(
    Eurydice_slice public_key,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *t_as_ntt_entry,
    Eurydice_slice r_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_2,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *message,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *result,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  int32_t buf[256U] = {0U};
  accumulator = buf;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    deserialize_to_reduced_ring_element_a7(ring_element, t_as_ntt_entry);
    accumulating_ntt_multiply_use_cache_64_a7(
        t_as_ntt_entry,
        &Eurydice_slice_index(
            r_as_ntt, i0,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
        accumulator,
        &Eurydice_slice_index(
            cache, i0, libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
  }
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, accumulator, int32_t), result);
  invert_ntt_montgomery_e1(result, scratch);
  add_message_error_reduce_64_a7(error_2, message, result, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void compress_d1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)4, (uint16_t)a->elements[i0]);
    a->elements[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress_4e
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void compress_4e_d1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  compress_d1(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.serialize.compress_then_serialize_4
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 re,
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re.coefficients[i0], scratch);
    compress_4e_d1(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_4_4e(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t *));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void compress_f4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)5, (uint16_t)a->elements[i0]);
    a->elements[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress_4e
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void compress_4e_f4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  compress_f4(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.serialize.compress_then_serialize_5
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 re,
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_representative_a7(&re.coefficients[i0], scratch);
    compress_4e_f4(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_5_4e(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)10U * i0,
                                 (size_t)10U * i0 + (size_t)10U, uint8_t *));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- COMPRESSION_FACTOR= 5
- OUT_LEN= 160
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_e9(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 re,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  compress_then_serialize_5_a7(re, out, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- V_COMPRESSION_FACTOR= 5
- C2_LEN= 160
*/
static KRML_MUSTINLINE void encrypt_c2_e9(
    Eurydice_slice public_key,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *t_as_ntt_entry,
    Eurydice_slice r_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_2,
    uint8_t *message, Eurydice_slice ciphertext,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12
      message_as_ring_element = ZERO_64_a7();
  deserialize_then_decompress_message_a7(message, &message_as_ring_element);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 v = ZERO_64_a7();
  compute_ring_element_v_e1(public_key, t_as_ntt_entry, r_as_ntt, error_2,
                            &message_as_ring_element, &v, scratch, cache,
                            accumulator);
  compress_then_serialize_ring_element_v_e9(v, ciphertext, scratch);
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- K_SQUARED= 16
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_LEN= 1408
- C2_LEN= 160
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static KRML_MUSTINLINE void encrypt_5a1(
    Eurydice_slice public_key, uint8_t *message, Eurydice_slice randomness,
    Eurydice_slice ciphertext,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *matrix_entry,
    Eurydice_slice r_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_2,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  encrypt_c1_921(randomness, matrix_entry,
                 Eurydice_slice_subslice_from(public_key, (size_t)1536U,
                                              uint8_t, size_t, uint8_t[]),
                 Eurydice_slice_subslice3(ciphertext, (size_t)0U, (size_t)1408U,
                                          uint8_t *),
                 r_as_ntt, error_2, scratch, cache, accumulator);
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  encrypt_c2_e9(uu____0, matrix_entry, r_as_ntt, error_2, message,
                Eurydice_slice_subslice_from(ciphertext, (size_t)1408U, uint8_t,
                                             size_t, uint8_t[]),
                scratch, cache, accumulator);
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.kdf_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE void kdf_cc_8a(Eurydice_slice shared_secret,
                                      Eurydice_slice out) {
  Eurydice_slice_copy(out, shared_secret, uint8_t);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
tuple_d1 libcrux_iot_ml_kem_ind_cca_encapsulate_351(
    libcrux_iot_ml_kem_types_MlKemPublicKey_64 *public_key,
    uint8_t *randomness) {
  uint8_t processed_randomness[32U] = {0U};
  entropy_preprocess_cc_22(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, processed_randomness, uint8_t));
  uint8_t to_hash[64U];
  libcrux_iot_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, processed_randomness, uint8_t),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_slice(
      (size_t)1568U, libcrux_iot_ml_kem_types_as_slice_63_af(public_key),
      uint8_t);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
          uint8_t, size_t, uint8_t[]));
  uint8_t hashed[64U] = {0U};
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[1568U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 r_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  r_as_ntt[i] = call_mut_92_351(&lvalue););
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 error_2 = ZERO_64_a7();
  libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  int32_t accumulator[256U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 cache[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  cache[i] = ZERO_64_a7(););
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 matrix_entry =
      ZERO_64_a7();
  encrypt_5a1(Eurydice_array_to_slice(
                  (size_t)1568U,
                  libcrux_iot_ml_kem_types_as_slice_63_af(public_key), uint8_t),
              processed_randomness, pseudorandomness,
              Eurydice_array_to_slice((size_t)1568U, ciphertext, uint8_t),
              &matrix_entry,
              Eurydice_array_to_slice(
                  (size_t)4U, r_as_ntt,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
              &error_2, &scratch,
              Eurydice_array_to_slice(
                  (size_t)4U, cache,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
              accumulator);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1568U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext ciphertext0 =
      libcrux_iot_ml_kem_types_from_9d_af(copy_of_ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  kdf_cc_8a(shared_secret,
            Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t));
  libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext uu____3 = ciphertext0;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_d1 lit;
  lit.fst = uu____3;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_iot_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt.call_mut_a5
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_a5_08(
    void **_) {
  return ZERO_64_a7();
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_to_uncompressed_ring_element_a7(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(bytes,
                                                         &re->coefficients[i0]);
  }
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.deserialize_vector
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_vector_e1(
    Eurydice_slice secret_key, Eurydice_slice secret_as_ntt) {
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      deserialize_to_uncompressed_ring_element_a7(
          Eurydice_slice_subslice3(
              secret_key,
              i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *),
          &Eurydice_slice_index(
              secret_as_ntt, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_iot_ml_kem::ind_cpa::decrypt_unpacked::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.decrypt_unpacked.call_mut_b7 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_b7_08(
    void **_) {
  return ZERO_64_a7();
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_ef(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        (int32_t)a->elements[i0] *
        (int32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)10);
    decompressed = decompressed >> (uint32_t)((int32_t)10 + (int32_t)1);
    a->elements[i0] = (int16_t)decompressed;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.decompress_ciphertext_coefficient_4e with
const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_4e_ef(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  decompress_ciphertext_coefficient_ef(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_10_a7(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)20U,
                                 i0 * (size_t)20U + (size_t)20U, uint8_t *);
    libcrux_iot_ml_kem_vector_portable_deserialize_10_4e(bytes,
                                                         &re->coefficients[i0]);
    decompress_ciphertext_coefficient_4e_ef(&re->coefficients[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_c4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        (int32_t)a->elements[i0] *
        (int32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)11);
    decompressed = decompressed >> (uint32_t)((int32_t)11 + (int32_t)1);
    a->elements[i0] = (int16_t)decompressed;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.decompress_ciphertext_coefficient_4e with
const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_4e_c4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  decompress_ciphertext_coefficient_c4(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_11_a7(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)22U,
                                 i0 * (size_t)22U + (size_t)22U, uint8_t *);
    libcrux_iot_ml_kem_vector_portable_deserialize_11_4e(bytes,
                                                         &re->coefficients[i0]);
    decompress_ciphertext_coefficient_4e_c4(&re->coefficients[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_u_93(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *output) {
  deserialize_then_decompress_11_a7(serialized, output);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_93(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)7U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  ntt_at_layer_3_a7(&zeta_i, re);
  ntt_at_layer_2_a7(&zeta_i, re);
  ntt_at_layer_1_a7(&zeta_i, re);
  poly_barrett_reduce_64_a7(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.deserialize_then_decompress_u with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_e9(
    uint8_t *ciphertext, Eurydice_slice u_as_ntt,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1568U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)11U / (size_t)8U),
        i0 * (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)11U / (size_t)8U) +
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U,
        uint8_t *);
    deserialize_then_decompress_ring_element_u_93(
        u_bytes, &Eurydice_slice_index(
                     u_as_ntt, i0,
                     libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                     libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
    ntt_vector_u_93(
        &Eurydice_slice_index(
            u_as_ntt, i0,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
        scratch);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_d1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        (int32_t)a->elements[i0] *
        (int32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)4);
    decompressed = decompressed >> (uint32_t)((int32_t)4 + (int32_t)1);
    a->elements[i0] = (int16_t)decompressed;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.decompress_ciphertext_coefficient_4e with
const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_4e_d1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  decompress_ciphertext_coefficient_d1(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_4_a7(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t *);
    libcrux_iot_ml_kem_vector_portable_deserialize_4_4e(bytes,
                                                        &re->coefficients[i0]);
    decompress_ciphertext_coefficient_4e_d1(&re->coefficients[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_f4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        (int32_t)a->elements[i0] *
        (int32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)5);
    decompressed = decompressed >> (uint32_t)((int32_t)5 + (int32_t)1);
    a->elements[i0] = (int16_t)decompressed;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.decompress_ciphertext_coefficient_4e with
const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_4e_f4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a) {
  decompress_ciphertext_coefficient_f4(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_5_a7(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)10U,
                                 i0 * (size_t)10U + (size_t)10U, uint8_t *);
    libcrux_iot_ml_kem_vector_portable_deserialize_5_4e(bytes,
                                                        &re->coefficients[i0]);
    decompress_ciphertext_coefficient_4e_f4(&re->coefficients[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_v_c5(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *output) {
  deserialize_then_decompress_5_a7(serialized, output);
}

/**
 Given two `KyberPolynomialRingElement`s in their NTT representations,
 compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
 the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:

 ```plaintext
 ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X²
 - ζ^(2·BitRev₇(i) + 1))
 ```

 This function almost implements <strong>Algorithm 10</strong> of the
 NIST FIPS 203 standard, which is reproduced below:

 ```plaintext
 Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
 Output: An array ĥ ∈ ℤq.

 for(i ← 0; i < 128; i++)
     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1],
 ζ^(2·BitRev₇(i) + 1)) end for return ĥ
 ```
 We say "almost" because the coefficients of the ring element output by
 this function are in the Montgomery domain.

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *myself,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *rhs,
    int32_t *accumulator) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_4e(
        &myself->coefficients[i0], &rhs->coefficients[i0],
        Eurydice_array_to_subslice3(accumulator, i0 * (size_t)16U,
                                    (i0 + (size_t)1U) * (size_t)16U, int32_t *),
        zeta((size_t)64U + (size_t)4U * i0),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)1U),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)2U),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)3U));
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_64_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *self,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *rhs,
    int32_t *accumulator) {
  accumulating_ntt_multiply_a7(self, rhs, accumulator);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.subtract_reduce
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void subtract_reduce_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *myself,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *b) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &b->coefficients[i0], (int16_t)1441);
    libcrux_iot_ml_kem_vector_portable_sub_4e(&b->coefficients[i0],
                                              &myself->coefficients[i0]);
    libcrux_iot_ml_kem_vector_portable_negate_4e(&b->coefficients[i0]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&b->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.subtract_reduce_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void subtract_reduce_64_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *self,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *b) {
  subtract_reduce_a7(self, b);
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_message
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_message_e1(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *v,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *secret_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *u_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *result,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int32_t *accumulator) {
  int32_t buf[256U] = {0U};
  accumulator = buf;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  accumulating_ntt_multiply_64_a7(&secret_as_ntt[i0],
                                                  &u_as_ntt[i0], accumulator););
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, accumulator, int32_t), result);
  invert_ntt_montgomery_e1(result, scratch);
  subtract_reduce_64_a7(v, result);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_message with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void compress_then_serialize_message_a7(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
                   to_unsigned_field_modulus_a7(&re->coefficients[i0], scratch);
                   libcrux_iot_ml_kem_vector_portable_compress_1_4e(scratch);
                   libcrux_iot_ml_kem_vector_portable_serialize_1_4e(
                       scratch, Eurydice_slice_subslice3(
                                    serialized, (size_t)2U * i0,
                                    (size_t)2U * i0 + (size_t)2U, uint8_t *)););
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE void decrypt_unpacked_08(
    IndCpaPrivateKeyUnpacked_4f *secret_key, uint8_t *ciphertext,
    Eurydice_slice decrypted,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int32_t *accumulator) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 u_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  u_as_ntt[i] = call_mut_b7_08(&lvalue););
  deserialize_then_decompress_u_e9(
      ciphertext,
      Eurydice_array_to_slice(
          (size_t)4U, u_as_ntt,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      scratch);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 v = ZERO_64_a7();
  deserialize_then_decompress_ring_element_v_c5(
      Eurydice_array_to_subslice_from((size_t)1568U, ciphertext, (size_t)1408U,
                                      uint8_t, size_t, uint8_t[]),
      &v);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 message = ZERO_64_a7();
  compute_message_e1(&v, secret_key->secret_as_ntt, u_as_ntt, &message, scratch,
                     accumulator);
  compress_then_serialize_message_a7(&message, decrypted, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE void decrypt_08(
    Eurydice_slice secret_key, uint8_t *ciphertext, Eurydice_slice decrypted,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int32_t *accumulator) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 secret_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  secret_as_ntt[i] = call_mut_a5_08(&lvalue););
  deserialize_vector_e1(
      secret_key, Eurydice_array_to_slice(
                      (size_t)4U, secret_as_ntt,
                      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12
      copy_of_secret_as_ntt[4U];
  memcpy(copy_of_secret_as_ntt, secret_as_ntt,
         (size_t)4U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  IndCpaPrivateKeyUnpacked_4f secret_key_unpacked;
  memcpy(secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
         (size_t)4U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  decrypt_unpacked_08(&secret_key_unpacked, ciphertext, decrypted, scratch,
                      accumulator);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_9e(Eurydice_slice input, Eurydice_slice out) {
  libcrux_iot_sha3_portable_shake256(out, input);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF_07
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_07_9e(Eurydice_slice input,
                                      Eurydice_slice out) {
  PRF_9e(input, out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_iot_ml_kem::ind_cca::decapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, SECRET_KEY_SIZE, CPA_SECRET_KEY_SIZE,
PUBLIC_KEY_SIZE, CIPHERTEXT_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE,
VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2, IMPLICIT_REJECTION_HASH_INPUT_SIZE>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate.call_mut_9b
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_9b_1b1(
    void **_) {
  return ZERO_64_a7();
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
void libcrux_iot_ml_kem_ind_cca_decapsulate_1b1(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_iot_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_iot_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U] = {0U};
  libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  int32_t accumulator[256U] = {0U};
  decrypt_08(ind_cpa_secret_key, ciphertext->value,
             Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), &scratch,
             accumulator);
  uint8_t to_hash0[64U];
  libcrux_iot_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(Eurydice_array_to_subslice_from(
                          (size_t)64U, to_hash0,
                          LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
                          uint8_t, size_t, uint8_t[]),
                      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U] = {0U};
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1600U];
  libcrux_iot_ml_kem_utils_into_padded_array_7f(implicit_rejection_value,
                                                to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____2, libcrux_iot_ml_kem_types_as_ref_84_af(ciphertext), uint8_t);
  uint8_t implicit_rejection_shared_secret[32U] = {0U};
  PRF_07_9e(Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t),
            Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret, uint8_t));
  uint8_t expected_ciphertext[1568U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 r_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  r_as_ntt[i] = call_mut_9b_1b1(&lvalue););
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 error_2 = ZERO_64_a7();
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 cache[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  cache[i] = ZERO_64_a7(););
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 matrix_entry =
      ZERO_64_a7();
  encrypt_5a1(
      ind_cpa_public_key, decrypted, pseudorandomness,
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t),
      &matrix_entry,
      Eurydice_array_to_slice(
          (size_t)4U, r_as_ntt,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      &error_2, &scratch,
      Eurydice_array_to_slice(
          (size_t)4U, cache,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      accumulator);
  uint8_t implicit_rejection_shared_secret_kdf[32U] = {0U};
  kdf_cc_8a(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret, uint8_t),
            Eurydice_array_to_slice(
                (size_t)32U, implicit_rejection_shared_secret_kdf, uint8_t));
  uint8_t shared_secret_kdf[32U] = {0U};
  kdf_cc_8a(shared_secret0,
            Eurydice_array_to_slice((size_t)32U, shared_secret_kdf, uint8_t));
  uint8_t shared_secret[32U] = {0U};
  libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_iot_ml_kem_types_as_ref_84_af(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret_kdf, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret_kdf,
                              uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t));
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_iot_ml_kem::ind_cca::validate_public_key::closure<Vector, K,
PUBLIC_KEY_SIZE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.validate_public_key.call_mut_42 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_42_64(
    void **_) {
  return ZERO_64_a7();
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_60(
    Eurydice_slice public_key, Eurydice_slice deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    deserialize_to_reduced_ring_element_a7(
        ring_element,
        &Eurydice_slice_index(
            deserialized_pk, i0,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
  }
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.serialize_vector
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void serialize_vector_60(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *key,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
               libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 re = key[i0];
    serialize_uncompressed_ring_element_a7(
        &re, scratch,
        Eurydice_slice_subslice3(
            out, i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            (i0 + (size_t)1U) *
                LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            uint8_t *));
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_mut_64(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *t_as_ntt,
    Eurydice_slice seed_for_a, Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  serialize_vector_60(
      t_as_ntt,
      Eurydice_slice_subslice3(
          serialized, (size_t)0U,
          libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)3U),
          uint8_t *),
      scratch);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_from(
          serialized,
          libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)3U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_public_key
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_iot_ml_kem_ind_cca_validate_public_key_64(uint8_t *public_key) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  deserialized_pk[i] = call_mut_42_64(&lvalue););
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1184U, public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
      uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_60(
      uu____0, Eurydice_array_to_slice(
                   (size_t)3U, deserialized_pk,
                   libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  uint8_t public_key_serialized[1184U] = {0U};
  libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *uu____1 =
      deserialized_pk;
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1184U, public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
      uint8_t, size_t, uint8_t[]);
  serialize_public_key_mut_64(
      uu____1, uu____2,
      Eurydice_array_to_slice((size_t)1184U, public_key_serialized, uint8_t),
      &scratch);
  return Eurydice_array_eq((size_t)1184U, public_key, public_key_serialized,
                           uint8_t);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key_only
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_only_39(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  uint8_t t[32U] = {0U};
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      Eurydice_array_to_subslice3(private_key->value, (size_t)384U * (size_t)3U,
                                  (size_t)768U * (size_t)3U + (size_t)32U,
                                  uint8_t *),
      Eurydice_array_to_slice((size_t)32U, t, uint8_t));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key->value, (size_t)768U * (size_t)3U + (size_t)32U,
      (size_t)768U * (size_t)3U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, t, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_b3(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_39(private_key);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $3size_t
*/
typedef struct IndCpaPrivateKeyUnpacked_df_s {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 secret_as_ntt[3U];
} IndCpaPrivateKeyUnpacked_df;

/**
This function found in impl {core::default::Default for
libcrux_iot_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.unpacked.default_1e
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE IndCpaPrivateKeyUnpacked_df default_1e_60(void) {
  IndCpaPrivateKeyUnpacked_df lit;
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] = ZERO_64_a7(););
  memcpy(lit.secret_as_ntt, repeat_expression,
         (size_t)3U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  return lit;
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $3size_t
- $9size_t
*/
typedef struct IndCpaPublicKeyUnpacked_12_s {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 A[9U];
} IndCpaPublicKeyUnpacked_12;

/**
This function found in impl {core::default::Default for
libcrux_iot_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.unpacked.default_1f
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static KRML_MUSTINLINE IndCpaPublicKeyUnpacked_12 default_1f_64(void) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 uu____0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  uu____0[i] = ZERO_64_a7(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_12 lit;
  memcpy(lit.t_as_ntt, uu____0,
         (size_t)3U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 repeat_expression[9U];
  KRML_MAYBE_FOR9(i, (size_t)0U, (size_t)9U, (size_t)1U,
                  repeat_expression[i] = ZERO_64_a7(););
  memcpy(lit.A, repeat_expression,
         (size_t)9U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  return lit;
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.cpa_keygen_seed_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void cpa_keygen_seed_cc_f9(
    Eurydice_slice key_generation_seed, Eurydice_slice out) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          seed, (size_t)0U,
          LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE,
          uint8_t *),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)3U;
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice((size_t)33U, seed, uint8_t), out);
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_64(
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *) <
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          uint8_t *randomness_i = Eurydice_slice_index(
              randomness, i1, uint8_t[504U], uint8_t(*)[504U]);
          int16_t *out_i =
              Eurydice_slice_index(out, i1, int16_t[272U], int16_t(*)[272U]);
          size_t sampled_coefficients_i =
              Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *);
          size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
              Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                          sampled_coefficients_i + (size_t)16U,
                                          int16_t *));
          size_t uu____0 = i1;
          Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                               size_t *) =
              Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                   size_t *) +
              sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) >=
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) =
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_640(
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *) <
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          uint8_t *randomness_i = Eurydice_slice_index(
              randomness, i1, uint8_t[168U], uint8_t(*)[168U]);
          int16_t *out_i =
              Eurydice_slice_index(out, i1, int16_t[272U], int16_t(*)[272U]);
          size_t sampled_coefficients_i =
              Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *);
          size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
              Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                          sampled_coefficients_i + (size_t)16U,
                                          int16_t *));
          size_t uu____0 = i1;
          Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                               size_t *) =
              Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                   size_t *) +
              sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) >=
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) =
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.sampling.sample_from_xof
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_from_xof_c91(
    Eurydice_slice seeds, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  libcrux_iot_ml_kem_hash_functions_portable_PortableHash xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  uint8_t randomness[3U][504U] = {{0U}};
  uint8_t randomness_blocksize[3U][168U] = {{0U}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state,
      Eurydice_array_to_slice((size_t)3U, randomness, uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_64(
      Eurydice_array_to_slice((size_t)3U, randomness, uint8_t[504U]),
      sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice((size_t)3U, randomness_blocksize,
                                              uint8_t[168U]));
      done = sample_from_uniform_distribution_next_640(
          Eurydice_array_to_slice((size_t)3U, randomness_blocksize,
                                  uint8_t[168U]),
          sampled_coefficients, out);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.sample_matrix_A
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_c90(Eurydice_slice A_transpose,
                                                uint8_t *seed, bool transpose) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_seed[34U];
      memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
      uint8_t seeds[3U][34U]; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          memcpy(seeds[i], copy_of_seed, (size_t)34U * sizeof(uint8_t)););
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      size_t sampled_coefficients[3U] = {0U}; int16_t out[3U][272U] = {{0U}};
      sample_from_xof_c91(
          Eurydice_array_to_slice((size_t)3U, seeds, uint8_t[34U]),
          Eurydice_array_to_slice((size_t)3U, sampled_coefficients, size_t),
          Eurydice_array_to_slice((size_t)3U, out, int16_t[272U]));
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice((size_t)3U, out, int16_t[272U]),
                   int16_t[272U]);
           i++) {
        size_t j = i;
        int16_t sample[272U];
        memcpy(sample, out[j], (size_t)272U * sizeof(int16_t));
        if (transpose) {
          Eurydice_slice uu____1 = Eurydice_array_to_subslice_to(
              (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
          from_i16_array_64_a7(
              uu____1,
              &Eurydice_slice_index(
                  A_transpose, j * (size_t)3U + i1,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
        } else {
          Eurydice_slice uu____2 = Eurydice_array_to_subslice_to(
              (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
          from_i16_array_64_a7(
              uu____2,
              &Eurydice_slice_index(
                  A_transpose, i1 * (size_t)3U + j,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
        }
      });
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE= 384
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_140(
    Eurydice_slice re_as_ntt, uint8_t *prf_input, uint8_t domain_separator,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[384U] = {0U};
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      Eurydice_array_to_slice((size_t)3U, prf_inputs, uint8_t[33U]),
      Eurydice_array_to_slice((size_t)384U, prf_outputs, uint8_t),
      (size_t)128U);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      Eurydice_slice randomness = Eurydice_array_to_subslice3(
          prf_outputs, i0 * (size_t)128U, (i0 + (size_t)1U) * (size_t)128U,
          uint8_t *);
      int16_t sample_buffer[256U] = {0U};
      sample_from_binomial_distribution_0b(randomness, sample_buffer);
      from_i16_array_64_a7(
          Eurydice_array_to_slice((size_t)256U, sample_buffer, int16_t),
          &Eurydice_slice_index(
              re_as_ntt, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
      ntt_binomially_sampled_ring_element_a7(
          &Eurydice_slice_index(
              re_as_ntt, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
          scratch););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_iot_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, K_SQUARED, ETA1, ETA1_RANDOMNESS_SIZE,
PRF_OUTPUT_SIZE1>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3,
TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_58 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_58_160(
    void **_) {
  return ZERO_64_a7();
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.entry
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *entry_60(
    Eurydice_slice matrix, size_t i, size_t j) {
  return &Eurydice_slice_index(
      matrix, i * (size_t)3U + j,
      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *);
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_As_plus_e
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_As_plus_e_60(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *t_as_ntt,
    Eurydice_slice matrix_A,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *s_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *s_cache,
    int32_t *accumulator) {
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *uu____0 =
          entry_60(matrix_A, (size_t)0U, j);
      accumulating_ntt_multiply_fill_cache_64_a7(uu____0, &s_as_ntt[j],
                                                 accumulator, &s_cache[j]););
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, accumulator, int32_t), t_as_ntt);
  add_standard_error_reduce_64_a7(t_as_ntt, error_as_ntt);
  KRML_MAYBE_FOR2(
      i, (size_t)1U, (size_t)3U, (size_t)1U, size_t i0 = i;
      int32_t buf[256U] = {0U}; accumulator = buf; KRML_MAYBE_FOR3(
          i1, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i1;
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *uu____1 =
              entry_60(matrix_A, i0, j);
          accumulating_ntt_multiply_use_cache_64_a7(uu____1, &s_as_ntt[j],
                                                    accumulator, &s_cache[j]););
      reducing_from_i32_array_64_a7(
          Eurydice_array_to_slice((size_t)256U, accumulator, int32_t),
          &t_as_ntt[i0]);
      add_standard_error_reduce_64_a7(&t_as_ntt[i0], &error_as_ntt[i0]););
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_160(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_df *private_key,
    IndCpaPublicKeyUnpacked_12 *public_key,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *scratch,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *s_cache,
    int32_t *accumulator) {
  uint8_t hashed[64U] = {0U};
  cpa_keygen_seed_cc_f9(key_generation_seed,
                        Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_slice uu____1 = Eurydice_array_to_slice(
      (size_t)9U, public_key->A,
      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12);
  uint8_t ret[34U];
  libcrux_iot_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  sample_matrix_A_c90(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_iot_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                                prf_input);
  uint8_t domain_separator = sample_vector_cbd_then_ntt_140(
      Eurydice_array_to_slice(
          (size_t)3U, private_key->secret_as_ntt,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      prf_input, 0U, scratch->coefficients);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 error_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_as_ntt[i] = call_mut_58_160(&lvalue););
  sample_vector_cbd_then_ntt_140(
      Eurydice_array_to_slice(
          (size_t)3U, error_as_ntt,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      prf_input, domain_separator, scratch->coefficients);
  compute_As_plus_e_60(
      public_key->t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)9U, public_key->A,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      private_key->secret_as_ntt, error_as_ntt, s_cache, accumulator);
  uint8_t uu____2[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U],
                           core_array_TryFromSliceError);
  core_result_unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.serialize_unpacked_secret_key with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- K_SQUARED= 9
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static void serialize_unpacked_secret_key_7c(
    IndCpaPublicKeyUnpacked_12 *public_key,
    IndCpaPrivateKeyUnpacked_df *private_key,
    Eurydice_slice serialized_private_key, Eurydice_slice serialized_public_key,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  serialize_public_key_mut_64(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      serialized_public_key, scratch);
  serialize_vector_60(private_key->secret_as_ntt, serialized_private_key,
                      scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE void generate_keypair_640(
    Eurydice_slice key_generation_seed,
    Eurydice_slice serialized_ind_cpa_private_key,
    Eurydice_slice serialized_public_key,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *scratch,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *s_cache,
    int32_t *accumulator) {
  IndCpaPrivateKeyUnpacked_df private_key = default_1e_60();
  IndCpaPublicKeyUnpacked_12 public_key = default_1f_64();
  generate_keypair_unpacked_160(key_generation_seed, &private_key, &public_key,
                                scratch, s_cache, accumulator);
  serialize_unpacked_secret_key_7c(
      &public_key, &private_key, serialized_ind_cpa_private_key,
      serialized_public_key, scratch->coefficients);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.serialize_kem_secret_key_mut with types
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_39(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      public_key,
      Eurydice_array_to_subslice3(
          serialized, pointer,
          pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t *));
  pointer = pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____6 = serialized;
  size_t uu____7 = pointer;
  size_t uu____8 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____6, uu____7,
          uu____8 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
libcrux_iot_ml_kem_mlkem768_MlKem768KeyPair
libcrux_iot_ml_kem_ind_cca_generate_keypair_b70(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  uint8_t public_key[1184U] = {0U};
  uint8_t secret_key_serialized[2400U] = {0U};
  uint8_t ind_cpa_private_key[1152U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 scratch = ZERO_64_a7();
  int32_t accumulator[256U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 s_cache[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  s_cache[i] = ZERO_64_a7(););
  generate_keypair_640(
      ind_cpa_keypair_randomness,
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t), &scratch,
      s_cache, accumulator);
  serialize_kem_secret_key_mut_39(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 private_key =
      libcrux_iot_ml_kem_types_from_56_28(copy_of_secret_key_serialized);
  libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 uu____1 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_iot_ml_kem_types_from_d9_74(
      uu____1, libcrux_iot_ml_kem_types_from_18_d0(copy_of_public_key));
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.entropy_preprocess_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void entropy_preprocess_cc_f9(Eurydice_slice randomness,
                                                     Eurydice_slice out) {
  Eurydice_slice_copy(out, randomness, uint8_t);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_iot_ml_kem::ind_cca::encapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE,
T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE, VECTOR_U_COMPRESSION_FACTOR,
VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1, PRF_OUTPUT_SIZE2>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate.call_mut_92
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_92_350(
    void **_) {
  return ZERO_64_a7();
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_iot_ml_kem::ind_cpa::encrypt_c1::closure<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1.call_mut_6f
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_6f_920(
    void **_) {
  return ZERO_64_a7();
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
- PRF_OUTPUT_SIZE= 384
*/
static KRML_MUSTINLINE uint8_t
sample_ring_element_cbd_140(uint8_t *prf_input, uint8_t domain_separator,
                            Eurydice_slice error_1, int16_t *sample_buffer) {
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[384U] = {0U};
  Eurydice_slice uu____0 = core_array___Array_T__N___as_slice(
      (size_t)3U, prf_inputs, uint8_t[33U], Eurydice_slice);
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      uu____0, Eurydice_array_to_slice((size_t)384U, prf_outputs, uint8_t),
      (size_t)128U);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      Eurydice_slice randomness = Eurydice_array_to_subslice3(
          prf_outputs, i0 * (size_t)128U, (i0 + (size_t)1U) * (size_t)128U,
          uint8_t *);
      sample_from_binomial_distribution_0b(randomness, sample_buffer);
      from_i16_array_64_a7(
          Eurydice_array_to_slice((size_t)256U, sample_buffer, int16_t),
          &Eurydice_slice_index(
              error_1, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_iot_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1.call_mut_33
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_33_920(
    void **_) {
  return ZERO_64_a7();
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_60(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t zeta_i =
      LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_a7(&zeta_i, re);
  invert_ntt_at_layer_2_a7(&zeta_i, re);
  invert_ntt_at_layer_3_a7(&zeta_i, re);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)7U, scratch);
  poly_barrett_reduce_64_a7(re);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_vector_u_c90(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *matrix_entry,
    Eurydice_slice seed, Eurydice_slice r_as_ntt, Eurydice_slice error_1,
    Eurydice_slice result,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  int32_t buf0[256U] = {0U};
  accumulator = buf0;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
      sample_matrix_entry_36(matrix_entry, seed, (size_t)0U, j);
      accumulating_ntt_multiply_fill_cache_64_a7(
          matrix_entry,
          &Eurydice_slice_index(
              r_as_ntt, j,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
          accumulator,
          &Eurydice_slice_index(
              cache, j, libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, accumulator, int32_t),
      &Eurydice_slice_index(
          result, (size_t)0U,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
  invert_ntt_montgomery_60(
      &Eurydice_slice_index(
          result, (size_t)0U,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
      scratch);
  add_error_reduce_64_a7(
      &Eurydice_slice_index(
          result, (size_t)0U,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
      &Eurydice_slice_index(
          error_1, (size_t)0U,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
  KRML_MAYBE_FOR2(
      i, (size_t)1U, (size_t)3U, (size_t)1U, size_t i0 = i;
      int32_t buf[256U] = {0U}; accumulator = buf; KRML_MAYBE_FOR3(
          i1, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i1;
          sample_matrix_entry_36(matrix_entry, seed, i0, j);
          accumulating_ntt_multiply_use_cache_64_a7(
              matrix_entry,
              &Eurydice_slice_index(
                  r_as_ntt, j,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
              accumulator,
              &Eurydice_slice_index(
                  cache, j,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
      reducing_from_i32_array_64_a7(
          Eurydice_array_to_slice((size_t)256U, accumulator, int32_t),
          &Eurydice_slice_index(
              result, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
      invert_ntt_montgomery_60(
          &Eurydice_slice_index(
              result, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
          scratch);
      add_error_reduce_64_a7(
          &Eurydice_slice_index(
              result, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
          &Eurydice_slice_index(
              error_1, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_10 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_10_7b(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re->coefficients[i0], scratch);
    compress_4e_ef(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_10_4e(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)20U * i0,
                                 (size_t)20U * i0 + (size_t)20U, uint8_t *));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_c3(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  compress_then_serialize_10_7b(re, serialized, scratch);
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- OUT_LEN= 960
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_u_7c(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 input[3U],
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
               libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12);
       i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 re = input[i0];
    compress_then_serialize_ring_element_u_c3(
        &re,
        Eurydice_slice_subslice3(
            out, i0 * ((size_t)960U / (size_t)3U),
            (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t *),
        scratch);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE void encrypt_c1_920(
    Eurydice_slice randomness,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *matrix_entry,
    Eurydice_slice seed_for_a, Eurydice_slice ciphertext,
    Eurydice_slice r_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_2,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  uint8_t prf_input[33U];
  libcrux_iot_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_140(r_as_ntt, prf_input, 0U, scratch);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 error_1[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_1[i] = call_mut_6f_920(&lvalue););
  int16_t sampling_buffer[256U] = {0U};
  uint8_t domain_separator = sample_ring_element_cbd_140(
      prf_input, domain_separator0,
      Eurydice_array_to_slice(
          (size_t)3U, error_1,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      sampling_buffer);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U] = {0U};
  PRF_07_a6(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
            Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  sample_from_binomial_distribution_0b(
      Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t),
      sampling_buffer);
  from_i16_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, sampling_buffer, int16_t), error_2);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 u[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  u[i] = call_mut_33_920(&lvalue););
  compute_vector_u_c90(
      matrix_entry, seed_for_a, r_as_ntt,
      Eurydice_array_to_slice(
          (size_t)3U, error_1,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      Eurydice_array_to_slice(
          (size_t)3U, u,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      scratch, cache, accumulator);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 copy_of_u[3U];
  memcpy(copy_of_u, u,
         (size_t)3U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  compress_then_serialize_u_7c(copy_of_u, ciphertext, scratch);
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_ring_element_v
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_ring_element_v_60(
    Eurydice_slice public_key,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *t_as_ntt_entry,
    Eurydice_slice r_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_2,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *message,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *result,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  int32_t buf[256U] = {0U};
  accumulator = buf;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    deserialize_to_reduced_ring_element_a7(ring_element, t_as_ntt_entry);
    accumulating_ntt_multiply_use_cache_64_a7(
        t_as_ntt_entry,
        &Eurydice_slice_index(
            r_as_ntt, i0,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
        accumulator,
        &Eurydice_slice_index(
            cache, i0, libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
  }
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, accumulator, int32_t), result);
  invert_ntt_montgomery_60(result, scratch);
  add_message_error_reduce_64_a7(error_2, message, result, scratch);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_6e(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 re,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  compress_then_serialize_4_a7(re, out, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_6e(
    Eurydice_slice public_key,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *t_as_ntt_entry,
    Eurydice_slice r_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_2,
    uint8_t *message, Eurydice_slice ciphertext,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12
      message_as_ring_element = ZERO_64_a7();
  deserialize_then_decompress_message_a7(message, &message_as_ring_element);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 v = ZERO_64_a7();
  compute_ring_element_v_60(public_key, t_as_ntt_entry, r_as_ntt, error_2,
                            &message_as_ring_element, &v, scratch, cache,
                            accumulator);
  compress_then_serialize_ring_element_v_6e(v, ciphertext, scratch);
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_LEN= 960
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE void encrypt_5a0(
    Eurydice_slice public_key, uint8_t *message, Eurydice_slice randomness,
    Eurydice_slice ciphertext,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *matrix_entry,
    Eurydice_slice r_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *error_2,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice cache, int32_t *accumulator) {
  encrypt_c1_920(
      randomness, matrix_entry,
      Eurydice_slice_subslice_from(public_key, (size_t)1152U, uint8_t, size_t,
                                   uint8_t[]),
      Eurydice_slice_subslice3(ciphertext, (size_t)0U, (size_t)960U, uint8_t *),
      r_as_ntt, error_2, scratch, cache, accumulator);
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  encrypt_c2_6e(uu____0, matrix_entry, r_as_ntt, error_2, message,
                Eurydice_slice_subslice_from(ciphertext, (size_t)960U, uint8_t,
                                             size_t, uint8_t[]),
                scratch, cache, accumulator);
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.kdf_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE void kdf_cc_39(Eurydice_slice shared_secret,
                                      Eurydice_slice out) {
  Eurydice_slice_copy(out, shared_secret, uint8_t);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
tuple_f4 libcrux_iot_ml_kem_ind_cca_encapsulate_350(
    libcrux_iot_ml_kem_types_MlKemPublicKey_30 *public_key,
    uint8_t *randomness) {
  uint8_t processed_randomness[32U] = {0U};
  entropy_preprocess_cc_f9(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, processed_randomness, uint8_t));
  uint8_t to_hash[64U];
  libcrux_iot_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, processed_randomness, uint8_t),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_iot_ml_kem_types_as_slice_63_d0(public_key),
      uint8_t);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
          uint8_t, size_t, uint8_t[]));
  uint8_t hashed[64U] = {0U};
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[1088U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 r_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  r_as_ntt[i] = call_mut_92_350(&lvalue););
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 error_2 = ZERO_64_a7();
  libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  int32_t accumulator[256U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 cache[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  cache[i] = ZERO_64_a7(););
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 matrix_entry =
      ZERO_64_a7();
  encrypt_5a0(Eurydice_array_to_slice(
                  (size_t)1184U,
                  libcrux_iot_ml_kem_types_as_slice_63_d0(public_key), uint8_t),
              processed_randomness, pseudorandomness,
              Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t),
              &matrix_entry,
              Eurydice_array_to_slice(
                  (size_t)3U, r_as_ntt,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
              &error_2, &scratch,
              Eurydice_array_to_slice(
                  (size_t)3U, cache,
                  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
              accumulator);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_iot_ml_kem_types_from_9d_80(copy_of_ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  kdf_cc_39(shared_secret,
            Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t));
  libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext uu____3 = ciphertext0;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_f4 lit;
  lit.fst = uu____3;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_iot_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt.call_mut_a5
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_a5_4d(
    void **_) {
  return ZERO_64_a7();
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.deserialize_vector
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_vector_60(
    Eurydice_slice secret_key, Eurydice_slice secret_as_ntt) {
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      deserialize_to_uncompressed_ring_element_a7(
          Eurydice_slice_subslice3(
              secret_key,
              i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *),
          &Eurydice_slice_index(
              secret_as_ntt, i0,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
              libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *)););
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_iot_ml_kem::ind_cpa::decrypt_unpacked::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.decrypt_unpacked.call_mut_b7 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_b7_4d(
    void **_) {
  return ZERO_64_a7();
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_u_cf(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *output) {
  deserialize_then_decompress_10_a7(serialized, output);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_cf(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *re,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)7U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  ntt_at_layer_3_a7(&zeta_i, re);
  ntt_at_layer_2_a7(&zeta_i, re);
  ntt_at_layer_1_a7(&zeta_i, re);
  poly_barrett_reduce_64_a7(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.deserialize_then_decompress_u with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_6e(
    uint8_t *ciphertext, Eurydice_slice u_as_ntt,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U),
        i0 * (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U) +
            LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U,
        uint8_t *);
    deserialize_then_decompress_ring_element_u_cf(
        u_bytes, &Eurydice_slice_index(
                     u_as_ntt, i0,
                     libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
                     libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *));
    ntt_vector_u_cf(
        &Eurydice_slice_index(
            u_as_ntt, i0,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12,
            libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *),
        scratch);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_v_64(
    Eurydice_slice serialized,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *output) {
  deserialize_then_decompress_4_a7(serialized, output);
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_message
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_message_60(
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *v,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *secret_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *u_as_ntt,
    libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 *result,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int32_t *accumulator) {
  int32_t buf[256U] = {0U};
  accumulator = buf;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  accumulating_ntt_multiply_64_a7(&secret_as_ntt[i0],
                                                  &u_as_ntt[i0], accumulator););
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice((size_t)256U, accumulator, int32_t), result);
  invert_ntt_montgomery_60(result, scratch);
  subtract_reduce_64_a7(v, result);
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void decrypt_unpacked_4d(
    IndCpaPrivateKeyUnpacked_df *secret_key, uint8_t *ciphertext,
    Eurydice_slice decrypted,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int32_t *accumulator) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 u_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  u_as_ntt[i] = call_mut_b7_4d(&lvalue););
  deserialize_then_decompress_u_6e(
      ciphertext,
      Eurydice_array_to_slice(
          (size_t)3U, u_as_ntt,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      scratch);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 v = ZERO_64_a7();
  deserialize_then_decompress_ring_element_v_64(
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]),
      &v);
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 message = ZERO_64_a7();
  compute_message_60(&v, secret_key->secret_as_ntt, u_as_ntt, &message, scratch,
                     accumulator);
  compress_then_serialize_message_a7(&message, decrypted, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void decrypt_4d(
    Eurydice_slice secret_key, uint8_t *ciphertext, Eurydice_slice decrypted,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int32_t *accumulator) {
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 secret_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  secret_as_ntt[i] = call_mut_a5_4d(&lvalue););
  deserialize_vector_60(
      secret_key, Eurydice_array_to_slice(
                      (size_t)3U, secret_as_ntt,
                      libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12
      copy_of_secret_as_ntt[3U];
  memcpy(copy_of_secret_as_ntt, secret_as_ntt,
         (size_t)3U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  IndCpaPrivateKeyUnpacked_df secret_key_unpacked;
  memcpy(secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
         (size_t)3U *
             sizeof(libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12));
  decrypt_unpacked_4d(&secret_key_unpacked, ciphertext, decrypted, scratch,
                      accumulator);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_iot_ml_kem::ind_cca::decapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, SECRET_KEY_SIZE, CPA_SECRET_KEY_SIZE,
PUBLIC_KEY_SIZE, CIPHERTEXT_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE,
VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2, IMPLICIT_REJECTION_HASH_INPUT_SIZE>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate.call_mut_9b
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 call_mut_9b_1b0(
    void **_) {
  return ZERO_64_a7();
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
void libcrux_iot_ml_kem_ind_cca_decapsulate_1b0(
    libcrux_iot_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_iot_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_iot_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U] = {0U};
  libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  int32_t accumulator[256U] = {0U};
  decrypt_4d(ind_cpa_secret_key, ciphertext->value,
             Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), &scratch,
             accumulator);
  uint8_t to_hash0[64U];
  libcrux_iot_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(Eurydice_array_to_subslice_from(
                          (size_t)64U, to_hash0,
                          LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
                          uint8_t, size_t, uint8_t[]),
                      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U] = {0U};
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_iot_ml_kem_utils_into_padded_array_15(implicit_rejection_value,
                                                to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____2, libcrux_iot_ml_kem_types_as_ref_84_80(ciphertext), uint8_t);
  uint8_t implicit_rejection_shared_secret[32U] = {0U};
  PRF_07_9e(Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
            Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret, uint8_t));
  uint8_t expected_ciphertext[1088U] = {0U};
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 r_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  r_as_ntt[i] = call_mut_9b_1b0(&lvalue););
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 error_2 = ZERO_64_a7();
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 cache[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  cache[i] = ZERO_64_a7(););
  libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12 matrix_entry =
      ZERO_64_a7();
  encrypt_5a0(
      ind_cpa_public_key, decrypted, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      &matrix_entry,
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      &error_2, &scratch,
      Eurydice_array_to_slice(
          (size_t)3U, cache,
          libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12),
      accumulator);
  uint8_t implicit_rejection_shared_secret_kdf[32U] = {0U};
  kdf_cc_39(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret, uint8_t),
            Eurydice_array_to_slice(
                (size_t)32U, implicit_rejection_shared_secret_kdf, uint8_t));
  uint8_t shared_secret_kdf[32U] = {0U};
  kdf_cc_39(shared_secret0,
            Eurydice_array_to_slice((size_t)32U, shared_secret_kdf, uint8_t));
  uint8_t shared_secret[32U] = {0U};
  libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_iot_ml_kem_types_as_ref_84_80(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret_kdf, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret_kdf,
                              uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t));
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
}
