/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: cdf02f9d8ed0d73f88c0a495c5b79359a51398fc
 * Karamel: 8e7262955105599e91f3a99c9ab3d3387f7046f2
 * F*: 89901492c020c74b82d811d27f3149c222d9b8b5
 * Libcrux: 2259f47ca2a2a060c9fd147ccc78ed3588bfd288
 */

#include "internal/libcrux_iot_mlkem_portable.h"

#include "internal/libcrux_iot_core.h"
#include "internal/libcrux_iot_sha3.h"
#include "libcrux_iot_core.h"
#include "libcrux_iot_sha3.h"

KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_G(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output) {
  libcrux_iot_sha3_portable_sha512(output, input);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_H(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output) {
  libcrux_iot_sha3_portable_sha256(output, input);
}

inline void libcrux_iot_ml_kem_hash_functions_portable_PRFxN(
    Eurydice_dst_ref_shared_d2 input, Eurydice_mut_borrow_slice_u8 outputs,
    size_t out_len) {
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(input, Eurydice_arr_3e);
       i++) {
    size_t i0 = i;
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_7e(
        outputs,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * out_len, .end = (i0 + (size_t)1U) * out_len}));
    libcrux_iot_sha3_portable_shake256(
        uu____0, core_array___Array_T__N___as_slice(
                     (size_t)33U,
                     &Eurydice_slice_index_shared(input, i0, Eurydice_arr_3e),
                     uint8_t, Eurydice_borrow_slice_u8));
  }
}

KRML_MUSTINLINE Eurydice_arr_5e
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final(
    Eurydice_dst_ref_shared_60 input) {
  Eurydice_arr_5e shake128_state;
  libcrux_iot_sha3_state_KeccakState repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] =
        libcrux_iot_sha3_portable_incremental_shake128_init();
  }
  memcpy(shake128_state.data, repeat_expression,
         (size_t)4U * sizeof(libcrux_iot_sha3_state_KeccakState));
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(input, Eurydice_arr_48);
       i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_KeccakState *uu____0 = &shake128_state.data[i0];
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_48 lvalue = libcrux_secrets_int_public_integers_classify_27_2c(
        Eurydice_slice_index_shared(input, i0, Eurydice_arr_48));
    libcrux_iot_sha3_portable_incremental_shake128_absorb_final(
        uu____0, Eurydice_array_to_slice_shared_8d(&lvalue));
  }
  return shake128_state;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
    Eurydice_arr_5e *st, Eurydice_dst_ref_mut_ea outputs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len((KRML_CLITERAL(Eurydice_dst_ref_shared_ea){
                                  .ptr = outputs.ptr, .meta = outputs.meta}),
                              Eurydice_arr_b0);
       i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_KeccakState *uu____0 = &st->data[i0];
    /* original Rust expression is not an lvalue in C */
    Eurydice_mut_borrow_slice_u8 lvalue =
        core_array___Array_T__N___as_mut_slice(
            (size_t)504U,
            &Eurydice_slice_index_mut(outputs, i0, Eurydice_arr_b0), uint8_t,
            Eurydice_mut_borrow_slice_u8);
    libcrux_iot_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
        uu____0, libcrux_secrets_int_classify_public_classify_ref_mut_a1_47(
                     &lvalue)[0U]);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
    Eurydice_arr_5e *st, Eurydice_dst_ref_mut_36 outputs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len((KRML_CLITERAL(Eurydice_dst_ref_shared_36){
                                  .ptr = outputs.ptr, .meta = outputs.meta}),
                              Eurydice_arr_27);
       i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_KeccakState *uu____0 = &st->data[i0];
    /* original Rust expression is not an lvalue in C */
    Eurydice_mut_borrow_slice_u8 lvalue =
        core_array___Array_T__N___as_mut_slice(
            (size_t)168U,
            &Eurydice_slice_index_mut(outputs, i0, Eurydice_arr_27), uint8_t,
            Eurydice_mut_borrow_slice_u8);
    libcrux_iot_sha3_portable_incremental_shake128_squeeze_next_block(
        uu____0, libcrux_secrets_int_classify_public_classify_ref_mut_a1_47(
                     &lvalue)[0U]);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_G_07(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output) {
  libcrux_iot_ml_kem_hash_functions_portable_G(input, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_H_07(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output) {
  libcrux_iot_ml_kem_hash_functions_portable_H(input, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
inline void libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
    Eurydice_dst_ref_shared_d2 input, Eurydice_mut_borrow_slice_u8 outputs,
    size_t out_len) {
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN(input, outputs, out_len);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE Eurydice_arr_5e
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
    Eurydice_dst_ref_shared_60 input) {
  return libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final(
      input);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
    Eurydice_arr_5e *self, Eurydice_dst_ref_mut_ea output) {
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
      self, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
    Eurydice_arr_5e *self, Eurydice_dst_ref_mut_36 output) {
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
      self, output);
}

#define ZETAS_TIMES_MONTGOMERY_R                                     \
  ((KRML_CLITERAL(Eurydice_arr_49){                                  \
      .data = {(int16_t) - 1044, (int16_t) - 758,  (int16_t) - 359,  \
               (int16_t) - 1517, (int16_t)1493,    (int16_t)1422,    \
               (int16_t)287,     (int16_t)202,     (int16_t) - 171,  \
               (int16_t)622,     (int16_t)1577,    (int16_t)182,     \
               (int16_t)962,     (int16_t) - 1202, (int16_t) - 1474, \
               (int16_t)1468,    (int16_t)573,     (int16_t) - 1325, \
               (int16_t)264,     (int16_t)383,     (int16_t) - 829,  \
               (int16_t)1458,    (int16_t) - 1602, (int16_t) - 130,  \
               (int16_t) - 681,  (int16_t)1017,    (int16_t)732,     \
               (int16_t)608,     (int16_t) - 1542, (int16_t)411,     \
               (int16_t) - 205,  (int16_t) - 1571, (int16_t)1223,    \
               (int16_t)652,     (int16_t) - 552,  (int16_t)1015,    \
               (int16_t) - 1293, (int16_t)1491,    (int16_t) - 282,  \
               (int16_t) - 1544, (int16_t)516,     (int16_t) - 8,    \
               (int16_t) - 320,  (int16_t) - 666,  (int16_t) - 1618, \
               (int16_t) - 1162, (int16_t)126,     (int16_t)1469,    \
               (int16_t) - 853,  (int16_t) - 90,   (int16_t) - 271,  \
               (int16_t)830,     (int16_t)107,     (int16_t) - 1421, \
               (int16_t) - 247,  (int16_t) - 951,  (int16_t) - 398,  \
               (int16_t)961,     (int16_t) - 1508, (int16_t) - 725,  \
               (int16_t)448,     (int16_t) - 1065, (int16_t)677,     \
               (int16_t) - 1275, (int16_t) - 1103, (int16_t)430,     \
               (int16_t)555,     (int16_t)843,     (int16_t) - 1251, \
               (int16_t)871,     (int16_t)1550,    (int16_t)105,     \
               (int16_t)422,     (int16_t)587,     (int16_t)177,     \
               (int16_t) - 235,  (int16_t) - 291,  (int16_t) - 460,  \
               (int16_t)1574,    (int16_t)1653,    (int16_t) - 246,  \
               (int16_t)778,     (int16_t)1159,    (int16_t) - 147,  \
               (int16_t) - 777,  (int16_t)1483,    (int16_t) - 602,  \
               (int16_t)1119,    (int16_t) - 1590, (int16_t)644,     \
               (int16_t) - 872,  (int16_t)349,     (int16_t)418,     \
               (int16_t)329,     (int16_t) - 156,  (int16_t) - 75,   \
               (int16_t)817,     (int16_t)1097,    (int16_t)603,     \
               (int16_t)610,     (int16_t)1322,    (int16_t) - 1285, \
               (int16_t) - 1465, (int16_t)384,     (int16_t) - 1215, \
               (int16_t) - 136,  (int16_t)1218,    (int16_t) - 1335, \
               (int16_t) - 874,  (int16_t)220,     (int16_t) - 1187, \
               (int16_t) - 1659, (int16_t) - 1185, (int16_t) - 1530, \
               (int16_t) - 1278, (int16_t)794,     (int16_t) - 1510, \
               (int16_t) - 854,  (int16_t) - 870,  (int16_t)478,     \
               (int16_t) - 108,  (int16_t) - 308,  (int16_t)996,     \
               (int16_t)991,     (int16_t)958,     (int16_t) - 1460, \
               (int16_t)1522,    (int16_t)1628}}))

static KRML_MUSTINLINE int16_t zeta(size_t i) {
  return ZETAS_TIMES_MONTGOMERY_R.data[i];
}

#define VECTORS_IN_RING_ELEMENT                                \
  (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / \
   LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR)

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_iot_ml_kem_vector_portable_vector_type_zero(void) {
  return libcrux_secrets_int_public_integers_classify_27_3a(
      (KRML_CLITERAL(Eurydice_arr_e2){.data = {0U}}));
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE Eurydice_arr_e2
libcrux_iot_ml_kem_vector_portable_ZERO_4e(void) {
  return libcrux_iot_ml_kem_vector_portable_vector_type_zero();
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_borrow_slice_i16 array, Eurydice_arr_e2 *out) {
  Eurydice_slice_copy(Eurydice_array_to_slice_mut_b4(out),
                      Eurydice_slice_subslice_shared_76(
                          array, (KRML_CLITERAL(core_ops_range_Range_08){
                                     .start = (size_t)0U, .end = (size_t)16U})),
                      int16_t);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_from_i16_array_4e(
    Eurydice_borrow_slice_i16 array, Eurydice_arr_e2 *out) {
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
  int32_t k = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(libcrux_secrets_int_as_i16_36(value)),
      libcrux_secrets_int_as_i32_b8(libcrux_secrets_int_public_integers_classify_27_df(
          LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R)));
  int32_t k_times_modulus = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(libcrux_secrets_int_as_i16_36(k)),
      libcrux_secrets_int_as_i32_f5(
          libcrux_secrets_int_public_integers_classify_27_39(
              LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
  int16_t c = libcrux_secrets_int_as_i16_36(
      k_times_modulus >>
      (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int16_t value_high = libcrux_secrets_int_as_i16_36(
      value >>
      (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int16_t res = core_num__i16__wrapping_sub(value_high, c);
  return res;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_reducing_from_i32_array(
    Eurydice_dst_ref_shared_fc array, Eurydice_arr_e2 *out) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
            Eurydice_slice_index_shared(array, i0, int32_t));
    out->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_reducing_from_i32_array_4e(
    Eurydice_dst_ref_shared_fc array, Eurydice_arr_e2 *out) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_reducing_from_i32_array(array,
                                                                        out);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_add(
    Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    lhs->data[i0] = core_num__i16__wrapping_add(lhs->data[i0], rhs->data[i0]);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_add_4e(
    Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_sub(
    Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = core_num__i16__wrapping_sub(lhs->data[i0], rhs->data[i0]);
    lhs->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_sub_4e(
    Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_sub(lhs, rhs);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_negate(
    Eurydice_arr_e2 *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = core_num__i16__wrapping_neg(vec->data[i0]);
    vec->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_negate_4e(
    Eurydice_arr_e2 *vec) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_negate(vec);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    Eurydice_arr_e2 *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = core_num__i16__wrapping_mul(vec->data[i0], c);
    vec->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_multiply_by_constant_4e(
    Eurydice_arr_e2 *vec, int16_t c) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_multiply_by_constant(vec, c);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    Eurydice_arr_e2 *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->data[uu____0] = vec->data[uu____0] & c;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(
    Eurydice_arr_e2 *vec, int16_t c) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(vec,
                                                                          c);
}

/**
 Note: This function is not secret independent
 Only use with public values.
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    Eurydice_arr_e2 *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    if (libcrux_secrets_int_public_integers_declassify_d8_39(vec->data[i0]) >=
        (int16_t)3329) {
      int16_t uu____0 =
          core_num__i16__wrapping_sub(vec->data[i0], (int16_t)3329);
      vec->data[i0] = uu____0;
    }
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_cond_subtract_3329_4e(
    Eurydice_arr_e2 *vec) {
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
  int32_t t = core_num__i32__wrapping_add(
      core_num__i32__wrapping_mul(
          libcrux_secrets_int_as_i32_f5(value),
          LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER),
      LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_R >> 1U);
  int16_t quotient = libcrux_secrets_int_as_i16_36(
      t >> (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT);
  int16_t uu____0 = value;
  int16_t result = core_num__i16__wrapping_sub(
      uu____0, core_num__i16__wrapping_mul(
                   quotient, LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  return result;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce(
    Eurydice_arr_e2 *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t vi =
        libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
            vec->data[i0]);
    vec->data[i0] = vi;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(
    Eurydice_arr_e2 *vec) {
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
  int32_t product = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(fe), libcrux_secrets_int_as_i32_f5(fer));
  return libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
      product);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    Eurydice_arr_e2 *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
            vec->data[i0], c);
    vec->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
    Eurydice_arr_e2 *vec, int16_t r) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
      vec, libcrux_secrets_int_public_integers_classify_27_39(r));
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
  int16_t shifted = core_num__i16__wrapping_sub(
      libcrux_secrets_int_public_integers_classify_27_39((int16_t)1664),
      libcrux_secrets_int_as_i16_ca(fe));
  int16_t mask = shifted >> 15U;
  int16_t shifted_to_positive = mask ^ shifted;
  int16_t shifted_positive_in_range =
      core_num__i16__wrapping_sub(shifted_to_positive, (int16_t)832);
  int16_t r0 = shifted_positive_in_range >> 15U;
  int16_t r1 = r0 & (int16_t)1;
  return libcrux_secrets_int_as_u8_f5(r1);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_compress_compress_1(
    Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_59(
        libcrux_iot_ml_kem_vector_portable_compress_compress_message_coefficient(
            libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_compress_1_4e(
    Eurydice_arr_e2 *a) {
  libcrux_iot_ml_kem_vector_portable_compress_compress_1(a);
}

KRML_MUSTINLINE uint32_t
libcrux_iot_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value) {
  uint32_t uu____0 = value;
  return uu____0 & core_num__u32__wrapping_sub(1U << (uint32_t)n, 1U);
}

KRML_MUSTINLINE int16_t
libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe) {
  uint64_t compressed = libcrux_secrets_int_as_u64_ca(fe)
                        << (uint32_t)coefficient_bits;
  compressed = core_num__u64__wrapping_add(compressed, 1664ULL);
  compressed = core_num__u64__wrapping_mul(compressed, 10321340ULL);
  compressed = compressed >> 35U;
  return libcrux_secrets_int_as_i16_b8(
      libcrux_iot_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
          coefficient_bits, libcrux_secrets_int_as_u32_a3(compressed)));
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(
    Eurydice_arr_e2 *vec, int16_t zeta, size_t i, size_t j) {
  int16_t t =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          vec->data[j],
          libcrux_secrets_int_public_integers_classify_27_39(zeta));
  int16_t a_minus_t = core_num__i16__wrapping_sub(vec->data[i], t);
  int16_t a_plus_t = core_num__i16__wrapping_add(vec->data[i], t);
  vec->data[j] = a_minus_t;
  vec->data[i] = a_plus_t;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    Eurydice_arr_e2 *vec, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
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
    Eurydice_arr_e2 *a, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_1_step(a, zeta0, zeta1,
                                                          zeta2, zeta3);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    Eurydice_arr_e2 *vec, int16_t zeta0, int16_t zeta1) {
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
    Eurydice_arr_e2 *a, int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_2_step(a, zeta0, zeta1);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    Eurydice_arr_e2 *vec, int16_t zeta) {
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
    Eurydice_arr_e2 *a, int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(
    Eurydice_arr_e2 *vec, int16_t zeta, size_t i, size_t j) {
  int16_t a_minus_b = core_num__i16__wrapping_sub(vec->data[j], vec->data[i]);
  int16_t a_plus_b = core_num__i16__wrapping_add(vec->data[j], vec->data[i]);
  int16_t o0 =
      libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
          a_plus_b);
  int16_t o1 =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, libcrux_secrets_int_public_integers_classify_27_39(zeta));
  vec->data[i] = o0;
  vec->data[j] = o1;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    Eurydice_arr_e2 *vec, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
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
    Eurydice_arr_e2 *a, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(a, zeta0, zeta1,
                                                              zeta2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    Eurydice_arr_e2 *vec, int16_t zeta0, int16_t zeta1) {
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
    Eurydice_arr_e2 *a, int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(a, zeta0, zeta1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    Eurydice_arr_e2 *vec, int16_t zeta) {
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
    Eurydice_arr_e2 *a, int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
    const Eurydice_arr_e2 *a, const Eurydice_arr_e2 *b, int16_t zeta, size_t i,
    Eurydice_dst_ref_mut_fc out) {
  int16_t ai = a->data[(size_t)2U * i];
  int16_t bi = b->data[(size_t)2U * i];
  int16_t aj = a->data[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->data[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bi));
  int32_t bj_zeta_ = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(bj), libcrux_secrets_int_as_i32_f5(zeta));
  int16_t bj_zeta =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          bj_zeta_);
  int32_t aj_bj_zeta =
      core_num__i32__wrapping_mul(libcrux_secrets_int_as_i32_f5(aj),
                                  libcrux_secrets_int_as_i32_f5(bj_zeta));
  int32_t ai_bi_aj_bj = core_num__i32__wrapping_add(ai_bi, aj_bj_zeta);
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bj));
  int32_t aj_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(aj), libcrux_secrets_int_as_i32_f5(bi));
  int32_t ai_bj_aj_bi = core_num__i32__wrapping_add(ai_bj, aj_bi);
  int32_t o1 = ai_bj_aj_bi;
  Eurydice_slice_index_mut(out, (size_t)2U * i, int32_t) =
      core_num__i32__wrapping_add(
          Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = out.ptr,
                                                         .meta = out.meta}),
              (size_t)2U * i, int32_t),
          o0);
  Eurydice_slice_index_mut(out, (size_t)2U * i + (size_t)1U, int32_t) =
      core_num__i32__wrapping_add(
          Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = out.ptr,
                                                         .meta = out.meta}),
              (size_t)2U * i + (size_t)1U, int32_t),
          o1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply(
    const Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs,
    Eurydice_dst_ref_mut_fc out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  int16_t nzeta0 = core_num__i16__wrapping_neg(zeta0);
  int16_t nzeta1 = core_num__i16__wrapping_neg(zeta1);
  int16_t nzeta2 = core_num__i16__wrapping_neg(zeta2);
  int16_t nzeta3 = core_num__i16__wrapping_neg(zeta3);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta0),
      (size_t)0U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta0),
      (size_t)1U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta1),
      (size_t)2U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta1),
      (size_t)3U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta2),
      (size_t)4U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta2),
      (size_t)5U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta3),
      (size_t)6U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta3),
      (size_t)7U, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_4e(
    const Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs,
    Eurydice_dst_ref_mut_fc out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
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
    const Eurydice_arr_e2 *a, const Eurydice_arr_e2 *b, int16_t zeta, size_t i,
    Eurydice_dst_ref_mut_fc out, Eurydice_arr_e2 *cache) {
  int16_t ai = a->data[(size_t)2U * i];
  int16_t bi = b->data[(size_t)2U * i];
  int16_t aj = a->data[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->data[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bi));
  int32_t bj_zeta_ = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(bj), libcrux_secrets_int_as_i32_f5(zeta));
  int16_t bj_zeta =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          bj_zeta_);
  cache->data[i] = bj_zeta;
  int32_t aj_bj_zeta =
      core_num__i32__wrapping_mul(libcrux_secrets_int_as_i32_f5(aj),
                                  libcrux_secrets_int_as_i32_f5(bj_zeta));
  int32_t ai_bi_aj_bj = core_num__i32__wrapping_add(ai_bi, aj_bj_zeta);
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bj));
  int32_t aj_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(aj), libcrux_secrets_int_as_i32_f5(bi));
  int32_t ai_bj_aj_bi = core_num__i32__wrapping_add(ai_bj, aj_bi);
  int32_t o1 = ai_bj_aj_bi;
  Eurydice_slice_index_mut(out, (size_t)2U * i, int32_t) =
      core_num__i32__wrapping_add(
          Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = out.ptr,
                                                         .meta = out.meta}),
              (size_t)2U * i, int32_t),
          o0);
  Eurydice_slice_index_mut(out, (size_t)2U * i + (size_t)1U, int32_t) =
      core_num__i32__wrapping_add(
          Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = out.ptr,
                                                         .meta = out.meta}),
              (size_t)2U * i + (size_t)1U, int32_t),
          o1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_fill_cache(
    const Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs,
    Eurydice_dst_ref_mut_fc out, Eurydice_arr_e2 *cache, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  int16_t nzeta0 = core_num__i16__wrapping_neg(zeta0);
  int16_t nzeta1 = core_num__i16__wrapping_neg(zeta1);
  int16_t nzeta2 = core_num__i16__wrapping_neg(zeta2);
  int16_t nzeta3 = core_num__i16__wrapping_neg(zeta3);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta0),
      (size_t)0U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta0),
      (size_t)1U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta1),
      (size_t)2U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta1),
      (size_t)3U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta2),
      (size_t)4U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta2),
      (size_t)5U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta3),
      (size_t)6U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta3),
      (size_t)7U, out, cache);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_fill_cache_4e(
    const Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs,
    Eurydice_dst_ref_mut_fc out, Eurydice_arr_e2 *cache, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_fill_cache(
      lhs, rhs, out, cache, zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
    const Eurydice_arr_e2 *a, const Eurydice_arr_e2 *b, size_t i,
    Eurydice_dst_ref_mut_fc out, const Eurydice_arr_e2 *cache) {
  int16_t ai = a->data[(size_t)2U * i];
  int16_t bi = b->data[(size_t)2U * i];
  int16_t aj = a->data[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->data[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bi));
  int32_t aj_bj_zeta = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(aj),
      libcrux_secrets_int_as_i32_f5(cache->data[i]));
  int32_t ai_bi_aj_bj = core_num__i32__wrapping_add(ai_bi, aj_bj_zeta);
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bj));
  int32_t aj_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(aj), libcrux_secrets_int_as_i32_f5(bi));
  int32_t ai_bj_aj_bi = core_num__i32__wrapping_add(ai_bj, aj_bi);
  int32_t o1 = ai_bj_aj_bi;
  Eurydice_slice_index_mut(out, (size_t)2U * i, int32_t) =
      core_num__i32__wrapping_add(
          Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = out.ptr,
                                                         .meta = out.meta}),
              (size_t)2U * i, int32_t),
          o0);
  Eurydice_slice_index_mut(out, (size_t)2U * i + (size_t)1U, int32_t) =
      core_num__i32__wrapping_add(
          Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = out.ptr,
                                                         .meta = out.meta}),
              (size_t)2U * i + (size_t)1U, int32_t),
          o1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_use_cache(
    const Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs,
    Eurydice_dst_ref_mut_fc out, const Eurydice_arr_e2 *cache) {
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
    const Eurydice_arr_e2 *lhs, const Eurydice_arr_e2 *rhs,
    Eurydice_dst_ref_mut_fc out, const Eurydice_arr_e2 *cache) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_use_cache(
      lhs, rhs, out, cache);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_1(
    const Eurydice_arr_e2 *v, Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_slice_index_mut(out, (size_t)0U, uint8_t) =
      (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v->data[0U]) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[1U]) << 1U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[2U]) << 2U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[3U]) << 3U) |
         (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[4U]) << 4U) |
        (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[5U]) << 5U) |
       (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[6U]) << 6U) |
      (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[7U]) << 7U;
  Eurydice_slice_index_mut(out, (size_t)1U, uint8_t) =
      (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v->data[8U]) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[9U]) << 1U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[10U]) << 2U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[11U]) << 3U) |
         (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[12U]) << 4U) |
        (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[13U]) << 5U) |
       (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[14U]) << 6U) |
      (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[15U]) << 7U;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_1_4e(
    const Eurydice_arr_e2 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_1(a, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_1(
    Eurydice_borrow_slice_u8 v, Eurydice_arr_e2 *out) {
  out->data[0U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)0U, uint8_t) & 1U);
  out->data[1U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)0U, uint8_t) >> 1U & 1U);
  out->data[2U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)0U, uint8_t) >> 2U & 1U);
  out->data[3U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)0U, uint8_t) >> 3U & 1U);
  out->data[4U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)0U, uint8_t) >> 4U & 1U);
  out->data[5U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)0U, uint8_t) >> 5U & 1U);
  out->data[6U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)0U, uint8_t) >> 6U & 1U);
  out->data[7U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)0U, uint8_t) >> 7U & 1U);
  out->data[8U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)1U, uint8_t) & 1U);
  out->data[9U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)1U, uint8_t) >> 1U & 1U);
  out->data[10U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)1U, uint8_t) >> 2U & 1U);
  out->data[11U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)1U, uint8_t) >> 3U & 1U);
  out->data[12U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)1U, uint8_t) >> 4U & 1U);
  out->data[13U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)1U, uint8_t) >> 5U & 1U);
  out->data[14U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)1U, uint8_t) >> 6U & 1U);
  out->data[15U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(v, (size_t)1U, uint8_t) >> 7U & 1U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_1_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_e2 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_1(a, out);
}

KRML_MUSTINLINE uint8_t_x4
libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t result0 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index_shared(v, (size_t)1U, int16_t))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index_shared(v, (size_t)0U, int16_t));
  uint8_t result1 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index_shared(v, (size_t)3U, int16_t))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index_shared(v, (size_t)2U, int16_t));
  uint8_t result2 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index_shared(v, (size_t)5U, int16_t))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index_shared(v, (size_t)4U, int16_t));
  uint8_t result3 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index_shared(v, (size_t)7U, int16_t))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index_shared(v, (size_t)6U, int16_t));
  return (KRML_CLITERAL(uint8_t_x4){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(result0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(result1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(result2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(result3)});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_4(
    const Eurydice_arr_e2 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x4 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)0U,
                                                         .end = (size_t)8U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  Eurydice_slice_index_mut(out, (size_t)0U, uint8_t) = uu____0.fst;
  Eurydice_slice_index_mut(out, (size_t)1U, uint8_t) = uu____1;
  Eurydice_slice_index_mut(out, (size_t)2U, uint8_t) = uu____2;
  Eurydice_slice_index_mut(out, (size_t)3U, uint8_t) = uu____3;
  uint8_t_x4 uu____4 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)8U,
                                                         .end = (size_t)16U})));
  uint8_t uu____5 = uu____4.snd;
  uint8_t uu____6 = uu____4.thd;
  uint8_t uu____7 = uu____4.f3;
  Eurydice_slice_index_mut(out, (size_t)4U, uint8_t) = uu____4.fst;
  Eurydice_slice_index_mut(out, (size_t)5U, uint8_t) = uu____5;
  Eurydice_slice_index_mut(out, (size_t)6U, uint8_t) = uu____6;
  Eurydice_slice_index_mut(out, (size_t)7U, uint8_t) = uu____7;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_4_4e(
    const Eurydice_arr_e2 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_4(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t v0 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)0U, uint8_t) & 15U);
  int16_t v1 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)0U, uint8_t) >> 4U &
      15U);
  int16_t v2 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t) & 15U);
  int16_t v3 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t) >> 4U &
      15U);
  int16_t v4 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t) & 15U);
  int16_t v5 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t) >> 4U &
      15U);
  int16_t v6 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)3U, uint8_t) & 15U);
  int16_t v7 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)3U, uint8_t) >> 4U &
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
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_e2 *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)0U, .end = (size_t)4U})));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  out->data[2U] = uu____2;
  out->data[3U] = uu____3;
  out->data[4U] = uu____4;
  out->data[5U] = uu____5;
  out->data[6U] = uu____6;
  out->data[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)4U, .end = (size_t)8U})));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  out->data[10U] = uu____10;
  out->data[11U] = uu____11;
  out->data[12U] = uu____12;
  out->data[13U] = uu____13;
  out->data[14U] = uu____14;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_4_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_e2 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(a), out);
}

KRML_MUSTINLINE uint8_t_x5
libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)0U, int16_t) |
      Eurydice_slice_index_shared(v, (size_t)1U, int16_t) << 5U);
  uint8_t r1 = libcrux_secrets_int_as_u8_f5(
      (Eurydice_slice_index_shared(v, (size_t)1U, int16_t) >> 3U |
       Eurydice_slice_index_shared(v, (size_t)2U, int16_t) << 2U) |
      Eurydice_slice_index_shared(v, (size_t)3U, int16_t) << 7U);
  uint8_t r2 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)3U, int16_t) >> 1U |
      Eurydice_slice_index_shared(v, (size_t)4U, int16_t) << 4U);
  uint8_t r3 = libcrux_secrets_int_as_u8_f5(
      (Eurydice_slice_index_shared(v, (size_t)4U, int16_t) >> 4U |
       Eurydice_slice_index_shared(v, (size_t)5U, int16_t) << 1U) |
      Eurydice_slice_index_shared(v, (size_t)6U, int16_t) << 6U);
  uint8_t r4 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)6U, int16_t) >> 2U |
      Eurydice_slice_index_shared(v, (size_t)7U, int16_t) << 3U);
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(r0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(r1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(r2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(r3),
      .f4 = libcrux_secrets_int_public_integers_declassify_d8_90(r4)});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_5(
    const Eurydice_arr_e2 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x5 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)0U,
                                                         .end = (size_t)8U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  Eurydice_slice_index_mut(out, (size_t)0U, uint8_t) = uu____0.fst;
  Eurydice_slice_index_mut(out, (size_t)1U, uint8_t) = uu____1;
  Eurydice_slice_index_mut(out, (size_t)2U, uint8_t) = uu____2;
  Eurydice_slice_index_mut(out, (size_t)3U, uint8_t) = uu____3;
  Eurydice_slice_index_mut(out, (size_t)4U, uint8_t) = uu____4;
  uint8_t_x5 uu____5 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)8U,
                                                         .end = (size_t)16U})));
  uint8_t uu____6 = uu____5.snd;
  uint8_t uu____7 = uu____5.thd;
  uint8_t uu____8 = uu____5.f3;
  uint8_t uu____9 = uu____5.f4;
  Eurydice_slice_index_mut(out, (size_t)5U, uint8_t) = uu____5.fst;
  Eurydice_slice_index_mut(out, (size_t)6U, uint8_t) = uu____6;
  Eurydice_slice_index_mut(out, (size_t)7U, uint8_t) = uu____7;
  Eurydice_slice_index_mut(out, (size_t)8U, uint8_t) = uu____8;
  Eurydice_slice_index_mut(out, (size_t)9U, uint8_t) = uu____9;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_5_4e(
    const Eurydice_arr_e2 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_5(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t v0 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)0U, uint8_t) & 31U);
  int16_t v1 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t) & 3U)
          << 3U |
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)0U, uint8_t) >> 5U);
  int16_t v2 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t) >> 2U &
      31U);
  int16_t v3 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t) & 15U)
          << 1U |
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t) >> 7U);
  int16_t v4 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)Eurydice_slice_index_shared(bytes, (size_t)3U, uint8_t) & 1U)
          << 4U |
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t) >> 4U);
  int16_t v5 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)3U, uint8_t) >> 1U &
      31U);
  int16_t v6 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)Eurydice_slice_index_shared(bytes, (size_t)4U, uint8_t) & 7U)
          << 2U |
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)3U, uint8_t) >> 6U);
  int16_t v7 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index_shared(bytes, (size_t)4U, uint8_t) >> 3U);
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
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_e2 *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)0U, .end = (size_t)5U})));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  out->data[2U] = uu____2;
  out->data[3U] = uu____3;
  out->data[4U] = uu____4;
  out->data[5U] = uu____5;
  out->data[6U] = uu____6;
  out->data[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)5U, .end = (size_t)10U})));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  out->data[10U] = uu____10;
  out->data[11U] = uu____11;
  out->data[12U] = uu____12;
  out->data[13U] = uu____13;
  out->data[14U] = uu____14;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_5_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_e2 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(a), out);
}

KRML_MUSTINLINE uint8_t_x5
libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)0U, int16_t) & (int16_t)255);
  uint8_t r1 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)1U, int16_t) & (int16_t)63)
          << 2U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)0U, int16_t) >> 8U &
          (int16_t)3);
  uint8_t r2 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)2U, int16_t) & (int16_t)15)
          << 4U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)1U, int16_t) >> 6U &
          (int16_t)15);
  uint8_t r3 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)3U, int16_t) & (int16_t)3)
          << 6U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)2U, int16_t) >> 4U &
          (int16_t)63);
  uint8_t r4 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)3U, int16_t) >> 2U & (int16_t)255);
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(r0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(r1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(r2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(r3),
      .f4 = libcrux_secrets_int_public_integers_declassify_d8_90(r4)});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_10(
    const Eurydice_arr_e2 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x5 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)0U,
                                                         .end = (size_t)4U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  Eurydice_slice_index_mut(out, (size_t)0U, uint8_t) = uu____0.fst;
  Eurydice_slice_index_mut(out, (size_t)1U, uint8_t) = uu____1;
  Eurydice_slice_index_mut(out, (size_t)2U, uint8_t) = uu____2;
  Eurydice_slice_index_mut(out, (size_t)3U, uint8_t) = uu____3;
  Eurydice_slice_index_mut(out, (size_t)4U, uint8_t) = uu____4;
  uint8_t_x5 uu____5 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)4U,
                                                         .end = (size_t)8U})));
  uint8_t uu____6 = uu____5.snd;
  uint8_t uu____7 = uu____5.thd;
  uint8_t uu____8 = uu____5.f3;
  uint8_t uu____9 = uu____5.f4;
  Eurydice_slice_index_mut(out, (size_t)5U, uint8_t) = uu____5.fst;
  Eurydice_slice_index_mut(out, (size_t)6U, uint8_t) = uu____6;
  Eurydice_slice_index_mut(out, (size_t)7U, uint8_t) = uu____7;
  Eurydice_slice_index_mut(out, (size_t)8U, uint8_t) = uu____8;
  Eurydice_slice_index_mut(out, (size_t)9U, uint8_t) = uu____9;
  uint8_t_x5 uu____10 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)8U,
                                                         .end = (size_t)12U})));
  uint8_t uu____11 = uu____10.snd;
  uint8_t uu____12 = uu____10.thd;
  uint8_t uu____13 = uu____10.f3;
  uint8_t uu____14 = uu____10.f4;
  Eurydice_slice_index_mut(out, (size_t)10U, uint8_t) = uu____10.fst;
  Eurydice_slice_index_mut(out, (size_t)11U, uint8_t) = uu____11;
  Eurydice_slice_index_mut(out, (size_t)12U, uint8_t) = uu____12;
  Eurydice_slice_index_mut(out, (size_t)13U, uint8_t) = uu____13;
  Eurydice_slice_index_mut(out, (size_t)14U, uint8_t) = uu____14;
  uint8_t_x5 uu____15 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)12U,
                                                         .end = (size_t)16U})));
  uint8_t uu____16 = uu____15.snd;
  uint8_t uu____17 = uu____15.thd;
  uint8_t uu____18 = uu____15.f3;
  uint8_t uu____19 = uu____15.f4;
  Eurydice_slice_index_mut(out, (size_t)15U, uint8_t) = uu____15.fst;
  Eurydice_slice_index_mut(out, (size_t)16U, uint8_t) = uu____16;
  Eurydice_slice_index_mut(out, (size_t)17U, uint8_t) = uu____17;
  Eurydice_slice_index_mut(out, (size_t)18U, uint8_t) = uu____18;
  Eurydice_slice_index_mut(out, (size_t)19U, uint8_t) = uu____19;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_10_4e(
    const Eurydice_arr_e2 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_10(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t r0 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t)) &
       (int16_t)3)
          << 8U |
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index_shared(bytes, (size_t)0U, uint8_t)) &
       (int16_t)255));
  int16_t r1 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t)) &
       (int16_t)15)
          << 6U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t)) >>
          2U);
  int16_t r2 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index_shared(bytes, (size_t)3U, uint8_t)) &
       (int16_t)63)
          << 4U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t)) >>
          4U);
  int16_t r3 = libcrux_secrets_int_as_i16_f5(
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index_shared(bytes, (size_t)4U, uint8_t))
          << 2U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index_shared(bytes, (size_t)3U, uint8_t)) >>
          6U);
  int16_t r4 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index_shared(bytes, (size_t)6U, uint8_t)) &
       (int16_t)3)
          << 8U |
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index_shared(bytes, (size_t)5U, uint8_t)) &
       (int16_t)255));
  int16_t r5 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index_shared(bytes, (size_t)7U, uint8_t)) &
       (int16_t)15)
          << 6U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index_shared(bytes, (size_t)6U, uint8_t)) >>
          2U);
  int16_t r6 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index_shared(bytes, (size_t)8U, uint8_t)) &
       (int16_t)63)
          << 4U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index_shared(bytes, (size_t)7U, uint8_t)) >>
          4U);
  int16_t r7 = libcrux_secrets_int_as_i16_f5(
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index_shared(bytes, (size_t)9U, uint8_t))
          << 2U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index_shared(bytes, (size_t)8U, uint8_t)) >>
          6U);
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
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_e2 *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)0U, .end = (size_t)10U})));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  out->data[2U] = uu____2;
  out->data[3U] = uu____3;
  out->data[4U] = uu____4;
  out->data[5U] = uu____5;
  out->data[6U] = uu____6;
  out->data[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)10U, .end = (size_t)20U})));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  out->data[10U] = uu____10;
  out->data[11U] = uu____11;
  out->data[12U] = uu____12;
  out->data[13U] = uu____13;
  out->data[14U] = uu____14;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_10_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_e2 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(a), out);
}

KRML_MUSTINLINE uint8_t_x11
libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)0U, int16_t));
  uint8_t r1 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)1U, int16_t) & (int16_t)31)
          << 3U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)0U, int16_t) >> 8U);
  uint8_t r2 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)2U, int16_t) & (int16_t)3)
          << 6U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)1U, int16_t) >> 5U);
  uint8_t r3 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)2U, int16_t) >> 2U & (int16_t)255);
  uint8_t r4 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)3U, int16_t) & (int16_t)127)
          << 1U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)2U, int16_t) >> 10U);
  uint8_t r5 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)4U, int16_t) & (int16_t)15)
          << 4U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)3U, int16_t) >> 7U);
  uint8_t r6 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)5U, int16_t) & (int16_t)1)
          << 7U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)4U, int16_t) >> 4U);
  uint8_t r7 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)5U, int16_t) >> 1U & (int16_t)255);
  uint8_t r8 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)6U, int16_t) & (int16_t)63)
          << 2U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)5U, int16_t) >> 9U);
  uint8_t r9 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)7U, int16_t) & (int16_t)7)
          << 5U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index_shared(v, (size_t)6U, int16_t) >> 6U);
  uint8_t r10 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)7U, int16_t) >> 3U);
  return (KRML_CLITERAL(uint8_t_x11){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(r0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(r1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(r2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(r3),
      .f4 = libcrux_secrets_int_public_integers_declassify_d8_90(r4),
      .f5 = libcrux_secrets_int_public_integers_declassify_d8_90(r5),
      .f6 = libcrux_secrets_int_public_integers_declassify_d8_90(r6),
      .f7 = libcrux_secrets_int_public_integers_declassify_d8_90(r7),
      .f8 = libcrux_secrets_int_public_integers_declassify_d8_90(r8),
      .f9 = libcrux_secrets_int_public_integers_declassify_d8_90(r9),
      .f10 = libcrux_secrets_int_public_integers_declassify_d8_90(r10)});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_11(
    const Eurydice_arr_e2 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x11 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)0U,
                                                         .end = (size_t)8U})));
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
  Eurydice_slice_index_mut(out, (size_t)0U, uint8_t) = uu____0.fst;
  Eurydice_slice_index_mut(out, (size_t)1U, uint8_t) = uu____1;
  Eurydice_slice_index_mut(out, (size_t)2U, uint8_t) = uu____2;
  Eurydice_slice_index_mut(out, (size_t)3U, uint8_t) = uu____3;
  Eurydice_slice_index_mut(out, (size_t)4U, uint8_t) = uu____4;
  Eurydice_slice_index_mut(out, (size_t)5U, uint8_t) = uu____5;
  Eurydice_slice_index_mut(out, (size_t)6U, uint8_t) = uu____6;
  Eurydice_slice_index_mut(out, (size_t)7U, uint8_t) = uu____7;
  Eurydice_slice_index_mut(out, (size_t)8U, uint8_t) = uu____8;
  Eurydice_slice_index_mut(out, (size_t)9U, uint8_t) = uu____9;
  Eurydice_slice_index_mut(out, (size_t)10U, uint8_t) = uu____10;
  uint8_t_x11 uu____11 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)8U,
                                                         .end = (size_t)16U})));
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
  Eurydice_slice_index_mut(out, (size_t)11U, uint8_t) = uu____11.fst;
  Eurydice_slice_index_mut(out, (size_t)12U, uint8_t) = uu____12;
  Eurydice_slice_index_mut(out, (size_t)13U, uint8_t) = uu____13;
  Eurydice_slice_index_mut(out, (size_t)14U, uint8_t) = uu____14;
  Eurydice_slice_index_mut(out, (size_t)15U, uint8_t) = uu____15;
  Eurydice_slice_index_mut(out, (size_t)16U, uint8_t) = uu____16;
  Eurydice_slice_index_mut(out, (size_t)17U, uint8_t) = uu____17;
  Eurydice_slice_index_mut(out, (size_t)18U, uint8_t) = uu____18;
  Eurydice_slice_index_mut(out, (size_t)19U, uint8_t) = uu____19;
  Eurydice_slice_index_mut(out, (size_t)20U, uint8_t) = uu____20;
  Eurydice_slice_index_mut(out, (size_t)21U, uint8_t) = uu____21;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_11_4e(
    const Eurydice_arr_e2 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_11(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t r0 = (libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t)) &
                (int16_t)7)
                   << 8U |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)0U, uint8_t));
  int16_t r1 = (libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t)) &
                (int16_t)63)
                   << 5U |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t)) >>
                   3U;
  int16_t r2 = ((libcrux_secrets_int_as_i16_59(
                     Eurydice_slice_index_shared(bytes, (size_t)4U, uint8_t)) &
                 (int16_t)1)
                    << 10U |
                libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index_shared(bytes, (size_t)3U, uint8_t))
                    << 2U) |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t)) >>
                   6U;
  int16_t r3 = (libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index_shared(bytes, (size_t)5U, uint8_t)) &
                (int16_t)15)
                   << 7U |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)4U, uint8_t)) >>
                   1U;
  int16_t r4 = (libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index_shared(bytes, (size_t)6U, uint8_t)) &
                (int16_t)127)
                   << 4U |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)5U, uint8_t)) >>
                   4U;
  int16_t r5 = ((libcrux_secrets_int_as_i16_59(
                     Eurydice_slice_index_shared(bytes, (size_t)8U, uint8_t)) &
                 (int16_t)3)
                    << 9U |
                libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index_shared(bytes, (size_t)7U, uint8_t))
                    << 1U) |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)6U, uint8_t)) >>
                   7U;
  int16_t r6 = (libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index_shared(bytes, (size_t)9U, uint8_t)) &
                (int16_t)31)
                   << 6U |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)8U, uint8_t)) >>
                   2U;
  int16_t r7 = libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)10U, uint8_t))
                   << 3U |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index_shared(bytes, (size_t)9U, uint8_t)) >>
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
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_e2 *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)0U, .end = (size_t)11U})));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  out->data[2U] = uu____2;
  out->data[3U] = uu____3;
  out->data[4U] = uu____4;
  out->data[5U] = uu____5;
  out->data[6U] = uu____6;
  out->data[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)11U, .end = (size_t)22U})));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  out->data[10U] = uu____10;
  out->data[11U] = uu____11;
  out->data[12U] = uu____12;
  out->data[13U] = uu____13;
  out->data[14U] = uu____14;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_11_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_e2 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(a), out);
}

KRML_MUSTINLINE uint8_t_x3
libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)0U, int16_t) & (int16_t)255);
  uint8_t r1 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)0U, int16_t) >> 8U |
      (Eurydice_slice_index_shared(v, (size_t)1U, int16_t) & (int16_t)15)
          << 4U);
  uint8_t r2 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index_shared(v, (size_t)1U, int16_t) >> 4U & (int16_t)255);
  return (KRML_CLITERAL(uint8_t_x3){.fst = r0, .snd = r1, .thd = r2});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_12(
    const Eurydice_arr_e2 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x3 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)0U,
                                                         .end = (size_t)2U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  Eurydice_slice_index_mut(out, (size_t)0U, uint8_t) = uu____0.fst;
  Eurydice_slice_index_mut(out, (size_t)1U, uint8_t) = uu____1;
  Eurydice_slice_index_mut(out, (size_t)2U, uint8_t) = uu____2;
  uint8_t_x3 uu____3 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)2U,
                                                         .end = (size_t)4U})));
  uint8_t uu____4 = uu____3.snd;
  uint8_t uu____5 = uu____3.thd;
  Eurydice_slice_index_mut(out, (size_t)3U, uint8_t) = uu____3.fst;
  Eurydice_slice_index_mut(out, (size_t)4U, uint8_t) = uu____4;
  Eurydice_slice_index_mut(out, (size_t)5U, uint8_t) = uu____5;
  uint8_t_x3 uu____6 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)4U,
                                                         .end = (size_t)6U})));
  uint8_t uu____7 = uu____6.snd;
  uint8_t uu____8 = uu____6.thd;
  Eurydice_slice_index_mut(out, (size_t)6U, uint8_t) = uu____6.fst;
  Eurydice_slice_index_mut(out, (size_t)7U, uint8_t) = uu____7;
  Eurydice_slice_index_mut(out, (size_t)8U, uint8_t) = uu____8;
  uint8_t_x3 uu____9 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)6U,
                                                         .end = (size_t)8U})));
  uint8_t uu____10 = uu____9.snd;
  uint8_t uu____11 = uu____9.thd;
  Eurydice_slice_index_mut(out, (size_t)9U, uint8_t) = uu____9.fst;
  Eurydice_slice_index_mut(out, (size_t)10U, uint8_t) = uu____10;
  Eurydice_slice_index_mut(out, (size_t)11U, uint8_t) = uu____11;
  uint8_t_x3 uu____12 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)8U,
                                                         .end = (size_t)10U})));
  uint8_t uu____13 = uu____12.snd;
  uint8_t uu____14 = uu____12.thd;
  Eurydice_slice_index_mut(out, (size_t)12U, uint8_t) = uu____12.fst;
  Eurydice_slice_index_mut(out, (size_t)13U, uint8_t) = uu____13;
  Eurydice_slice_index_mut(out, (size_t)14U, uint8_t) = uu____14;
  uint8_t_x3 uu____15 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)10U,
                                                         .end = (size_t)12U})));
  uint8_t uu____16 = uu____15.snd;
  uint8_t uu____17 = uu____15.thd;
  Eurydice_slice_index_mut(out, (size_t)15U, uint8_t) = uu____15.fst;
  Eurydice_slice_index_mut(out, (size_t)16U, uint8_t) = uu____16;
  Eurydice_slice_index_mut(out, (size_t)17U, uint8_t) = uu____17;
  uint8_t_x3 uu____18 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)12U,
                                                         .end = (size_t)14U})));
  uint8_t uu____19 = uu____18.snd;
  uint8_t uu____20 = uu____18.thd;
  Eurydice_slice_index_mut(out, (size_t)18U, uint8_t) = uu____18.fst;
  Eurydice_slice_index_mut(out, (size_t)19U, uint8_t) = uu____19;
  Eurydice_slice_index_mut(out, (size_t)20U, uint8_t) = uu____20;
  uint8_t_x3 uu____21 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_85(
              v, (KRML_CLITERAL(core_ops_range_Range_08){.start = (size_t)14U,
                                                         .end = (size_t)16U})));
  uint8_t uu____22 = uu____21.snd;
  uint8_t uu____23 = uu____21.thd;
  Eurydice_slice_index_mut(out, (size_t)21U, uint8_t) = uu____21.fst;
  Eurydice_slice_index_mut(out, (size_t)22U, uint8_t) = uu____22;
  Eurydice_slice_index_mut(out, (size_t)23U, uint8_t) = uu____23;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_12_4e(
    const Eurydice_arr_e2 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_12(a, out);
}

KRML_MUSTINLINE int16_t_x2
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t byte0 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index_shared(bytes, (size_t)0U, uint8_t));
  int16_t byte1 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index_shared(bytes, (size_t)1U, uint8_t));
  int16_t byte2 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index_shared(bytes, (size_t)2U, uint8_t));
  int16_t r0 = (byte1 & (int16_t)15) << 8U | (byte0 & (int16_t)255);
  int16_t r1 = byte2 << 4U | (byte1 >> 4U & (int16_t)15);
  return (KRML_CLITERAL(int16_t_x2){.fst = r0, .snd = r1});
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_e2 *out) {
  int16_t_x2 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)0U, .end = (size_t)3U})));
  int16_t uu____1 = uu____0.snd;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  int16_t_x2 uu____2 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)3U, .end = (size_t)6U})));
  int16_t uu____3 = uu____2.snd;
  out->data[2U] = uu____2.fst;
  out->data[3U] = uu____3;
  int16_t_x2 uu____4 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)6U, .end = (size_t)9U})));
  int16_t uu____5 = uu____4.snd;
  out->data[4U] = uu____4.fst;
  out->data[5U] = uu____5;
  int16_t_x2 uu____6 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)9U, .end = (size_t)12U})));
  int16_t uu____7 = uu____6.snd;
  out->data[6U] = uu____6.fst;
  out->data[7U] = uu____7;
  int16_t_x2 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)12U, .end = (size_t)15U})));
  int16_t uu____9 = uu____8.snd;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  int16_t_x2 uu____10 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)15U, .end = (size_t)18U})));
  int16_t uu____11 = uu____10.snd;
  out->data[10U] = uu____10.fst;
  out->data[11U] = uu____11;
  int16_t_x2 uu____12 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)18U, .end = (size_t)21U})));
  int16_t uu____13 = uu____12.snd;
  out->data[12U] = uu____12.fst;
  out->data[13U] = uu____13;
  int16_t_x2 uu____14 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_7e(
              bytes, (KRML_CLITERAL(core_ops_range_Range_08){
                         .start = (size_t)21U, .end = (size_t)24U})));
  int16_t uu____15 = uu____14.snd;
  out->data[14U] = uu____14.fst;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_e2 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12(a, out);
}

KRML_MUSTINLINE size_t libcrux_iot_ml_kem_vector_portable_sampling_rej_sample(
    Eurydice_borrow_slice_u8 a, Eurydice_mut_borrow_slice_i16 out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(a, uint8_t) / (size_t)3U;
       i++) {
    size_t i0 = i;
    int16_t b1 = (int16_t)Eurydice_slice_index_shared(
        a, i0 * (size_t)3U + (size_t)0U, uint8_t);
    int16_t b2 = (int16_t)Eurydice_slice_index_shared(
        a, i0 * (size_t)3U + (size_t)1U, uint8_t);
    int16_t b3 = (int16_t)Eurydice_slice_index_shared(
        a, i0 * (size_t)3U + (size_t)2U, uint8_t);
    int16_t d1 = (b2 & (int16_t)15) << 8U | b1;
    int16_t d2 = b3 << 4U | b2 >> 4U;
    if (d1 < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
      if (sampled < (size_t)16U) {
        Eurydice_slice_index_mut(out, sampled, int16_t) = d1;
        sampled++;
      }
    }
    if (d2 < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
      if (sampled < (size_t)16U) {
        Eurydice_slice_index_mut(out, sampled, int16_t) = d2;
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
    Eurydice_borrow_slice_u8 a, Eurydice_mut_borrow_slice_i16 out) {
  return libcrux_iot_ml_kem_vector_portable_sampling_rej_sample(a, out);
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
inline Eurydice_arr_e2 libcrux_iot_ml_kem_vector_portable_vector_type_clone_9c(
    const Eurydice_arr_e2 *self) {
  return self[0U];
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $4size_t
*/
typedef struct arr_f2_s {
  Eurydice_arr_3d0 data[4U];
} arr_f2;

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
static Eurydice_arr_3d0 ZERO_64_a7(void) {
  Eurydice_arr_3d0 lit;
  Eurydice_arr_e2 repeat_expression[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression[i] = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  }
  memcpy(lit.data, repeat_expression, (size_t)16U * sizeof(Eurydice_arr_e2));
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
static Eurydice_arr_3d0 call_mut_42_c5(void **_) { return ZERO_64_a7(); }

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
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)24U, .end = i0 * (size_t)24U + (size_t)24U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(bytes, &re->data[i0]);
    libcrux_iot_ml_kem_vector_portable_cond_subtract_3329_4e(&re->data[i0]);
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
    Eurydice_borrow_slice_u8 public_key,
    Eurydice_dst_ref_mut_64 deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 ring_element = Eurydice_slice_subslice_shared_7e(
        public_key,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}));
    deserialize_to_reduced_ring_element_a7(
        libcrux_secrets_int_classify_public_classify_ref_9b_90(ring_element),
        &Eurydice_slice_index_mut(deserialized_pk, i0, Eurydice_arr_3d0));
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 4
*/
static Eurydice_dst_ref_mut_64 array_to_slice_mut_340(arr_f2 *a) {
  Eurydice_dst_ref_mut_64 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 4
*/
static Eurydice_dst_ref_shared_64 array_to_slice_shared_340(const arr_f2 *a) {
  Eurydice_dst_ref_shared_64 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE void shift_right_ef(Eurydice_arr_e2 *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->data[uu____0] = vec->data[uu____0] >> (uint32_t)(int32_t)15;
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
static KRML_MUSTINLINE void shift_right_4e_ef(Eurydice_arr_e2 *vec) {
  shift_right_ef(vec);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void to_unsigned_representative_a7(
    const Eurydice_arr_e2 *a, Eurydice_arr_e2 *out) {
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
    const Eurydice_arr_e2 *a, Eurydice_arr_e2 *out) {
  to_unsigned_representative_a7(a, out);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_a7(
    const Eurydice_arr_3d0 *re, Eurydice_arr_e2 *scratch,
    Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re->data[i0], scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_12_4e(
        scratch, Eurydice_slice_subslice_mut_7e(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                                     .start = (size_t)24U * i0,
                                     .end = (size_t)24U * i0 + (size_t)24U})));
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
    const arr_f2 *key, Eurydice_mut_borrow_slice_u8 out,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(array_to_slice_shared_340(key), Eurydice_arr_3d0);
       i++) {
    size_t i0 = i;
    Eurydice_arr_3d0 re = key->data[i0];
    serialize_uncompressed_ring_element_a7(
        &re, scratch,
        Eurydice_slice_subslice_mut_7e(
            out,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT})));
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
    const arr_f2 *t_as_ntt, Eurydice_borrow_slice_u8 seed_for_a,
    Eurydice_mut_borrow_slice_u8 serialized, Eurydice_arr_e2 *scratch) {
  /* original Rust expression is not an lvalue in C */
  Eurydice_mut_borrow_slice_u8 lvalue = Eurydice_slice_subslice_mut_7e(
      serialized,
      (KRML_CLITERAL(core_ops_range_Range_08){
          .start = (size_t)0U,
          .end = libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)4U)}));
  serialize_vector_e1(
      t_as_ntt,
      libcrux_secrets_int_classify_public_classify_ref_mut_a1_47(&lvalue)[0U],
      scratch);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_from_mut_6b(
          serialized,
          libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)4U)),
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
bool libcrux_iot_ml_kem_ind_cca_validate_public_key_c5(
    const Eurydice_arr_00 *public_key) {
  arr_f2 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_42_c5(&lvalue);
  }
  arr_f2 deserialized_pk = arr_struct;
  Eurydice_borrow_slice_u8 uu____0 = Eurydice_array_to_subslice_to_shared_6e1(
      public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U));
  deserialize_ring_elements_reduced_e1(
      uu____0, array_to_slice_mut_340(&deserialized_pk));
  Eurydice_arr_00 public_key_serialized = {.data = {0U}};
  Eurydice_arr_e2 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  const arr_f2 *uu____1 = &deserialized_pk;
  Eurydice_borrow_slice_u8 uu____2 = Eurydice_array_to_subslice_from_shared_8c4(
      public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U));
  serialize_public_key_mut_c5(
      uu____1, uu____2, Eurydice_array_to_slice_mut_4e(&public_key_serialized),
      &scratch);
  return Eurydice_array_eq((size_t)1568U, public_key, &public_key_serialized,
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
    const Eurydice_arr_17 *private_key) {
  Eurydice_arr_600 t;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(t.data, repeat_expression, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      Eurydice_array_to_subslice_shared_3612(
          private_key, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = (size_t)384U * (size_t)4U,
                           .end = (size_t)768U * (size_t)4U + (size_t)32U})),
      Eurydice_array_to_slice_mut_6e(&t));
  Eurydice_borrow_slice_u8 expected =
      libcrux_secrets_int_classify_public_declassify_ref_7f_90(
          Eurydice_array_to_subslice_shared_3612(
              private_key,
              (KRML_CLITERAL(core_ops_range_Range_08){
                  .start = (size_t)768U * (size_t)4U + (size_t)32U,
                  .end = (size_t)768U * (size_t)4U + (size_t)64U})));
  /* original Rust expression is not an lvalue in C */
  Eurydice_borrow_slice_u8 lvalue =
      libcrux_secrets_int_classify_public_declassify_ref_7f_90(
          core_array___Array_T__N___as_slice((size_t)32U, &t, uint8_t,
                                             Eurydice_borrow_slice_u8));
  return Eurydice_slice_eq_shared(&lvalue, &expected, uint8_t, bool);
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
    const Eurydice_arr_17 *private_key, const Eurydice_arr_00 *_ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_8a(private_key);
}

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
static KRML_MUSTINLINE arr_f2 default_1e_e1(void) {
  arr_f2 lit;
  Eurydice_arr_3d0 repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(lit.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_3d0));
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $16size_t
*/
typedef struct arr_5c_s {
  Eurydice_arr_3d0 data[16U];
} arr_5c;

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $4size_t
- $16size_t
*/
typedef struct IndCpaPublicKeyUnpacked_81_s {
  arr_f2 t_as_ntt;
  Eurydice_arr_600 seed_for_A;
  arr_5c A;
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
  arr_f2 uu____0;
  Eurydice_arr_3d0 repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] = ZERO_64_a7();
  }
  memcpy(uu____0.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_3d0));
  Eurydice_arr_600 uu____1 = {.data = {0U}};
  IndCpaPublicKeyUnpacked_81 lit;
  lit.t_as_ntt = uu____0;
  lit.seed_for_A = uu____1;
  Eurydice_arr_3d0 repeat_expression[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(lit.A.data, repeat_expression, (size_t)16U * sizeof(Eurydice_arr_3d0));
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
    Eurydice_borrow_slice_u8 key_generation_seed,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_3e seed;
  uint8_t repeat_expression[33U];
  for (size_t i = (size_t)0U; i < (size_t)33U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(seed.data, repeat_expression, (size_t)33U * sizeof(uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_362(
          &seed,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE})),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      libcrux_secrets_int_public_integers_classify_27_90((uint8_t)(size_t)4U);
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_610(&seed), out);
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 16
*/
static Eurydice_dst_ref_mut_64 array_to_slice_mut_343(arr_5c *a) {
  Eurydice_dst_ref_mut_64 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
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
    Eurydice_dst_ref_shared_ea randomness,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                  .ptr = sampled_coefficients.ptr,
                  .meta = sampled_coefficients.meta}),
              i1, size_t) <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_b0 *randomness_i =
            &Eurydice_slice_index_shared(randomness, i1, Eurydice_arr_b0);
        Eurydice_arr_a0 *out_i =
            &Eurydice_slice_index_mut(out, i1, Eurydice_arr_a0);
        size_t sampled_coefficients_i = Eurydice_slice_index_shared(
            (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                .ptr = sampled_coefficients.ptr,
                .meta = sampled_coefficients.meta}),
            i1, size_t);
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_363(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_08){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_85(
                out_i, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        size_t uu____0 = i1;
        Eurydice_slice_index_mut(sampled_coefficients, uu____0, size_t) =
            Eurydice_slice_index_shared(
                (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                    .ptr = sampled_coefficients.ptr,
                    .meta = sampled_coefficients.meta}),
                uu____0, size_t) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index_shared((KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                                        .ptr = sampled_coefficients.ptr,
                                        .meta = sampled_coefficients.meta}),
                                    i0, size_t) >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index_mut(sampled_coefficients, i0, size_t) =
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
- K= 4
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_c50(
    Eurydice_dst_ref_shared_36 randomness,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                  .ptr = sampled_coefficients.ptr,
                  .meta = sampled_coefficients.meta}),
              i1, size_t) <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_27 *randomness_i =
            &Eurydice_slice_index_shared(randomness, i1, Eurydice_arr_27);
        Eurydice_arr_a0 *out_i =
            &Eurydice_slice_index_mut(out, i1, Eurydice_arr_a0);
        size_t sampled_coefficients_i = Eurydice_slice_index_shared(
            (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                .ptr = sampled_coefficients.ptr,
                .meta = sampled_coefficients.meta}),
            i1, size_t);
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_364(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_08){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_85(
                out_i, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        size_t uu____0 = i1;
        Eurydice_slice_index_mut(sampled_coefficients, uu____0, size_t) =
            Eurydice_slice_index_shared(
                (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                    .ptr = sampled_coefficients.ptr,
                    .meta = sampled_coefficients.meta}),
                uu____0, size_t) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index_shared((KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                                        .ptr = sampled_coefficients.ptr,
                                        .meta = sampled_coefficients.meta}),
                                    i0, size_t) >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index_mut(sampled_coefficients, i0, size_t) =
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
- K= 4
*/
static KRML_MUSTINLINE void sample_from_xof_c92(
    Eurydice_dst_ref_shared_60 seeds,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  Eurydice_arr_5e xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  Eurydice_arr_ec randomness = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_a6 randomness_blocksize = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state, Eurydice_array_to_slice_mut_e92(&randomness));
  bool done = sample_from_uniform_distribution_next_c5(
      Eurydice_array_to_slice_shared_e92(&randomness), sampled_coefficients,
      out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice_mut_e72(&randomness_blocksize));
      done = sample_from_uniform_distribution_next_c50(
          Eurydice_array_to_slice_shared_e72(&randomness_blocksize),
          sampled_coefficients, out);
    }
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
static KRML_MUSTINLINE void from_i16_array_64_a7(Eurydice_borrow_slice_i16 a,
                                                 Eurydice_arr_3d0 *out) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_from_i16_array_4e(
        Eurydice_slice_subslice_shared_76(
            a, (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = i0 * (size_t)16U,
                   .end = (i0 + (size_t)1U) * (size_t)16U})),
        &out->data[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.sample_matrix_A
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_c91(
    Eurydice_dst_ref_mut_64 A_transpose, const Eurydice_arr_48 *seed,
    bool transpose) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    Eurydice_arr_78 seeds;
    Eurydice_arr_48 repeat_expression[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression[i] = seed[0U];
    }
    memcpy(seeds.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_48));
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t j = i;
      seeds.data[j].data[32U] = (uint8_t)i1;
      seeds.data[j].data[33U] = (uint8_t)j;
    }
    Eurydice_arr_33 sampled_coefficients = {.data = {0U}};
    Eurydice_arr_8a out = {
        .data = {
            {.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
    sample_from_xof_c92(Eurydice_array_to_slice_shared_c72(&seeds),
                        Eurydice_array_to_slice_mut_4d(&sampled_coefficients),
                        Eurydice_array_to_slice_mut_302(&out));
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(Eurydice_array_to_slice_shared_301(&out),
                                Eurydice_arr_a0);
         i++) {
      size_t j = i;
      Eurydice_arr_a0 sample = out.data[j];
      if (transpose) {
        Eurydice_borrow_slice_i16 uu____0 =
            libcrux_secrets_int_classify_public_classify_ref_9b_39(
                Eurydice_array_to_subslice_to_shared_11(&sample, (size_t)256U));
        from_i16_array_64_a7(
            uu____0, &Eurydice_slice_index_mut(A_transpose, j * (size_t)4U + i1,
                                               Eurydice_arr_3d0));
      } else {
        Eurydice_borrow_slice_i16 uu____1 =
            libcrux_secrets_int_classify_public_classify_ref_9b_39(
                Eurydice_array_to_subslice_to_shared_11(&sample, (size_t)256U));
        from_i16_array_64_a7(
            uu____1, &Eurydice_slice_index_mut(A_transpose, i1 * (size_t)4U + j,
                                               Eurydice_arr_3d0));
      }
    }
  }
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
    Eurydice_borrow_slice_u8 randomness,
    Eurydice_mut_borrow_slice_i16 sampled_i16s) {
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i0++) {
    size_t chunk_number = i0;
    Eurydice_borrow_slice_u8 byte_chunk = Eurydice_slice_subslice_shared_7e(
        randomness, (KRML_CLITERAL(core_ops_range_Range_08){
                        .start = chunk_number * (size_t)4U,
                        .end = chunk_number * (size_t)4U + (size_t)4U}));
    uint32_t random_bits_as_u32 =
        ((libcrux_secrets_int_as_u32_59(
              Eurydice_slice_index_shared(byte_chunk, (size_t)0U, uint8_t)) |
          libcrux_secrets_int_as_u32_59(
              Eurydice_slice_index_shared(byte_chunk, (size_t)1U, uint8_t))
              << 8U) |
         libcrux_secrets_int_as_u32_59(
             Eurydice_slice_index_shared(byte_chunk, (size_t)2U, uint8_t))
             << 16U) |
        libcrux_secrets_int_as_u32_59(
            Eurydice_slice_index_shared(byte_chunk, (size_t)3U, uint8_t))
            << 24U;
    uint32_t even_bits =
        random_bits_as_u32 &
        libcrux_secrets_int_public_integers_classify_27_df(1431655765U);
    uint32_t odd_bits =
        random_bits_as_u32 >> 1U &
        libcrux_secrets_int_public_integers_classify_27_df(1431655765U);
    uint32_t coin_toss_outcomes = even_bits + odd_bits;
    for (uint32_t i = 0U; i < 32U / 4U; i++) {
      uint32_t outcome_set = i;
      uint32_t outcome_set0 = outcome_set * 4U;
      int16_t outcome_1 = libcrux_secrets_int_as_i16_b8(
          coin_toss_outcomes >> (uint32_t)outcome_set0 &
          libcrux_secrets_int_public_integers_classify_27_df(3U));
      int16_t outcome_2 = libcrux_secrets_int_as_i16_b8(
          coin_toss_outcomes >> (uint32_t)(outcome_set0 + 2U) &
          libcrux_secrets_int_public_integers_classify_27_df(3U));
      size_t offset = (size_t)(outcome_set0 >> 2U);
      Eurydice_slice_index_mut(sampled_i16s, (size_t)8U * chunk_number + offset,
                               int16_t) = outcome_1 - outcome_2;
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
    Eurydice_borrow_slice_u8 randomness, Eurydice_arr_c1 *output) {
  sample_from_binomial_distribution_2_a7(
      randomness, Eurydice_array_to_slice_mut_1a(output));
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_7
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_a7(Eurydice_arr_3d0 *re,
                                              Eurydice_arr_e2 *scratch) {
  size_t step = VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    scratch[0U] = re->data[j + step];
    libcrux_iot_ml_kem_vector_portable_multiply_by_constant_4e(scratch,
                                                               (int16_t)-1600);
    re->data[j + step] = re->data[j];
    libcrux_iot_ml_kem_vector_portable_add_4e(&re->data[j], scratch);
    libcrux_iot_ml_kem_vector_portable_sub_4e(&re->data[j + step], scratch);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.traits.montgomery_multiply_fe with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void montgomery_multiply_fe_a7(Eurydice_arr_e2 *v,
                                                      int16_t fer) {
  libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(v, fer);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_layer_int_vec_step_a7(
    Eurydice_arr_3d0 *coefficients, size_t a, size_t b,
    Eurydice_arr_e2 *scratch, int16_t zeta_r) {
  scratch[0U] = coefficients->data[b];
  montgomery_multiply_fe_a7(scratch, zeta_r);
  coefficients->data[b] = coefficients->data[a];
  libcrux_iot_ml_kem_vector_portable_add_4e(&coefficients->data[a], scratch);
  libcrux_iot_ml_kem_vector_portable_sub_4e(&coefficients->data[b], scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_a7(size_t *zeta_i,
                                                   Eurydice_arr_3d0 *re,
                                                   size_t layer,
                                                   Eurydice_arr_e2 *scratch) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec = step / (size_t)16U;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      ntt_layer_int_vec_step_a7(re, a_offset + j, b_offset + j, scratch,
                                zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_3
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_3_a7(size_t *zeta_i,
                                              Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_iot_ml_kem_vector_portable_ntt_layer_3_step_4e(&re->data[round],
                                                           zeta(zeta_i[0U]));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_a7(size_t *zeta_i,
                                              Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_iot_ml_kem_vector_portable_ntt_layer_2_step_4e(
        &re->data[round], zeta(zeta_i[0U]), zeta(zeta_i[0U] + (size_t)1U));
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_a7(size_t *zeta_i,
                                              Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_iot_ml_kem_vector_portable_ntt_layer_1_step_4e(
        &re->data[round], zeta(zeta_i[0U]), zeta(zeta_i[0U] + (size_t)1U),
        zeta(zeta_i[0U] + (size_t)2U), zeta(zeta_i[0U] + (size_t)3U));
    zeta_i[0U] = zeta_i[0U] + (size_t)3U;
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
static KRML_MUSTINLINE void poly_barrett_reduce_64_a7(Eurydice_arr_3d0 *self) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&self->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_a7(
    Eurydice_arr_3d0 *re, Eurydice_arr_e2 *scratch) {
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
    Eurydice_dst_ref_mut_64 re_as_ntt, const Eurydice_arr_3e *prf_input,
    uint8_t domain_separator, Eurydice_arr_e2 *scratch) {
  Eurydice_arr_65 prf_inputs;
  Eurydice_arr_3e repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e);
  }
  memcpy(prf_inputs.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_ac(&prf_inputs, domain_separator);
  Eurydice_arr_0b prf_outputs;
  uint8_t repeat_expression1[512U];
  for (size_t i = (size_t)0U; i < (size_t)512U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_outputs.data, repeat_expression1, (size_t)512U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      Eurydice_array_to_slice_shared_612(&prf_inputs),
      Eurydice_array_to_slice_mut_44(&prf_outputs), (size_t)128U);
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    Eurydice_borrow_slice_u8 randomness =
        Eurydice_array_to_subslice_shared_3611(
            &prf_outputs, (KRML_CLITERAL(core_ops_range_Range_08){
                              .start = i1 * (size_t)128U,
                              .end = (i1 + (size_t)1U) * (size_t)128U}));
    Eurydice_arr_c1 sample_buffer;
    int16_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] =
          libcrux_secrets_int_public_integers_classify_27_39((int16_t)0);
    }
    memcpy(sample_buffer.data, repeat_expression,
           (size_t)256U * sizeof(int16_t));
    sample_from_binomial_distribution_0b(randomness, &sample_buffer);
    from_i16_array_64_a7(
        Eurydice_array_to_slice_shared_1a(&sample_buffer),
        &Eurydice_slice_index_mut(re_as_ntt, i1, Eurydice_arr_3d0));
    ntt_binomially_sampled_ring_element_a7(
        &Eurydice_slice_index_mut(re_as_ntt, i1, Eurydice_arr_3d0), scratch);
  }
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
static Eurydice_arr_3d0 call_mut_58_161(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.entry
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static const Eurydice_arr_3d0 *entry_e1(Eurydice_dst_ref_shared_64 matrix,
                                        size_t i, size_t j) {
  return &Eurydice_slice_index_shared(matrix, i * (size_t)4U + j,
                                      Eurydice_arr_3d0);
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
    const Eurydice_arr_3d0 *self, const Eurydice_arr_3d0 *rhs,
    Eurydice_arr_c3 *accumulator, Eurydice_arr_3d0 *cache) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_fill_cache_4e(
        &self->data[i0], &rhs->data[i0],
        Eurydice_array_to_subslice_mut_7f(
            accumulator, (KRML_CLITERAL(core_ops_range_Range_08){
                             .start = i0 * (size_t)16U,
                             .end = (i0 + (size_t)1U) * (size_t)16U})),
        &cache->data[i0], zeta((size_t)64U + (size_t)4U * i0),
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
libcrux_iot_ml_kem.polynomial.reducing_from_i32_array_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void reducing_from_i32_array_64_a7(
    Eurydice_dst_ref_shared_fc a, Eurydice_arr_3d0 *out) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_reducing_from_i32_array_4e(
        Eurydice_slice_subslice_shared_46(
            a, (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = i0 * (size_t)16U,
                   .end = (i0 + (size_t)1U) * (size_t)16U})),
        &out->data[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.traits.to_standard_domain
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void to_standard_domain_a7(Eurydice_arr_e2 *v) {
  libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
      v,
      LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
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
    Eurydice_arr_3d0 *self, const Eurydice_arr_3d0 *error) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    to_standard_domain_a7(&self->data[j]);
    libcrux_iot_ml_kem_vector_portable_add_4e(&self->data[j], &error->data[j]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&self->data[j]);
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
    const Eurydice_arr_3d0 *self, const Eurydice_arr_3d0 *rhs,
    Eurydice_arr_c3 *accumulator, const Eurydice_arr_3d0 *cache) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_use_cache_4e(
        &self->data[i0], &rhs->data[i0],
        Eurydice_array_to_subslice_mut_7f(
            accumulator, (KRML_CLITERAL(core_ops_range_Range_08){
                             .start = i0 * (size_t)16U,
                             .end = (i0 + (size_t)1U) * (size_t)16U})),
        &cache->data[i0]);
  }
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
    arr_f2 *t_as_ntt, Eurydice_dst_ref_shared_64 matrix_A,
    const arr_f2 *s_as_ntt, const arr_f2 *error_as_ntt, arr_f2 *s_cache,
    Eurydice_arr_c3 *accumulator) {
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t j = i;
    accumulating_ntt_multiply_fill_cache_64_a7(
        entry_e1(matrix_A, (size_t)0U, j), &s_as_ntt->data[j], accumulator,
        &s_cache->data[j]);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_20(accumulator),
                                t_as_ntt->data);
  add_standard_error_reduce_64_a7(t_as_ntt->data, error_as_ntt->data);
  for (size_t i0 = (size_t)1U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    int32_t uu____0 =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
    Eurydice_arr_c3 lit;
    int32_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] = uu____0;
    }
    memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
    accumulator[0U] = lit;
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t j = i;
      accumulating_ntt_multiply_use_cache_64_a7(entry_e1(matrix_A, i1, j),
                                                &s_as_ntt->data[j], accumulator,
                                                &s_cache->data[j]);
    }
    reducing_from_i32_array_64_a7(
        Eurydice_array_to_slice_shared_20(accumulator), &t_as_ntt->data[i1]);
    add_standard_error_reduce_64_a7(&t_as_ntt->data[i1],
                                    &error_as_ntt->data[i1]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 16
*/
static Eurydice_dst_ref_shared_64 array_to_slice_shared_343(const arr_5c *a) {
  Eurydice_dst_ref_shared_64 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
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
    Eurydice_borrow_slice_u8 key_generation_seed, arr_f2 *private_key,
    IndCpaPublicKeyUnpacked_81 *public_key, Eurydice_arr_3d0 *scratch,
    arr_f2 *s_cache, Eurydice_arr_c3 *accumulator) {
  Eurydice_arr_06 hashed;
  uint8_t repeat_expression[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression, (size_t)64U * sizeof(uint8_t));
  cpa_keygen_seed_cc_22(key_generation_seed,
                        Eurydice_array_to_slice_mut_d8(&hashed));
  Eurydice_dst_ref_shared_uint8_t_size_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_d8(&hashed), (size_t)32U, uint8_t,
      Eurydice_dst_ref_shared_uint8_t_size_t_x2);
  Eurydice_borrow_slice_u8 seed_for_A = uu____0.fst;
  Eurydice_borrow_slice_u8 seed_for_secret_and_error = uu____0.snd;
  Eurydice_dst_ref_mut_64 uu____1 = array_to_slice_mut_343(&public_key->A);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue0 =
      libcrux_secrets_int_public_integers_declassify_d8_2c(
          libcrux_iot_ml_kem_utils_into_padded_array_b6(seed_for_A));
  sample_matrix_A_c91(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_iot_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator = sample_vector_cbd_then_ntt_141(
      array_to_slice_mut_340(private_key), &prf_input, 0U, scratch->data);
  arr_f2 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_58_161(&lvalue);
  }
  arr_f2 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_141(array_to_slice_mut_340(&error_as_ntt),
                                 &prf_input, domain_separator, scratch->data);
  compute_As_plus_e_e1(&public_key->t_as_ntt,
                       array_to_slice_shared_343(&public_key->A), private_key,
                       &error_as_ntt, s_cache, accumulator);
  Eurydice_mut_borrow_slice_u8 uu____2 =
      Eurydice_array_to_slice_mut_6e(&public_key->seed_for_A);
  Eurydice_slice_copy(
      uu____2,
      libcrux_secrets_int_classify_public_declassify_ref_7f_90(seed_for_A),
      uint8_t);
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
    const IndCpaPublicKeyUnpacked_81 *public_key, const arr_f2 *private_key,
    Eurydice_mut_borrow_slice_u8 serialized_private_key,
    Eurydice_mut_borrow_slice_u8 serialized_public_key,
    Eurydice_arr_e2 *scratch) {
  serialize_public_key_mut_c5(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice_shared_6e(&public_key->seed_for_A),
      serialized_public_key, scratch);
  serialize_vector_e1(private_key, serialized_private_key, scratch);
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
    Eurydice_borrow_slice_u8 key_generation_seed,
    Eurydice_mut_borrow_slice_u8 serialized_ind_cpa_private_key,
    Eurydice_mut_borrow_slice_u8 serialized_public_key,
    Eurydice_arr_3d0 *scratch, arr_f2 *s_cache, Eurydice_arr_c3 *accumulator) {
  arr_f2 private_key = default_1e_e1();
  IndCpaPublicKeyUnpacked_81 public_key = default_1f_c5();
  generate_keypair_unpacked_161(key_generation_seed, &private_key, &public_key,
                                scratch, s_cache, accumulator);
  serialize_unpacked_secret_key_00(&public_key, &private_key,
                                   serialized_ind_cpa_private_key,
                                   serialized_public_key, scratch->data);
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
    Eurydice_borrow_slice_u8 private_key, Eurydice_borrow_slice_u8 public_key,
    Eurydice_borrow_slice_u8 implicit_rejection_value,
    Eurydice_arr_17 *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_17 *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_368(
          uu____0,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = uu____1,
              .end = uu____2 + Eurydice_slice_len(private_key, uint8_t)})),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_17 *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_mut_borrow_slice_u8 uu____6 = Eurydice_array_to_subslice_mut_368(
      uu____3, (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = uu____4,
                   .end = uu____5 + Eurydice_slice_len(public_key, uint8_t)}));
  Eurydice_slice_copy(
      uu____6,
      libcrux_secrets_int_classify_public_classify_ref_9b_90(public_key),
      uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(public_key),
      Eurydice_array_to_subslice_mut_368(
          serialized,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = pointer,
              .end = pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE})));
  pointer = pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_17 *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_368(
          uu____7,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = uu____8,
              .end = uu____9 +
                     Eurydice_slice_len(implicit_rejection_value, uint8_t)})),
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
libcrux_iot_ml_kem_types_MlKemKeyPair_f7
libcrux_iot_ml_kem_ind_cca_generate_keypair_b71(
    const Eurydice_arr_06 *randomness) {
  Eurydice_borrow_slice_u8 ind_cpa_keypair_randomness =
      Eurydice_array_to_subslice_shared_366(
          randomness,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}));
  Eurydice_borrow_slice_u8 implicit_rejection_value =
      Eurydice_array_to_subslice_from_shared_8c0(
          randomness,
          LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE);
  Eurydice_arr_00 public_key = {.data = {0U}};
  Eurydice_arr_17 secret_key_serialized;
  uint8_t repeat_expression0[3168U];
  for (size_t i = (size_t)0U; i < (size_t)3168U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(secret_key_serialized.data, repeat_expression0,
         (size_t)3168U * sizeof(uint8_t));
  Eurydice_arr_38 ind_cpa_private_key;
  uint8_t repeat_expression1[1536U];
  for (size_t i = (size_t)0U; i < (size_t)1536U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(ind_cpa_private_key.data, repeat_expression1,
         (size_t)1536U * sizeof(uint8_t));
  Eurydice_arr_3d0 scratch = ZERO_64_a7();
  Eurydice_arr_c3 accumulator;
  int32_t repeat_expression2[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  }
  memcpy(accumulator.data, repeat_expression2, (size_t)256U * sizeof(int32_t));
  arr_f2 s_cache;
  Eurydice_arr_3d0 repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(s_cache.data, repeat_expression,
         (size_t)4U * sizeof(Eurydice_arr_3d0));
  generate_keypair_641(ind_cpa_keypair_randomness,
                       Eurydice_array_to_slice_mut_c9(&ind_cpa_private_key),
                       Eurydice_array_to_slice_mut_4e(&public_key), &scratch,
                       &s_cache, &accumulator);
  serialize_kem_secret_key_mut_8a(
      Eurydice_array_to_slice_shared_c9(&ind_cpa_private_key),
      Eurydice_array_to_slice_shared_4e(&public_key), implicit_rejection_value,
      &secret_key_serialized);
  Eurydice_arr_17 private_key =
      libcrux_iot_ml_kem_types_from_56_39(secret_key_serialized);
  return libcrux_iot_ml_kem_types_from_d9_94(
      private_key, libcrux_iot_ml_kem_types_from_18_af(public_key));
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
static KRML_MUSTINLINE void entropy_preprocess_cc_22(
    Eurydice_borrow_slice_u8 randomness, Eurydice_mut_borrow_slice_u8 out) {
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
static Eurydice_arr_3d0 call_mut_92_351(void **_) { return ZERO_64_a7(); }

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
static Eurydice_arr_3d0 call_mut_6f_921(void **_) { return ZERO_64_a7(); }

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
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_141(
    const Eurydice_arr_3e *prf_input, uint8_t domain_separator,
    Eurydice_dst_ref_mut_64 error_1, Eurydice_arr_c1 *sample_buffer) {
  Eurydice_arr_65 prf_inputs;
  Eurydice_arr_3e repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e);
  }
  memcpy(prf_inputs.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_ac(&prf_inputs, domain_separator);
  Eurydice_arr_0b prf_outputs;
  uint8_t repeat_expression[512U];
  for (size_t i = (size_t)0U; i < (size_t)512U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_outputs.data, repeat_expression, (size_t)512U * sizeof(uint8_t));
  Eurydice_dst_ref_shared_d2 uu____0 = core_array___Array_T__N___as_slice(
      (size_t)4U, &prf_inputs, Eurydice_arr_3e, Eurydice_dst_ref_shared_d2);
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      uu____0, Eurydice_array_to_slice_mut_44(&prf_outputs), (size_t)128U);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 randomness =
        Eurydice_array_to_subslice_shared_3611(
            &prf_outputs, (KRML_CLITERAL(core_ops_range_Range_08){
                              .start = i0 * (size_t)128U,
                              .end = (i0 + (size_t)1U) * (size_t)128U}));
    sample_from_binomial_distribution_0b(randomness, sample_buffer);
    from_i16_array_64_a7(
        Eurydice_array_to_slice_shared_1a(sample_buffer),
        &Eurydice_slice_index_mut(error_1, i0, Eurydice_arr_3d0));
  }
  return domain_separator;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_a6(Eurydice_borrow_slice_u8 input,
                                   Eurydice_mut_borrow_slice_u8 out) {
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
static KRML_MUSTINLINE void PRF_07_a6(Eurydice_borrow_slice_u8 input,
                                      Eurydice_mut_borrow_slice_u8 out) {
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
static Eurydice_arr_3d0 call_mut_33_921(void **_) { return ZERO_64_a7(); }

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
    Eurydice_dst_ref_shared_ea randomness,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)1U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                  .ptr = sampled_coefficients.ptr,
                  .meta = sampled_coefficients.meta}),
              i1, size_t) <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_b0 *randomness_i =
            &Eurydice_slice_index_shared(randomness, i1, Eurydice_arr_b0);
        Eurydice_arr_a0 *out_i =
            &Eurydice_slice_index_mut(out, i1, Eurydice_arr_a0);
        size_t sampled_coefficients_i = Eurydice_slice_index_shared(
            (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                .ptr = sampled_coefficients.ptr,
                .meta = sampled_coefficients.meta}),
            i1, size_t);
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_363(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_08){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_85(
                out_i, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        size_t uu____0 = i1;
        Eurydice_slice_index_mut(sampled_coefficients, uu____0, size_t) =
            Eurydice_slice_index_shared(
                (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                    .ptr = sampled_coefficients.ptr,
                    .meta = sampled_coefficients.meta}),
                uu____0, size_t) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index_shared((KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                                        .ptr = sampled_coefficients.ptr,
                                        .meta = sampled_coefficients.meta}),
                                    i0, size_t) >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index_mut(sampled_coefficients, i0, size_t) =
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
    Eurydice_dst_ref_shared_36 randomness,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)1U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                  .ptr = sampled_coefficients.ptr,
                  .meta = sampled_coefficients.meta}),
              i1, size_t) <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_27 *randomness_i =
            &Eurydice_slice_index_shared(randomness, i1, Eurydice_arr_27);
        Eurydice_arr_a0 *out_i =
            &Eurydice_slice_index_mut(out, i1, Eurydice_arr_a0);
        size_t sampled_coefficients_i = Eurydice_slice_index_shared(
            (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                .ptr = sampled_coefficients.ptr,
                .meta = sampled_coefficients.meta}),
            i1, size_t);
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_364(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_08){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_85(
                out_i, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        size_t uu____0 = i1;
        Eurydice_slice_index_mut(sampled_coefficients, uu____0, size_t) =
            Eurydice_slice_index_shared(
                (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                    .ptr = sampled_coefficients.ptr,
                    .meta = sampled_coefficients.meta}),
                uu____0, size_t) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index_shared((KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                                        .ptr = sampled_coefficients.ptr,
                                        .meta = sampled_coefficients.meta}),
                                    i0, size_t) >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index_mut(sampled_coefficients, i0, size_t) =
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
    Eurydice_dst_ref_shared_60 seeds,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  Eurydice_arr_5e xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  Eurydice_arr_e4 randomness = {.data = {{.data = {0U}}}};
  Eurydice_arr_75 randomness_blocksize = {.data = {{.data = {0U}}}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state, Eurydice_array_to_slice_mut_e9(&randomness));
  bool done = sample_from_uniform_distribution_next_1b(
      Eurydice_array_to_slice_shared_e9(&randomness), sampled_coefficients,
      out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice_mut_e7(&randomness_blocksize));
      done = sample_from_uniform_distribution_next_1b0(
          Eurydice_array_to_slice_shared_e7(&randomness_blocksize),
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
    Eurydice_arr_3d0 *out, Eurydice_borrow_slice_u8 seed, size_t i, size_t j) {
  Eurydice_arr_48 seed_ij = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_363(
          &seed_ij, (KRML_CLITERAL(core_ops_range_Range_08){
                        .start = (size_t)0U, .end = (size_t)32U})),
      seed, uint8_t);
  seed_ij.data[32U] = (uint8_t)i;
  seed_ij.data[33U] = (uint8_t)j;
  Eurydice_arr_e40 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_8b out_raw = {.data = {{.data = {0U}}}};
  Eurydice_arr_b8 uu____0 = {.data = {seed_ij}};
  sample_from_xof_c9(Eurydice_array_to_slice_shared_c7(&uu____0),
                     Eurydice_array_to_slice_mut_26(&sampled_coefficients),
                     Eurydice_array_to_slice_mut_30(&out_raw));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_a0 lvalue =
      libcrux_secrets_int_public_integers_classify_27_9a(out_raw.data[0U]);
  from_i16_array_64_a7(
      core_array___Array_T__N___as_slice((size_t)272U, &lvalue, int16_t,
                                         Eurydice_borrow_slice_i16),
      out);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_a7(size_t *zeta_i,
                                                     Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_1_step_4e(
        &re->data[round], zeta(zeta_i[0U]), zeta(zeta_i[0U] - (size_t)1U),
        zeta(zeta_i[0U] - (size_t)2U), zeta(zeta_i[0U] - (size_t)3U));
    zeta_i[0U] = zeta_i[0U] - (size_t)3U;
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_2_a7(size_t *zeta_i,
                                                     Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_2_step_4e(
        &re->data[round], zeta(zeta_i[0U]), zeta(zeta_i[0U] - (size_t)1U));
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_a7(size_t *zeta_i,
                                                     Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_3_step_4e(
        &re->data[round], zeta(zeta_i[0U]));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void inv_ntt_layer_int_vec_step_reduce_a7(
    Eurydice_arr_3d0 *coefficients, size_t a, size_t b,
    Eurydice_arr_e2 *scratch, int16_t zeta_r) {
  scratch[0U] = coefficients->data[a];
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients->data[b]);
  libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(scratch);
  coefficients->data[a] = scratch[0U];
  libcrux_iot_ml_kem_vector_portable_negate_4e(scratch);
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients->data[b]);
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients->data[b]);
  montgomery_multiply_fe_a7(scratch, zeta_r);
  coefficients->data[b] = scratch[0U];
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_a7(
    size_t *zeta_i, Eurydice_arr_3d0 *re, size_t layer,
    Eurydice_arr_e2 *scratch) {
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
      inv_ntt_layer_int_vec_step_reduce_a7(re, a_offset + j, b_offset + j,
                                           scratch, zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_e1(Eurydice_arr_3d0 *re,
                                                     Eurydice_arr_e2 *scratch) {
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
    Eurydice_arr_3d0 *self, const Eurydice_arr_3d0 *error) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &self->data[j], (int16_t)1441);
    libcrux_iot_ml_kem_vector_portable_add_4e(&self->data[j], &error->data[j]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&self->data[j]);
  }
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
    Eurydice_arr_3d0 *matrix_entry, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_shared_64 r_as_ntt, Eurydice_dst_ref_shared_64 error_1,
    Eurydice_dst_ref_mut_64 result, Eurydice_arr_e2 *scratch,
    Eurydice_dst_ref_mut_64 cache, Eurydice_arr_c3 *accumulator) {
  int32_t uu____0 =
      libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  Eurydice_arr_c3 lit0;
  int32_t repeat_expression0[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression0[i] = uu____0;
  }
  memcpy(lit0.data, repeat_expression0, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit0;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t j = i;
    sample_matrix_entry_36(matrix_entry, seed, (size_t)0U, j);
    accumulating_ntt_multiply_fill_cache_64_a7(
        matrix_entry,
        &Eurydice_slice_index_shared(r_as_ntt, j, Eurydice_arr_3d0),
        accumulator, &Eurydice_slice_index_mut(cache, j, Eurydice_arr_3d0));
  }
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice_shared_20(accumulator),
      &Eurydice_slice_index_mut(result, (size_t)0U, Eurydice_arr_3d0));
  invert_ntt_montgomery_e1(
      &Eurydice_slice_index_mut(result, (size_t)0U, Eurydice_arr_3d0), scratch);
  add_error_reduce_64_a7(
      &Eurydice_slice_index_mut(result, (size_t)0U, Eurydice_arr_3d0),
      &Eurydice_slice_index_shared(error_1, (size_t)0U, Eurydice_arr_3d0));
  for (size_t i0 = (size_t)1U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    int32_t uu____1 =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
    Eurydice_arr_c3 lit;
    int32_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] = uu____1;
    }
    memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
    accumulator[0U] = lit;
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t j = i;
      sample_matrix_entry_36(matrix_entry, seed, i1, j);
      accumulating_ntt_multiply_use_cache_64_a7(
          matrix_entry,
          &Eurydice_slice_index_shared(r_as_ntt, j, Eurydice_arr_3d0),
          accumulator,
          &Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_64){.ptr = cache.ptr,
                                                         .meta = cache.meta}),
              j, Eurydice_arr_3d0));
    }
    reducing_from_i32_array_64_a7(
        Eurydice_array_to_slice_shared_20(accumulator),
        &Eurydice_slice_index_mut(result, i1, Eurydice_arr_3d0));
    invert_ntt_montgomery_e1(
        &Eurydice_slice_index_mut(result, i1, Eurydice_arr_3d0), scratch);
    add_error_reduce_64_a7(
        &Eurydice_slice_index_mut(result, i1, Eurydice_arr_3d0),
        &Eurydice_slice_index_shared(error_1, i1, Eurydice_arr_3d0));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void compress_ef(Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)10, libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
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
static KRML_MUSTINLINE void compress_4e_ef(Eurydice_arr_e2 *a) {
  compress_ef(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void compress_c4(Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)11, libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
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
static KRML_MUSTINLINE void compress_4e_c4(Eurydice_arr_e2 *a) {
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
    const Eurydice_arr_3d0 *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_representative_a7(&re->data[i0], scratch);
    compress_4e_c4(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_11_4e(
        scratch, Eurydice_slice_subslice_mut_7e(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                                     .start = (size_t)22U * i0,
                                     .end = (size_t)22U * i0 + (size_t)22U})));
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
    const Eurydice_arr_3d0 *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_e2 *scratch) {
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
    arr_f2 input, Eurydice_mut_borrow_slice_u8 out, Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(array_to_slice_shared_340(&input), Eurydice_arr_3d0);
       i++) {
    size_t i0 = i;
    Eurydice_arr_3d0 re = input.data[i0];
    compress_then_serialize_ring_element_u_d2(
        &re,
        Eurydice_slice_subslice_mut_7e(
            out, (KRML_CLITERAL(core_ops_range_Range_08){
                     .start = i0 * ((size_t)1408U / (size_t)4U),
                     .end = (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U)})),
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
    Eurydice_borrow_slice_u8 randomness, Eurydice_arr_3d0 *matrix_entry,
    Eurydice_borrow_slice_u8 seed_for_a,
    Eurydice_mut_borrow_slice_u8 ciphertext, Eurydice_dst_ref_mut_64 r_as_ntt,
    Eurydice_arr_3d0 *error_2, Eurydice_arr_e2 *scratch,
    Eurydice_dst_ref_mut_64 cache, Eurydice_arr_c3 *accumulator) {
  Eurydice_arr_3e prf_input =
      libcrux_iot_ml_kem_utils_into_padded_array_c8(randomness);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_141(r_as_ntt, &prf_input, 0U, scratch);
  arr_f2 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_6f_921(&lvalue);
  }
  arr_f2 error_1 = arr_struct;
  Eurydice_arr_c1 sampling_buffer;
  int16_t repeat_expression0[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_39((int16_t)0);
  }
  memcpy(sampling_buffer.data, repeat_expression0,
         (size_t)256U * sizeof(int16_t));
  uint8_t domain_separator0 = sample_ring_element_cbd_141(
      &prf_input, domain_separator, array_to_slice_mut_340(&error_1),
      &sampling_buffer);
  prf_input.data[32U] =
      libcrux_secrets_int_public_integers_classify_27_90(domain_separator0);
  Eurydice_arr_d1 prf_output;
  uint8_t repeat_expression[128U];
  for (size_t i = (size_t)0U; i < (size_t)128U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_output.data, repeat_expression, (size_t)128U * sizeof(uint8_t));
  PRF_07_a6(Eurydice_array_to_slice_shared_610(&prf_input),
            Eurydice_array_to_slice_mut_18(&prf_output));
  sample_from_binomial_distribution_0b(
      Eurydice_array_to_slice_shared_18(&prf_output), &sampling_buffer);
  from_i16_array_64_a7(Eurydice_array_to_slice_shared_1a(&sampling_buffer),
                       error_2);
  arr_f2 arr_struct0;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct0.data[i] = call_mut_33_921(&lvalue);
  }
  arr_f2 u = arr_struct0;
  compute_vector_u_c91(matrix_entry, seed_for_a,
                       (KRML_CLITERAL(Eurydice_dst_ref_shared_64){
                           .ptr = r_as_ntt.ptr, .meta = r_as_ntt.meta}),
                       array_to_slice_shared_340(&error_1),
                       array_to_slice_mut_340(&u), scratch, cache, accumulator);
  compress_then_serialize_u_00(u, ciphertext, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.traits.decompress_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void decompress_1_a7(Eurydice_arr_e2 *vec) {
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
    const Eurydice_arr_600 *serialized, Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_deserialize_1_4e(
        Eurydice_array_to_subslice_shared_365(
            serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                            .start = (size_t)2U * i0,
                            .end = (size_t)2U * i0 + (size_t)2U})),
        &re->data[i0]);
    decompress_1_a7(&re->data[i0]);
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
    const Eurydice_arr_3d0 *self, const Eurydice_arr_3d0 *message,
    Eurydice_arr_3d0 *result, Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &result->data[i0], (int16_t)1441);
    scratch[0U] = self->data[i0];
    libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &message->data[i0]);
    libcrux_iot_ml_kem_vector_portable_add_4e(&result->data[i0], scratch);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&result->data[i0]);
  }
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
    Eurydice_borrow_slice_u8 public_key, Eurydice_arr_3d0 *t_as_ntt_entry,
    Eurydice_dst_ref_shared_64 r_as_ntt, const Eurydice_arr_3d0 *error_2,
    const Eurydice_arr_3d0 *message, Eurydice_arr_3d0 *result,
    Eurydice_arr_e2 *scratch, Eurydice_dst_ref_shared_64 cache,
    Eurydice_arr_c3 *accumulator) {
  int32_t uu____0 =
      libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  Eurydice_arr_c3 lit;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] = uu____0;
  }
  memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 ring_element = Eurydice_slice_subslice_shared_7e(
        public_key,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}));
    deserialize_to_reduced_ring_element_a7(
        libcrux_secrets_int_classify_public_classify_ref_9b_90(ring_element),
        t_as_ntt_entry);
    accumulating_ntt_multiply_use_cache_64_a7(
        t_as_ntt_entry,
        &Eurydice_slice_index_shared(r_as_ntt, i0, Eurydice_arr_3d0),
        accumulator, &Eurydice_slice_index_shared(cache, i0, Eurydice_arr_3d0));
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_20(accumulator),
                                result);
  invert_ntt_montgomery_e1(result, scratch);
  add_message_error_reduce_64_a7(error_2, message, result, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void compress_d1(Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)4, libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
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
static KRML_MUSTINLINE void compress_4e_d1(Eurydice_arr_e2 *a) {
  compress_d1(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.serialize.compress_then_serialize_4
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_a7(
    Eurydice_arr_3d0 re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re.data[i0], scratch);
    compress_4e_d1(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_4_4e(
        scratch, Eurydice_slice_subslice_mut_7e(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                                     .start = (size_t)8U * i0,
                                     .end = (size_t)8U * i0 + (size_t)8U})));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void compress_f4(Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)5, libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
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
static KRML_MUSTINLINE void compress_4e_f4(Eurydice_arr_e2 *a) {
  compress_f4(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.serialize.compress_then_serialize_5
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_a7(
    Eurydice_arr_3d0 re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_representative_a7(&re.data[i0], scratch);
    compress_4e_f4(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_5_4e(
        scratch, Eurydice_slice_subslice_mut_7e(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                                     .start = (size_t)10U * i0,
                                     .end = (size_t)10U * i0 + (size_t)10U})));
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
    Eurydice_arr_3d0 re, Eurydice_mut_borrow_slice_u8 out,
    Eurydice_arr_e2 *scratch) {
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
    Eurydice_borrow_slice_u8 public_key, Eurydice_arr_3d0 *t_as_ntt_entry,
    Eurydice_dst_ref_shared_64 r_as_ntt, const Eurydice_arr_3d0 *error_2,
    const Eurydice_arr_600 *message, Eurydice_mut_borrow_slice_u8 ciphertext,
    Eurydice_arr_e2 *scratch, Eurydice_dst_ref_shared_64 cache,
    Eurydice_arr_c3 *accumulator) {
  Eurydice_arr_3d0 message_as_ring_element = ZERO_64_a7();
  deserialize_then_decompress_message_a7(message, &message_as_ring_element);
  Eurydice_arr_3d0 v = ZERO_64_a7();
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
    Eurydice_borrow_slice_u8 public_key, const Eurydice_arr_600 *message,
    Eurydice_borrow_slice_u8 randomness,
    Eurydice_mut_borrow_slice_u8 ciphertext, Eurydice_arr_3d0 *matrix_entry,
    Eurydice_dst_ref_mut_64 r_as_ntt, Eurydice_arr_3d0 *error_2,
    Eurydice_arr_e2 *scratch, Eurydice_dst_ref_mut_64 cache,
    Eurydice_arr_c3 *accumulator) {
  encrypt_c1_921(
      randomness, matrix_entry,
      Eurydice_slice_subslice_from_shared_6b(public_key, (size_t)1536U),
      Eurydice_slice_subslice_mut_7e(
          ciphertext, (KRML_CLITERAL(core_ops_range_Range_08){
                          .start = (size_t)0U, .end = (size_t)1408U})),
      r_as_ntt, error_2, scratch, cache, accumulator);
  encrypt_c2_e9(Eurydice_slice_subslice_to_shared_c6(public_key, (size_t)1536U),
                matrix_entry,
                (KRML_CLITERAL(Eurydice_dst_ref_shared_64){
                    .ptr = r_as_ntt.ptr, .meta = r_as_ntt.meta}),
                error_2, message,
                Eurydice_slice_subslice_from_mut_6b(ciphertext, (size_t)1408U),
                scratch,
                (KRML_CLITERAL(Eurydice_dst_ref_shared_64){.ptr = cache.ptr,
                                                           .meta = cache.meta}),
                accumulator);
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
static KRML_MUSTINLINE void kdf_cc_8a(Eurydice_borrow_slice_u8 shared_secret,
                                      Eurydice_mut_borrow_slice_u8 out) {
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
tuple_32 libcrux_iot_ml_kem_ind_cca_encapsulate_351(
    const Eurydice_arr_00 *public_key, const Eurydice_arr_600 *randomness) {
  Eurydice_arr_600 processed_randomness;
  uint8_t repeat_expression0[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(processed_randomness.data, repeat_expression0,
         (size_t)32U * sizeof(uint8_t));
  entropy_preprocess_cc_22(
      Eurydice_array_to_slice_shared_6e(randomness),
      Eurydice_array_to_slice_mut_6e(&processed_randomness));
  Eurydice_arr_06 to_hash = libcrux_iot_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice_shared_6e(&processed_randomness));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_00 lvalue0 =
      libcrux_secrets_int_public_integers_classify_27_b7(public_key[0U]);
  Eurydice_borrow_slice_u8 uu____0 = core_array___Array_T__N___as_slice(
      (size_t)1568U, &lvalue0, uint8_t, Eurydice_borrow_slice_u8);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      uu____0, Eurydice_array_to_subslice_from_mut_8c(
                   &to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE));
  Eurydice_arr_06 hashed;
  uint8_t repeat_expression1[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression1, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_d8(&to_hash),
      Eurydice_array_to_slice_mut_d8(&hashed));
  Eurydice_dst_ref_shared_uint8_t_size_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_d8(&hashed),
      LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_dst_ref_shared_uint8_t_size_t_x2);
  Eurydice_borrow_slice_u8 shared_secret = uu____1.fst;
  Eurydice_borrow_slice_u8 pseudorandomness = uu____1.snd;
  Eurydice_arr_00 ciphertext = {.data = {0U}};
  arr_f2 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_92_351(&lvalue);
  }
  arr_f2 r_as_ntt = arr_struct;
  Eurydice_arr_3d0 error_2 = ZERO_64_a7();
  Eurydice_arr_e2 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  Eurydice_arr_c3 accumulator;
  int32_t repeat_expression2[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  }
  memcpy(accumulator.data, repeat_expression2, (size_t)256U * sizeof(int32_t));
  arr_f2 cache;
  Eurydice_arr_3d0 repeat_expression3[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression3[i] = ZERO_64_a7();
  }
  memcpy(cache.data, repeat_expression3, (size_t)4U * sizeof(Eurydice_arr_3d0));
  Eurydice_arr_3d0 matrix_entry = ZERO_64_a7();
  const Eurydice_arr_00 *uu____2 =
      libcrux_iot_ml_kem_types_as_slice_63_af(public_key);
  encrypt_5a1(Eurydice_array_to_slice_shared_4e(uu____2), &processed_randomness,
              pseudorandomness, Eurydice_array_to_slice_mut_4e(&ciphertext),
              &matrix_entry, array_to_slice_mut_340(&r_as_ntt), &error_2,
              &scratch, array_to_slice_mut_340(&cache), &accumulator);
  Eurydice_arr_00 ciphertext0 = libcrux_iot_ml_kem_types_from_9d_af(ciphertext);
  Eurydice_arr_600 shared_secret_array;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret_array.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_8a(shared_secret,
            Eurydice_array_to_slice_mut_6e(&shared_secret_array));
  return (
      KRML_CLITERAL(tuple_32){.fst = ciphertext0, .snd = shared_secret_array});
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
static Eurydice_arr_3d0 call_mut_a5_08(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_to_uncompressed_ring_element_a7(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)24U, .end = i0 * (size_t)24U + (size_t)24U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(bytes, &re->data[i0]);
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
    Eurydice_borrow_slice_u8 secret_key,
    Eurydice_dst_ref_mut_64 secret_as_ntt) {
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    deserialize_to_uncompressed_ring_element_a7(
        Eurydice_slice_subslice_shared_7e(
            secret_key,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT})),
        &Eurydice_slice_index_mut(secret_as_ntt, i0, Eurydice_arr_3d0));
  }
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
static Eurydice_arr_3d0 call_mut_b7_08(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_ef(
    Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = core_num__i32__wrapping_mul(
        libcrux_secrets_int_as_i32_f5(a->data[i0]),
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
    decompressed = core_num__i32__wrapping_add(
        decompressed << 1U, (int32_t)1 << (uint32_t)(int32_t)10);
    decompressed = decompressed >> (uint32_t)((int32_t)10 + (int32_t)1);
    a->data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
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
    Eurydice_arr_e2 *a) {
  decompress_ciphertext_coefficient_ef(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_10_a7(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)20U, .end = i0 * (size_t)20U + (size_t)20U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_10_4e(bytes, &re->data[i0]);
    decompress_ciphertext_coefficient_4e_ef(&re->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_c4(
    Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = core_num__i32__wrapping_mul(
        libcrux_secrets_int_as_i32_f5(a->data[i0]),
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
    decompressed = core_num__i32__wrapping_add(
        decompressed << 1U, (int32_t)1 << (uint32_t)(int32_t)11);
    decompressed = decompressed >> (uint32_t)((int32_t)11 + (int32_t)1);
    a->data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
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
    Eurydice_arr_e2 *a) {
  decompress_ciphertext_coefficient_c4(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_11_a7(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)22U, .end = i0 * (size_t)22U + (size_t)22U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_11_4e(bytes, &re->data[i0]);
    decompress_ciphertext_coefficient_4e_c4(&re->data[i0]);
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
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *output) {
  deserialize_then_decompress_11_a7(serialized, output);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_93(Eurydice_arr_3d0 *re,
                                            Eurydice_arr_e2 *scratch) {
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
    const Eurydice_arr_00 *ciphertext, Eurydice_dst_ref_mut_64 u_as_ntt,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice_shared_4e(ciphertext),
                              uint8_t) /
               (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 u_bytes = Eurydice_array_to_subslice_shared_3610(
        ciphertext,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start =
                i0 *
                (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                 (size_t)11U / (size_t)8U),
            .end =
                i0 *
                    (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                     (size_t)11U / (size_t)8U) +
                LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                    (size_t)11U / (size_t)8U}));
    deserialize_then_decompress_ring_element_u_93(
        u_bytes, &Eurydice_slice_index_mut(u_as_ntt, i0, Eurydice_arr_3d0));
    ntt_vector_u_93(&Eurydice_slice_index_mut(u_as_ntt, i0, Eurydice_arr_3d0),
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
    Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = core_num__i32__wrapping_mul(
        libcrux_secrets_int_as_i32_f5(a->data[i0]),
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
    decompressed = core_num__i32__wrapping_add(
        decompressed << 1U, (int32_t)1 << (uint32_t)(int32_t)4);
    decompressed = decompressed >> (uint32_t)((int32_t)4 + (int32_t)1);
    a->data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
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
    Eurydice_arr_e2 *a) {
  decompress_ciphertext_coefficient_d1(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_4_a7(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)8U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_4_4e(bytes, &re->data[i0]);
    decompress_ciphertext_coefficient_4e_d1(&re->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_f4(
    Eurydice_arr_e2 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = core_num__i32__wrapping_mul(
        libcrux_secrets_int_as_i32_f5(a->data[i0]),
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
    decompressed = core_num__i32__wrapping_add(
        decompressed << 1U, (int32_t)1 << (uint32_t)(int32_t)5);
    decompressed = decompressed >> (uint32_t)((int32_t)5 + (int32_t)1);
    a->data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
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
    Eurydice_arr_e2 *a) {
  decompress_ciphertext_coefficient_f4(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_5_a7(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_7e(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * (size_t)10U, .end = i0 * (size_t)10U + (size_t)10U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_5_4e(bytes, &re->data[i0]);
    decompress_ciphertext_coefficient_4e_f4(&re->data[i0]);
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
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *output) {
  deserialize_then_decompress_5_a7(serialized, output);
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
    const Eurydice_arr_3d0 *self, const Eurydice_arr_3d0 *rhs,
    Eurydice_arr_c3 *accumulator) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_4e(
        &self->data[i0], &rhs->data[i0],
        Eurydice_array_to_subslice_mut_7f(
            accumulator, (KRML_CLITERAL(core_ops_range_Range_08){
                             .start = i0 * (size_t)16U,
                             .end = (i0 + (size_t)1U) * (size_t)16U})),
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
A monomorphic instance of libcrux_iot_ml_kem.polynomial.subtract_reduce_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void subtract_reduce_64_a7(const Eurydice_arr_3d0 *self,
                                                  Eurydice_arr_3d0 *b) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &b->data[i0], (int16_t)1441);
    libcrux_iot_ml_kem_vector_portable_sub_4e(&b->data[i0], &self->data[i0]);
    libcrux_iot_ml_kem_vector_portable_negate_4e(&b->data[i0]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&b->data[i0]);
  }
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
static KRML_MUSTINLINE void compute_message_e1(const Eurydice_arr_3d0 *v,
                                               const arr_f2 *secret_as_ntt,
                                               const arr_f2 *u_as_ntt,
                                               Eurydice_arr_3d0 *result,
                                               Eurydice_arr_e2 *scratch,
                                               Eurydice_arr_c3 *accumulator) {
  int32_t uu____0 =
      libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  Eurydice_arr_c3 lit;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] = uu____0;
  }
  memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    accumulating_ntt_multiply_64_a7(&secret_as_ntt->data[i0],
                                    &u_as_ntt->data[i0], accumulator);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_20(accumulator),
                                result);
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
    const Eurydice_arr_3d0 *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re->data[i0], scratch);
    libcrux_iot_ml_kem_vector_portable_compress_1_4e(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_1_4e(
        scratch, Eurydice_slice_subslice_mut_7e(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                                     .start = (size_t)2U * i0,
                                     .end = (size_t)2U * i0 + (size_t)2U})));
  }
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
    const arr_f2 *secret_key, const Eurydice_arr_00 *ciphertext,
    Eurydice_mut_borrow_slice_u8 decrypted, Eurydice_arr_e2 *scratch,
    Eurydice_arr_c3 *accumulator) {
  arr_f2 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_b7_08(&lvalue);
  }
  arr_f2 u_as_ntt = arr_struct;
  deserialize_then_decompress_u_e9(ciphertext,
                                   array_to_slice_mut_340(&u_as_ntt), scratch);
  Eurydice_arr_3d0 v = ZERO_64_a7();
  deserialize_then_decompress_ring_element_v_c5(
      Eurydice_array_to_subslice_from_shared_8c4(ciphertext, (size_t)1408U),
      &v);
  Eurydice_arr_3d0 message = ZERO_64_a7();
  compute_message_e1(&v, secret_key, &u_as_ntt, &message, scratch, accumulator);
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
static KRML_MUSTINLINE void decrypt_08(Eurydice_borrow_slice_u8 secret_key,
                                       const Eurydice_arr_00 *ciphertext,
                                       Eurydice_mut_borrow_slice_u8 decrypted,
                                       Eurydice_arr_e2 *scratch,
                                       Eurydice_arr_c3 *accumulator) {
  arr_f2 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_a5_08(&lvalue);
  }
  arr_f2 secret_as_ntt = arr_struct;
  deserialize_vector_e1(secret_key, array_to_slice_mut_340(&secret_as_ntt));
  arr_f2 secret_key_unpacked = secret_as_ntt;
  decrypt_unpacked_08(&secret_key_unpacked, ciphertext, decrypted, scratch,
                      accumulator);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_9e(Eurydice_borrow_slice_u8 input,
                                   Eurydice_mut_borrow_slice_u8 out) {
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
static KRML_MUSTINLINE void PRF_07_9e(Eurydice_borrow_slice_u8 input,
                                      Eurydice_mut_borrow_slice_u8 out) {
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
static Eurydice_arr_3d0 call_mut_9b_1b1(void **_) { return ZERO_64_a7(); }

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
Eurydice_arr_600 libcrux_iot_ml_kem_ind_cca_decapsulate_1b1(
    const Eurydice_arr_17 *private_key, const Eurydice_arr_00 *ciphertext) {
  Eurydice_dst_ref_shared_uint8_t_size_t_x4 uu____0 =
      libcrux_iot_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice_shared_a6(private_key));
  Eurydice_borrow_slice_u8 ind_cpa_secret_key = uu____0.fst;
  Eurydice_borrow_slice_u8 ind_cpa_public_key = uu____0.snd;
  Eurydice_borrow_slice_u8 ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_borrow_slice_u8 implicit_rejection_value = uu____0.f3;
  Eurydice_arr_600 decrypted;
  uint8_t repeat_expression0[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(decrypted.data, repeat_expression0, (size_t)32U * sizeof(uint8_t));
  Eurydice_arr_e2 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  Eurydice_arr_c3 accumulator;
  int32_t repeat_expression1[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  }
  memcpy(accumulator.data, repeat_expression1, (size_t)256U * sizeof(int32_t));
  decrypt_08(ind_cpa_secret_key, ciphertext,
             Eurydice_array_to_slice_mut_6e(&decrypted), &scratch,
             &accumulator);
  Eurydice_arr_06 to_hash0 = libcrux_iot_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice_shared_6e(&decrypted));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from_mut_8c(
          &to_hash0, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE),
      libcrux_secrets_int_classify_public_classify_ref_9b_90(
          ind_cpa_public_key_hash),
      uint8_t);
  Eurydice_arr_06 hashed;
  uint8_t repeat_expression2[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression2, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_d8(&to_hash0),
      Eurydice_array_to_slice_mut_d8(&hashed));
  Eurydice_dst_ref_shared_uint8_t_size_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_d8(&hashed),
      LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_dst_ref_shared_uint8_t_size_t_x2);
  Eurydice_borrow_slice_u8 shared_secret = uu____1.fst;
  Eurydice_borrow_slice_u8 pseudorandomness = uu____1.snd;
  Eurydice_arr_e7 to_hash =
      libcrux_iot_ml_kem_utils_into_padded_array_7f(implicit_rejection_value);
  Eurydice_mut_borrow_slice_u8 uu____2 =
      Eurydice_array_to_subslice_from_mut_8c2(
          &to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_00 lvalue0 =
      libcrux_secrets_int_public_integers_classify_27_b7(ciphertext[0U]);
  Eurydice_slice_copy(
      uu____2,
      core_array___Array_T__N___as_slice((size_t)1568U, &lvalue0, uint8_t,
                                         Eurydice_borrow_slice_u8),
      uint8_t);
  Eurydice_arr_600 implicit_rejection_shared_secret;
  uint8_t repeat_expression3[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression3[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(implicit_rejection_shared_secret.data, repeat_expression3,
         (size_t)32U * sizeof(uint8_t));
  PRF_07_9e(Eurydice_array_to_slice_shared_8e(&to_hash),
            Eurydice_array_to_slice_mut_6e(&implicit_rejection_shared_secret));
  Eurydice_arr_00 expected_ciphertext = {.data = {0U}};
  arr_f2 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_9b_1b1(&lvalue);
  }
  arr_f2 r_as_ntt = arr_struct;
  Eurydice_arr_3d0 error_2 = ZERO_64_a7();
  arr_f2 cache;
  Eurydice_arr_3d0 repeat_expression4[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression4[i] = ZERO_64_a7();
  }
  memcpy(cache.data, repeat_expression4, (size_t)4U * sizeof(Eurydice_arr_3d0));
  Eurydice_arr_3d0 matrix_entry = ZERO_64_a7();
  encrypt_5a1(ind_cpa_public_key, &decrypted, pseudorandomness,
              Eurydice_array_to_slice_mut_4e(&expected_ciphertext),
              &matrix_entry, array_to_slice_mut_340(&r_as_ntt), &error_2,
              &scratch, array_to_slice_mut_340(&cache), &accumulator);
  Eurydice_arr_600 implicit_rejection_shared_secret_kdf;
  uint8_t repeat_expression5[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression5[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(implicit_rejection_shared_secret_kdf.data, repeat_expression5,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_8a(
      Eurydice_array_to_slice_shared_6e(&implicit_rejection_shared_secret),
      Eurydice_array_to_slice_mut_6e(&implicit_rejection_shared_secret_kdf));
  Eurydice_arr_600 shared_secret_kdf;
  uint8_t repeat_expression6[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression6[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret_kdf.data, repeat_expression6,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_8a(shared_secret, Eurydice_array_to_slice_mut_6e(&shared_secret_kdf));
  Eurydice_arr_600 shared_secret0;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret0.data, repeat_expression, (size_t)32U * sizeof(uint8_t));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_00 lvalue1 =
      libcrux_secrets_int_public_integers_classify_27_b7(ciphertext[0U]);
  Eurydice_borrow_slice_u8 uu____3 = core_array___Array_T__N___as_slice(
      (size_t)1568U, &lvalue1, uint8_t, Eurydice_borrow_slice_u8);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_00 lvalue =
      libcrux_secrets_int_public_integers_classify_27_b7(expected_ciphertext);
  Eurydice_borrow_slice_u8 uu____4 = core_array___Array_T__N___as_slice(
      (size_t)1568U, &lvalue, uint8_t, Eurydice_borrow_slice_u8);
  libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      uu____3, uu____4, Eurydice_array_to_slice_shared_6e(&shared_secret_kdf),
      Eurydice_array_to_slice_shared_6e(&implicit_rejection_shared_secret_kdf),
      Eurydice_array_to_slice_mut_6e(&shared_secret0));
  return shared_secret0;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $3size_t
*/
typedef struct arr_21_s {
  Eurydice_arr_3d0 data[3U];
} arr_21;

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
static Eurydice_arr_3d0 call_mut_42_64(void **_) { return ZERO_64_a7(); }

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
    Eurydice_borrow_slice_u8 public_key,
    Eurydice_dst_ref_mut_64 deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 ring_element = Eurydice_slice_subslice_shared_7e(
        public_key,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}));
    deserialize_to_reduced_ring_element_a7(
        libcrux_secrets_int_classify_public_classify_ref_9b_90(ring_element),
        &Eurydice_slice_index_mut(deserialized_pk, i0, Eurydice_arr_3d0));
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 3
*/
static Eurydice_dst_ref_mut_64 array_to_slice_mut_341(arr_21 *a) {
  Eurydice_dst_ref_mut_64 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 3
*/
static Eurydice_dst_ref_shared_64 array_to_slice_shared_341(const arr_21 *a) {
  Eurydice_dst_ref_shared_64 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
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
    const arr_21 *key, Eurydice_mut_borrow_slice_u8 out,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(array_to_slice_shared_341(key), Eurydice_arr_3d0);
       i++) {
    size_t i0 = i;
    Eurydice_arr_3d0 re = key->data[i0];
    serialize_uncompressed_ring_element_a7(
        &re, scratch,
        Eurydice_slice_subslice_mut_7e(
            out,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT})));
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
    const arr_21 *t_as_ntt, Eurydice_borrow_slice_u8 seed_for_a,
    Eurydice_mut_borrow_slice_u8 serialized, Eurydice_arr_e2 *scratch) {
  /* original Rust expression is not an lvalue in C */
  Eurydice_mut_borrow_slice_u8 lvalue = Eurydice_slice_subslice_mut_7e(
      serialized,
      (KRML_CLITERAL(core_ops_range_Range_08){
          .start = (size_t)0U,
          .end = libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)3U)}));
  serialize_vector_60(
      t_as_ntt,
      libcrux_secrets_int_classify_public_classify_ref_mut_a1_47(&lvalue)[0U],
      scratch);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_from_mut_6b(
          serialized,
          libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)3U)),
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
bool libcrux_iot_ml_kem_ind_cca_validate_public_key_64(
    const Eurydice_arr_74 *public_key) {
  arr_21 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_42_64(&lvalue);
  }
  arr_21 deserialized_pk = arr_struct;
  Eurydice_borrow_slice_u8 uu____0 = Eurydice_array_to_subslice_to_shared_6e0(
      public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U));
  deserialize_ring_elements_reduced_60(
      uu____0, array_to_slice_mut_341(&deserialized_pk));
  Eurydice_arr_74 public_key_serialized = {.data = {0U}};
  Eurydice_arr_e2 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  const arr_21 *uu____1 = &deserialized_pk;
  Eurydice_borrow_slice_u8 uu____2 = Eurydice_array_to_subslice_from_shared_8c3(
      public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U));
  serialize_public_key_mut_64(
      uu____1, uu____2, Eurydice_array_to_slice_mut_45(&public_key_serialized),
      &scratch);
  return Eurydice_array_eq((size_t)1184U, public_key, &public_key_serialized,
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
    const Eurydice_arr_ea *private_key) {
  Eurydice_arr_600 t;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(t.data, repeat_expression, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      Eurydice_array_to_subslice_shared_369(
          private_key, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = (size_t)384U * (size_t)3U,
                           .end = (size_t)768U * (size_t)3U + (size_t)32U})),
      Eurydice_array_to_slice_mut_6e(&t));
  Eurydice_borrow_slice_u8 expected =
      libcrux_secrets_int_classify_public_declassify_ref_7f_90(
          Eurydice_array_to_subslice_shared_369(
              private_key,
              (KRML_CLITERAL(core_ops_range_Range_08){
                  .start = (size_t)768U * (size_t)3U + (size_t)32U,
                  .end = (size_t)768U * (size_t)3U + (size_t)64U})));
  /* original Rust expression is not an lvalue in C */
  Eurydice_borrow_slice_u8 lvalue =
      libcrux_secrets_int_classify_public_declassify_ref_7f_90(
          core_array___Array_T__N___as_slice((size_t)32U, &t, uint8_t,
                                             Eurydice_borrow_slice_u8));
  return Eurydice_slice_eq_shared(&lvalue, &expected, uint8_t, bool);
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
    const Eurydice_arr_ea *private_key, const Eurydice_arr_2c *_ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_39(private_key);
}

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
static KRML_MUSTINLINE arr_21 default_1e_60(void) {
  arr_21 lit;
  Eurydice_arr_3d0 repeat_expression[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(lit.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_3d0));
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $9size_t
*/
typedef struct arr_85_s {
  Eurydice_arr_3d0 data[9U];
} arr_85;

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $3size_t
- $9size_t
*/
typedef struct IndCpaPublicKeyUnpacked_12_s {
  arr_21 t_as_ntt;
  Eurydice_arr_600 seed_for_A;
  arr_85 A;
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
  arr_21 uu____0;
  Eurydice_arr_3d0 repeat_expression0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression0[i] = ZERO_64_a7();
  }
  memcpy(uu____0.data, repeat_expression0,
         (size_t)3U * sizeof(Eurydice_arr_3d0));
  Eurydice_arr_600 uu____1 = {.data = {0U}};
  IndCpaPublicKeyUnpacked_12 lit;
  lit.t_as_ntt = uu____0;
  lit.seed_for_A = uu____1;
  Eurydice_arr_3d0 repeat_expression[9U];
  for (size_t i = (size_t)0U; i < (size_t)9U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(lit.A.data, repeat_expression, (size_t)9U * sizeof(Eurydice_arr_3d0));
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
    Eurydice_borrow_slice_u8 key_generation_seed,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_3e seed;
  uint8_t repeat_expression[33U];
  for (size_t i = (size_t)0U; i < (size_t)33U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(seed.data, repeat_expression, (size_t)33U * sizeof(uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_362(
          &seed,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE})),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      libcrux_secrets_int_public_integers_classify_27_90((uint8_t)(size_t)3U);
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_610(&seed), out);
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 9
*/
static Eurydice_dst_ref_mut_64 array_to_slice_mut_342(arr_85 *a) {
  Eurydice_dst_ref_mut_64 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)9U;
  return lit;
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
    Eurydice_dst_ref_shared_ea randomness,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                  .ptr = sampled_coefficients.ptr,
                  .meta = sampled_coefficients.meta}),
              i1, size_t) <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_b0 *randomness_i =
            &Eurydice_slice_index_shared(randomness, i1, Eurydice_arr_b0);
        Eurydice_arr_a0 *out_i =
            &Eurydice_slice_index_mut(out, i1, Eurydice_arr_a0);
        size_t sampled_coefficients_i = Eurydice_slice_index_shared(
            (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                .ptr = sampled_coefficients.ptr,
                .meta = sampled_coefficients.meta}),
            i1, size_t);
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_363(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_08){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_85(
                out_i, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        size_t uu____0 = i1;
        Eurydice_slice_index_mut(sampled_coefficients, uu____0, size_t) =
            Eurydice_slice_index_shared(
                (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                    .ptr = sampled_coefficients.ptr,
                    .meta = sampled_coefficients.meta}),
                uu____0, size_t) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index_shared((KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                                        .ptr = sampled_coefficients.ptr,
                                        .meta = sampled_coefficients.meta}),
                                    i0, size_t) >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index_mut(sampled_coefficients, i0, size_t) =
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
- K= 3
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_640(
    Eurydice_dst_ref_shared_36 randomness,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                  .ptr = sampled_coefficients.ptr,
                  .meta = sampled_coefficients.meta}),
              i1, size_t) <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_27 *randomness_i =
            &Eurydice_slice_index_shared(randomness, i1, Eurydice_arr_27);
        Eurydice_arr_a0 *out_i =
            &Eurydice_slice_index_mut(out, i1, Eurydice_arr_a0);
        size_t sampled_coefficients_i = Eurydice_slice_index_shared(
            (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                .ptr = sampled_coefficients.ptr,
                .meta = sampled_coefficients.meta}),
            i1, size_t);
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_364(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_08){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_85(
                out_i, (KRML_CLITERAL(core_ops_range_Range_08){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        size_t uu____0 = i1;
        Eurydice_slice_index_mut(sampled_coefficients, uu____0, size_t) =
            Eurydice_slice_index_shared(
                (KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                    .ptr = sampled_coefficients.ptr,
                    .meta = sampled_coefficients.meta}),
                uu____0, size_t) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index_shared((KRML_CLITERAL(Eurydice_dst_ref_shared_06){
                                        .ptr = sampled_coefficients.ptr,
                                        .meta = sampled_coefficients.meta}),
                                    i0, size_t) >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index_mut(sampled_coefficients, i0, size_t) =
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
- K= 3
*/
static KRML_MUSTINLINE void sample_from_xof_c91(
    Eurydice_dst_ref_shared_60 seeds,
    Eurydice_dst_ref_mut_06 sampled_coefficients, Eurydice_dst_ref_mut_1d out) {
  Eurydice_arr_5e xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  Eurydice_arr_35 randomness = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_d6 randomness_blocksize = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state, Eurydice_array_to_slice_mut_e91(&randomness));
  bool done = sample_from_uniform_distribution_next_64(
      Eurydice_array_to_slice_shared_e91(&randomness), sampled_coefficients,
      out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice_mut_e71(&randomness_blocksize));
      done = sample_from_uniform_distribution_next_640(
          Eurydice_array_to_slice_shared_e71(&randomness_blocksize),
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
static KRML_MUSTINLINE void sample_matrix_A_c90(
    Eurydice_dst_ref_mut_64 A_transpose, const Eurydice_arr_48 *seed,
    bool transpose) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    Eurydice_arr_84 seeds;
    Eurydice_arr_48 repeat_expression[3U];
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      repeat_expression[i] = seed[0U];
    }
    memcpy(seeds.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_48));
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      seeds.data[j].data[32U] = (uint8_t)i1;
      seeds.data[j].data[33U] = (uint8_t)j;
    }
    Eurydice_arr_c8 sampled_coefficients = {.data = {0U}};
    Eurydice_arr_d4 out = {
        .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
    sample_from_xof_c91(Eurydice_array_to_slice_shared_c71(&seeds),
                        Eurydice_array_to_slice_mut_92(&sampled_coefficients),
                        Eurydice_array_to_slice_mut_301(&out));
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(Eurydice_array_to_slice_shared_300(&out),
                                Eurydice_arr_a0);
         i++) {
      size_t j = i;
      Eurydice_arr_a0 sample = out.data[j];
      if (transpose) {
        Eurydice_borrow_slice_i16 uu____0 =
            libcrux_secrets_int_classify_public_classify_ref_9b_39(
                Eurydice_array_to_subslice_to_shared_11(&sample, (size_t)256U));
        from_i16_array_64_a7(
            uu____0, &Eurydice_slice_index_mut(A_transpose, j * (size_t)3U + i1,
                                               Eurydice_arr_3d0));
      } else {
        Eurydice_borrow_slice_i16 uu____1 =
            libcrux_secrets_int_classify_public_classify_ref_9b_39(
                Eurydice_array_to_subslice_to_shared_11(&sample, (size_t)256U));
        from_i16_array_64_a7(
            uu____1, &Eurydice_slice_index_mut(A_transpose, i1 * (size_t)3U + j,
                                               Eurydice_arr_3d0));
      }
    }
  }
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
    Eurydice_dst_ref_mut_64 re_as_ntt, const Eurydice_arr_3e *prf_input,
    uint8_t domain_separator, Eurydice_arr_e2 *scratch) {
  Eurydice_arr_46 prf_inputs;
  Eurydice_arr_3e repeat_expression0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression0[i] =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e);
  }
  memcpy(prf_inputs.data, repeat_expression0,
         (size_t)3U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_e0(&prf_inputs, domain_separator);
  Eurydice_arr_cc prf_outputs;
  uint8_t repeat_expression1[384U];
  for (size_t i = (size_t)0U; i < (size_t)384U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_outputs.data, repeat_expression1, (size_t)384U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      Eurydice_array_to_slice_shared_611(&prf_inputs),
      Eurydice_array_to_slice_mut_fe(&prf_outputs), (size_t)128U);
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    Eurydice_borrow_slice_u8 randomness = Eurydice_array_to_subslice_shared_361(
        &prf_outputs, (KRML_CLITERAL(core_ops_range_Range_08){
                          .start = i1 * (size_t)128U,
                          .end = (i1 + (size_t)1U) * (size_t)128U}));
    Eurydice_arr_c1 sample_buffer;
    int16_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] =
          libcrux_secrets_int_public_integers_classify_27_39((int16_t)0);
    }
    memcpy(sample_buffer.data, repeat_expression,
           (size_t)256U * sizeof(int16_t));
    sample_from_binomial_distribution_0b(randomness, &sample_buffer);
    from_i16_array_64_a7(
        Eurydice_array_to_slice_shared_1a(&sample_buffer),
        &Eurydice_slice_index_mut(re_as_ntt, i1, Eurydice_arr_3d0));
    ntt_binomially_sampled_ring_element_a7(
        &Eurydice_slice_index_mut(re_as_ntt, i1, Eurydice_arr_3d0), scratch);
  }
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
static Eurydice_arr_3d0 call_mut_58_160(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.entry
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static const Eurydice_arr_3d0 *entry_60(Eurydice_dst_ref_shared_64 matrix,
                                        size_t i, size_t j) {
  return &Eurydice_slice_index_shared(matrix, i * (size_t)3U + j,
                                      Eurydice_arr_3d0);
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
    arr_21 *t_as_ntt, Eurydice_dst_ref_shared_64 matrix_A,
    const arr_21 *s_as_ntt, const arr_21 *error_as_ntt, arr_21 *s_cache,
    Eurydice_arr_c3 *accumulator) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t j = i;
    accumulating_ntt_multiply_fill_cache_64_a7(
        entry_60(matrix_A, (size_t)0U, j), &s_as_ntt->data[j], accumulator,
        &s_cache->data[j]);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_20(accumulator),
                                t_as_ntt->data);
  add_standard_error_reduce_64_a7(t_as_ntt->data, error_as_ntt->data);
  for (size_t i0 = (size_t)1U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    int32_t uu____0 =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
    Eurydice_arr_c3 lit;
    int32_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] = uu____0;
    }
    memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
    accumulator[0U] = lit;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      accumulating_ntt_multiply_use_cache_64_a7(entry_60(matrix_A, i1, j),
                                                &s_as_ntt->data[j], accumulator,
                                                &s_cache->data[j]);
    }
    reducing_from_i32_array_64_a7(
        Eurydice_array_to_slice_shared_20(accumulator), &t_as_ntt->data[i1]);
    add_standard_error_reduce_64_a7(&t_as_ntt->data[i1],
                                    &error_as_ntt->data[i1]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 9
*/
static Eurydice_dst_ref_shared_64 array_to_slice_shared_342(const arr_85 *a) {
  Eurydice_dst_ref_shared_64 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)9U;
  return lit;
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
    Eurydice_borrow_slice_u8 key_generation_seed, arr_21 *private_key,
    IndCpaPublicKeyUnpacked_12 *public_key, Eurydice_arr_3d0 *scratch,
    arr_21 *s_cache, Eurydice_arr_c3 *accumulator) {
  Eurydice_arr_06 hashed;
  uint8_t repeat_expression[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression, (size_t)64U * sizeof(uint8_t));
  cpa_keygen_seed_cc_f9(key_generation_seed,
                        Eurydice_array_to_slice_mut_d8(&hashed));
  Eurydice_dst_ref_shared_uint8_t_size_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_d8(&hashed), (size_t)32U, uint8_t,
      Eurydice_dst_ref_shared_uint8_t_size_t_x2);
  Eurydice_borrow_slice_u8 seed_for_A = uu____0.fst;
  Eurydice_borrow_slice_u8 seed_for_secret_and_error = uu____0.snd;
  Eurydice_dst_ref_mut_64 uu____1 = array_to_slice_mut_342(&public_key->A);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue0 =
      libcrux_secrets_int_public_integers_declassify_d8_2c(
          libcrux_iot_ml_kem_utils_into_padded_array_b6(seed_for_A));
  sample_matrix_A_c90(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_iot_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator = sample_vector_cbd_then_ntt_140(
      array_to_slice_mut_341(private_key), &prf_input, 0U, scratch->data);
  arr_21 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_58_160(&lvalue);
  }
  arr_21 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_140(array_to_slice_mut_341(&error_as_ntt),
                                 &prf_input, domain_separator, scratch->data);
  compute_As_plus_e_60(&public_key->t_as_ntt,
                       array_to_slice_shared_342(&public_key->A), private_key,
                       &error_as_ntt, s_cache, accumulator);
  Eurydice_mut_borrow_slice_u8 uu____2 =
      Eurydice_array_to_slice_mut_6e(&public_key->seed_for_A);
  Eurydice_slice_copy(
      uu____2,
      libcrux_secrets_int_classify_public_declassify_ref_7f_90(seed_for_A),
      uint8_t);
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
    const IndCpaPublicKeyUnpacked_12 *public_key, const arr_21 *private_key,
    Eurydice_mut_borrow_slice_u8 serialized_private_key,
    Eurydice_mut_borrow_slice_u8 serialized_public_key,
    Eurydice_arr_e2 *scratch) {
  serialize_public_key_mut_64(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice_shared_6e(&public_key->seed_for_A),
      serialized_public_key, scratch);
  serialize_vector_60(private_key, serialized_private_key, scratch);
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
    Eurydice_borrow_slice_u8 key_generation_seed,
    Eurydice_mut_borrow_slice_u8 serialized_ind_cpa_private_key,
    Eurydice_mut_borrow_slice_u8 serialized_public_key,
    Eurydice_arr_3d0 *scratch, arr_21 *s_cache, Eurydice_arr_c3 *accumulator) {
  arr_21 private_key = default_1e_60();
  IndCpaPublicKeyUnpacked_12 public_key = default_1f_64();
  generate_keypair_unpacked_160(key_generation_seed, &private_key, &public_key,
                                scratch, s_cache, accumulator);
  serialize_unpacked_secret_key_7c(&public_key, &private_key,
                                   serialized_ind_cpa_private_key,
                                   serialized_public_key, scratch->data);
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
    Eurydice_borrow_slice_u8 private_key, Eurydice_borrow_slice_u8 public_key,
    Eurydice_borrow_slice_u8 implicit_rejection_value,
    Eurydice_arr_ea *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_ea *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_366(
          uu____0,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = uu____1,
              .end = uu____2 + Eurydice_slice_len(private_key, uint8_t)})),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_ea *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_mut_borrow_slice_u8 uu____6 = Eurydice_array_to_subslice_mut_366(
      uu____3, (KRML_CLITERAL(core_ops_range_Range_08){
                   .start = uu____4,
                   .end = uu____5 + Eurydice_slice_len(public_key, uint8_t)}));
  Eurydice_slice_copy(
      uu____6,
      libcrux_secrets_int_classify_public_classify_ref_9b_90(public_key),
      uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(public_key),
      Eurydice_array_to_subslice_mut_366(
          serialized,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = pointer,
              .end = pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE})));
  pointer = pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_ea *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_366(
          uu____7,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = uu____8,
              .end = uu____9 +
                     Eurydice_slice_len(implicit_rejection_value, uint8_t)})),
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
libcrux_iot_ml_kem_types_MlKemKeyPair_5f
libcrux_iot_ml_kem_ind_cca_generate_keypair_b70(
    const Eurydice_arr_06 *randomness) {
  Eurydice_borrow_slice_u8 ind_cpa_keypair_randomness =
      Eurydice_array_to_subslice_shared_366(
          randomness,
          (KRML_CLITERAL(core_ops_range_Range_08){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}));
  Eurydice_borrow_slice_u8 implicit_rejection_value =
      Eurydice_array_to_subslice_from_shared_8c0(
          randomness,
          LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE);
  Eurydice_arr_74 public_key = {.data = {0U}};
  Eurydice_arr_ea secret_key_serialized;
  uint8_t repeat_expression0[2400U];
  for (size_t i = (size_t)0U; i < (size_t)2400U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(secret_key_serialized.data, repeat_expression0,
         (size_t)2400U * sizeof(uint8_t));
  Eurydice_arr_60 ind_cpa_private_key;
  uint8_t repeat_expression1[1152U];
  for (size_t i = (size_t)0U; i < (size_t)1152U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(ind_cpa_private_key.data, repeat_expression1,
         (size_t)1152U * sizeof(uint8_t));
  Eurydice_arr_3d0 scratch = ZERO_64_a7();
  Eurydice_arr_c3 accumulator;
  int32_t repeat_expression2[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  }
  memcpy(accumulator.data, repeat_expression2, (size_t)256U * sizeof(int32_t));
  arr_21 s_cache;
  Eurydice_arr_3d0 repeat_expression[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(s_cache.data, repeat_expression,
         (size_t)3U * sizeof(Eurydice_arr_3d0));
  generate_keypair_640(ind_cpa_keypair_randomness,
                       Eurydice_array_to_slice_mut_06(&ind_cpa_private_key),
                       Eurydice_array_to_slice_mut_45(&public_key), &scratch,
                       &s_cache, &accumulator);
  serialize_kem_secret_key_mut_39(
      Eurydice_array_to_slice_shared_06(&ind_cpa_private_key),
      Eurydice_array_to_slice_shared_45(&public_key), implicit_rejection_value,
      &secret_key_serialized);
  Eurydice_arr_ea private_key =
      libcrux_iot_ml_kem_types_from_56_28(secret_key_serialized);
  return libcrux_iot_ml_kem_types_from_d9_74(
      private_key, libcrux_iot_ml_kem_types_from_18_d0(public_key));
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
static KRML_MUSTINLINE void entropy_preprocess_cc_f9(
    Eurydice_borrow_slice_u8 randomness, Eurydice_mut_borrow_slice_u8 out) {
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
static Eurydice_arr_3d0 call_mut_92_350(void **_) { return ZERO_64_a7(); }

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
static Eurydice_arr_3d0 call_mut_6f_920(void **_) { return ZERO_64_a7(); }

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
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_140(
    const Eurydice_arr_3e *prf_input, uint8_t domain_separator,
    Eurydice_dst_ref_mut_64 error_1, Eurydice_arr_c1 *sample_buffer) {
  Eurydice_arr_46 prf_inputs;
  Eurydice_arr_3e repeat_expression0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression0[i] =
        core_array__core__clone__Clone_for__Array_T__N___clone(
            (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e);
  }
  memcpy(prf_inputs.data, repeat_expression0,
         (size_t)3U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_e0(&prf_inputs, domain_separator);
  Eurydice_arr_cc prf_outputs;
  uint8_t repeat_expression[384U];
  for (size_t i = (size_t)0U; i < (size_t)384U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_outputs.data, repeat_expression, (size_t)384U * sizeof(uint8_t));
  Eurydice_dst_ref_shared_d2 uu____0 = core_array___Array_T__N___as_slice(
      (size_t)3U, &prf_inputs, Eurydice_arr_3e, Eurydice_dst_ref_shared_d2);
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      uu____0, Eurydice_array_to_slice_mut_fe(&prf_outputs), (size_t)128U);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 randomness = Eurydice_array_to_subslice_shared_361(
        &prf_outputs, (KRML_CLITERAL(core_ops_range_Range_08){
                          .start = i0 * (size_t)128U,
                          .end = (i0 + (size_t)1U) * (size_t)128U}));
    sample_from_binomial_distribution_0b(randomness, sample_buffer);
    from_i16_array_64_a7(
        Eurydice_array_to_slice_shared_1a(sample_buffer),
        &Eurydice_slice_index_mut(error_1, i0, Eurydice_arr_3d0));
  }
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
static Eurydice_arr_3d0 call_mut_33_920(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_60(Eurydice_arr_3d0 *re,
                                                     Eurydice_arr_e2 *scratch) {
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
    Eurydice_arr_3d0 *matrix_entry, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_shared_64 r_as_ntt, Eurydice_dst_ref_shared_64 error_1,
    Eurydice_dst_ref_mut_64 result, Eurydice_arr_e2 *scratch,
    Eurydice_dst_ref_mut_64 cache, Eurydice_arr_c3 *accumulator) {
  int32_t uu____0 =
      libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  Eurydice_arr_c3 lit0;
  int32_t repeat_expression0[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression0[i] = uu____0;
  }
  memcpy(lit0.data, repeat_expression0, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit0;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t j = i;
    sample_matrix_entry_36(matrix_entry, seed, (size_t)0U, j);
    accumulating_ntt_multiply_fill_cache_64_a7(
        matrix_entry,
        &Eurydice_slice_index_shared(r_as_ntt, j, Eurydice_arr_3d0),
        accumulator, &Eurydice_slice_index_mut(cache, j, Eurydice_arr_3d0));
  }
  reducing_from_i32_array_64_a7(
      Eurydice_array_to_slice_shared_20(accumulator),
      &Eurydice_slice_index_mut(result, (size_t)0U, Eurydice_arr_3d0));
  invert_ntt_montgomery_60(
      &Eurydice_slice_index_mut(result, (size_t)0U, Eurydice_arr_3d0), scratch);
  add_error_reduce_64_a7(
      &Eurydice_slice_index_mut(result, (size_t)0U, Eurydice_arr_3d0),
      &Eurydice_slice_index_shared(error_1, (size_t)0U, Eurydice_arr_3d0));
  for (size_t i0 = (size_t)1U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    int32_t uu____1 =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
    Eurydice_arr_c3 lit;
    int32_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] = uu____1;
    }
    memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
    accumulator[0U] = lit;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      sample_matrix_entry_36(matrix_entry, seed, i1, j);
      accumulating_ntt_multiply_use_cache_64_a7(
          matrix_entry,
          &Eurydice_slice_index_shared(r_as_ntt, j, Eurydice_arr_3d0),
          accumulator,
          &Eurydice_slice_index_shared(
              (KRML_CLITERAL(Eurydice_dst_ref_shared_64){.ptr = cache.ptr,
                                                         .meta = cache.meta}),
              j, Eurydice_arr_3d0));
    }
    reducing_from_i32_array_64_a7(
        Eurydice_array_to_slice_shared_20(accumulator),
        &Eurydice_slice_index_mut(result, i1, Eurydice_arr_3d0));
    invert_ntt_montgomery_60(
        &Eurydice_slice_index_mut(result, i1, Eurydice_arr_3d0), scratch);
    add_error_reduce_64_a7(
        &Eurydice_slice_index_mut(result, i1, Eurydice_arr_3d0),
        &Eurydice_slice_index_shared(error_1, i1, Eurydice_arr_3d0));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_10 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_10_7b(
    const Eurydice_arr_3d0 *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re->data[i0], scratch);
    compress_4e_ef(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_10_4e(
        scratch, Eurydice_slice_subslice_mut_7e(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_08){
                                     .start = (size_t)20U * i0,
                                     .end = (size_t)20U * i0 + (size_t)20U})));
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
    const Eurydice_arr_3d0 *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_e2 *scratch) {
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
    arr_21 input, Eurydice_mut_borrow_slice_u8 out, Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U;
       i <
       Eurydice_slice_len(array_to_slice_shared_341(&input), Eurydice_arr_3d0);
       i++) {
    size_t i0 = i;
    Eurydice_arr_3d0 re = input.data[i0];
    compress_then_serialize_ring_element_u_c3(
        &re,
        Eurydice_slice_subslice_mut_7e(
            out, (KRML_CLITERAL(core_ops_range_Range_08){
                     .start = i0 * ((size_t)960U / (size_t)3U),
                     .end = (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U)})),
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
    Eurydice_borrow_slice_u8 randomness, Eurydice_arr_3d0 *matrix_entry,
    Eurydice_borrow_slice_u8 seed_for_a,
    Eurydice_mut_borrow_slice_u8 ciphertext, Eurydice_dst_ref_mut_64 r_as_ntt,
    Eurydice_arr_3d0 *error_2, Eurydice_arr_e2 *scratch,
    Eurydice_dst_ref_mut_64 cache, Eurydice_arr_c3 *accumulator) {
  Eurydice_arr_3e prf_input =
      libcrux_iot_ml_kem_utils_into_padded_array_c8(randomness);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_140(r_as_ntt, &prf_input, 0U, scratch);
  arr_21 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_6f_920(&lvalue);
  }
  arr_21 error_1 = arr_struct;
  Eurydice_arr_c1 sampling_buffer;
  int16_t repeat_expression0[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_39((int16_t)0);
  }
  memcpy(sampling_buffer.data, repeat_expression0,
         (size_t)256U * sizeof(int16_t));
  uint8_t domain_separator0 = sample_ring_element_cbd_140(
      &prf_input, domain_separator, array_to_slice_mut_341(&error_1),
      &sampling_buffer);
  prf_input.data[32U] =
      libcrux_secrets_int_public_integers_classify_27_90(domain_separator0);
  Eurydice_arr_d1 prf_output;
  uint8_t repeat_expression[128U];
  for (size_t i = (size_t)0U; i < (size_t)128U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_output.data, repeat_expression, (size_t)128U * sizeof(uint8_t));
  PRF_07_a6(Eurydice_array_to_slice_shared_610(&prf_input),
            Eurydice_array_to_slice_mut_18(&prf_output));
  sample_from_binomial_distribution_0b(
      Eurydice_array_to_slice_shared_18(&prf_output), &sampling_buffer);
  from_i16_array_64_a7(Eurydice_array_to_slice_shared_1a(&sampling_buffer),
                       error_2);
  arr_21 arr_struct0;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct0.data[i] = call_mut_33_920(&lvalue);
  }
  arr_21 u = arr_struct0;
  compute_vector_u_c90(matrix_entry, seed_for_a,
                       (KRML_CLITERAL(Eurydice_dst_ref_shared_64){
                           .ptr = r_as_ntt.ptr, .meta = r_as_ntt.meta}),
                       array_to_slice_shared_341(&error_1),
                       array_to_slice_mut_341(&u), scratch, cache, accumulator);
  compress_then_serialize_u_7c(u, ciphertext, scratch);
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
    Eurydice_borrow_slice_u8 public_key, Eurydice_arr_3d0 *t_as_ntt_entry,
    Eurydice_dst_ref_shared_64 r_as_ntt, const Eurydice_arr_3d0 *error_2,
    const Eurydice_arr_3d0 *message, Eurydice_arr_3d0 *result,
    Eurydice_arr_e2 *scratch, Eurydice_dst_ref_shared_64 cache,
    Eurydice_arr_c3 *accumulator) {
  int32_t uu____0 =
      libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  Eurydice_arr_c3 lit;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] = uu____0;
  }
  memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 ring_element = Eurydice_slice_subslice_shared_7e(
        public_key,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}));
    deserialize_to_reduced_ring_element_a7(
        libcrux_secrets_int_classify_public_classify_ref_9b_90(ring_element),
        t_as_ntt_entry);
    accumulating_ntt_multiply_use_cache_64_a7(
        t_as_ntt_entry,
        &Eurydice_slice_index_shared(r_as_ntt, i0, Eurydice_arr_3d0),
        accumulator, &Eurydice_slice_index_shared(cache, i0, Eurydice_arr_3d0));
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_20(accumulator),
                                result);
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
    Eurydice_arr_3d0 re, Eurydice_mut_borrow_slice_u8 out,
    Eurydice_arr_e2 *scratch) {
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
    Eurydice_borrow_slice_u8 public_key, Eurydice_arr_3d0 *t_as_ntt_entry,
    Eurydice_dst_ref_shared_64 r_as_ntt, const Eurydice_arr_3d0 *error_2,
    const Eurydice_arr_600 *message, Eurydice_mut_borrow_slice_u8 ciphertext,
    Eurydice_arr_e2 *scratch, Eurydice_dst_ref_shared_64 cache,
    Eurydice_arr_c3 *accumulator) {
  Eurydice_arr_3d0 message_as_ring_element = ZERO_64_a7();
  deserialize_then_decompress_message_a7(message, &message_as_ring_element);
  Eurydice_arr_3d0 v = ZERO_64_a7();
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
    Eurydice_borrow_slice_u8 public_key, const Eurydice_arr_600 *message,
    Eurydice_borrow_slice_u8 randomness,
    Eurydice_mut_borrow_slice_u8 ciphertext, Eurydice_arr_3d0 *matrix_entry,
    Eurydice_dst_ref_mut_64 r_as_ntt, Eurydice_arr_3d0 *error_2,
    Eurydice_arr_e2 *scratch, Eurydice_dst_ref_mut_64 cache,
    Eurydice_arr_c3 *accumulator) {
  encrypt_c1_920(
      randomness, matrix_entry,
      Eurydice_slice_subslice_from_shared_6b(public_key, (size_t)1152U),
      Eurydice_slice_subslice_mut_7e(
          ciphertext, (KRML_CLITERAL(core_ops_range_Range_08){
                          .start = (size_t)0U, .end = (size_t)960U})),
      r_as_ntt, error_2, scratch, cache, accumulator);
  encrypt_c2_6e(Eurydice_slice_subslice_to_shared_c6(public_key, (size_t)1152U),
                matrix_entry,
                (KRML_CLITERAL(Eurydice_dst_ref_shared_64){
                    .ptr = r_as_ntt.ptr, .meta = r_as_ntt.meta}),
                error_2, message,
                Eurydice_slice_subslice_from_mut_6b(ciphertext, (size_t)960U),
                scratch,
                (KRML_CLITERAL(Eurydice_dst_ref_shared_64){.ptr = cache.ptr,
                                                           .meta = cache.meta}),
                accumulator);
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
static KRML_MUSTINLINE void kdf_cc_39(Eurydice_borrow_slice_u8 shared_secret,
                                      Eurydice_mut_borrow_slice_u8 out) {
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
tuple_50 libcrux_iot_ml_kem_ind_cca_encapsulate_350(
    const Eurydice_arr_74 *public_key, const Eurydice_arr_600 *randomness) {
  Eurydice_arr_600 processed_randomness;
  uint8_t repeat_expression0[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(processed_randomness.data, repeat_expression0,
         (size_t)32U * sizeof(uint8_t));
  entropy_preprocess_cc_f9(
      Eurydice_array_to_slice_shared_6e(randomness),
      Eurydice_array_to_slice_mut_6e(&processed_randomness));
  Eurydice_arr_06 to_hash = libcrux_iot_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice_shared_6e(&processed_randomness));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_74 lvalue0 =
      libcrux_secrets_int_public_integers_classify_27_aa(public_key[0U]);
  Eurydice_borrow_slice_u8 uu____0 = core_array___Array_T__N___as_slice(
      (size_t)1184U, &lvalue0, uint8_t, Eurydice_borrow_slice_u8);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      uu____0, Eurydice_array_to_subslice_from_mut_8c(
                   &to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE));
  Eurydice_arr_06 hashed;
  uint8_t repeat_expression1[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression1, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_d8(&to_hash),
      Eurydice_array_to_slice_mut_d8(&hashed));
  Eurydice_dst_ref_shared_uint8_t_size_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_d8(&hashed),
      LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_dst_ref_shared_uint8_t_size_t_x2);
  Eurydice_borrow_slice_u8 shared_secret = uu____1.fst;
  Eurydice_borrow_slice_u8 pseudorandomness = uu____1.snd;
  Eurydice_arr_2c ciphertext = {.data = {0U}};
  arr_21 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_92_350(&lvalue);
  }
  arr_21 r_as_ntt = arr_struct;
  Eurydice_arr_3d0 error_2 = ZERO_64_a7();
  Eurydice_arr_e2 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  Eurydice_arr_c3 accumulator;
  int32_t repeat_expression2[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  }
  memcpy(accumulator.data, repeat_expression2, (size_t)256U * sizeof(int32_t));
  arr_21 cache;
  Eurydice_arr_3d0 repeat_expression3[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression3[i] = ZERO_64_a7();
  }
  memcpy(cache.data, repeat_expression3, (size_t)3U * sizeof(Eurydice_arr_3d0));
  Eurydice_arr_3d0 matrix_entry = ZERO_64_a7();
  const Eurydice_arr_74 *uu____2 =
      libcrux_iot_ml_kem_types_as_slice_63_d0(public_key);
  encrypt_5a0(Eurydice_array_to_slice_shared_45(uu____2), &processed_randomness,
              pseudorandomness, Eurydice_array_to_slice_mut_42(&ciphertext),
              &matrix_entry, array_to_slice_mut_341(&r_as_ntt), &error_2,
              &scratch, array_to_slice_mut_341(&cache), &accumulator);
  Eurydice_arr_2c ciphertext0 = libcrux_iot_ml_kem_types_from_9d_80(ciphertext);
  Eurydice_arr_600 shared_secret_array;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret_array.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_39(shared_secret,
            Eurydice_array_to_slice_mut_6e(&shared_secret_array));
  return (
      KRML_CLITERAL(tuple_50){.fst = ciphertext0, .snd = shared_secret_array});
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
static Eurydice_arr_3d0 call_mut_a5_4d(void **_) { return ZERO_64_a7(); }

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
    Eurydice_borrow_slice_u8 secret_key,
    Eurydice_dst_ref_mut_64 secret_as_ntt) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    deserialize_to_uncompressed_ring_element_a7(
        Eurydice_slice_subslice_shared_7e(
            secret_key,
            (KRML_CLITERAL(core_ops_range_Range_08){
                .start =
                    i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT})),
        &Eurydice_slice_index_mut(secret_as_ntt, i0, Eurydice_arr_3d0));
  }
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
static Eurydice_arr_3d0 call_mut_b7_4d(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_u_cf(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *output) {
  deserialize_then_decompress_10_a7(serialized, output);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_cf(Eurydice_arr_3d0 *re,
                                            Eurydice_arr_e2 *scratch) {
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
    const Eurydice_arr_2c *ciphertext, Eurydice_dst_ref_mut_64 u_as_ntt,
    Eurydice_arr_e2 *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice_shared_42(ciphertext),
                              uint8_t) /
               (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 u_bytes = Eurydice_array_to_subslice_shared_368(
        ciphertext,
        (KRML_CLITERAL(core_ops_range_Range_08){
            .start =
                i0 *
                (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                 (size_t)10U / (size_t)8U),
            .end =
                i0 *
                    (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                     (size_t)10U / (size_t)8U) +
                LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                    (size_t)10U / (size_t)8U}));
    deserialize_then_decompress_ring_element_u_cf(
        u_bytes, &Eurydice_slice_index_mut(u_as_ntt, i0, Eurydice_arr_3d0));
    ntt_vector_u_cf(&Eurydice_slice_index_mut(u_as_ntt, i0, Eurydice_arr_3d0),
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
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_3d0 *output) {
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
static KRML_MUSTINLINE void compute_message_60(const Eurydice_arr_3d0 *v,
                                               const arr_21 *secret_as_ntt,
                                               const arr_21 *u_as_ntt,
                                               Eurydice_arr_3d0 *result,
                                               Eurydice_arr_e2 *scratch,
                                               Eurydice_arr_c3 *accumulator) {
  int32_t uu____0 =
      libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  Eurydice_arr_c3 lit;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] = uu____0;
  }
  memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    accumulating_ntt_multiply_64_a7(&secret_as_ntt->data[i0],
                                    &u_as_ntt->data[i0], accumulator);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_20(accumulator),
                                result);
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
    const arr_21 *secret_key, const Eurydice_arr_2c *ciphertext,
    Eurydice_mut_borrow_slice_u8 decrypted, Eurydice_arr_e2 *scratch,
    Eurydice_arr_c3 *accumulator) {
  arr_21 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_b7_4d(&lvalue);
  }
  arr_21 u_as_ntt = arr_struct;
  deserialize_then_decompress_u_6e(ciphertext,
                                   array_to_slice_mut_341(&u_as_ntt), scratch);
  Eurydice_arr_3d0 v = ZERO_64_a7();
  deserialize_then_decompress_ring_element_v_64(
      Eurydice_array_to_subslice_from_shared_8c2(ciphertext, (size_t)960U), &v);
  Eurydice_arr_3d0 message = ZERO_64_a7();
  compute_message_60(&v, secret_key, &u_as_ntt, &message, scratch, accumulator);
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
static KRML_MUSTINLINE void decrypt_4d(Eurydice_borrow_slice_u8 secret_key,
                                       const Eurydice_arr_2c *ciphertext,
                                       Eurydice_mut_borrow_slice_u8 decrypted,
                                       Eurydice_arr_e2 *scratch,
                                       Eurydice_arr_c3 *accumulator) {
  arr_21 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_a5_4d(&lvalue);
  }
  arr_21 secret_as_ntt = arr_struct;
  deserialize_vector_60(secret_key, array_to_slice_mut_341(&secret_as_ntt));
  arr_21 secret_key_unpacked = secret_as_ntt;
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
static Eurydice_arr_3d0 call_mut_9b_1b0(void **_) { return ZERO_64_a7(); }

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
Eurydice_arr_600 libcrux_iot_ml_kem_ind_cca_decapsulate_1b0(
    const Eurydice_arr_ea *private_key, const Eurydice_arr_2c *ciphertext) {
  Eurydice_dst_ref_shared_uint8_t_size_t_x4 uu____0 =
      libcrux_iot_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice_shared_ec(private_key));
  Eurydice_borrow_slice_u8 ind_cpa_secret_key = uu____0.fst;
  Eurydice_borrow_slice_u8 ind_cpa_public_key = uu____0.snd;
  Eurydice_borrow_slice_u8 ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_borrow_slice_u8 implicit_rejection_value = uu____0.f3;
  Eurydice_arr_600 decrypted;
  uint8_t repeat_expression0[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(decrypted.data, repeat_expression0, (size_t)32U * sizeof(uint8_t));
  Eurydice_arr_e2 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  Eurydice_arr_c3 accumulator;
  int32_t repeat_expression1[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_a8((int32_t)0);
  }
  memcpy(accumulator.data, repeat_expression1, (size_t)256U * sizeof(int32_t));
  decrypt_4d(ind_cpa_secret_key, ciphertext,
             Eurydice_array_to_slice_mut_6e(&decrypted), &scratch,
             &accumulator);
  Eurydice_arr_06 to_hash0 = libcrux_iot_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice_shared_6e(&decrypted));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from_mut_8c(
          &to_hash0, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE),
      libcrux_secrets_int_classify_public_classify_ref_9b_90(
          ind_cpa_public_key_hash),
      uint8_t);
  Eurydice_arr_06 hashed;
  uint8_t repeat_expression2[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression2, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_d8(&to_hash0),
      Eurydice_array_to_slice_mut_d8(&hashed));
  Eurydice_dst_ref_shared_uint8_t_size_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_d8(&hashed),
      LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_dst_ref_shared_uint8_t_size_t_x2);
  Eurydice_borrow_slice_u8 shared_secret = uu____1.fst;
  Eurydice_borrow_slice_u8 pseudorandomness = uu____1.snd;
  Eurydice_arr_480 to_hash =
      libcrux_iot_ml_kem_utils_into_padded_array_15(implicit_rejection_value);
  Eurydice_mut_borrow_slice_u8 uu____2 =
      Eurydice_array_to_subslice_from_mut_8c1(
          &to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_2c lvalue0 =
      libcrux_secrets_int_public_integers_classify_27_33(ciphertext[0U]);
  Eurydice_slice_copy(
      uu____2,
      core_array___Array_T__N___as_slice((size_t)1088U, &lvalue0, uint8_t,
                                         Eurydice_borrow_slice_u8),
      uint8_t);
  Eurydice_arr_600 implicit_rejection_shared_secret;
  uint8_t repeat_expression3[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression3[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(implicit_rejection_shared_secret.data, repeat_expression3,
         (size_t)32U * sizeof(uint8_t));
  PRF_07_9e(Eurydice_array_to_slice_shared_74(&to_hash),
            Eurydice_array_to_slice_mut_6e(&implicit_rejection_shared_secret));
  Eurydice_arr_2c expected_ciphertext = {.data = {0U}};
  arr_21 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_9b_1b0(&lvalue);
  }
  arr_21 r_as_ntt = arr_struct;
  Eurydice_arr_3d0 error_2 = ZERO_64_a7();
  arr_21 cache;
  Eurydice_arr_3d0 repeat_expression4[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression4[i] = ZERO_64_a7();
  }
  memcpy(cache.data, repeat_expression4, (size_t)3U * sizeof(Eurydice_arr_3d0));
  Eurydice_arr_3d0 matrix_entry = ZERO_64_a7();
  encrypt_5a0(ind_cpa_public_key, &decrypted, pseudorandomness,
              Eurydice_array_to_slice_mut_42(&expected_ciphertext),
              &matrix_entry, array_to_slice_mut_341(&r_as_ntt), &error_2,
              &scratch, array_to_slice_mut_341(&cache), &accumulator);
  Eurydice_arr_600 implicit_rejection_shared_secret_kdf;
  uint8_t repeat_expression5[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression5[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(implicit_rejection_shared_secret_kdf.data, repeat_expression5,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_39(
      Eurydice_array_to_slice_shared_6e(&implicit_rejection_shared_secret),
      Eurydice_array_to_slice_mut_6e(&implicit_rejection_shared_secret_kdf));
  Eurydice_arr_600 shared_secret_kdf;
  uint8_t repeat_expression6[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression6[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret_kdf.data, repeat_expression6,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_39(shared_secret, Eurydice_array_to_slice_mut_6e(&shared_secret_kdf));
  Eurydice_arr_600 shared_secret0;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret0.data, repeat_expression, (size_t)32U * sizeof(uint8_t));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_2c lvalue1 =
      libcrux_secrets_int_public_integers_classify_27_33(ciphertext[0U]);
  Eurydice_borrow_slice_u8 uu____3 = core_array___Array_T__N___as_slice(
      (size_t)1088U, &lvalue1, uint8_t, Eurydice_borrow_slice_u8);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_2c lvalue =
      libcrux_secrets_int_public_integers_classify_27_33(expected_ciphertext);
  Eurydice_borrow_slice_u8 uu____4 = core_array___Array_T__N___as_slice(
      (size_t)1088U, &lvalue, uint8_t, Eurydice_borrow_slice_u8);
  libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      uu____3, uu____4, Eurydice_array_to_slice_shared_6e(&shared_secret_kdf),
      Eurydice_array_to_slice_shared_6e(&implicit_rejection_shared_secret_kdf),
      Eurydice_array_to_slice_mut_6e(&shared_secret0));
  return shared_secret0;
}
