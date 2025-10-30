/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 2381cbc416ef2ad0b561c362c500bc84f36b6785
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: 05bdc0e603c669df888620fb36bfe347e811d91e
 */

#ifndef libcrux_mlkem_iot_H
#define libcrux_mlkem_iot_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_sha3.h"

void libcrux_iot_ml_kem_hash_functions_portable_G(Eurydice_slice input,
                                                  Eurydice_slice output);

void libcrux_iot_ml_kem_hash_functions_portable_H(Eurydice_slice input,
                                                  Eurydice_slice output);

void libcrux_iot_ml_kem_hash_functions_portable_PRFxN(Eurydice_slice input,
                                                      Eurydice_slice outputs,
                                                      size_t out_len);

typedef struct libcrux_iot_ml_kem_hash_functions_portable_PortableHash_s {
  libcrux_iot_sha3_state_KeccakState shake128_state[4U];
} libcrux_iot_ml_kem_hash_functions_portable_PortableHash;

libcrux_iot_ml_kem_hash_functions_portable_PortableHash
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final(
    Eurydice_slice input);

void libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
    libcrux_iot_ml_kem_hash_functions_portable_PortableHash *st,
    Eurydice_slice outputs);

void libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
    libcrux_iot_ml_kem_hash_functions_portable_PortableHash *st,
    Eurydice_slice outputs);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_G_07(Eurydice_slice input,
                                                     Eurydice_slice output);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_H_07(Eurydice_slice input,
                                                     Eurydice_slice output);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(Eurydice_slice input,
                                                         Eurydice_slice outputs,
                                                         size_t out_len);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
libcrux_iot_ml_kem_hash_functions_portable_PortableHash
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
    Eurydice_slice input);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
    libcrux_iot_ml_kem_hash_functions_portable_PortableHash *self,
    Eurydice_slice output);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
    libcrux_iot_ml_kem_hash_functions_portable_PortableHash *self,
    Eurydice_slice output);

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR ((size_t)16U)

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS ((int16_t)3329)

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS \
  ((int16_t)1353)

typedef struct libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector_s {
  int16_t elements[16U];
} libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector;

libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
libcrux_iot_ml_kem_vector_portable_vector_type_zero(void);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
libcrux_iot_ml_kem_vector_portable_ZERO_4e(void);

void libcrux_iot_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_from_i16_array_4e(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (62209U)

#define LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (16U)

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
    int32_t value);

void libcrux_iot_ml_kem_vector_portable_vector_type_reducing_from_i32_array(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_reducing_from_i32_array_4e(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

void libcrux_iot_ml_kem_vector_portable_vector_type_to_i16_array(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *x,
    Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_to_i16_array_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *x,
    Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_vector_type_from_bytes(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_from_bytes_4e(
    Eurydice_slice array,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

void libcrux_iot_ml_kem_vector_portable_vector_type_to_bytes(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector x,
    Eurydice_slice bytes);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_to_bytes_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector x,
    Eurydice_slice bytes);

void libcrux_iot_ml_kem_vector_portable_arithmetic_add(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_add_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs);

void libcrux_iot_ml_kem_vector_portable_arithmetic_sub(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_sub_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs);

void libcrux_iot_ml_kem_vector_portable_arithmetic_negate(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_negate_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec);

void libcrux_iot_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_multiply_by_constant_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c);

void libcrux_iot_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c);

/**
 Note: This function is not secret independent
 Only use with public values.
*/
void libcrux_iot_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_cond_subtract_3329_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec);

#define LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int32_t)20159)

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT ((int32_t)26)

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_R \
  ((int32_t)1 << (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT)

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
int16_t libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
    int16_t value);

void libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec);

/**
 If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
 `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
 `x · y`, as follows:

    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`

 `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a
 representative `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod
 FIELD_MODULUS)`.
*/
int16_t
libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int16_t fe, int16_t fer);

void libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t c);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t r);

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
uint8_t
libcrux_iot_ml_kem_vector_portable_compress_compress_message_coefficient(
    uint16_t fe);

void libcrux_iot_ml_kem_vector_portable_compress_compress_1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_compress_1_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a);

uint32_t
libcrux_iot_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value);

int16_t
libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe);

void libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j);

void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_ntt_layer_1_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_ntt_layer_2_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta0, int16_t zeta1);

void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_ntt_layer_3_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta);

void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j);

void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_1_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_2_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta0, int16_t zeta1);

void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_3_step_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *b,
    int16_t zeta, size_t i, Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3);

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
void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *b,
    int16_t zeta, size_t i, Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_fill_cache(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_fill_cache_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *b, size_t i,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_use_cache(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_use_cache_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    Eurydice_slice out,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *cache);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_serialize_1(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_1_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_1(
    Eurydice_slice v,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

void libcrux_iot_ml_kem_vector_portable_deserialize_1(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_1_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

typedef struct uint8_t_x4_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
} uint8_t_x4;

uint8_t_x4 libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
    Eurydice_slice v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_serialize_4(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_4_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

typedef struct int16_t_x8_s {
  int16_t fst;
  int16_t snd;
  int16_t thd;
  int16_t f3;
  int16_t f4;
  int16_t f5;
  int16_t f6;
  int16_t f7;
} int16_t_x8;

int16_t_x8 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_slice bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

void libcrux_iot_ml_kem_vector_portable_deserialize_4(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_4_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

typedef struct uint8_t_x5_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
} uint8_t_x5;

uint8_t_x5 libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
    Eurydice_slice v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_5(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_serialize_5(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_5_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

int16_t_x8 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
    Eurydice_slice bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

void libcrux_iot_ml_kem_vector_portable_deserialize_5(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_5_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

uint8_t_x5 libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
    Eurydice_slice v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_10(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_serialize_10(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_10_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

int16_t_x8 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_slice bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

void libcrux_iot_ml_kem_vector_portable_deserialize_10(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_10_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

typedef struct uint8_t_x11_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
  uint8_t f5;
  uint8_t f6;
  uint8_t f7;
  uint8_t f8;
  uint8_t f9;
  uint8_t f10;
} uint8_t_x11;

uint8_t_x11 libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
    Eurydice_slice v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_11(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_serialize_11(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_11_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

int16_t_x8 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
    Eurydice_slice bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

void libcrux_iot_ml_kem_vector_portable_deserialize_11(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_11_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

typedef struct uint8_t_x3_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
} uint8_t_x3;

uint8_t_x3 libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
    Eurydice_slice v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_12(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out);

void libcrux_iot_ml_kem_vector_portable_serialize_12(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_12_4e(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out);

typedef struct int16_t_x2_s {
  int16_t fst;
  int16_t snd;
} int16_t_x2;

int16_t_x2 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_slice bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12(
    Eurydice_slice bytes,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

void libcrux_iot_ml_kem_vector_portable_deserialize_12(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(
    Eurydice_slice a,
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *out);

size_t libcrux_iot_ml_kem_vector_portable_sampling_rej_sample(
    Eurydice_slice a, Eurydice_slice result);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
size_t libcrux_iot_ml_kem_vector_portable_rej_sample_4e(Eurydice_slice a,
                                                        Eurydice_slice out);

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
libcrux_iot_ml_kem_vector_portable_vector_type_clone_9c(
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector *self);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem_iot_H_DEFINED
#endif /* libcrux_mlkem_iot_H */
