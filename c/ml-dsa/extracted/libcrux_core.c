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
 * Libcrux: 4c0c9248a551dd42901dc5208f62cc9e92e7e0c3
 */

#include "internal/libcrux_core.h"

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t classify_27_49(uint64_t self) { return self; }

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t declassify_d8_df(uint32_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self) {
  return classify_27_49((uint64_t)declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t classify_27_df(uint32_t self) { return self; }

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t declassify_d8_49(uint64_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self) {
  return classify_27_df((uint32_t)declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self) {
  return self;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 4627
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_ad_c2(
    libcrux_iot_ml_dsa_types_MLDSASignature_9b *self) {
  return self->value;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 2592
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_e9_d8(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe *self) {
  return self->value;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 4896
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_f8_32(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 *self) {
  return self->value;
}

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 4627
*/
libcrux_iot_ml_dsa_types_MLDSASignature_9b libcrux_iot_ml_dsa_types_zero_ad_c2(
    void) {
  return (
      KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSASignature_9b){.value = {0U}});
}

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 2592
*/
libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe
libcrux_iot_ml_dsa_types_new_e9_d8(uint8_t value[2592U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[2592U];
  memcpy(copy_of_value, value, (size_t)2592U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSAVerificationKey_fe lit;
  memcpy(lit.value, copy_of_value, (size_t)2592U * sizeof(uint8_t));
  return lit;
}

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 4896
*/
libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 libcrux_iot_ml_dsa_types_new_f8_32(
    uint8_t value[4896U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[4896U];
  memcpy(copy_of_value, value, (size_t)4896U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSASigningKey_a3 lit;
  memcpy(lit.value, copy_of_value, (size_t)4896U * sizeof(uint8_t));
  return lit;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 3309
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_ad_fa(
    libcrux_iot_ml_dsa_types_MLDSASignature_8f *self) {
  return self->value;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 1952
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_e9_97(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea *self) {
  return self->value;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 4032
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_f8_09(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_22 *self) {
  return self->value;
}

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 3309
*/
libcrux_iot_ml_dsa_types_MLDSASignature_8f libcrux_iot_ml_dsa_types_zero_ad_fa(
    void) {
  return (
      KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSASignature_8f){.value = {0U}});
}

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 1952
*/
libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea
libcrux_iot_ml_dsa_types_new_e9_97(uint8_t value[1952U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1952U];
  memcpy(copy_of_value, value, (size_t)1952U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSAVerificationKey_ea lit;
  memcpy(lit.value, copy_of_value, (size_t)1952U * sizeof(uint8_t));
  return lit;
}

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 4032
*/
libcrux_iot_ml_dsa_types_MLDSASigningKey_22 libcrux_iot_ml_dsa_types_new_f8_09(
    uint8_t value[4032U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[4032U];
  memcpy(copy_of_value, value, (size_t)4032U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSASigningKey_22 lit;
  memcpy(lit.value, copy_of_value, (size_t)4032U * sizeof(uint8_t));
  return lit;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 2420
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_ad_1a(
    libcrux_iot_ml_dsa_types_MLDSASignature_64 *self) {
  return self->value;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 1312
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_e9_db(
    libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c *self) {
  return self->value;
}

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 2560
*/
uint8_t *libcrux_iot_ml_dsa_types_as_ref_f8_ff(
    libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 *self) {
  return self->value;
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_68(core_result_Result_15 self, uint8_t ret[8U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[8U];
    memcpy(f0, self.val.case_Ok, (size_t)8U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)8U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 2420
*/
libcrux_iot_ml_dsa_types_MLDSASignature_64 libcrux_iot_ml_dsa_types_zero_ad_1a(
    void) {
  return (
      KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSASignature_64){.value = {0U}});
}

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 1312
*/
libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c
libcrux_iot_ml_dsa_types_new_e9_db(uint8_t value[1312U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1312U];
  memcpy(copy_of_value, value, (size_t)1312U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSAVerificationKey_4c lit;
  memcpy(lit.value, copy_of_value, (size_t)1312U * sizeof(uint8_t));
  return lit;
}

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 2560
*/
libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 libcrux_iot_ml_dsa_types_new_f8_ff(
    uint8_t value[2560U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[2560U];
  memcpy(copy_of_value, value, (size_t)2560U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_types_MLDSASigningKey_b8 lit;
  memcpy(lit.value, copy_of_value, (size_t)2560U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[168size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_09(uint8_t self[168U],
                                                        uint8_t ret[168U]) {
  memcpy(ret, self, (size_t)168U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[64size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_7b(uint8_t self[64U],
                                                        uint8_t ret[64U]) {
  memcpy(ret, self, (size_t)64U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[48size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_4d(uint8_t self[48U],
                                                        uint8_t ret[48U]) {
  memcpy(ret, self, (size_t)48U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[32size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_ee0(uint8_t self[32U],
                                                         uint8_t ret[32U]) {
  memcpy(ret, self, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[28size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_ae(uint8_t self[28U],
                                                        uint8_t ret[28U]) {
  memcpy(ret, self, (size_t)28U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[136size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_3f(uint8_t self[136U],
                                                        uint8_t ret[136U]) {
  memcpy(ret, self, (size_t)136U * sizeof(uint8_t));
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[4size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_0a(core_result_Result_12 self, uint8_t ret[4U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[4U];
    memcpy(f0, self.val.case_Ok, (size_t)4U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)4U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t[200size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_e7(uint8_t self[200U],
                                                        uint8_t ret[200U]) {
  memcpy(ret, self, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_derefed_slice uint8_t

*/
uint8_t (*libcrux_secrets_int_public_integers_classify_ref_c5_45(
    uint8_t (*self)[]))[] {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t[2size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_93(uint32_t self[2U],
                                                        uint32_t ret[2U]) {
  memcpy(ret, self, (size_t)2U * sizeof(uint32_t));
}
