/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon:
 * Eurydice:
 * Karamel:
 * F*: unset
 * Libcrux: ff6b1583cfa91b1fb03fffe855308b44e2728708
 */

#include "internal/libcrux_iot_core.h"

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
with types uint8_t[136size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_3f(uint8_t self[136U],
                                                        uint8_t ret[136U]) {
  memcpy(ret, self, (size_t)136U * sizeof(uint8_t));
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
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_slice uint8_t

*/
Eurydice_slice *libcrux_secrets_int_public_integers_classify_ref_c5_ba(
    Eurydice_slice *self) {
  return self;
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
with types uint32_t[2size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_93(uint32_t self[2U],
                                                        uint32_t ret[2U]) {
  memcpy(ret, self, (size_t)2U * sizeof(uint32_t));
}
