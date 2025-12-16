/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: cdf02f9d8ed0d73f88c0a495c5b79359a51398fc
 * Karamel: 8e7262955105599e91f3a99c9ab3d3387f7046f2
 * F*: unset
 * Libcrux: 1ad7c25705450131b575043e252c944035898962
 */

#include "internal/libcrux_iot_mldsa_core.h"

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
const Eurydice_arr_38 *libcrux_iot_ml_dsa_types_as_ref_ad_c2(
    const Eurydice_arr_38 *self) {
  return self;
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
const Eurydice_arr_510 *libcrux_iot_ml_dsa_types_as_ref_e9_d8(
    const Eurydice_arr_510 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4627
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_24(
    const Eurydice_arr_38 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4627U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2592
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f70(
    const Eurydice_arr_510 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2592U;
  return lit;
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
const Eurydice_arr_180 *libcrux_iot_ml_dsa_types_as_ref_f8_32(
    const Eurydice_arr_180 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4896
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_e2(
    const Eurydice_arr_180 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4896U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4627
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_24(
    Eurydice_arr_38 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4627U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_59 Eurydice_array_to_slice_shared_6d1(
    const Eurydice_arr_05 *a) {
  Eurydice_dst_ref_shared_59 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 8
*/
Eurydice_dst_ref_mut_59 Eurydice_array_to_slice_mut_6d1(Eurydice_arr_05 *a) {
  Eurydice_dst_ref_mut_59 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1024
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_fd(
    const Eurydice_arr_9e *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1024U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1024
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fd(
    Eurydice_arr_9e *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1024U;
  return lit;
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
Eurydice_arr_38 libcrux_iot_ml_dsa_types_zero_ad_c2(void) {
  return (KRML_CLITERAL(Eurydice_arr_38){.data = {0U}});
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
Eurydice_arr_510 libcrux_iot_ml_dsa_types_new_e9_d8(Eurydice_arr_510 value) {
  return value;
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
Eurydice_arr_180 libcrux_iot_ml_dsa_types_new_f8_32(Eurydice_arr_180 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2592
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f70(
    Eurydice_arr_510 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2592U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4896
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_e2(
    Eurydice_arr_180 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4896U;
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
const Eurydice_arr_96 *libcrux_iot_ml_dsa_types_as_ref_ad_fa(
    const Eurydice_arr_96 *self) {
  return self;
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
const Eurydice_arr_4a *libcrux_iot_ml_dsa_types_as_ref_e9_97(
    const Eurydice_arr_4a *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 3309
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ee0(
    const Eurydice_arr_96 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3309U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1952
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_5b(
    const Eurydice_arr_4a *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1952U;
  return lit;
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
const Eurydice_arr_d10 *libcrux_iot_ml_dsa_types_as_ref_f8_09(
    const Eurydice_arr_d10 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4032
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ef(
    const Eurydice_arr_d10 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4032U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 3309
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ee0(
    Eurydice_arr_96 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3309U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 6
*/
Eurydice_dst_ref_shared_59 Eurydice_array_to_slice_shared_6d0(
    const Eurydice_arr_e6 *a) {
  Eurydice_dst_ref_shared_59 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 6
*/
Eurydice_dst_ref_mut_59 Eurydice_array_to_slice_mut_6d0(Eurydice_arr_e6 *a) {
  Eurydice_dst_ref_mut_59 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 48
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_95(
    const Eurydice_arr_5f *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)48U;
  return lit;
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
Eurydice_arr_96 libcrux_iot_ml_dsa_types_zero_ad_fa(void) {
  return (KRML_CLITERAL(Eurydice_arr_96){.data = {0U}});
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
Eurydice_arr_4a libcrux_iot_ml_dsa_types_new_e9_97(Eurydice_arr_4a value) {
  return value;
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
Eurydice_arr_d10 libcrux_iot_ml_dsa_types_new_f8_09(Eurydice_arr_d10 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1952
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_5b(
    Eurydice_arr_4a *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1952U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4032
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ef(
    Eurydice_arr_d10 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4032U;
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
const Eurydice_arr_400 *libcrux_iot_ml_dsa_types_as_ref_ad_1a(
    const Eurydice_arr_400 *self) {
  return self;
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
const Eurydice_arr_40 *libcrux_iot_ml_dsa_types_as_ref_e9_db(
    const Eurydice_arr_40 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2420
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_180(
    const Eurydice_arr_400 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2420U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1312
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_bb(
    const Eurydice_arr_40 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1312U;
  return lit;
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
const Eurydice_arr_18 *libcrux_iot_ml_dsa_types_as_ref_f8_ff(
    const Eurydice_arr_18 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2560
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_59(
    const Eurydice_arr_18 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2560U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2420
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_180(
    Eurydice_arr_400 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2420U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_59 Eurydice_array_to_slice_shared_6d(
    const Eurydice_arr_51 *a) {
  Eurydice_dst_ref_shared_59 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_59 Eurydice_array_to_slice_mut_6d(Eurydice_arr_51 *a) {
  Eurydice_dst_ref_mut_59 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_mut_fc Eurydice_array_to_subslice_mut_7f(
    Eurydice_arr_c3 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_mut_fc){.ptr = a->data + r.start,
                                                 .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_8c(
    const Eurydice_arr_3d *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)136U - r});
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
Eurydice_array_u8x8 unwrap_26_ab(Result_a4 self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 768
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ee(
    const Eurydice_arr_56 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)768U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 768
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ee(
    Eurydice_arr_56 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)768U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 640
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_7d(
    const Eurydice_arr_c30 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)640U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 640
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_7d(
    Eurydice_arr_c30 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)640U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 576
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_fa0(
    const Eurydice_arr_5f0 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)576U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 576
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fa(
    Eurydice_arr_5f0 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)576U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 11
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_da(
    const Eurydice_arr_cb *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)11U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_07(
    const Eurydice_arr_f10 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
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
Eurydice_arr_400 libcrux_iot_ml_dsa_types_zero_ad_1a(void) {
  return (KRML_CLITERAL(Eurydice_arr_400){.data = {0U}});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_200(
    const Eurydice_arr_c3 *a) {
  Eurydice_dst_ref_shared_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
  return lit;
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
Eurydice_arr_40 libcrux_iot_ml_dsa_types_new_e9_db(Eurydice_arr_40 value) {
  return value;
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
Eurydice_arr_18 libcrux_iot_ml_dsa_types_new_f8_ff(Eurydice_arr_18 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1312
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_bb(
    Eurydice_arr_40 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1312U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2560
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_59(
    Eurydice_arr_18 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2560U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_d8(
    const Eurydice_arr_06 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)64U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 66
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_39(
    const Eurydice_arr_a2 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)66U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$263size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_2c Eurydice_array_to_slice_mut_f6(Eurydice_arr_46 *a) {
  Eurydice_dst_ref_mut_2c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 263
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_20(
    const Eurydice_arr_13 *a) {
  Eurydice_dst_ref_shared_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)263U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_7b(
    const Eurydice_arr_27 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)168U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 840
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_a8(
    const Eurydice_arr_12 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)840U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types int32_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
int32_t with const generics
- N= 263
*/
Eurydice_dst_ref_mut_fc Eurydice_array_to_subslice_from_mut_96(
    Eurydice_arr_13 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_mut_fc){.ptr = a->data + r,
                                                 .meta = (size_t)263U - r});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 34
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_8d(
    const Eurydice_arr_48 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)34U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 128
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_18(
    const Eurydice_arr_d1 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)128U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 128
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_18(
    Eurydice_arr_d1 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)128U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_26(
    const Eurydice_array_u8x2 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_6e(
    const Eurydice_arr_60 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)32U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_subslice_shared_7f(
    const Eurydice_arr_d4 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = a->data + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_fc Eurydice_array_to_slice_shared_a7(
    const Eurydice_arr_d4 *a) {
  Eurydice_dst_ref_shared_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
Eurydice_dst_ref_shared_fc Eurydice_slice_subslice_shared_46(
    Eurydice_dst_ref_shared_fc s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_fc){.ptr = s.ptr + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_mut_fc Eurydice_array_to_slice_mut_a7(Eurydice_arr_d4 *a) {
  Eurydice_dst_ref_mut_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 66
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_362(
    Eurydice_arr_a2 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_361(
    Eurydice_arr_48 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_d4(
    Eurydice_arr_3d *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)136U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_7b(
    Eurydice_arr_27 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)168U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 840
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_a8(
    Eurydice_arr_12 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)840U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_d8(
    Eurydice_arr_06 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)64U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$64size_t]]

*/
Eurydice_arr_06 libcrux_secrets_int_public_integers_classify_27_490(
    Eurydice_arr_06 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 48
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_95(
    Eurydice_arr_5f *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)48U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$48size_t]]

*/
Eurydice_arr_5f libcrux_secrets_int_public_integers_classify_27_7d(
    Eurydice_arr_5f self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 32
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_6e(
    Eurydice_arr_60 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)32U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$32size_t]]

*/
Eurydice_arr_60 libcrux_secrets_int_public_integers_classify_27_62(
    Eurydice_arr_60 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 28
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_c0(
    Eurydice_arr_f1 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)28U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$28size_t]]

*/
Eurydice_arr_f1 libcrux_secrets_int_public_integers_classify_27_4b(
    Eurydice_arr_f1 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_361(
    const Eurydice_array_u8x4 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$136size_t]]

*/
Eurydice_arr_3d libcrux_secrets_int_public_integers_classify_27_df0(
    Eurydice_arr_3d self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_360(
    const Eurydice_arr_3d *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_from_shared_6b(
    Eurydice_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr + r,
                                                  .meta = s.meta - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_360(
    Eurydice_arr_3d *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_d4(
    const Eurydice_arr_3d *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)136U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_to_shared_c6(
    Eurydice_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr, .meta = r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_8c(
    Eurydice_arr_3d *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){
      .ptr = a->data + r, .meta = (size_t)136U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_36(
    const Eurydice_arr_88 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f7(
    Eurydice_arr_88 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)200U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_60(
    const Eurydice_array_u8x4 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_mut_7e(
    Eurydice_mut_borrow_slice_u8 s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = s.ptr + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f7(
    const Eurydice_arr_88 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)200U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_shared_7e(
    Eurydice_borrow_slice_u8 s, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_36(
    Eurydice_arr_88 *a, core_ops_range_Range_08 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$200size_t]]

*/
Eurydice_arr_88 libcrux_secrets_int_public_integers_classify_27_c1(
    Eurydice_arr_88 self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint32_t[[$2size_t]]

*/
Eurydice_arr_b2 libcrux_secrets_int_public_integers_classify_27_54(
    Eurydice_arr_b2 self) {
  return self;
}
