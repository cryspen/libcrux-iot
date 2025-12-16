#pragma once

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _MSC_VER
// For __popcnt
#include <intrin.h>
#endif

#include "krml/internal/target.h"
#include "krml/lowstar_endianness.h"

// C++ HELPERS

#if defined(__cplusplus)

#ifndef KRML_HOST_EPRINTF
#define KRML_HOST_EPRINTF(...) fprintf(stderr, __VA_ARGS__)
#endif

#include <utility>

#ifndef __cpp_lib_type_identity
template <class T>
struct type_identity {
  using type = T
};

template <class T>
using type_identity_t = typename type_identity<T>::type;
#else
using std::type_identity_t;
#endif

#define KRML_UNION_CONSTRUCTOR(T)                              \
  template <typename V>                                        \
  constexpr T(int t, V U::*m, type_identity_t<V> v) : tag(t) { \
    val.*m = std::move(v);                                     \
  }                                                            \
  T() = default;

#endif

// GENERAL-PURPOSE STUFF

#define LowStar_Ignore_ignore(e, t, _ret_t) ((void)e)

#define EURYDICE_ASSERT(test, msg)                                            \
  do {                                                                        \
    if (!(test)) {                                                            \
      fprintf(stderr, "assertion \"%s\" failed: file \"%s\", line %d\n", msg, \
              __FILE__, __LINE__);                                            \
      exit(255);                                                              \
    }                                                                         \
  } while (0)

// SLICES, ARRAYS, ETC.
#if defined(__cplusplus)
#define KRML_CLITERAL(type) type
#else
#define KRML_CLITERAL(type) (type)
#endif

#if defined(__cplusplus) && defined(__cpp_designated_initializers) || \
    !(defined(__cplusplus))
#define EURYDICE_CFIELD(X) X
#else
#define EURYDICE_CFIELD(X)
#endif

#define Eurydice_slice_eq_shared(s1, s2, t, _) \
  ((s1)->meta == (s2)->meta &&                 \
   memcmp((s1)->ptr, (s2)->ptr, (s1)->meta * sizeof(t)) == 0)

// Slice length
#define EURYDICE_SLICE_LEN(s, _) (s).meta
#define Eurydice_slice_len(s, _) (s).meta

#define Eurydice_slice_index_mut(s, i, t) ((s).ptr[i])
#define Eurydice_slice_index_shared(s, i, t) ((s).ptr[i])

// Copy a slice with memcopy
#define Eurydice_slice_copy(dst, src, t) \
  memcpy(dst.ptr, src.ptr, dst.meta * sizeof(t))

#define core_array___Array_T__N___as_slice(len_, ptr_, t, ret_t) \
  (KRML_CLITERAL(ret_t){EURYDICE_CFIELD(.ptr =)(ptr_)->data,     \
                        EURYDICE_CFIELD(.meta =) len_})

#define core_array___Array_T__N___as_mut_slice(len_, ptr_, t, ret_t) \
  (KRML_CLITERAL(ret_t){EURYDICE_CFIELD(.ptr =)(ptr_)->data,         \
                        EURYDICE_CFIELD(.meta =) len_})

#define core_array__core__clone__Clone_for__Array_T__N___clone( \
    len, src, elem_type, _ret_t)                                \
  (*(src))

#define TryFromSliceError uint8_t
#define core_array_TryFromSliceError uint8_t

#define Eurydice_array_eq(sz, a1, a2, t) (memcmp(a1, a2, sz * sizeof(t)) == 0)

// core::cmp::PartialEq<&0 (@Slice<U>)> for @Array<T, N>
#define Eurydice_array_eq_slice(sz, a1, s2, t, _) \
  (memcmp(a1, (s2)->ptr, sz * sizeof(t)) == 0)

#define core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq( \
    sz, a1, a2, t, _, _ret_t)                                                           \
  Eurydice_array_eq(sz, a1, a2, t, _)
#define core_array_equality___core__cmp__PartialEq__0___Slice_U____for__Array_T__N___3__eq( \
    sz, a1, a2, t, _, _ret_t)                                                               \
  Eurydice_array_eq(sz, a1, ((a2)->ptr), t, _)

#define Eurydice_slice_split_at(slice, mid, element_type, ret_t)        \
  KRML_CLITERAL(ret_t) {                                                \
    EURYDICE_CFIELD(.fst =){EURYDICE_CFIELD(.ptr =)((slice).ptr),       \
                            EURYDICE_CFIELD(.meta =) mid},              \
        EURYDICE_CFIELD(.snd =) {                                       \
      EURYDICE_CFIELD(.ptr =)                                           \
      ((slice).ptr + mid), EURYDICE_CFIELD(.meta =)((slice).meta - mid) \
    }                                                                   \
  }

#define Eurydice_slice_split_at_mut(slice, mid, element_type, ret_t)    \
  KRML_CLITERAL(ret_t) {                                                \
    EURYDICE_CFIELD(.fst =){EURYDICE_CFIELD(.ptr =)((slice).ptr),       \
                            EURYDICE_CFIELD(.meta =) mid},              \
        EURYDICE_CFIELD(.snd =) {                                       \
      EURYDICE_CFIELD(.ptr =)                                           \
      ((slice).ptr + mid), EURYDICE_CFIELD(.meta =)((slice).meta - mid) \
    }                                                                   \
  }

// Conversion of slice to an array, rewritten (by Eurydice) to name the
// destination array, since arrays are not values in C.
// N.B.: see note in karamel/lib/Inlining.ml if you change this.
#define Eurydice_slice_to_array2(dst, src, _0, t_arr, _1)                 \
  Eurydice_slice_to_array3(&(dst)->tag, (char *)&(dst)->val.case_Ok, src, \
                           sizeof(t_arr))

// CORE STUFF (conversions, endianness, ...)

// We slap extern "C" on declarations that intend to implement a prototype
// generated by Eurydice, because Eurydice prototypes are always emitted within
// an extern "C" block, UNLESS you use -fcxx17-compat, in which case, you must
// pass -DKRML_CXX17_COMPAT="" to your C++ compiler.
#if defined(__cplusplus) && !defined(KRML_CXX17_COMPAT)
extern "C" {
#endif

// [ u8; 2 ]
typedef struct Eurydice_array_u8x2_s {
  uint8_t data[2];
} Eurydice_array_u8x2;

// [ u8; 4 ]
typedef struct Eurydice_array_u8x4_s {
  uint8_t data[4];
} Eurydice_array_u8x4;

// [ u8; 8 ]
typedef struct Eurydice_array_u8x8_s {
  uint8_t data[8];
} Eurydice_array_u8x8;

// &mut [u8]
typedef struct Eurydice_mut_borrow_slice_u8_s {
  uint8_t *ptr;
  size_t meta;
} Eurydice_mut_borrow_slice_u8;

// &[u8]
typedef struct Eurydice_borrow_slice_u8_s {
  const uint8_t *ptr;
  size_t meta;
} Eurydice_borrow_slice_u8;

// &mut [i16]
typedef struct Eurydice_mut_borrow_slice_i16_s {
  int16_t *ptr;
  size_t meta;
} Eurydice_mut_borrow_slice_i16;

// &[i16]
typedef struct Eurydice_borrow_slice_i16_s {
  const int16_t *ptr;
  size_t meta;
} Eurydice_borrow_slice_i16;

static inline void core_num__u32__to_be_bytes(uint32_t src, uint8_t dst[4]) {
  // TODO: why not store32_be?
  uint32_t x = htobe32(src);
  memcpy(dst, &x, 4);
}

static inline Eurydice_array_u8x4 core_num__u32__to_le_bytes(uint32_t src) {
  Eurydice_array_u8x4 a;
  store32_le(a.data, src);
  return a;
}

static inline uint32_t core_num__u32__from_le_bytes(Eurydice_array_u8x4 buf) {
  return load32_le(buf.data);
}

static inline Eurydice_array_u8x8 core_num__u64__to_le_bytes(uint64_t v) {
  Eurydice_array_u8x8 a;
  store64_le(a.data, v);
  return a;
}

static inline uint64_t core_num__u64__from_le_bytes(Eurydice_array_u8x8 buf) {
  return load64_le(buf.data);
}

static inline int64_t
core_convert_num___core__convert__From_i32__for_i64___from(int32_t x) {
  return x;
}

static inline uint64_t
core_convert_num___core__convert__From_u8__for_u64___from(uint8_t x) {
  return x;
}

static inline uint64_t
core_convert_num___core__convert__From_u16__for_u64___from(uint16_t x) {
  return x;
}

static inline size_t
core_convert_num___core__convert__From_u16__for_usize___from(uint16_t x) {
  return x;
}

static inline uint32_t core_num__u8__count_ones(uint8_t x0) {
#ifdef _MSC_VER
  return __popcnt(x0);
#else
  return __builtin_popcount(x0);
#endif
}

static inline uint32_t core_num__i32__count_ones(int32_t x0) {
#ifdef _MSC_VER
  return __popcnt(x0);
#else
  return __builtin_popcount(x0);
#endif
}

static inline size_t core_cmp_impls___core__cmp__Ord_for_usize___min(size_t a,
                                                                     size_t b) {
  if (a <= b)
    return a;
  else
    return b;
}

// unsigned overflow wraparound semantics in C
static inline uint16_t core_num__u16__wrapping_add(uint16_t x, uint16_t y) {
  return x + y;
}
static inline uint8_t core_num__u8__wrapping_sub(uint8_t x, uint8_t y) {
  return x - y;
}
static inline uint64_t core_num__u64__rotate_left(uint64_t x0, uint32_t x1) {
  return (x0 << x1 | x0 >> (64 - x1));
}

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1) {
  return (x0 << x1) | (x0 >> ((-x1) & 31));
}

static inline void core_ops_arith__i32__add_assign(int32_t *x0, int32_t *x1) {
  *x0 = *x0 + *x1;
}

static inline uint8_t Eurydice_bitand_pv_u8(const uint8_t *p, uint8_t v) {
  return (*p) & v;
}
static inline uint8_t Eurydice_shr_pv_u8(const uint8_t *p, int32_t v) {
  return (*p) >> v;
}

static inline uint32_t Eurydice_min_u32(uint32_t x, uint32_t y) {
  return x < y ? x : y;
}

static inline uint8_t
core_ops_bit__core__ops__bit__BitAnd_u8__u8__for__0__u8___bitand(
    const uint8_t *x0, uint8_t x1) {
  return Eurydice_bitand_pv_u8(x0, x1);
}

static inline uint8_t
core_ops_bit__core__ops__bit__Shr_i32__u8__for__0__u8___shr(const uint8_t *x0,
                                                            int32_t x1) {
  return Eurydice_shr_pv_u8(x0, x1);
}

#define core_num_nonzero_private_NonZeroUsizeInner size_t
static inline core_num_nonzero_private_NonZeroUsizeInner
core_num_nonzero_private___core__clone__Clone_for_core__num__nonzero__private__NonZeroUsizeInner__26__clone(
    core_num_nonzero_private_NonZeroUsizeInner *x0) {
  return *x0;
}

#if defined(__cplusplus) && !defined(KRML_CXX17_COMPAT)
}
#endif

// ITERATORS

#define Eurydice_range_iter_next(iter_ptr, t, ret_t)      \
  (((iter_ptr)->start >= (iter_ptr)->end)                 \
       ? (KRML_CLITERAL(ret_t){EURYDICE_CFIELD(.tag =) 0, \
                               EURYDICE_CFIELD(.f0 =) 0}) \
       : (KRML_CLITERAL(ret_t){EURYDICE_CFIELD(.tag =) 1, \
                               EURYDICE_CFIELD(.f0 =)(iter_ptr)->start++}))

#define core_iter_range___core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___6__next \
  Eurydice_range_iter_next

// See note in karamel/lib/Inlining.ml if you change this
#define Eurydice_into_iter(x, t, _ret_t, _) (x)
#define core_iter_traits_collect___core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__1__into_iter \
  Eurydice_into_iter

// using it anyway??
#define Eurydice_slice_subslice3(s, start, end, t_ptr) \
  EURYDICE_SLICE((t_ptr)s.ptr, (start), (end))

#define core_slice___Slice_T___chunks(slice_, sz_, t, _ret_t) \
  ((Eurydice_chunks){.slice = slice_, .chunk_size = sz_})
#define core_slice___Slice_T___chunks_exact(slice_, sz_, t, _ret_t)         \
  ((Eurydice_chunks){                                                       \
      .slice = {.ptr = slice_.ptr, .len = slice_.len - (slice_.len % sz_)}, \
      .chunk_size = sz_})
#define core_slice_iter_Chunks Eurydice_chunks
#define core_slice_iter_ChunksExact Eurydice_chunks
#define Eurydice_chunks_next(iter, t, ret_t)                     \
  (((iter)->slice.len == 0) ? ((ret_t){.tag = core_option_None}) \
                            : ((ret_t){.tag = core_option_Some,  \
                                       .f0 = chunk_next(iter, sizeof(t))}))
#define core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Chunks__a__T___70__next \
  Eurydice_chunks_next
// This name changed on 20240627
#define core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Chunks__a__T___71__next \
  Eurydice_chunks_next
#define core_slice_iter__core__slice__iter__ChunksExact__a__T__89__next( \
    iter, t, _ret_t)                                                     \
  core_slice_iter__core__slice__iter__Chunks__a__T__70__next(iter, t)

#define core_option__core__option__Option_T__TraitClause_0___is_some(X, _0, \
                                                                     _1)    \
  ((X)->tag == 1)
// STRINGS

typedef char Eurydice_c_char_t;
typedef const Eurydice_c_char_t *Prims_string;
typedef void Eurydice_c_void_t;
