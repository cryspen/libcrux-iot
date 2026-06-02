#pragma once

#include "eurydice_glue.h"

#define core_array___T__N___as_mut_slice(len_, ptr_, t, ret_t) \
  (KRML_CLITERAL(ret_t){EURYDICE_CFIELD(.ptr =)(ptr_)->data,   \
                        EURYDICE_CFIELD(.meta =) len_})

#define Eurydice_slice_eq_shared(s1, s2, t, _) \
  ((s1)->meta == (s2)->meta &&                 \
   memcmp((s1)->ptr, (s2)->ptr, (s1)->meta * sizeof(t)) == 0)

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1) {
  uint32_t n = x1 & 31;
  return (x0 << n) | (x0 >> ((-n) & 31));
}
