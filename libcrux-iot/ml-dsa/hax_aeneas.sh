#!/bin/sh

# hax version: 7b4bd97058e0fcbf9135b76297ca91942f2327a6
# aeneas version: 863909af

cargo hax into aeneas-lean \
  --charon-args="\
    --start-from crate::simd::portable::invntt::invert_ntt_montgomery\
    --start-from crate::simd::portable::ntt::ntt\
    --start-from crate::simd::portable::arithmetic::montgomery_multiply"

sed -i \
    's/import Aeneas/import Aeneas\nimport CoreModels\nopen core_models/' \
    proofs/aeneas-lean/LibcruxIotMlDsa/Extraction/Funs.lean