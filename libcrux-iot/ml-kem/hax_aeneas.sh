#!/bin/sh

# hax version: 7b4bd97058e0fcbf9135b76297ca91942f2327a6
# aeneas version: 863909af

cargo hax into aeneas-lean \
  --charon-args="\
    --start-from crate::ntt::*\
    --start-from crate::vector::portable::ntt::*"

sed -i \
    's/import Aeneas/import Aeneas\nimport CoreModels\nopen core_models/' \
    proofs/aeneas-lean/LibcruxIotMlKem/Extraction/Funs.lean