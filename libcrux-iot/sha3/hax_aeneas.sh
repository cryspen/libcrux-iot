#!/bin/sh

# hax version: 7b4bd97058e0fcbf9135b76297ca91942f2327a6
# aeneas version: 863909af

cargo hax into aeneas-lean

sed -i \
    's/import Aeneas/import Aeneas\nimport LibcruxIotSha3.Extraction.Missing\nopen core_models/' \
    proofs/aeneas-lean/LibcruxIotSha3/Extraction/Funs.lean