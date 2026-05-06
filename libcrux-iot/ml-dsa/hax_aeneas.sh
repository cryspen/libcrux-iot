#!/bin/sh

# hax version: c11d79045605edbceb02377c1053e03f7c36b8c4
# aeneas version: 863909af

cargo hax into aeneas-lean

sed -i \
    's/import Aeneas/import Aeneas\nimport LibcruxIotSha3.Extraction.Missing\nopen core_models/' \
    proofs/aeneas-lean/LibcruxIotSha3/Extraction/Funs.lean