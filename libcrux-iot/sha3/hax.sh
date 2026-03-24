#!/usr/bin/env bash

set -e

cargo hax into lean

sed -i '1s/^/import extraction.helpers\n/' proofs/lean/extraction/libcrux_iot_sha3.lean
