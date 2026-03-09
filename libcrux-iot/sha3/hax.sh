#!/usr/bin/env bash

set -e

if [ ! -L hax ]; then
    echo -e "\033[1mWarning: Create a symlink \`hax\` linking to the \`libcrux-iot\` branch of \`hax\`\033[0m"
fi

cargo hax into lean

sed -i '1s/^/import extraction.helpers\n/' proofs/lean/extraction/libcrux_iot_sha3.lean
