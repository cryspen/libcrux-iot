#!/usr/bin/env bash

# QEMU counterpart of measure-stacks.sh: builds the stack measurement binaries
# in release mode under qemu-system-arm and writes results to
# stack-${REV}-qemu.dat.
#
# Stack figures match the real board's layout (RAM origin + size are identical
# in memory-qemu.x), but the underlying CPU model and toolchain are simulated.

set -euo pipefail

cd "$(dirname "$0")"

REV=$(git rev-parse HEAD)
FILE="stack-${REV}-qemu.dat"

echo "Repository at commit: $REV (qemu)" > "$FILE"

echo "Starting QEMU measurements (mps2-an386)"
for bin in mlkem_stack_keygen mlkem_stack_encaps mlkem_stack_decaps \
           mldsa_stack_keygen mldsa_stack_sign mldsa_stack_verify; do
    echo "[$bin]"
    ./run-qemu.sh --release --features stack --quiet --bin "$bin" >> "$FILE"
done
echo "wrote $FILE"
