#!/bin/bash

# This script will compile and run the cycles measurement binaries in
# release mode, writing the results to `cycles-{$REV}.dat` (will be
# overwritten if it exists).

export REV=$(git rev-parse HEAD)
export FILE="cycles-${REV}.dat"

echo -n "Repository at commit: " > "$FILE"
echo "$REV" >> "$FILE"

echo "Starting measurements"
echo "[ML-KEM]"
DEFMT_LOG=info cargo rrb mlkem --quiet >> "$FILE"

echo "[ML-DSA]"
DEFMT_LOG=info cargo rrb mldsa --quiet >> "$FILE"
echo "Done"
