#!/usr/bin/env bash
# Build a libcrux-nucleo-l4r5zi binary and run it under qemu-system-arm.
#
# Usage:
#   ./run-qemu.sh --bin mldsa_stack_keygen --features stack
#   ./run-qemu.sh --release --bin mlkem_stack_keygen --features stack
#
# All arguments are forwarded to `cargo run`. The `qemu` feature is added
# automatically and the `board` default-feature is disabled.

set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"

for tool in "${QEMU:-qemu-system-arm}" defmt-print; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        echo "error: $tool not found in PATH (use the nix dev shell)" >&2
        exit 1
    fi
done

export CARGO_TARGET_THUMBV7EM_NONE_EABIHF_RUNNER="$here/qemu-runner.sh"

# Benchmark the most expensive variants
exec cargo run --no-default-features --features qemu,mldsa87,mlkem1024 "$@"
