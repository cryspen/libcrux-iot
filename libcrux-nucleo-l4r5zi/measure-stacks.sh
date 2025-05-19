#!/bin/bash

# This script will compile and run the stack measurement binaries in
# release mode, writing the results to `stack.dat` (will be
# overwritten if it exists).
# 
# The stack measurement binaries run the operations in sequence at the
# moment, so if an earlier operation uses more stack than a later one,
# the latter's measurement will be shadowed by the former's. (Or if
# the stack is not fully cleared between operations for some reason.)

echo "Starting measurements"
echo "[ML-KEM] KeyGen"
cargo rrb mlkem_stack_keygen --quiet --features stack > stack.dat
echo "[ML-KEM] Encaps"
cargo rrb mlkem_stack_encaps --quiet --features stack >> stack.dat
echo "[ML-KEM] Decaps"
cargo rrb mlkem_stack_decaps --quiet --features stack >> stack.dat

echo "[ML-DSA] KeyGen"
cargo rrb mldsa_stack_keygen --quiet --features stack >> stack.dat
echo "[ML-DSA] Sign"
cargo rrb mldsa_stack_sign --quiet --features stack >> stack.dat
echo "[ML-DSA] Verify"
cargo rrb mldsa_stack_verify --quiet --features stack >> stack.dat
echo "Done"
