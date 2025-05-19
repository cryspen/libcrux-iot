#!/bin/bash

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
echo "[ML-DSA] Verify Decaps"
cargo rrb mldsa_stack_verify --quiet --features stack >> stack.dat
echo "Done"
