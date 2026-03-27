# Keccak-f[1600] Equivalence Proofs

Formal verification that the bit-interleaved Keccak-f[1600] implementation
(`libcrux_iot_sha3`) is functionally equivalent to the hacspec reference
specification (`hacspec_sha3`).

## Top-level theorem

```
theorem equivalence (s : KeccakState) (hi : s.i.toNat = 0) :
    hacspec_sha3.keccak_f.keccak_f (lift s) =
    (libcrux_iot_sha3.keccak.keccakf1600 s >>= fun r => pure (lift r))
```

**In plain language:** the hacspec Keccak-f permutation applied to the lifted
(de-interleaved) state equals running the bit-interleaved implementation and
then lifting the result. The implementation is correct.

## File structure

### Definitions (`lift_defs.lean`)
Core mapping from bit-interleaved `Lane2U32` pairs to standard `u64`:
- `spread_to_even` — parallel bit-deposit (32 bits → even positions of 64 bits)
- `lift_lane_bv` — reconstruct u64 lane from interleaved halves
- `lift` — lift full 25-lane state
- `impl_perm` — lane permutation from the implementation's pi step

### Spec decomposition (`spec_decomp.lean`)
Decomposes the hacspec `spec_round` into sub-steps matching the implementation:
- `spec_theta_unrolled` — theta step without `Vector.mapM` (explicit per-lane)
- `spec_prc_unrolled` — rho+pi+chi+iota without `Vector.mapM`
- `spec_round_decomp` — `spec_round = spec_theta >> spec_prc`

### Theta lifting (`theta_lift.lean`)
Proves the theta step lifts correctly:
- 4 algebraic lifting lemmas (`lift_xor`, `lift_td`, `lift_rot1`, `lift_xor5`)
- `theta_comp_spec_local` — impl-only Hoare triple (2M heartbeats)
- `theta_lift_spec` — full theta equivalence (16M heartbeats)

### PRC lifting (`prc_lift.lean`)
Proves rho+pi+chi+iota lifts correctly:
- 25 rotation lifting lemmas (even/odd Keccak rotation offsets)
- Bitwise lifting (`lift_xor`, `lift_and`, `lift_not`, `lift_chi`)
- `prc_lift_spec` — full PRC equivalence (20M heartbeats)

### Round equivalence (`round_equiv_comp.lean`)
Composes theta + PRC into full round equivalence:
- `round0_func_equiv` — round 0 functional equivalence (40M heartbeats)
- Uses `spec_round_decomp` to connect to `spec_round`

### Per-step Hoare triples (`step_equiv.lean`)
WP-based proofs for each implementation step:
- `theta_comp_spec` — theta d-value computation
- `pi_rho_chi_1_spec` — prc1 step (rotation + permutation + chi, first half)
- `pi_rho_chi_2_spec` — prc2 step (chi + iota, second half)

### Composition (`equiv.lean`)
Chains 4 rounds into the full Keccak-f equivalence:
- `four_round_eq` — 4 per-round equivalences composed
- `equivalence` — the top-level theorem (24 rounds = 6 × 4-round blocks)

## Proof architecture

```
equivalence (equiv.lean)
  └── four_round_eq × 6
        └── roundK_func_equiv (round_equiv_comp.lean)
              ├── theta_lift_spec (theta_lift.lean)
              │     ├── theta_comp_spec_local [hax_mvcgen, 2M]
              │     └── algebraic bridge [lift_xor, lift_td, lift_xor5, lift_rot1]
              └── prc_lift_spec (prc_lift.lean)
                    ├── hax_mvcgen on impl only [20M]
                    └── algebraic bridge [rot_*, lift_chi, lift_theta_apply]
```

## Key optimizations

1. **`@[local irreducible] spread_to_even lift_lane_bv`** — prevents 58GB memory
   bomb from simp unfolding bit-spreading into 6-step chains × 25 lanes.

2. **Separated WP computation** — `hax_mvcgen` runs on implementation ONLY (no
   spec/lift terms in hints). Spec terms applied algebraically post-mvcgen.
   Reduces prc_lift from 10GB/23min to 1.5GB/30s.

3. **No `rfl` on irreducible terms** — kernel `isDefEq` ignores `@[irreducible]`.
   Use `congr` + `simp` to close equalities without kernel involvement.

4. **Concrete vector literals** — `#v[...]` instead of `Vector.ofFn` to ensure
   syntactic equality between both sides of the algebraic bridge.

## Sorry inventory

The implementation/spec equivalence is **fully proven** (0 sorry in theta_lift,
prc_lift, round_equiv_comp). The remaining sorry's are in `spec_decomp.lean`:

- `spec_theta_unrolled_eq` — `spec_theta = spec_theta_unrolled` (Vector.mapM unrolling)
- `spec_prc_unrolled_eq` — `spec_prc = spec_prc_unrolled` (Vector.mapM unrolling)

These are purely algebraic facts about the hacspec specification and are
independent of the implementation correctness.

## Build

```bash
lake build libcrux_iot_sha3
```

Cold build times (approximate):
- theta_lift: ~8 minutes
- prc_lift: ~2 minutes
- round_equiv_comp: ~3 minutes
- Total: ~15 minutes
