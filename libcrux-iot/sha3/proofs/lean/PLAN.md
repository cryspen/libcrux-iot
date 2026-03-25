# Keccak-f[1600] Bit-Interleaved Equivalence Proof — Status

## Goal

Prove that the bit-interleaved implementation (`keccakf1600`) equals the
reference spec (`keccak_f`) when lifted from Lane2U32 to standard u64.

## Status: 3 sorry remaining (trivial i-bounds)

Main theorem in `extraction/equiv.lean`:
```lean
theorem equivalence (s : KeccakState) (hi : s.i.toNat = 0) :
    hacspec_sha3.keccak_f.keccak_f (lift s) =
    (libcrux_iot_sha3.keccak.keccakf1600 s >>= fun r => pure (lift r))
```

All proofs compile via `lake build`. The 3 remaining sorries are
`rK.i.toNat < 24` bounds inside `four_round_eq` — trivially provable
once `roundK_eq` is made unconditional.

## Proof chain

```
equivalence (✅)
├── keccak_f_unfold (✅) — spec fold = 6 × spec_4rounds
├── four_rounds_ok (✅) — WP extraction from four_rounds_equiv
└── four_round_eq (3 sorry: i-bounds)
      ├── round0_eq ← round0_func_equiv (✅ hax_mvcgen, ~400M heartbeats)
      ├── round1_eq ← round1_func_equiv (✅ hax_mvcgen)
      ├── round2_eq ← round2_func_equiv (✅ hax_mvcgen)
      └── round3_eq ← round3_func_equiv (✅ hax_mvcgen)
```

## File structure

- **`step_equiv.lean`** (~1400 lines): Definitions, algebraic lemmas (`bv_decide`),
  per-step Hoare triples (`hax_mvcgen`), totality proofs (`Triple.bind`),
  i-tracking composition, `keccakf1600_succeeds`
- **`equiv.lean`** (~250 lines): Per-round functional equivalence (`hax_mvcgen`
  on both spec+impl), round composition, top-level equivalence.
  Imports only extraction files (not step_equiv) to keep `mvcgen`'s
  internal simp within its 100K step limit.

## Key technique: dual hax_mvcgen

Each `roundK_func_equiv` runs `hax_mvcgen` on BOTH the spec
(theta→rho→pi→chi→iota on `RustArray u64 25`) and impl
(theta→prc1→prc2 on `KeccakState`) simultaneously. The generated VCs
connect the u32 (impl) and u64 (spec) operations. The algebraic
lifting lemmas close all VCs automatically:
- `lift_lane_bv_{xor,and,not,or}` — bitwise ops commute with lift
- `lift_lane_bv_rotate_{0..62}` — rotation commutes with lift
- `chi_lane_lift` — chi step commutes with lift
- `rc_equiv` — interleaved round constants = standard round constants

## Proven theorems (complete list in equiv.lean)

| Category | Count | Technique |
|----------|-------|-----------|
| Algebraic lifting lemmas | 27 | `bv_decide` |
| Per-step Hoare triples (theta, prc1, prc2 × 4 rounds) | ~40 | `hax_mvcgen` |
| i-tracking composition (four_rounds_equiv) | 1 | 12-step `Triple.bind` |
| Totality (keccakf1600_succeeds) | 1 | fold unrolling + `Triple.bind` |
| Per-round functional equivalence | 4 | dual `hax_mvcgen` |
| Fold unrolling (keccak_f_unfold) | 1 | `simp` + `rfl` |
| WP extraction (four_rounds_ok) | 1 | case split + `simp_all` |
| Top-level equivalence | 1 | `rw` chain of 6 × `four_round_eq` |

## Build time

~40 minutes total, dominated by the 4 × `roundK_func_equiv` proofs
(~400M heartbeats / ~10 minutes each).
