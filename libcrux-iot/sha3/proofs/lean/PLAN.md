# Keccak-f[1600] Bit-Interleaved Equivalence Proof — Status & Plan

## Goal

Prove that the bit-interleaved implementation (`keccakf1600`) equals the
reference spec (`keccak_f`) when lifted from Lane2U32 to standard u64.

Main theorem in `extraction/equiv.lean`:
```lean
theorem equivalence (s : KeccakState) :
  hacspec_sha3.keccak_f.keccak_f (lift s) =
    (do pure (lift (← libcrux_iot_sha3.keccak.keccakf1600 s)))
```

## Current Status: 2 sorry remaining (four_rounds_equiv, equivalence)

### Proven theorems (no sorry):
| Theorem | Proof technique |
|---------|----------------|
| `lift_lane_bv_{xor,and,not,or}` (4) | `bv_decide` |
| `lift_lane_bv_rotate_{0,1,2,...,62}` (23) | `bv_decide` |
| `theta_c_lift`, `theta_d_lift`, `theta_apply_lift` | `simp [lift_lane_bv_xor]` |
| `chi_lane_lift` | `simp [lift_lane_bv_{xor,not,and}]` |
| `theta_c_x{0..4}_z{0,1}_spec` (10) | `theta_c_proof` macro |
| `theta_d_d{0..4}z{0,1}_spec` (10) | `theta_d_proof` macro |
| `theta_comp_spec` | `theta_comp_proof` macro (8M heartbeats) |
| `impl_perm_pow4_eq_id` | `decide` |
| `lift_perm_id` | `unfold + rfl` |
| `rc_equiv_aux` / `rc_equiv` | `decide` over Fin 24 |
| `pi_rho_chi_1_spec` | `hax_mvcgen` + `rw [dif_pos]` for WP (40M heartbeats) |
| `pi_rho_chi_2_spec` | `hax_mvcgen` (80M heartbeats, 3000 recDepth) |
| `pi_rho_chi_round0_lift` | `Triple.bind` composing prc1 + prc2 specs |
| `round0_equiv` | `Triple.bind` composing theta + prc1 + prc2 |
| `roundK_theta_spec` (rounds 1-3) | `theta_comp_proof` macro (8M each) |
| `roundK_prc1_spec` (rounds 1-3) | `hax_mvcgen` + `rw [dif_pos]` (40M each) |
| `roundK_prc2_spec` (rounds 1-3) | `prc2_proof` macro (80M each) |
| `roundK_compose` | Generic Triple.bind helper for 3-step round |

### Sorry #1: `four_rounds_equiv`
- **Structure**: `keccakf1600_4rounds` is a flat 12-step bind chain (4 rounds × 3 steps).
  After `unfold`, it doesn't group into 3-step blocks that `roundK_compose` expects.
- **Approach**: Either (a) 12 individual `Triple.bind` calls tracking `i.toNat` in Nat
  (avoids usize arithmetic issues with omega), or (b) prove bind reassociation to
  group into 4 × 3-step blocks.
- **Blocker**: usize arithmetic (`s.i + 1 + 1 = s.i + 2`) doesn't simplify automatically;
  needs explicit `USize64.toNat` conversion at each step.
- **All sub-step specs are proven** — only the composition plumbing remains.

### Sorry #2: `equivalence` (top-level)
- Composes 6 × `four_rounds_equiv` via `fold_range` + loop invariant.
- Use `Spec.forIn_monoLoopCombinator` from SpecLemmas.lean.
- Depends on `four_rounds_equiv`.

**Established composition patterns**:
- `Triple.bind` for sequencing Hoare triples
- `Triple.of_entails_right` + `PostCond.entails.of_left_entails` for weakening
- `strengthen_pre` / `weaken_to_true` / `triple_of_neg` helpers
- `by_cases` to bridge SPred preconditions to Lean-level hypotheses

## Key Architecture

### Bit-interleaved representation
- Each 64-bit Keccak lane stored as `Lane2U32 = { _0 : RustArray u32 2 }`
- `_0[0]` = even-indexed bits (z0), `_0[1]` = odd-indexed bits (z1)
- `lift_lane_bv z0 z1 = spread_to_even z0 ||| (spread_to_even z1 <<< 1)`

### The pi permutation
- Implementation does pi_rho_chi in-place (no data movement for pi)
- After each round, state is in `impl_perm`-permuted layout
- `impl_perm(5*x + z) = 5*x + (3*z + 2*x) % 5`
- Cycle structure: 5 fixed points + 5 disjoint 4-cycles
- **impl_perm^4 = id** — 4-round blocks return to standard layout
- Each of the 4 rounds (round0–round3) has specialized access patterns

### Implementation structure
- `keccakf1600` = 6 × `keccakf1600_4rounds`
- `keccakf1600_4rounds` = (theta → pi_rho_chi_1 → pi_rho_chi_2) × 4 rounds
- `pi_rho_chi_1`: rows y=0,1 (includes iota with RC_INTERLEAVED)
- `pi_rho_chi_2`: rows y=2,3,4 (no iota)
- Rounds 0–3 differ in get/set_with_zeta arguments (accumulated permutation)

### Proof tactic pattern (from theta, reused for pi_rho_chi)
```lean
hax_mvcgen [core_models.num.Impl_8.rotate_left,
            instGetElemResultOutputOfIndex_extraction,
            libcrux_secrets.traits.Classify.classify]
all_goals (first | intro h; subst h | skip)
all_goals simp (config := { decide := true, maxSteps := 200000 })
  [getElemResult, core_models.ops.index.Index.index]
all_goals (first | (simp_all (...) [Vector.getElem_set]; try rfl) | skip)
all_goals (reduce_usize_sizes; simp (...) [Vector.getElem_set]; try rfl)
all_goals (repeat' constructor)
all_goals (first | rfl | skip)
all_goals (first | (simp_all (...) [Vector.getElem_set, rot32]; try rfl) | skip)
all_goals (first | omega | simp_all | rfl | skip)
```

## Critical Files

- `extraction/equiv.lean` — main proof file
- `extraction/hacspec_sha3.lean` — reference spec (theta, rho, pi, chi, iota, keccak_f)
- `extraction/libcrux_iot_sha3.lean` — bit-interleaved implementation
- `extraction/helpers.lean` — Hax instances, Classify.classify = pure x
- `extraction/spec.lean` — alternative spec (not used in equiv proof)
- `.lake/packages/Hax/.../Std/Do/Triple/Basic.lean` — Hoare triple API
