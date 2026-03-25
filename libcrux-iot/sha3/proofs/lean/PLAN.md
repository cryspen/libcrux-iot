# Plan: Eliminate Sorries in equiv.lean

## Context

We have 8 sorry'd theorems in `extraction/equiv.lean` forming the proof chain for
the Keccak-f[1600] equivalence. The theorem stubs typecheck. Now we need to prove them.

**File to modify:** `extraction/equiv.lean`

## The 8 Sorries (in dependency order)

| # | Theorem | Line | Difficulty | Approach |
|---|---------|------|------------|----------|
| 1 | `lift_perm_id` | 648 | Trivial | simp/unfold |
| 2 | `rc_equiv` | 659 | Easy | interval_cases + native_decide |
| 3 | `pi_rho_chi_1_spec` | 691 | Hard | hax_mvcgen (~30M heartbeats) |
| 4 | `pi_rho_chi_2_spec` | 704 | Hard | hax_mvcgen (~40M heartbeats) |
| 5 | `pi_rho_chi_round0_lift` | 717 | Hard | strengthen postcondition + algebraic lemmas |
| 6 | `round0_equiv` | 736 | Medium | compose theta_comp_spec + pi_rho_chi specs |
| 7 | `four_rounds_equiv` | 753 | Medium | compose 4 round equivs |
| 8 | `equivalence` | 772 | Medium | compose 6 x four_rounds_equiv |

Items 5-8 currently have `True` as postcondition -- they need to be **strengthened first**
before the sorry can be meaningfully eliminated.

## Key Architectural Insight: The Pi Permutation

The implementation does pi_rho_chi **in-place**: reads from pi-permuted source positions,
applies rho+chi+iota, writes back without materializing pi as data movement.

- `impl_perm(5*x + z) = 5*x + (3*z + 2*x) % 5` maps impl lane index to spec lane index
- Cycle structure: 5 fixed points + 5 disjoint 4-cycles
- **impl_perm^4 = id** (proven by `decide`) -- after each 4-round block, state is standard
- This is why the implementation repeats the same 4-round block 6 times for 24 rounds

## Execution Plan

### Step 1: `lift_perm_id` (trivial)

Current: `simp only [lift_perm, lift, id]; sorry`
Goal after simp is `Vector.ofFn` with `(id i).val` vs `i` (Fin coercion).
Fix with `congr`/`ext`/`simp [Fin.val]` or unfold `id` further.

### Step 2: `rc_equiv` (round constant equivalence)

Strategy: case-split on `i` (24 cases) and use `native_decide` on each.

```lean
theorem rc_equiv (i : Nat) (hi : i < 24) : ... := by
  interval_cases i <;> native_decide
```

May need `simp` to unfold `RustM.of_isOk`, `RustArray.ofVec`, `lift_lane_bv`,
`spread_to_even` before `native_decide`. If too slow, try `bv_decide` or `decide`.

### Step 3: `pi_rho_chi_1_spec` (monadic spec, ~370 lines)

Follow the theta_comp_proof pattern:

```lean
set_option maxHeartbeats 30000000 in
open Std.Do in
theorem pi_rho_chi_1_spec ... := by
  hax_mvcgen [core_models.num.Impl_8.rotate_left,
              instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify]
  all_goals (first | intro h; subst h | skip)
  all_goals simp (config := { decide := true })
    [getElemResult, core_models.ops.index.Index.index]
  all_goals (first | (simp_all [Vector.getElem_set]; try rfl) | skip)
  all_goals (reduce_usize_sizes;
             simp (config := { decide := true }) [Vector.getElem_set]; try rfl)
  all_goals (repeat' constructor)
  all_goals (first | rfl | skip)
  all_goals (simp_all [Vector.getElem_set, rot32]; try rfl)
```

Additional unfolds vs theta: `Classify.classify` (= `pure x`), possibly RC arrays.
If 30M heartbeats insufficient: increase to 100M or split into per-row specs.

### Step 4: `pi_rho_chi_2_spec` (same approach, ~547 lines)

Same tactic pattern, ~40M heartbeats. No iota/RC constants (pi_rho_chi_2 doesn't
touch round constants).

### Steps 5-8: Higher-level compositions (deferred)

Require strengthening `True` postconditions to real equivalence statements.
Depend on pi_rho_chi specs having full output-lane postconditions.

## Session Strategy

1. Prove `lift_perm_id` and `rc_equiv` (quick wins)
2. Attempt `pi_rho_chi_1_spec` with hax_mvcgen at 30M heartbeats
3. If time: `pi_rho_chi_2_spec`, then strengthen postconditions of 5-8

## Verification

After each proof: `PATH="$HOME/.elan/bin:$PATH" lake env lean extraction/equiv.lean`
Check sorry count (should decrease from 8).

## Critical Files

- `extraction/equiv.lean` -- main proof file (modify)
- `extraction/hacspec_sha3.lean` -- reference spec (read-only)
- `extraction/libcrux_iot_sha3.lean` -- implementation (read-only)
- `extraction/helpers.lean` -- Hax instances (read-only)
