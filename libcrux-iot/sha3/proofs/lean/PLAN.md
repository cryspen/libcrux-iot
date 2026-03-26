# Compositional Round Proof — Implementation Plan

Branch: `alex/compositional-round-proof`
Working dir: `/Users/karthik/libcrux-iot-lean/libcrux-iot/sha3/proofs/lean`

## Goal

Replace monolithic `round_equiv.lean` (4 × 400M heartbeats = 73% of build) with
compositional proofs: theta_lift + prc_lift → round equiv.

## Current State

### Files on branch:
- `extraction/lift_defs.lean` — definitions (lift, lift_lane_bv, impl_perm, etc.) ✅ compiles
- `extraction/spec_decomp.lean` — spec_theta_unrolled, spec_prc_unrolled, decomposition ✅ compiles
- `extraction/theta_lift.lean` — theta_comp_spec_local (2M, proven) + theta_lift_spec (**sorry**) ✅ compiles
- `extraction/prc_lift.lean` — prc_lift_spec (**sorry**, needs rotation/chi lemmas + WP delta)

### What's proven:
- theta_comp_spec_local: impl theta produces correct d values (2M heartbeats)
- All lifting lemmas: lift_xor, lift_td, lift_xor5 (by bv_decide, fast)
- Composition: theta_lift + prc_lift → round_equiv (type-checked in lean_run_code)

## Next Steps (in order)

### Step 1: Prove theta_lift_spec (pure algebraic bridge)

The theorem: after impl theta, spec_theta_unrolled(lift(s)) = lift_theta_applied(result).

**Approach**: Use `Triple.of_entails_right` to weaken `theta_comp_spec_local`:

    apply Triple.of_entails_right _ _ _ _ (theta_comp_spec_local s)
    apply PostCond.entails.of_left_entails; intro r
    rw [← SPred.entails_true_intro]
    exact SPred.pure_intro fun ⟨hd0z0, hd0z1, ..., hst, hi⟩ => by
      -- 1. Substitute r.st = s.st (from hst)
      -- 2. Substitute concrete d values (from hd0z0 etc.)
      -- 3. Unfold spec_theta_unrolled and lift_theta_applied
      -- 4. Apply simp [lift_xor, lift_td, lift_xor5, u32_xor_toBitVec, rot32]
      -- 5. Close with rfl

**Critical**: Do NOT unfold `lift`, `lift_lane`, `spread_to_even`, or `lift_lane_bv`.
They must stay opaque. Only use the lifting rewrite lemmas.

Key simp lemmas needed (all rfl or by bv_decide):
- `u32_xor_toBitVec : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec`
- `u32_ofBitVec_toBitVec : (UInt32.ofBitVec x).toBitVec = x`
- `u64_ofBitVec_xor : UInt64.ofBitVec (a ^^^ b) = UInt64.ofBitVec a ^^^ UInt64.ofBitVec b`
- `lift_xor`, `lift_td`, `lift_xor5` (proven before @[local irreducible])

The pure bridge should be fast since all terms are small (lift_lane_bv is irreducible).
Individual lane equations verified in lean_run_code.

### Step 2: Prove prc_lift_spec

Same pattern as theta_lift but for rho+pi+chi+iota.

prc_lift.lean already has all 25 rotation lemmas + chi/xor/and/not lifting lemmas.
Needs:
- WP delta block for RC_INTERLEAVED access (same as existing prc1_proof)
- `@[local irreducible] spread_to_even lift_lane_bv`

Two options:
- **Option A**: Combined hax_mvcgen on impl prc1+prc2 + spec_prc_unrolled (80M, tested)
- **Option B**: Separate impl prc spec + pure algebraic bridge (safer, more code)

### Step 3: Compose theta_lift + prc_lift → round_equiv

Triple.bind to chain, then spec_round_decomp to rewrite. Pure plumbing, already type-checked.

### Step 4: Replicate for rounds 1-3 and replace round_equiv.lean
