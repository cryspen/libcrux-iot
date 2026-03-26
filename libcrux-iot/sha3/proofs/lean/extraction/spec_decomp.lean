import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3

/-! ## Spec decomposition for compositional round proofs

We decompose `spec_round` (theta ∘ rho ∘ pi ∘ chi ∘ iota) into two stages
that match the implementation structure:
  1. `spec_theta` = theta step
  2. `spec_prc`   = rho ∘ pi ∘ chi ∘ iota (everything after theta)

The unrolled versions avoid `createi`/`Vector.mapM` which can't be
reduced by simp in the WP monad.
-/

/-- Spec theta step: just hacspec theta. -/
def spec_theta (state : RustArray u64 25) : RustM (RustArray u64 25) :=
  hacspec_sha3.keccak_f.theta state

/-- Spec theta, fully unrolled (no createi/Vector.mapM). -/
def spec_theta_unrolled (state : RustArray u64 25) : RustM (RustArray u64 25) := do
  let c0 := state.toVec[0] ^^^ state.toVec[1] ^^^ state.toVec[2] ^^^ state.toVec[3] ^^^ state.toVec[4]
  let c1 := state.toVec[5] ^^^ state.toVec[6] ^^^ state.toVec[7] ^^^ state.toVec[8] ^^^ state.toVec[9]
  let c2 := state.toVec[10] ^^^ state.toVec[11] ^^^ state.toVec[12] ^^^ state.toVec[13] ^^^ state.toVec[14]
  let c3 := state.toVec[15] ^^^ state.toVec[16] ^^^ state.toVec[17] ^^^ state.toVec[18] ^^^ state.toVec[19]
  let c4 := state.toVec[20] ^^^ state.toVec[21] ^^^ state.toVec[22] ^^^ state.toVec[23] ^^^ state.toVec[24]
  let d0 := c4 ^^^ UInt64.ofBitVec (c1.toBitVec.rotateLeft 1)
  let d1 := c0 ^^^ UInt64.ofBitVec (c2.toBitVec.rotateLeft 1)
  let d2 := c1 ^^^ UInt64.ofBitVec (c3.toBitVec.rotateLeft 1)
  let d3 := c2 ^^^ UInt64.ofBitVec (c4.toBitVec.rotateLeft 1)
  let d4 := c3 ^^^ UInt64.ofBitVec (c0.toBitVec.rotateLeft 1)
  pure (RustArray.ofVec #v[
    state.toVec[0] ^^^ d0, state.toVec[1] ^^^ d0, state.toVec[2] ^^^ d0, state.toVec[3] ^^^ d0, state.toVec[4] ^^^ d0,
    state.toVec[5] ^^^ d1, state.toVec[6] ^^^ d1, state.toVec[7] ^^^ d1, state.toVec[8] ^^^ d1, state.toVec[9] ^^^ d1,
    state.toVec[10] ^^^ d2, state.toVec[11] ^^^ d2, state.toVec[12] ^^^ d2, state.toVec[13] ^^^ d2, state.toVec[14] ^^^ d2,
    state.toVec[15] ^^^ d3, state.toVec[16] ^^^ d3, state.toVec[17] ^^^ d3, state.toVec[18] ^^^ d3, state.toVec[19] ^^^ d3,
    state.toVec[20] ^^^ d4, state.toVec[21] ^^^ d4, state.toVec[22] ^^^ d4, state.toVec[23] ^^^ d4, state.toVec[24] ^^^ d4])

/-- spec_theta_unrolled equals spec_theta (both compute the same theta step).
    Proof deferred: requires unrolling Vector.mapM in the WP monad. -/
theorem spec_theta_unrolled_eq (state : RustArray u64 25) :
    spec_theta state = spec_theta_unrolled state := by
  sorry

/-- Spec post-theta step: rho + pi + chi + iota. -/
def spec_prc (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.rho state
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

/-- spec_round decomposes as spec_prc ∘ spec_theta. -/
theorem spec_round_decomp (state : RustArray u64 25) (round : usize) :
    (do let s ← hacspec_sha3.keccak_f.theta state
        let s ← hacspec_sha3.keccak_f.rho s
        let s ← hacspec_sha3.keccak_f.pi s
        let s ← hacspec_sha3.keccak_f.chi s
        hacspec_sha3.keccak_f.iota s round) =
    (do let s ← spec_theta state
        spec_prc s round) := by
  unfold spec_theta spec_prc
  rfl
