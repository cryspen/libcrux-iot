import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3

/-! ## Spec decomposition for compositional round proofs

We decompose `spec_round` (theta ∘ rho ∘ pi ∘ chi ∘ iota) into two stages
that match the implementation structure:
  1. `spec_theta` = theta step
  2. `spec_prc`   = rho ∘ pi ∘ chi ∘ iota (everything after theta)

This enables proving per-step lifting separately and composing,
instead of one monolithic proof for the entire round.
-/

/-- Spec theta step: just hacspec theta. -/
def spec_theta (state : RustArray u64 25) : RustM (RustArray u64 25) :=
  hacspec_sha3.keccak_f.theta state

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
