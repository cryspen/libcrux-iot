/-
  Round-1 ρ∘π∘χ∘ι lift spec (stub; body `sorry`).

  Same shape as `prc_lift_spec` (round 0) but on the round-1 impl chain.
  The output `lift_perm` uses `impl_perm` composed with itself
  (`impl_perm ∘ impl_perm`), because the input state is already in the
  round-0 layout and round 1 advances by one more `impl_perm`.

  Kept in its own file so adding/proving it does not invalidate the
  round-0 cascade's `.olean` (60s per-file verification policy).
-/
import LibcruxIotSha3.Equivalence.PrcLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

-- @[spec] (added when proof is filled in; omitted here to avoid
-- polluting mvcgen's candidate space while body is `sorry`)
theorem prc_lift_spec_1 (s : state.KeccakState) (hi_lt : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let r1 ← keccak.keccakf1600_round1_pi_rho_chi_1 0#usize s
        keccak.keccakf1600_round1_pi_rho_chi_2 r1)
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled (lift_theta_applied s)
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm) impl_swap)).holds ⌝ ⦄ := by
  sorry

end libcrux_iot_sha3.Equivalence
