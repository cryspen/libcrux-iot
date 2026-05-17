/-
  Round-3 ρ∘π∘χ∘ι lift spec (stub; body `sorry`).

  After round 3, the cumulative permutation is `impl_perm^[4] = id`
  (`impl_perm_pow4_eq_id`), so the output `lift_perm` uses `id`
  rather than four-fold composition.
-/
import LibcruxIotSha3.Equivalence.PrcLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

-- @[spec] (added when proof is filled in)
theorem prc_lift_spec_3 (s : state.KeccakState) (hi_lt : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let r1 ← keccak.keccakf1600_round3_pi_rho_chi_1 0#usize s
        keccak.keccakf1600_round3_pi_rho_chi_2 r1)
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled (lift_theta_applied s)
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl id impl_swap)).holds ⌝ ⦄ := by
  sorry

end libcrux_iot_sha3.Equivalence
