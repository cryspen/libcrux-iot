/-
  Round-2 ρ∘π∘χ∘ι lift spec (stub; body `sorry`).
-/
import LibcruxIotSha3.Equivalence.PrcLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

-- @[spec] (added when proof is filled in)
theorem prc_lift_spec_2 (s : state.KeccakState) (hi_lt : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let r1 ← keccak.keccakf1600_round2_pi_rho_chi_1 0#usize s
        keccak.keccakf1600_round2_pi_rho_chi_2 r1)
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled (lift_theta_applied s)
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl
                  (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))).holds ⌝ ⦄ := by
  sorry

end libcrux_iot_sha3.Equivalence
