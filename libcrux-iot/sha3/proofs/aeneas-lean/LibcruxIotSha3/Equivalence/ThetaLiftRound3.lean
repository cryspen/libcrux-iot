/-
  Round-3 θ lift spec (stub; body `sorry`).
-/
import LibcruxIotSha3.Equivalence.ThetaLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

-- @[spec] (added when proof is filled in)
set_option maxHeartbeats 16000000 in
theorem theta_lift_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r_impl => ⌜
      r_impl.i = s.i ∧
      (do
        let r_spec ← keccak_f.theta_unrolled
          (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap)
        pure (r_spec = lift_theta_applied r_impl)).holds ⌝ ⦄ := by
  sorry

end libcrux_iot_sha3.Equivalence
