import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import extraction.spec_decomp
import extraction.step_equiv
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## PRC lifting: impl prc1+prc2 output lifts to spec rho+pi+chi+iota output

After `keccakf1600_round0_pi_rho_chi_1` + `keccakf1600_round0_pi_rho_chi_2`,
the result state, when lifted with `impl_perm`, equals `spec_prc(theta_applied, round)`.

The `theta_applied` parameter is the spec-level theta output (from `theta_lift_spec`).
The impl reads `s.st` and `s.d` to apply theta_apply + rho + pi + chi + iota in-place.
-/

/-- After prc1+prc2, the lifted-with-permutation result equals spec_prc of theta output. -/
set_option maxRecDepth 2000 in
open Std.Do in
theorem prc_lift_spec (s : KeccakState) (theta_applied : RustArray u64 25)
    (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
       libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      spec_prc theta_applied s.i = .ok (lift_perm r impl_perm)
    ⌝ ⦄ := by
  sorry
