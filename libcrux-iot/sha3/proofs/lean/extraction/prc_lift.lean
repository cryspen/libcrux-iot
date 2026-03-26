import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import extraction.spec_decomp
import extraction.theta_lift
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## PRC lifting: impl prc1+prc2 output lifts to spec rho+pi+chi+iota output

After `keccakf1600_round0_pi_rho_chi_1` + `keccakf1600_round0_pi_rho_chi_2`,
the result state, when lifted with `impl_perm`, equals `spec_prc(lift_theta_applied(s), s.i)`.

`lift_theta_applied(s)` captures the theta-applied state: each lane `i` has
`lift(st[i] ⊕ d[i/5])`, which is the spec theta output.
-/

/-- After prc1+prc2, the lifted-with-permutation result equals spec_prc of theta-applied state. -/
set_option maxRecDepth 2000 in
open Std.Do in
theorem prc_lift_spec (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
       libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      spec_prc (lift_theta_applied s) s.i = .ok (lift_perm r impl_perm)
    ⌝ ⦄ := by
  sorry
