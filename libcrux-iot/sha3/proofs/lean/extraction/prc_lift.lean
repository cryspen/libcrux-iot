import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import extraction.spec_decomp
import extraction.lift_defs
import extraction.theta_lift
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## PRC lifting: impl prc1+prc2 output lifts to spec rho+pi+chi+iota output -/

-- Rotation lifting lemmas (even rotations: both halves rotate by k)
private theorem rot_0 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 0 = lift_lane_bv (z0.rotateLeft 0) (z1.rotateLeft 0) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_2 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 2 = lift_lane_bv (z0.rotateLeft 1) (z1.rotateLeft 1) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_6 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 6 = lift_lane_bv (z0.rotateLeft 3) (z1.rotateLeft 3) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_8 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 8 = lift_lane_bv (z0.rotateLeft 4) (z1.rotateLeft 4) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_10 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 10 = lift_lane_bv (z0.rotateLeft 5) (z1.rotateLeft 5) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_14 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 14 = lift_lane_bv (z0.rotateLeft 7) (z1.rotateLeft 7) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_18 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 18 = lift_lane_bv (z0.rotateLeft 9) (z1.rotateLeft 9) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_20 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 20 = lift_lane_bv (z0.rotateLeft 10) (z1.rotateLeft 10) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_28 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 28 = lift_lane_bv (z0.rotateLeft 14) (z1.rotateLeft 14) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_36 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 36 = lift_lane_bv (z0.rotateLeft 18) (z1.rotateLeft 18) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_44 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 44 = lift_lane_bv (z0.rotateLeft 22) (z1.rotateLeft 22) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_56 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 56 = lift_lane_bv (z0.rotateLeft 28) (z1.rotateLeft 28) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_62 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 62 = lift_lane_bv (z0.rotateLeft 31) (z1.rotateLeft 31) := by unfold lift_lane_bv spread_to_even; bv_decide
-- Odd rotations: z0/z1 swap with adjusted rotation
private theorem rot_1 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 1 = lift_lane_bv (z1.rotateLeft 1) (z0.rotateLeft 0) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_3 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 3 = lift_lane_bv (z1.rotateLeft 2) (z0.rotateLeft 1) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_15 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 15 = lift_lane_bv (z1.rotateLeft 8) (z0.rotateLeft 7) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_21 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 21 = lift_lane_bv (z1.rotateLeft 11) (z0.rotateLeft 10) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_25 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 25 = lift_lane_bv (z1.rotateLeft 13) (z0.rotateLeft 12) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_27 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 27 = lift_lane_bv (z1.rotateLeft 14) (z0.rotateLeft 13) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_39 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 39 = lift_lane_bv (z1.rotateLeft 20) (z0.rotateLeft 19) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_41 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 41 = lift_lane_bv (z1.rotateLeft 21) (z0.rotateLeft 20) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_43 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 43 = lift_lane_bv (z1.rotateLeft 22) (z0.rotateLeft 21) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_45 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 45 = lift_lane_bv (z1.rotateLeft 23) (z0.rotateLeft 22) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_55 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 55 = lift_lane_bv (z1.rotateLeft 28) (z0.rotateLeft 27) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem rot_61 (z0 z1 : BitVec 32) : (lift_lane_bv z0 z1).rotateLeft 61 = lift_lane_bv (z1.rotateLeft 31) (z0.rotateLeft 30) := by unfold lift_lane_bv spread_to_even; bv_decide

-- Bitwise lifting lemmas
private theorem lift_xor (a0 a1 b0 b1 : BitVec 32) : lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem lift_and (a0 a1 b0 b1 : BitVec 32) : lift_lane_bv (a0 &&& b0) (a1 &&& b1) = lift_lane_bv a0 a1 &&& lift_lane_bv b0 b1 := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem lift_not (a0 a1 : BitVec 32) : lift_lane_bv (~~~a0) (~~~a1) = ~~~(lift_lane_bv a0 a1) := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem lift_chi (bx0_z0 bx0_z1 bx1_z0 bx1_z1 bx2_z0 bx2_z1 : BitVec 32) :
    lift_lane_bv (bx0_z0 ^^^ ((~~~bx1_z0) &&& bx2_z0)) (bx0_z1 ^^^ ((~~~bx1_z1) &&& bx2_z1)) =
    lift_lane_bv bx0_z0 bx0_z1 ^^^ ((~~~(lift_lane_bv bx1_z0 bx1_z1)) &&& lift_lane_bv bx2_z0 bx2_z1) := by
  simp only [lift_xor, lift_not, lift_and]
private theorem lift_theta_apply (a0 a1 d0 d1 : BitVec 32) : lift_lane_bv (a0 ^^^ d0) (a1 ^^^ d1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv d0 d1 := by simp only [lift_xor]
private theorem lift_theta_d (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) = lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by unfold lift_lane_bv spread_to_even; bv_decide

abbrev rot32' (x : u32) (n : Nat) : u32 := UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n)

/-- After prc1+prc2, the lifted-with-permutation result equals spec_prc_unrolled of theta-applied state. -/
set_option maxHeartbeats 80000000 in
set_option maxRecDepth 5000 in
open Std.Do in
theorem prc_lift_spec (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← do
         let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
         libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
       let r_spec ← spec_prc_unrolled (lift_theta_applied s) s.i
       pure (r_spec = lift_perm r_impl impl_perm)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  sorry -- TODO: needs optimization (see PLAN.md Step 2)
