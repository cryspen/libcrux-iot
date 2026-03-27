import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import extraction.spec_decomp
import extraction.lift_defs
import extraction.theta_lift
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## PRC step: lifting proof (rho + pi + chi + iota)

Proves that the bit-interleaved prc implementation (pi_rho_chi_1 + pi_rho_chi_2)
produces the same result as `spec_prc_unrolled` applied to the lifted theta output.

### Rotation lifting lemmas

The Keccak rho step rotates each lane by a fixed offset. In the bit-interleaved
representation, a 64-bit rotation by `n` becomes:
- **Even n**: both halves rotate by `n/2` (no swap)
- **Odd n**: halves swap, z0 gets `rot(z1, (n+1)/2)`, z1 gets `rot(z0, n/2)`

All 25 rotation offsets used by Keccak are covered below (proven by `bv_decide`).

### Proof strategy

Same as theta_lift: `hax_mvcgen` runs on the impl ONLY (no spec/lift terms in hints),
then algebraic lifting lemmas connect the impl output to the spec in post-mvcgen simp.

Key optimization: `impl_perm`, `rot32'`, `lift_theta_applied`, `lift_perm` are NOT in
the `hax_mvcgen` hint list. They are only resolved in the post-mvcgen algebraic simp.
This reduces the WP from 80M heartbeats + 10GB to 20M heartbeats + 1.5GB.
-/

-- Rotation lifting: even rotations (both halves rotate by k, no swap)
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
-- Rotation lifting: odd rotations (halves swap with adjusted sub-rotation)
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

-- Bitwise lifting lemmas for chi step
private theorem lift_xor (a0 a1 b0 b1 : BitVec 32) : lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem lift_and (a0 a1 b0 b1 : BitVec 32) : lift_lane_bv (a0 &&& b0) (a1 &&& b1) = lift_lane_bv a0 a1 &&& lift_lane_bv b0 b1 := by unfold lift_lane_bv spread_to_even; bv_decide
private theorem lift_not (a0 a1 : BitVec 32) : lift_lane_bv (~~~a0) (~~~a1) = ~~~(lift_lane_bv a0 a1) := by unfold lift_lane_bv spread_to_even; bv_decide
/-- Chi step lifting: a ⊕ (¬b ∧ c) distributes through interleaved representation. -/
private theorem lift_chi (bx0_z0 bx0_z1 bx1_z0 bx1_z1 bx2_z0 bx2_z1 : BitVec 32) :
    lift_lane_bv (bx0_z0 ^^^ ((~~~bx1_z0) &&& bx2_z0)) (bx0_z1 ^^^ ((~~~bx1_z1) &&& bx2_z1)) =
    lift_lane_bv bx0_z0 bx0_z1 ^^^ ((~~~(lift_lane_bv bx1_z0 bx1_z1)) &&& lift_lane_bv bx2_z0 bx2_z1) := by
  simp only [lift_xor, lift_not, lift_and]
/-- Theta-apply lifting: XOR with d-value distributes through lifting. -/
private theorem lift_theta_apply (a0 a1 d0 d1 : BitVec 32) : lift_lane_bv (a0 ^^^ d0) (a1 ^^^ d1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv d0 d1 := by simp only [lift_xor]
/-- Theta-d structure: the interleaved theta-d computation lifts correctly. -/
private theorem lift_theta_d (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) = lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by unfold lift_lane_bv spread_to_even; bv_decide

/-- Alternative rotation abbreviation used in prc implementation. -/
abbrev rot32' (x : u32) (n : Nat) : u32 := UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n)

section PrcLift
-- Mark irreducible AFTER proving all lifting lemmas above.
attribute [local irreducible] spread_to_even lift_lane_bv

/-- PRC lifting: the bit-interleaved prc1+prc2 output, after lifting and permutation,
    equals `spec_prc_unrolled` applied to the lifted theta-applied state.

    Proof outline:
    1. Unfold `spec_prc_unrolled` to expose the spec computation
    2. `hax_mvcgen` on impl only (no lift/spec terms in WP — critical for performance)
    3. Post-mvcgen simp closes WP goals with concrete index arithmetic
    4. Algebraic simp with lifting lemmas connects impl output to spec
    5. WP delta block handles the RC_INTERLEAVED round-constant access -/
set_option maxHeartbeats 20000000 in
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
  unfold spec_prc_unrolled
  -- hax_mvcgen on impl ONLY: no lift_theta_applied/lift_perm/impl_perm/rot32' in hints
  hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify]
  -- Close WP goals
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 200000 }) only [getElemResult, core_models.ops.index.Index.index,
    ↓reduceDIte, USize64.reduceToNat, USize64.add_zero, USize64.toNat_zero, ↓reduceIte,
    USize64.toBitVec_ofNat, bind_pure_comp, pure_bind, USize64.reduceAdd, map_pure,
    Vector.size, Nat.zero_lt_succ, bind_pure, Std.Do.WP.pure, Vector.getElem_set,
    Std.Do.SPred.down_pure, rot32,
    show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl,
    show (2 : usize).toNat = 2 from rfl, show (255 : usize).toNat = 255 from rfl]
  all_goals (repeat' constructor)
  all_goals (first | subst_vars; rfl | rfl | skip)
  -- Algebraic bridge: lift_theta_applied/lift_perm/impl_perm resolved HERE (not in mvcgen)
  all_goals (first | (simp only [lift_theta_applied, lta, lift_perm, lift_getElem,
    lift_xor, lift_and, lift_not, lift_chi, lift_theta_apply, lift_theta_d,
    rot32', impl_perm,
    rot_0, rot_1, rot_2, rot_3, rot_6, rot_8, rot_10, rot_14, rot_15, rot_18, rot_20, rot_21,
    rot_25, rot_27, rot_28, rot_36, rot_39, rot_41, rot_43, rot_44, rot_45, rot_55, rot_56, rot_61, rot_62,
    u64_ofBitVec_xor, u64_toBitVec_ofBitVec, u64_xor_toBitVec,
    u32_xor_toBitVec, u32_ofBitVec_toBitVec,
    Vector.getElem_set]; rfl) | skip)
  all_goals (first | omega | rfl | skip)
  -- WP delta block for RC_INTERLEAVED round-constant table access
  all_goals (open Std.Do in
    delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
    have h255 : USize64.toNat s.i < 255 := by omega
    rw [dif_pos h255, dif_pos h255]
    have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
      simp [BitVec.uaddOverflow]; omega
    rw [if_neg huadd]
    delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
    first | rfl | simp_all)

end PrcLift
