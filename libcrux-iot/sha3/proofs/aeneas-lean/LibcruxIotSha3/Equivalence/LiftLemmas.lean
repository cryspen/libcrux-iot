/-
  Algebraic lifting lemmas for `lift_lane_bv` and `spread_to_even`.

  Every lemma here is a pure BitVec identity discharged by `bv_decide`,
  reducing equality of two `lift_lane_bv ... ... ?` expressions to a
  decidable SAT instance over BitVec primitives. After these are
  established, downstream proof files mark `spread_to_even` and
  `lift_lane_bv` `@[local irreducible]` — otherwise every later simp
  unfolds them into a six-step parallel-bit-deposit cascade × 25 lanes
  and the term sizes blow up.

  ## Catalog

  - **Rotation table** (`rot_N` for the 25 ρ offsets used by Keccak):
    converts a 64-bit rotation of a lifted lane to two 32-bit rotations
    on the interleaved halves. Even `N` rotates both halves by `N/2`
    without swapping; odd `N` swaps the halves and adjusts.
  - **Bitwise distributivity** (`lift_xor`/`lift_and`/`lift_not`):
    XOR/AND/NOT commute with lifting.
  - **Step-specific composites** (`lift_chi`/`lift_xor5`/`lift_td`/
    `lift_rot1`): the exact patterns that show up in the post-mvcgen
    goals for θ and ρ∘π∘χ.
-/
import LibcruxIotSha3.Equivalence.Lift
import Std.Tactic.BVDecide

namespace libcrux_iot_sha3.Equivalence

/-! ## Rotation lifting: even offsets

For even `N`, a 64-bit rotation of a lifted lane equals lifting each
32-bit half rotated by `N/2`. -/

theorem rot_0 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 0 = lift_lane_bv (z0.rotateLeft 0) (z1.rotateLeft 0) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_2 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 2 = lift_lane_bv (z0.rotateLeft 1) (z1.rotateLeft 1) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_6 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 6 = lift_lane_bv (z0.rotateLeft 3) (z1.rotateLeft 3) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_8 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 8 = lift_lane_bv (z0.rotateLeft 4) (z1.rotateLeft 4) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_10 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 10 = lift_lane_bv (z0.rotateLeft 5) (z1.rotateLeft 5) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_14 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 14 = lift_lane_bv (z0.rotateLeft 7) (z1.rotateLeft 7) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_18 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 18 = lift_lane_bv (z0.rotateLeft 9) (z1.rotateLeft 9) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_20 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 20 = lift_lane_bv (z0.rotateLeft 10) (z1.rotateLeft 10) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_28 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 28 = lift_lane_bv (z0.rotateLeft 14) (z1.rotateLeft 14) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_36 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 36 = lift_lane_bv (z0.rotateLeft 18) (z1.rotateLeft 18) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_44 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 44 = lift_lane_bv (z0.rotateLeft 22) (z1.rotateLeft 22) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_56 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 56 = lift_lane_bv (z0.rotateLeft 28) (z1.rotateLeft 28) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_62 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 62 = lift_lane_bv (z0.rotateLeft 31) (z1.rotateLeft 31) := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-! ## Rotation lifting: odd offsets

For odd `N`, the halves swap. `z0` is taken from `z1.rotateLeft ((N+1)/2)`
and `z1` is taken from `z0.rotateLeft (N/2)`. -/

theorem rot_1 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 1 = lift_lane_bv (z1.rotateLeft 1) (z0.rotateLeft 0) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_3 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 3 = lift_lane_bv (z1.rotateLeft 2) (z0.rotateLeft 1) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_15 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 15 = lift_lane_bv (z1.rotateLeft 8) (z0.rotateLeft 7) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_21 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 21 = lift_lane_bv (z1.rotateLeft 11) (z0.rotateLeft 10) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_25 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 25 = lift_lane_bv (z1.rotateLeft 13) (z0.rotateLeft 12) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_27 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 27 = lift_lane_bv (z1.rotateLeft 14) (z0.rotateLeft 13) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_39 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 39 = lift_lane_bv (z1.rotateLeft 20) (z0.rotateLeft 19) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_41 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 41 = lift_lane_bv (z1.rotateLeft 21) (z0.rotateLeft 20) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_43 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 43 = lift_lane_bv (z1.rotateLeft 22) (z0.rotateLeft 21) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_45 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 45 = lift_lane_bv (z1.rotateLeft 23) (z0.rotateLeft 22) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_55 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 55 = lift_lane_bv (z1.rotateLeft 28) (z0.rotateLeft 27) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem rot_61 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 61 = lift_lane_bv (z1.rotateLeft 31) (z0.rotateLeft 30) := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-! ## Bitwise distributivity over lifting -/

@[agrind =, grind =]
theorem lift_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

@[agrind =, grind =]
theorem lift_and (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 &&& b0) (a1 &&& b1) = lift_lane_bv a0 a1 &&& lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

@[agrind =, grind =]
theorem lift_not (a0 a1 : BitVec 32) :
    lift_lane_bv (~~~a0) (~~~a1) = ~~~(lift_lane_bv a0 a1) := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-! ## Step-specific composites -/

/-- χ step lifting: `a ⊕ (¬b ∧ c)` distributes through interleaved
    representation. -/
theorem lift_chi (bx0_z0 bx0_z1 bx1_z0 bx1_z1 bx2_z0 bx2_z1 : BitVec 32) :
    lift_lane_bv (bx0_z0 ^^^ ((~~~bx1_z0) &&& bx2_z0))
                 (bx0_z1 ^^^ ((~~~bx1_z1) &&& bx2_z1)) =
    lift_lane_bv bx0_z0 bx0_z1 ^^^
      ((~~~(lift_lane_bv bx1_z0 bx1_z1)) &&& lift_lane_bv bx2_z0 bx2_z1) := by
  simp only [lift_xor, lift_not, lift_and]

/-- θ-apply lifting: XOR with a `d`-value distributes through lifting. -/
theorem lift_theta_apply (a0 a1 d0 d1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ d0) (a1 ^^^ d1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv d0 d1 := by
  simp only [lift_xor]

/-- θ-d structure: the interleaved θ-d computation lifts correctly.
    `lift(cL ⊕ rot(cR,1), cL' ⊕ cR') = lift(cL,cL') ⊕ rotateLeft(lift(cR,cR'),1)`. -/
@[agrind =, grind =]
theorem lift_td (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) =
    lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-- Single odd-1 rotation: halves swap with adjusted sub-rotations.
    `rotateLeft(lift(z0,z1), 1) = lift(rot(z1,1), z0)`. -/
@[agrind =, grind =]
theorem lift_rot1 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 1 = lift_lane_bv (z1.rotateLeft 1) z0 := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-- XOR of 5 lanes distributes through interleaved lifting. Used for the
    C-row computation in θ. -/
@[agrind =, grind =]
theorem lift_xor5 (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0 ^^^ c0 ^^^ d0 ^^^ e0)
                 (a1 ^^^ b1 ^^^ c1 ^^^ d1 ^^^ e1) =
    lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 ^^^ lift_lane_bv c0 c1 ^^^
      lift_lane_bv d0 d1 ^^^ lift_lane_bv e0 e1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

end libcrux_iot_sha3.Equivalence
