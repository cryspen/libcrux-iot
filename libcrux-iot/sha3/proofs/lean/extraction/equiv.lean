import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane
open libcrux_iot_sha3.state

/-! ## Lift: Interleaved Lane2U32 → standard u64

The implementation stores each 64-bit Keccak lane as two u32 values in
bit-interleaved form: `_0[0]` holds even-indexed bits, `_0[1]` holds
odd-indexed bits. We reconstruct the standard u64 by spreading these
bits back to their natural positions.
-/

/-- Spread 32 bits into even positions of a 64-bit value.
    Bit k of input → bit 2k of output. -/
def spread_to_even (x : BitVec 32) : BitVec 64 :=
  let x : BitVec 64 := x.zeroExtend 64
  let x := (x ||| (x <<< 16)) &&& 0x0000ffff0000ffff#64
  let x := (x ||| (x <<<  8)) &&& 0x00ff00ff00ff00ff#64
  let x := (x ||| (x <<<  4)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := (x ||| (x <<<  2)) &&& 0x3333333333333333#64
  let x := (x ||| (x <<<  1)) &&& 0x5555555555555555#64
  x

/-- Reconstruct a u64 from interleaved zeta components.
    Bit 2k of result = bit k of z0 (even bits),
    bit 2k+1 of result = bit k of z1 (odd bits). -/
def lift_lane_bv (z0 z1 : BitVec 32) : BitVec 64 :=
  spread_to_even z0 ||| (spread_to_even z1 <<< 1)

def lift_lane (l : Lane2U32) : u64 :=
  UInt64.ofBitVec (lift_lane_bv l._0.toVec[0].toBitVec l._0.toVec[1].toBitVec)

def lift (s : KeccakState) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i => lift_lane s.st.toVec[i])

/-! ## Core bitwise lemmas: operations commute with lift -/

@[simp]
theorem lift_lane_bv_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) =
    lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even
  bv_decide

@[simp]
theorem lift_lane_bv_and (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 &&& b0) (a1 &&& b1) =
    lift_lane_bv a0 a1 &&& lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even
  bv_decide

@[simp]
theorem lift_lane_bv_not (a0 a1 : BitVec 32) :
    lift_lane_bv (~~~a0) (~~~a1) =
    ~~~(lift_lane_bv a0 a1) := by
  unfold lift_lane_bv spread_to_even
  bv_decide

@[simp]
theorem lift_lane_bv_or (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ||| b0) (a1 ||| b1) =
    lift_lane_bv a0 a1 ||| lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even
  bv_decide

/-! ## Rotation equivalence

In the interleaved representation, u64 rotation by R corresponds to:
- Even R=2k: rotate both z0 and z1 by k
- Odd R=2k+1: new_z0 = rotateLeft(z1, k+1), new_z1 = rotateLeft(z0, k)
-/

-- Rotation by 0 (trivial)
@[simp]
theorem lift_lane_bv_rotate_0 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 0 =
    lift_lane_bv (z0.rotateLeft 0) (z1.rotateLeft 0) := by
  unfold lift_lane_bv spread_to_even
  bv_decide

-- Rotation by 1 (odd: 2*0+1, new_z0=rot(z1,1), new_z1=rot(z0,0))
@[simp]
theorem lift_lane_bv_rotate_1 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 1 =
    lift_lane_bv (z1.rotateLeft 1) (z0.rotateLeft 0) := by
  unfold lift_lane_bv spread_to_even
  bv_decide

-- Even rotations: rotateLeft (2k) = lift (rotateLeft k, rotateLeft k)
@[simp] theorem lift_lane_bv_rotate_2 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 2 = lift_lane_bv (z0.rotateLeft 1) (z1.rotateLeft 1) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_6 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 6 = lift_lane_bv (z0.rotateLeft 3) (z1.rotateLeft 3) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_8 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 8 = lift_lane_bv (z0.rotateLeft 4) (z1.rotateLeft 4) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_10 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 10 = lift_lane_bv (z0.rotateLeft 5) (z1.rotateLeft 5) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_14 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 14 = lift_lane_bv (z0.rotateLeft 7) (z1.rotateLeft 7) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_18 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 18 = lift_lane_bv (z0.rotateLeft 9) (z1.rotateLeft 9) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_20 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 20 = lift_lane_bv (z0.rotateLeft 10) (z1.rotateLeft 10) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_28 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 28 = lift_lane_bv (z0.rotateLeft 14) (z1.rotateLeft 14) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_36 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 36 = lift_lane_bv (z0.rotateLeft 18) (z1.rotateLeft 18) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_44 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 44 = lift_lane_bv (z0.rotateLeft 22) (z1.rotateLeft 22) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_56 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 56 = lift_lane_bv (z0.rotateLeft 28) (z1.rotateLeft 28) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_62 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 62 = lift_lane_bv (z0.rotateLeft 31) (z1.rotateLeft 31) := by
  unfold lift_lane_bv spread_to_even; bv_decide

-- Odd rotations: rotateLeft (2k+1) = lift (rotateLeft(z1, k+1), rotateLeft(z0, k))
@[simp] theorem lift_lane_bv_rotate_3 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 3 = lift_lane_bv (z1.rotateLeft 2) (z0.rotateLeft 1) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_15 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 15 = lift_lane_bv (z1.rotateLeft 8) (z0.rotateLeft 7) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_21 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 21 = lift_lane_bv (z1.rotateLeft 11) (z0.rotateLeft 10) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_25 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 25 = lift_lane_bv (z1.rotateLeft 13) (z0.rotateLeft 12) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_27 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 27 = lift_lane_bv (z1.rotateLeft 14) (z0.rotateLeft 13) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_39 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 39 = lift_lane_bv (z1.rotateLeft 20) (z0.rotateLeft 19) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_41 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 41 = lift_lane_bv (z1.rotateLeft 21) (z0.rotateLeft 20) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_43 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 43 = lift_lane_bv (z1.rotateLeft 22) (z0.rotateLeft 21) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_45 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 45 = lift_lane_bv (z1.rotateLeft 23) (z0.rotateLeft 22) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_55 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 55 = lift_lane_bv (z1.rotateLeft 28) (z0.rotateLeft 27) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_rotate_61 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 61 = lift_lane_bv (z1.rotateLeft 31) (z0.rotateLeft 30) := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-! ## Theta step equivalence (proof of concept)

The theta step computes:
  c[x]    = a[x,0] ⊕ a[x,1] ⊕ a[x,2] ⊕ a[x,3] ⊕ a[x,4]   (column parity)
  d[x]    = c[(x+4)%5] ⊕ rotateLeft(c[(x+1)%5], 1)            (theta diff)
  a'[x,y] = a[x,y] ⊕ d[x]                                      (apply diff)

In the interleaved representation, all these operations decompose per-zeta.
We prove that the interleaved computations produce correct lifted results.
-/

-- Column parity: XOR of 5 interleaved lanes lifts correctly.
-- This is what keccakf1600_round0_theta_c_x0_{z0,z1} computes.
theorem theta_c_lift (z0₀ z0₁ z1₀ z1₁ z2₀ z2₁ z3₀ z3₁ z4₀ z4₁ : BitVec 32) :
    lift_lane_bv (z0₀ ^^^ z1₀ ^^^ z2₀ ^^^ z3₀ ^^^ z4₀)
                 (z0₁ ^^^ z1₁ ^^^ z2₁ ^^^ z3₁ ^^^ z4₁) =
    lift_lane_bv z0₀ z0₁ ^^^ lift_lane_bv z1₀ z1₁ ^^^ lift_lane_bv z2₀ z2₁ ^^^
    lift_lane_bv z3₀ z3₁ ^^^ lift_lane_bv z4₀ z4₁ := by
  simp only [lift_lane_bv_xor]

-- Theta diff: d[0] = c[4] ⊕ rotateLeft(c[1], 1)
-- In interleaved form (rotation by 1 is odd: 2*0+1):
--   d[0].z0 = c[4].z0 ⊕ rotateLeft₃₂(c[1].z1, 1)
--   d[0].z1 = c[4].z1 ⊕ c[1].z0
theorem theta_d0_lift (c4_z0 c4_z1 c1_z0 c1_z1 : BitVec 32) :
    lift_lane_bv (c4_z0 ^^^ c1_z1.rotateLeft 1) (c4_z1 ^^^ c1_z0) =
    lift_lane_bv c4_z0 c4_z1 ^^^ (lift_lane_bv c1_z0 c1_z1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

-- General theta diff pattern: d[x] = c[(x+4)%5] ⊕ rotateLeft(c[(x+1)%5], 1)
-- All 5 d values follow the same pattern. Here's the general form:
theorem theta_d_lift (cL_z0 cL_z1 cR_z0 cR_z1 : BitVec 32) :
    lift_lane_bv (cL_z0 ^^^ cR_z1.rotateLeft 1) (cL_z1 ^^^ cR_z0) =
    lift_lane_bv cL_z0 cL_z1 ^^^ (lift_lane_bv cR_z0 cR_z1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

-- Applying d: a'[x,y] = a[x,y] ⊕ d[x]
-- This is pure XOR, which commutes with lift trivially.
theorem theta_apply_lift (a_z0 a_z1 d_z0 d_z1 : BitVec 32) :
    lift_lane_bv (a_z0 ^^^ d_z0) (a_z1 ^^^ d_z1) =
    lift_lane_bv a_z0 a_z1 ^^^ lift_lane_bv d_z0 d_z1 := by
  simp only [lift_lane_bv_xor]

/-! ## Chi step equivalence (proof of concept)

Chi computes: a'[x,y] = a[x,y] ⊕ (¬a[(x+1)%5, y] ∧ a[(x+2)%5, y])
This uses XOR, NOT, AND — all commute with lift.
-/

theorem chi_lane_lift (bx0_z0 bx0_z1 bx1_z0 bx1_z1 bx2_z0 bx2_z1 : BitVec 32) :
    lift_lane_bv (bx0_z0 ^^^ ((~~~bx1_z0) &&& bx2_z0))
                 (bx0_z1 ^^^ ((~~~bx1_z1) &&& bx2_z1)) =
    lift_lane_bv bx0_z0 bx0_z1 ^^^
      ((~~~(lift_lane_bv bx1_z0 bx1_z1)) &&& lift_lane_bv bx2_z0 bx2_z1) := by
  simp only [lift_lane_bv_xor, lift_lane_bv_not, lift_lane_bv_and]

/-! ## Iota step equivalence (proof of concept)

Iota XORs a round constant into lane a[0,0].
The interleaved round constants RC_INTERLEAVED_0[i] and RC_INTERLEAVED_1[i]
should deinterleave to the standard ROUND_CONSTANTS[round].

For a full proof, we'd need:
  lift_lane_bv RC_INTERLEAVED_0[i] RC_INTERLEAVED_1[i] = ROUND_CONSTANTS[round]
for the corresponding round/i relationship.
-/

/-! ## Monadic plumbing: connecting implementation to spec via Hoare triples

The proof pattern for each theta_c function:
1. `hax_mvcgen []` generates weakest-precondition verification conditions
2. `intro + subst` substitutes the first array access
3. `simp` with `getElemResult` + `core_models.ops.index.Index.index` reduces:
   - Arithmetic overflow checks (concrete usize operations)
   - RustArray and Lane2U32 indexing
4. For non-zero array indices, `Vector.size` must be reduced to a numeral
   so `dite` conditions in `update_at_usize` can evaluate
5. `Vector.getElem_set` closes the final equality
-/

-- Reusable tactic for reducing usize-related sizes in wp goals
macro "reduce_usize_sizes" : tactic =>
  `(tactic| simp only [Vector.size, show (5 : usize).toNat = 5 from rfl,
                        show (25 : usize).toNat = 25 from rfl,
                        show (2 : usize).toNat = 2 from rfl])

-- Reusable proof strategy for theta_c-like specs
macro "theta_c_proof" : tactic =>
  `(tactic| (
    hax_mvcgen []
    intro h₁; subst h₁
    simp (config := { decide := true }) [getElemResult, core_models.ops.index.Index.index]
    all_goals (first | (simp_all [Vector.getElem_set]; try rfl) | skip)
    all_goals (reduce_usize_sizes;
               simp (config := { decide := true }) [Vector.getElem_set];
               try rfl)))

open Std.Do in
theorem theta_c_x0_z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.c.toVec[0]._0.toVec[0] =
        s.st.toVec[0]._0.toVec[0] ^^^ s.st.toVec[1]._0.toVec[0] ^^^
        s.st.toVec[2]._0.toVec[0] ^^^ s.st.toVec[3]._0.toVec[0] ^^^
        s.st.toVec[4]._0.toVec[0] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x0_z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.c.toVec[0]._0.toVec[1] =
        s.st.toVec[0]._0.toVec[1] ^^^ s.st.toVec[1]._0.toVec[1] ^^^
        s.st.toVec[2]._0.toVec[1] ^^^ s.st.toVec[3]._0.toVec[1] ^^^
        s.st.toVec[4]._0.toVec[1] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x1_z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.c.toVec[1]._0.toVec[0] =
        s.st.toVec[5]._0.toVec[0] ^^^ s.st.toVec[6]._0.toVec[0] ^^^
        s.st.toVec[7]._0.toVec[0] ^^^ s.st.toVec[8]._0.toVec[0] ^^^
        s.st.toVec[9]._0.toVec[0] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x1_z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.c.toVec[1]._0.toVec[1] =
        s.st.toVec[5]._0.toVec[1] ^^^ s.st.toVec[6]._0.toVec[1] ^^^
        s.st.toVec[7]._0.toVec[1] ^^^ s.st.toVec[8]._0.toVec[1] ^^^
        s.st.toVec[9]._0.toVec[1] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x2_z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.c.toVec[2]._0.toVec[0] =
        s.st.toVec[10]._0.toVec[0] ^^^ s.st.toVec[11]._0.toVec[0] ^^^
        s.st.toVec[12]._0.toVec[0] ^^^ s.st.toVec[13]._0.toVec[0] ^^^
        s.st.toVec[14]._0.toVec[0] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x2_z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.c.toVec[2]._0.toVec[1] =
        s.st.toVec[10]._0.toVec[1] ^^^ s.st.toVec[11]._0.toVec[1] ^^^
        s.st.toVec[12]._0.toVec[1] ^^^ s.st.toVec[13]._0.toVec[1] ^^^
        s.st.toVec[14]._0.toVec[1] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x3_z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.c.toVec[3]._0.toVec[0] =
        s.st.toVec[15]._0.toVec[0] ^^^ s.st.toVec[16]._0.toVec[0] ^^^
        s.st.toVec[17]._0.toVec[0] ^^^ s.st.toVec[18]._0.toVec[0] ^^^
        s.st.toVec[19]._0.toVec[0] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x3_z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.c.toVec[3]._0.toVec[1] =
        s.st.toVec[15]._0.toVec[1] ^^^ s.st.toVec[16]._0.toVec[1] ^^^
        s.st.toVec[17]._0.toVec[1] ^^^ s.st.toVec[18]._0.toVec[1] ^^^
        s.st.toVec[19]._0.toVec[1] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x4_z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.c.toVec[4]._0.toVec[0] =
        s.st.toVec[20]._0.toVec[0] ^^^ s.st.toVec[21]._0.toVec[0] ^^^
        s.st.toVec[22]._0.toVec[0] ^^^ s.st.toVec[23]._0.toVec[0] ^^^
        s.st.toVec[24]._0.toVec[0] ⌝ ⦄ := by theta_c_proof

open Std.Do in
theorem theta_c_x4_z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.c.toVec[4]._0.toVec[1] =
        s.st.toVec[20]._0.toVec[1] ^^^ s.st.toVec[21]._0.toVec[1] ^^^
        s.st.toVec[22]._0.toVec[1] ^^^ s.st.toVec[23]._0.toVec[1] ^^^
        s.st.toVec[24]._0.toVec[1] ⌝ ⦄ := by theta_c_proof

/-! ## Theta_d: d[x] = c[(x+4)%5] ⊕ rotateLeft(c[(x+1)%5], 1)

In interleaved form (rotation by 1 is odd: 2*0+1):
  d[x].z0 = c[(x+4)%5].z0 ⊕ rotateLeft₃₂(c[(x+1)%5].z1, 1)
  d[x].z1 = c[(x+4)%5].z1 ⊕ c[(x+1)%5].z0
-/

-- Proof tactic for theta_d (extends theta_c_proof with rotate_left + Lane2U32 indexing)
macro "theta_d_proof" : tactic =>
  `(tactic| (
    hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction]
    all_goals (first | intro h₁; subst h₁ | skip)
    all_goals simp (config := { decide := true }) [getElemResult, core_models.ops.index.Index.index]
    all_goals (first | (simp_all [Vector.getElem_set]; try rfl) | skip)
    all_goals (reduce_usize_sizes;
               simp (config := { decide := true }) [Vector.getElem_set];
               try rfl)))

-- d[0].z0 = c[4].z0 ⊕ rot₃₂(c[1].z1, 1)
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d0z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[0]._0.toVec[0] =
        s.c.toVec[4]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[1]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[0].z1 = c[4].z1 ⊕ c[1].z0
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d0z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[0]._0.toVec[1] =
        s.c.toVec[4]._0.toVec[1] ^^^ s.c.toVec[1]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

-- d[1].z0 = c[0].z0 ⊕ rot₃₂(c[2].z1, 1)
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d1z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[1]._0.toVec[0] =
        s.c.toVec[0]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[2]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[1].z1 = c[0].z1 ⊕ c[2].z0
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d1z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[1]._0.toVec[1] =
        s.c.toVec[0]._0.toVec[1] ^^^ s.c.toVec[2]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

-- d[2].z0 = c[1].z0 ⊕ rot₃₂(c[3].z1, 1)
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d2z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[2]._0.toVec[0] =
        s.c.toVec[1]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[3]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[2].z1 = c[1].z1 ⊕ c[3].z0
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d2z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[2]._0.toVec[1] =
        s.c.toVec[1]._0.toVec[1] ^^^ s.c.toVec[3]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

-- d[3].z0 = c[2].z0 ⊕ rot₃₂(c[4].z1, 1)
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d3z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[3]._0.toVec[0] =
        s.c.toVec[2]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[4]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[3].z1 = c[2].z1 ⊕ c[4].z0
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d3z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[3]._0.toVec[1] =
        s.c.toVec[2]._0.toVec[1] ^^^ s.c.toVec[4]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

-- d[4].z0 = c[3].z0 ⊕ rot₃₂(c[0].z1, 1)
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d4z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[4]._0.toVec[0] =
        s.c.toVec[3]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[0]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[4].z1 = c[3].z1 ⊕ c[0].z0
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_d_d4z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[4]._0.toVec[1] =
        s.c.toVec[3]._0.toVec[1] ^^^ s.c.toVec[0]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

/-! ## Theta composition: keccakf1600_round0_theta
    Composes theta_c (column parity) and theta_d (differences).
    The end-to-end spec expresses d[x]._0[z] in terms of the original s.st values.
-/

-- Helper: abbreviation for rotate_left on u32
abbrev rot32 (x : u32) (n : Nat) : u32 :=
  UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n)

-- Full theta composition: expresses all d[x]._0[z] in terms of original s.st values
-- d[x].z0 = c[(x+4)%5].z0 ⊕ rot₃₂(c[(x+1)%5].z1, 1)
-- d[x].z1 = c[(x+4)%5].z1 ⊕ c[(x+1)%5].z0
-- where c[x].z = st[5x].z ⊕ st[5x+1].z ⊕ st[5x+2].z ⊕ st[5x+3].z ⊕ st[5x+4].z
-- Reusable tactic for theta composition proofs
macro "theta_comp_proof" : tactic =>
  `(tactic| (
    hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction]
    all_goals (first | intro h₁; subst h₁ | skip)
    all_goals simp (config := { decide := true }) [getElemResult, core_models.ops.index.Index.index]
    all_goals (first | (simp_all [Vector.getElem_set]; try rfl) | skip)
    all_goals (reduce_usize_sizes;
               simp (config := { decide := true }) [Vector.getElem_set];
               try rfl)
    -- Split all nested conjunctions and close each part
    all_goals (repeat' constructor)
    all_goals (first | rfl | skip)
    all_goals (simp_all [Vector.getElem_set, rot32]; try rfl)))

-- Full theta composition: all d[x]._0[z] in terms of original s.st values
-- d[x].z0 = c[(x+4)%5].z0 ⊕ rot₃₂(c[(x+1)%5].z1, 1)
-- d[x].z1 = c[(x+4)%5].z1 ⊕ c[(x+1)%5].z0
-- where c[x].z = st[5x].z ⊕ st[5x+1].z ⊕ st[5x+2].z ⊕ st[5x+3].z ⊕ st[5x+4].z
set_option maxHeartbeats 8000000 in
open Std.Do in
theorem theta_comp_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜
      -- d[0].z0 = c[4].z0 ⊕ rot(c[1].z1, 1)
      r.d.toVec[0]._0.toVec[0] =
        (s.st.toVec[20]._0.toVec[0] ^^^ s.st.toVec[21]._0.toVec[0] ^^^
         s.st.toVec[22]._0.toVec[0] ^^^ s.st.toVec[23]._0.toVec[0] ^^^
         s.st.toVec[24]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[5]._0.toVec[1] ^^^ s.st.toVec[6]._0.toVec[1] ^^^
               s.st.toVec[7]._0.toVec[1] ^^^ s.st.toVec[8]._0.toVec[1] ^^^
               s.st.toVec[9]._0.toVec[1]) 1
      ∧
      -- d[0].z1 = c[4].z1 ⊕ c[1].z0
      r.d.toVec[0]._0.toVec[1] =
        (s.st.toVec[20]._0.toVec[1] ^^^ s.st.toVec[21]._0.toVec[1] ^^^
         s.st.toVec[22]._0.toVec[1] ^^^ s.st.toVec[23]._0.toVec[1] ^^^
         s.st.toVec[24]._0.toVec[1]) ^^^
        (s.st.toVec[5]._0.toVec[0] ^^^ s.st.toVec[6]._0.toVec[0] ^^^
         s.st.toVec[7]._0.toVec[0] ^^^ s.st.toVec[8]._0.toVec[0] ^^^
         s.st.toVec[9]._0.toVec[0])
      ∧
      -- d[1].z0 = c[0].z0 ⊕ rot(c[2].z1, 1)
      r.d.toVec[1]._0.toVec[0] =
        (s.st.toVec[0]._0.toVec[0] ^^^ s.st.toVec[1]._0.toVec[0] ^^^
         s.st.toVec[2]._0.toVec[0] ^^^ s.st.toVec[3]._0.toVec[0] ^^^
         s.st.toVec[4]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[10]._0.toVec[1] ^^^ s.st.toVec[11]._0.toVec[1] ^^^
               s.st.toVec[12]._0.toVec[1] ^^^ s.st.toVec[13]._0.toVec[1] ^^^
               s.st.toVec[14]._0.toVec[1]) 1
      ∧
      -- d[1].z1 = c[0].z1 ⊕ c[2].z0
      r.d.toVec[1]._0.toVec[1] =
        (s.st.toVec[0]._0.toVec[1] ^^^ s.st.toVec[1]._0.toVec[1] ^^^
         s.st.toVec[2]._0.toVec[1] ^^^ s.st.toVec[3]._0.toVec[1] ^^^
         s.st.toVec[4]._0.toVec[1]) ^^^
        (s.st.toVec[10]._0.toVec[0] ^^^ s.st.toVec[11]._0.toVec[0] ^^^
         s.st.toVec[12]._0.toVec[0] ^^^ s.st.toVec[13]._0.toVec[0] ^^^
         s.st.toVec[14]._0.toVec[0])
      ∧
      -- d[2].z0 = c[1].z0 ⊕ rot(c[3].z1, 1)
      r.d.toVec[2]._0.toVec[0] =
        (s.st.toVec[5]._0.toVec[0] ^^^ s.st.toVec[6]._0.toVec[0] ^^^
         s.st.toVec[7]._0.toVec[0] ^^^ s.st.toVec[8]._0.toVec[0] ^^^
         s.st.toVec[9]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[15]._0.toVec[1] ^^^ s.st.toVec[16]._0.toVec[1] ^^^
               s.st.toVec[17]._0.toVec[1] ^^^ s.st.toVec[18]._0.toVec[1] ^^^
               s.st.toVec[19]._0.toVec[1]) 1
      ∧
      -- d[2].z1 = c[1].z1 ⊕ c[3].z0
      r.d.toVec[2]._0.toVec[1] =
        (s.st.toVec[5]._0.toVec[1] ^^^ s.st.toVec[6]._0.toVec[1] ^^^
         s.st.toVec[7]._0.toVec[1] ^^^ s.st.toVec[8]._0.toVec[1] ^^^
         s.st.toVec[9]._0.toVec[1]) ^^^
        (s.st.toVec[15]._0.toVec[0] ^^^ s.st.toVec[16]._0.toVec[0] ^^^
         s.st.toVec[17]._0.toVec[0] ^^^ s.st.toVec[18]._0.toVec[0] ^^^
         s.st.toVec[19]._0.toVec[0])
      ∧
      -- d[3].z0 = c[2].z0 ⊕ rot(c[4].z1, 1)
      r.d.toVec[3]._0.toVec[0] =
        (s.st.toVec[10]._0.toVec[0] ^^^ s.st.toVec[11]._0.toVec[0] ^^^
         s.st.toVec[12]._0.toVec[0] ^^^ s.st.toVec[13]._0.toVec[0] ^^^
         s.st.toVec[14]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[20]._0.toVec[1] ^^^ s.st.toVec[21]._0.toVec[1] ^^^
               s.st.toVec[22]._0.toVec[1] ^^^ s.st.toVec[23]._0.toVec[1] ^^^
               s.st.toVec[24]._0.toVec[1]) 1
      ∧
      -- d[3].z1 = c[2].z1 ⊕ c[4].z0
      r.d.toVec[3]._0.toVec[1] =
        (s.st.toVec[10]._0.toVec[1] ^^^ s.st.toVec[11]._0.toVec[1] ^^^
         s.st.toVec[12]._0.toVec[1] ^^^ s.st.toVec[13]._0.toVec[1] ^^^
         s.st.toVec[14]._0.toVec[1]) ^^^
        (s.st.toVec[20]._0.toVec[0] ^^^ s.st.toVec[21]._0.toVec[0] ^^^
         s.st.toVec[22]._0.toVec[0] ^^^ s.st.toVec[23]._0.toVec[0] ^^^
         s.st.toVec[24]._0.toVec[0])
      ∧
      -- d[4].z0 = c[3].z0 ⊕ rot(c[0].z1, 1)
      r.d.toVec[4]._0.toVec[0] =
        (s.st.toVec[15]._0.toVec[0] ^^^ s.st.toVec[16]._0.toVec[0] ^^^
         s.st.toVec[17]._0.toVec[0] ^^^ s.st.toVec[18]._0.toVec[0] ^^^
         s.st.toVec[19]._0.toVec[0]) ^^^
        rot32 (s.st.toVec[0]._0.toVec[1] ^^^ s.st.toVec[1]._0.toVec[1] ^^^
               s.st.toVec[2]._0.toVec[1] ^^^ s.st.toVec[3]._0.toVec[1] ^^^
               s.st.toVec[4]._0.toVec[1]) 1
      ∧
      -- d[4].z1 = c[3].z1 ⊕ c[0].z0
      r.d.toVec[4]._0.toVec[1] =
        (s.st.toVec[15]._0.toVec[1] ^^^ s.st.toVec[16]._0.toVec[1] ^^^
         s.st.toVec[17]._0.toVec[1] ^^^ s.st.toVec[18]._0.toVec[1] ^^^
         s.st.toVec[19]._0.toVec[1]) ^^^
        (s.st.toVec[0]._0.toVec[0] ^^^ s.st.toVec[1]._0.toVec[0] ^^^
         s.st.toVec[2]._0.toVec[0] ^^^ s.st.toVec[3]._0.toVec[0] ^^^
         s.st.toVec[4]._0.toVec[0])
      ∧
      -- st is preserved
      r.st = s.st
    ⌝ ⦄ := by theta_comp_proof

/-! ## Pi permutation and permuted lift

The implementation does pi_rho_chi **in-place**: it reads from pi-permuted source
positions, applies rho+chi+iota, and writes results back without materializing the
pi permutation as a data movement. After each round, the implementation state is in
a permuted layout relative to the spec state.

The permutation after one round is `impl_perm`: it maps an implementation lane index
to the corresponding spec lane index. Its formula is:
  impl_perm(5*x + z) = 5*x + (3*z + 2*x) % 5

This permutation has cycle structure: 5 fixed points {0,9,13,17,21} and
5 disjoint 4-cycles: (1 3 4 2)(5 7 8 6)(10 14 11 12)(15 16 19 18)(20 23 22 24).
Therefore **impl_perm^4 = id**, meaning after each 4-round block the state returns
to standard layout and `lift` works without permutation adjustment.
-/

/-- The pi permutation on lane indices: σ(5*x+y) = 5*((x+3y)%5) + x.
    Maps an output position to the source position it reads from. -/
def pi_perm (i : Fin 25) : Fin 25 :=
  let x := i.val / 5
  let y := i.val % 5
  ⟨5 * ((x + 3 * y) % 5) + x, by omega⟩

/-- The implementation-to-spec permutation after one round.
    impl_state[k] holds the spec value at position impl_perm(k).
    Formula: impl_perm(5*x + z) = 5*x + (3*z + 2*x) % 5 -/
def impl_perm (i : Fin 25) : Fin 25 :=
  let x := i.val / 5
  let z := i.val % 5
  ⟨5 * x + (3 * z + 2 * x) % 5, by omega⟩

/-- impl_perm has order 4: after 4 rounds the lane layout returns to identity. -/
theorem impl_perm_pow4_eq_id : ∀ i : Fin 25, impl_perm (impl_perm (impl_perm (impl_perm i))) = i := by
  decide

/-- Lift with a permutation applied to lane indices. -/
def lift_perm (s : KeccakState) (p : Fin 25 → Fin 25) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i => lift_lane s.st.toVec[(p i).val])

-- lift_perm with identity is just lift.
theorem lift_perm_id (s : KeccakState) : lift_perm s id = lift s := by
  unfold lift_perm lift; rfl

/-! ## Iota / Round constant equivalence

The implementation XORs with `RC_INTERLEAVED_0[i]` (z0) and `RC_INTERLEAVED_1[i]` (z1).
The spec XORs with `ROUND_CONSTANTS[round]` (u64).
We need: `lift_lane_bv RC0[i] RC1[i] = ROUND_CONSTANTS[i]` for each round.
-/

-- Round constant equivalence: interleaved RC lifts to standard RC.
-- We prove this for each concrete round by native_decide.
open libcrux_iot_sha3.keccak in
private theorem rc_equiv_aux (i : Fin 24) :
    have : i.val < USize64.toNat 255 := by
      simp only [show USize64.toNat 255 = 255 from rfl]; omega
    lift_lane_bv
      (RC_INTERLEAVED_0.toVec[i.val].toBitVec)
      (RC_INTERLEAVED_1.toVec[i.val].toBitVec) =
    (hacspec_sha3.keccak_f.ROUND_CONSTANTS.toVec[i.val].toBitVec) := by
  revert i; decide

open libcrux_iot_sha3.keccak in
theorem rc_equiv (i : Nat) (hi : i < 24) :
    have : i < USize64.toNat 255 := by
      simp only [show USize64.toNat 255 = 255 from rfl]; omega
    lift_lane_bv
      (RC_INTERLEAVED_0.toVec[i].toBitVec)
      (RC_INTERLEAVED_1.toVec[i].toBitVec) =
    (hacspec_sha3.keccak_f.ROUND_CONSTANTS.toVec[i].toBitVec) :=
  rc_equiv_aux ⟨i, hi⟩

/-! ## Pi-Rho-Chi step equivalence

The implementation fuses theta_apply + rho + pi + chi + iota into two monadic functions:
- `keccakf1600_round0_pi_rho_chi_1`: processes chi-sheets for output rows y=0,1
- `keccakf1600_round0_pi_rho_chi_2`: processes chi-sheets for output rows y=2,3,4

Each sheet reads 5 source lanes (determined by the pi permutation), XORs with d
(theta_apply), rotates (rho), applies chi, and writes back.

For row y, the 5 source lanes are at indices σ(5*x+y) for x=0..4. The interleaved
rotation amounts are derived from RHO_OFFSETS at those source positions.
-/

-- Helper: apply chi to a 5-element vector at position x.
-- chi(x) = b[x] ⊕ (¬b[(x+1)%5] ∧ b[(x+2)%5])
def chi_u32 (b : Fin 5 → u32) (x : Fin 5) : u32 :=
  b x ^^^ (~~~(b ⟨(x.val + 1) % 5, by omega⟩) &&& b ⟨(x.val + 2) % 5, by omega⟩)

-- Monadic spec for pi_rho_chi_1 (round 0).
-- Processes chi-sheets for output rows y=0,1.
-- Output lane sets: {0,6,12,18,24} (row y=0) and {2,8,14,15,21} (row y=1).
-- The `i` field is incremented by 1 (one iota round constant consumed).
set_option maxRecDepth 2000 in
set_option maxHeartbeats 40000000 in
open Std.Do in
theorem pi_rho_chi_1_spec (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
    ⦃ ⇓ r => ⌜
      -- i is incremented, d is preserved
      r.i = s.i + 1 ∧ r.d = s.d
    ⌝ ⦄ := by
  hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify]
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 200000 }) [getElemResult, core_models.ops.index.Index.index]
  all_goals (first | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set]; try rfl) | skip)
  all_goals (reduce_usize_sizes;
             simp (config := { decide := true, maxSteps := 200000 }) [Vector.getElem_set];
             try rfl)
  all_goals (repeat' constructor)
  all_goals (first | rfl | skip)
  all_goals (first | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set, rot32]; try rfl) | skip)
  all_goals (first | omega | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set, rot32]; try rfl) | assumption | rfl | skip)
  -- Remaining goals: RC_INTERLEAVED array bounds + i+1 overflow
  all_goals (first | omega | simp_all | rfl | skip)
  all_goals sorry -- WP of RustM.fail: needs instWP unfolding, blocked by open Std.Do scoping

-- Monadic spec for pi_rho_chi_2 (round 0).
-- Processes rows y=2,3,4. Output lane sets:
-- {4,5,11,17,23} (y=2), {1,7,13,19,20} (y=3), {3,9,10,16,22} (y=4).
open Std.Do in
theorem pi_rho_chi_2_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.d = s.d ⌝ ⦄ := by
  sorry

/-! ## Pi-Rho-Chi lifting theorem

After pi_rho_chi_1 + pi_rho_chi_2, the lifted state (with impl_perm applied)
matches the spec's iota(chi(pi(rho(theta_applied_state)))).
-/

open Std.Do in
theorem pi_rho_chi_round0_lift (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
       libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      True -- placeholder: full statement involves all 25 lifted lanes
      -- lift_perm r impl_perm = iota(chi(pi(rho(theta_apply(lift s, d))))) s.i
    ⌝ ⦄ := by
  sorry

/-! ## Single round equivalence

Combines theta (which computes c, d while preserving st) with pi_rho_chi
(which reads st and d, applies theta_apply+rho+pi+chi+iota).

After one round, the implementation state is in impl_perm-permuted layout.
-/

open Std.Do in
theorem round0_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
       let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
       libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      True -- placeholder: lift_perm r impl_perm = spec_one_round (lift s) s.i
    ⌝ ⦄ := by
  sorry

/-! ## 4-round block equivalence

Since impl_perm^4 = id, after 4 rounds the state is back in standard layout.
The 4-round block processes rounds i, i+1, i+2, i+3 of the spec.
-/

open Std.Do in
theorem four_rounds_equiv (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s
    ⦃ ⇓ r => ⌜
      -- After 4 rounds, impl_perm^4 = id, so lift (no perm) equals 4 spec rounds
      True -- placeholder: lift r = spec_4_rounds (lift s) s.i
    ⌝ ⦄ := by
  sorry

/-! ## Main equivalence theorem

The full keccak is 6 repetitions of the 4-round block = 24 spec rounds.
Since each 4-round block returns the state to standard layout (impl_perm^4 = id),
the composition is straightforward.
-/

#check hacspec_sha3.keccak_f.keccak_f
#check libcrux_iot_sha3.keccak.keccakf1600

theorem equivalence (s : KeccakState) :
  hacspec_sha3.keccak_f.keccak_f (lift s) =
    (do pure (lift (← libcrux_iot_sha3.keccak.keccakf1600 s))) := sorry
