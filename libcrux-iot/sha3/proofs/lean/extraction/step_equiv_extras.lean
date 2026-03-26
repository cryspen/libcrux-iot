import extraction.step_equiv

/-! ## Unused-by-equivalence theorems
These theorems are not in the dependency chain of the main `equivalence` theorem
but are preserved for future use (e.g., strengthening placeholder postconditions).
-/

open libcrux_iot_sha3.lane
open libcrux_iot_sha3.state

/-! ## Core bitwise lemmas: operations commute with lift -/

theorem lift_lane_bv_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) =
    lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even
  bv_decide

theorem lift_lane_bv_and (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 &&& b0) (a1 &&& b1) =
    lift_lane_bv a0 a1 &&& lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even
  bv_decide

theorem lift_lane_bv_not (a0 a1 : BitVec 32) :
    lift_lane_bv (~~~a0) (~~~a1) =
    ~~~(lift_lane_bv a0 a1) := by
  unfold lift_lane_bv spread_to_even
  bv_decide

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
theorem lift_lane_bv_rotate_0 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 0 =
    lift_lane_bv (z0.rotateLeft 0) (z1.rotateLeft 0) := by
  unfold lift_lane_bv spread_to_even
  bv_decide

-- Rotation by 1 (odd: 2*0+1, new_z0=rot(z1,1), new_z1=rot(z0,0))
theorem lift_lane_bv_rotate_1 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 1 =
    lift_lane_bv (z1.rotateLeft 1) (z0.rotateLeft 0) := by
  unfold lift_lane_bv spread_to_even
  bv_decide

-- Even rotations: rotateLeft (2k) = lift (rotateLeft k, rotateLeft k)
theorem lift_lane_bv_rotate_2 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 2 = lift_lane_bv (z0.rotateLeft 1) (z1.rotateLeft 1) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_6 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 6 = lift_lane_bv (z0.rotateLeft 3) (z1.rotateLeft 3) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_8 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 8 = lift_lane_bv (z0.rotateLeft 4) (z1.rotateLeft 4) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_10 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 10 = lift_lane_bv (z0.rotateLeft 5) (z1.rotateLeft 5) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_14 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 14 = lift_lane_bv (z0.rotateLeft 7) (z1.rotateLeft 7) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_18 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 18 = lift_lane_bv (z0.rotateLeft 9) (z1.rotateLeft 9) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_20 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 20 = lift_lane_bv (z0.rotateLeft 10) (z1.rotateLeft 10) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_28 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 28 = lift_lane_bv (z0.rotateLeft 14) (z1.rotateLeft 14) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_36 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 36 = lift_lane_bv (z0.rotateLeft 18) (z1.rotateLeft 18) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_44 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 44 = lift_lane_bv (z0.rotateLeft 22) (z1.rotateLeft 22) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_56 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 56 = lift_lane_bv (z0.rotateLeft 28) (z1.rotateLeft 28) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_62 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 62 = lift_lane_bv (z0.rotateLeft 31) (z1.rotateLeft 31) := by
  unfold lift_lane_bv spread_to_even; bv_decide

-- Odd rotations: rotateLeft (2k+1) = lift (rotateLeft(z1, k+1), rotateLeft(z0, k))
theorem lift_lane_bv_rotate_3 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 3 = lift_lane_bv (z1.rotateLeft 2) (z0.rotateLeft 1) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_15 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 15 = lift_lane_bv (z1.rotateLeft 8) (z0.rotateLeft 7) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_21 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 21 = lift_lane_bv (z1.rotateLeft 11) (z0.rotateLeft 10) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_25 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 25 = lift_lane_bv (z1.rotateLeft 13) (z0.rotateLeft 12) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_27 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 27 = lift_lane_bv (z1.rotateLeft 14) (z0.rotateLeft 13) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_39 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 39 = lift_lane_bv (z1.rotateLeft 20) (z0.rotateLeft 19) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_41 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 41 = lift_lane_bv (z1.rotateLeft 21) (z0.rotateLeft 20) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_43 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 43 = lift_lane_bv (z1.rotateLeft 22) (z0.rotateLeft 21) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_45 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 45 = lift_lane_bv (z1.rotateLeft 23) (z0.rotateLeft 22) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_55 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 55 = lift_lane_bv (z1.rotateLeft 28) (z0.rotateLeft 27) := by
  unfold lift_lane_bv spread_to_even; bv_decide
theorem lift_lane_bv_rotate_61 (z0 z1 : BitVec 32) :
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
-- Optimized: single simp pass with exact lemma set (from simp?) + rfl
macro "theta_c_proof" : tactic =>
  `(tactic| (
    hax_mvcgen []
    intro h₁; subst h₁
    simp (config := { decide := true }) only [getElemResult, core_models.ops.index.Index.index,
      ↓reduceDIte, USize64.reduceToNat, USize64.add_zero, USize64.toNat_zero, ↓reduceIte,
      USize64.toBitVec_ofNat, bind_pure_comp, pure_bind, USize64.reduceAdd, map_pure,
      Vector.size, Nat.zero_lt_succ, bind_pure, Std.Do.WP.pure, Vector.getElem_set,
      Std.Do.SPred.down_pure,
      show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl,
      show (2 : usize).toNat = 2 from rfl]
    rfl))

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
-- Optimized: single simp pass with exact lemma set (from simp?) + subst_vars + rfl
macro "theta_d_proof" : tactic =>
  `(tactic| (
    hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction]
    all_goals (first | intro h₁; subst h₁ | skip)
    all_goals simp (config := { decide := true }) only [getElemResult, core_models.ops.index.Index.index,
      ↓reduceDIte, USize64.reduceToNat, USize64.toNat_zero, ↓reduceIte,
      bind_pure_comp, map_pure, Vector.size, Nat.zero_lt_succ,
      Std.Do.WP.pure, Vector.getElem_set, Std.Do.SPred.down_pure,
      show (5 : usize).toNat = 5 from rfl, show (2 : usize).toNat = 2 from rfl]
    all_goals (first | subst_vars; rfl | rfl)))

-- d[0].z0 = c[4].z0 ⊕ rot₃₂(c[1].z1, 1)
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d0z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[0]._0.toVec[0] =
        s.c.toVec[4]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[1]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[0].z1 = c[4].z1 ⊕ c[1].z0
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d0z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[0]._0.toVec[1] =
        s.c.toVec[4]._0.toVec[1] ^^^ s.c.toVec[1]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

-- d[1].z0 = c[0].z0 ⊕ rot₃₂(c[2].z1, 1)
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d1z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[1]._0.toVec[0] =
        s.c.toVec[0]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[2]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[1].z1 = c[0].z1 ⊕ c[2].z0
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d1z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[1]._0.toVec[1] =
        s.c.toVec[0]._0.toVec[1] ^^^ s.c.toVec[2]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

-- d[2].z0 = c[1].z0 ⊕ rot₃₂(c[3].z1, 1)
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d2z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[2]._0.toVec[0] =
        s.c.toVec[1]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[3]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[2].z1 = c[1].z1 ⊕ c[3].z0
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d2z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[2]._0.toVec[1] =
        s.c.toVec[1]._0.toVec[1] ^^^ s.c.toVec[3]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

-- d[3].z0 = c[2].z0 ⊕ rot₃₂(c[4].z1, 1)
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d3z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[3]._0.toVec[0] =
        s.c.toVec[2]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[4]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[3].z1 = c[2].z1 ⊕ c[4].z0
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d3z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[3]._0.toVec[1] =
        s.c.toVec[2]._0.toVec[1] ^^^ s.c.toVec[4]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

-- d[4].z0 = c[3].z0 ⊕ rot₃₂(c[0].z1, 1)
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d4z0_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[4]._0.toVec[0] =
        s.c.toVec[3]._0.toVec[0] ^^^
        UInt32.ofBitVec (BitVec.rotateLeft s.c.toVec[0]._0.toVec[1].toBitVec 1) ⌝ ⦄ := by
  theta_d_proof

-- d[4].z1 = c[3].z1 ⊕ c[0].z0
set_option maxHeartbeats 400000 in
open Std.Do in
theorem theta_d_d4z1_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.d.toVec[4]._0.toVec[1] =
        s.c.toVec[3]._0.toVec[1] ^^^ s.c.toVec[0]._0.toVec[0] ⌝ ⦄ := by
  theta_d_proof

/-! ## Placeholder proofs (postcondition True, need strengthening) -/

/-! ## Pi-Rho-Chi lifting theorem. STATUS: sorry (placeholder postcondition).

After pi_rho_chi_1 + pi_rho_chi_2, the lifted state (with impl_perm applied)
matches the spec's iota(chi(pi(rho(theta_applied_state)))).

TODO: Strengthen postcondition from `True` to the actual lifting equivalence,
then prove by composing pi_rho_chi_1_spec + pi_rho_chi_2_spec with the algebraic
lifting lemmas (lift_lane_bv_{xor,and,not,or}, rotation lemmas, chi_lane_lift).
Requires Std.Do.Triple composition API (Triple.bind, Triple.of_entails_right).
-/

set_option maxRecDepth 2000 in
open Std.Do in
theorem pi_rho_chi_round0_lift (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
       libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  apply Triple.bind (Q := fun _ => ⌜True⌝)
  · apply Triple.of_entails_right _ _ _ _ (pi_rho_chi_1_spec s hi)
    apply PostCond.entails.of_left_entails; intro _
    rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial
  · intro s₁
    apply Triple.of_entails_right _ _ _ _ (pi_rho_chi_2_spec s₁)
    apply PostCond.entails.of_left_entails; intro _
    rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial

/-! ## Single round equivalence. STATUS: sorry (placeholder postcondition).

Combines theta (which computes c, d while preserving st) with pi_rho_chi
(which reads st and d, applies theta_apply+rho+pi+chi+iota).

After one round, the implementation state is in impl_perm-permuted layout.

TODO: Strengthen postcondition, then prove by chaining theta_comp_spec with
pi_rho_chi_round0_lift. Repeat for rounds 1-3 (different access patterns).
-/

set_option maxRecDepth 2000 in
open Std.Do in
theorem round0_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
       let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
       libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  apply Triple.bind (Q := fun s₁ => ⌜ s₁.i.toNat < 24 ⌝)
  · -- theta preserves i (from theta_comp_spec), so result.i = s.i < 24
    apply Triple.of_entails_right _ _ _ _ (theta_comp_spec s)
    apply PostCond.entails.of_left_entails; intro r
    rw [← SPred.entails_true_intro]
    exact SPred.pure_intro fun ⟨_,_,_,_,_,_,_,_,_,_,_,hi_eq⟩ => hi_eq ▸ hi
  · -- prc1 + prc2: extract hi from SPred precondition via by_cases
    intro s₁
    by_cases hi₁ : s₁.i.toNat < 24
    · exact Triple.of_entails_left ⌜True⌝ _ _ _ (pi_rho_chi_round0_lift s₁ hi₁)
        (by rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial)
    · -- precondition is ⌜False⌝, so triple holds vacuously
      rw [Triple, show (s₁.i.toNat < 24) = False from propext ⟨(absurd · hi₁), False.elim⟩]
      rw [← SPred.entails_true_intro]
      exact SPred.pure_intro fun h => absurd h id

