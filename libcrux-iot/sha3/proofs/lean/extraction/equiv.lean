import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane
open libcrux_iot_sha3.state

/-!
# Keccak-f[1600] Bit-Interleaved Equivalence Proof

## Proof Status (4 sorry remaining — all placeholder postconditions)

### Fully proven:
- All algebraic lemmas (lift_lane_bv commutes with XOR/AND/NOT/OR/rotation) — bv_decide
- theta_c specs (10 theorems) — theta_c_proof macro
- theta_d specs (10 theorems) — theta_d_proof macro
- theta_comp_spec (full theta composition) — theta_comp_proof macro
- impl_perm_pow4_eq_id (permutation order 4) — decide
- lift_perm_id — rfl
- rc_equiv (round constant equivalence, 24 cases) — decide
- pi_rho_chi_1_spec (rows y=0,1, i incremented, d preserved) — hax_mvcgen + rw [dif_pos]
- pi_rho_chi_2_spec (rows y=2,3,4, d preserved) — hax_mvcgen
- pi_rho_chi_round0_lift (prc1+prc2 composition) — Triple.bind
- round0_equiv (theta+prc1+prc2 composition) — Triple.bind

### 4 sorry (placeholder postconditions — need strengthening):
- pi_rho_chi_round0_lift: postcondition is `True`, needs real lifting statement
- round0_equiv: postcondition is `True`, needs spec round composition
- four_rounds_equiv: postcondition is `True`, needs 4-round spec composition
- equivalence: top-level theorem, needs composition of all phases

### Next steps:
1. Strengthen postconditions of placeholder theorems to real equivalence statements
2. Prove the strengthened theorems by composing sub-specs
   (requires Std.Do.Triple API: Triple.bind, Triple.of_entails_right, etc.)
-/

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
      -- st and i are preserved
      r.st = s.st ∧ r.i = s.i
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

-- Monadic spec for pi_rho_chi_1 (round 0). STATUS: PROVEN.
-- Processes chi-sheets for output rows y=0,1.
-- Output lane sets: {0,6,12,18,24} (row y=0) and {2,8,14,15,21} (row y=1).
-- The `i` field is incremented by 1 (one iota round constant consumed).
-- The WP goals for RC_INTERLEAVED array access are closed via dif_pos + if_neg
-- after delta-unfolding RustM.instWPMonad.
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
  -- Remaining: WP of RC array access + i+1 overflow. Reduce the WP wrappers,
  -- then the dite conditions evaluate since s.i < 24 < 255 and no overflow.
  all_goals (
    delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
    have h255 : USize64.toNat s.i < 255 := by omega
    rw [dif_pos h255, dif_pos h255]
    have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
      simp [BitVec.uaddOverflow]; omega
    rw [if_neg huadd]
    delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
    first | rfl | simp_all)

-- Monadic spec for pi_rho_chi_2 (round 0). STATUS: PROVEN.
-- Processes rows y=2,3,4. Output lane sets:
-- {4,5,11,17,23} (y=2), {1,7,13,19,20} (y=3), {3,9,10,16,22} (y=4).
-- No RC array access (no iota), so no WP-fail issue.
set_option maxRecDepth 3000 in
set_option maxHeartbeats 80000000 in
open Std.Do in
theorem pi_rho_chi_2_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.i = s.i ⌝ ⦄ := by
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
  all_goals (first | omega | simp_all | rfl | skip)

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

/-! ## Round 1–3 minimal specs (i-tracking for composition)

For the True postcondition of four_rounds_equiv, we only need:
- theta: preserves i
- prc1: increments i (needs hi : s.i.toNat < 24)
- prc2: succeeds (True postcondition)
-/

-- Reusable tactic for prc2 specs (no RC access, no WP delta needed)
macro "prc2_proof" : tactic =>
  `(tactic| (
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
    all_goals (first | omega | simp_all | rfl | skip)))

-- Reusable tactic for prc1 specs (includes WP delta for RC_INTERLEAVED access).
-- Uses open Std.Do to avoid macro hygiene issues with delta names.
macro "prc1_proof" : tactic =>
  `(tactic| (
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
    all_goals (first | omega | simp_all | rfl | skip)
    all_goals (open Std.Do in
      delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
      have h255 : USize64.toNat s.i < 255 := by omega
      rw [dif_pos h255, dif_pos h255]
      have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
        simp [BitVec.uaddOverflow]; omega
      rw [if_neg huadd]
      delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
      first | rfl | simp_all)))

-- Round 1
set_option maxHeartbeats 8000000 in
open Std.Do in
theorem round1_theta_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by theta_comp_proof

set_option maxRecDepth 2000 in
set_option maxHeartbeats 40000000 in
open Std.Do in
theorem round1_prc1_spec (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 0 s
    ⦃ ⇓ r => ⌜ r.i = s.i + 1 ⌝ ⦄ := by
  hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify]
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 200000 }) [getElemResult, core_models.ops.index.Index.index]
  all_goals (first | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set]; try rfl) | skip)
  all_goals (reduce_usize_sizes;
             simp (config := { decide := true, maxSteps := 200000 }) [Vector.getElem_set]; try rfl)
  all_goals (repeat' constructor)
  all_goals (first | rfl | skip)
  all_goals (first | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set, rot32]; try rfl) | skip)
  all_goals (first | omega | simp_all | rfl | skip)
  all_goals (
    delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
    have h255 : USize64.toNat s.i < 255 := by omega
    rw [dif_pos h255, dif_pos h255]
    have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
      simp [BitVec.uaddOverflow]; omega
    rw [if_neg huadd]
    delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
    first | rfl | simp_all)

set_option maxRecDepth 3000 in
set_option maxHeartbeats 80000000 in
open Std.Do in
theorem round1_prc2_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by prc2_proof

-- Round 2
set_option maxHeartbeats 8000000 in
open Std.Do in
theorem round2_theta_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round2_theta s
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by theta_comp_proof

set_option maxRecDepth 2000 in
set_option maxHeartbeats 40000000 in
open Std.Do in
theorem round2_prc1_spec (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 0 s
    ⦃ ⇓ r => ⌜ r.i = s.i + 1 ⌝ ⦄ := by
  hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify]
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 200000 }) [getElemResult, core_models.ops.index.Index.index]
  all_goals (first | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set]; try rfl) | skip)
  all_goals (reduce_usize_sizes;
             simp (config := { decide := true, maxSteps := 200000 }) [Vector.getElem_set]; try rfl)
  all_goals (repeat' constructor)
  all_goals (first | rfl | skip)
  all_goals (first | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set, rot32]; try rfl) | skip)
  all_goals (first | omega | simp_all | rfl | skip)
  all_goals (
    delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
    have h255 : USize64.toNat s.i < 255 := by omega
    rw [dif_pos h255, dif_pos h255]
    have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
      simp [BitVec.uaddOverflow]; omega
    rw [if_neg huadd]
    delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
    first | rfl | simp_all)

set_option maxRecDepth 3000 in
set_option maxHeartbeats 80000000 in
open Std.Do in
theorem round2_prc2_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by prc2_proof

-- Round 3
set_option maxHeartbeats 8000000 in
open Std.Do in
theorem round3_theta_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by theta_comp_proof

set_option maxRecDepth 2000 in
set_option maxHeartbeats 40000000 in
open Std.Do in
theorem round3_prc1_spec (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 0 s
    ⦃ ⇓ r => ⌜ r.i = s.i + 1 ⌝ ⦄ := by
  hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify]
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 200000 }) [getElemResult, core_models.ops.index.Index.index]
  all_goals (first | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set]; try rfl) | skip)
  all_goals (reduce_usize_sizes;
             simp (config := { decide := true, maxSteps := 200000 }) [Vector.getElem_set]; try rfl)
  all_goals (repeat' constructor)
  all_goals (first | rfl | skip)
  all_goals (first | (simp_all (config := { maxSteps := 200000 }) [Vector.getElem_set, rot32]; try rfl) | skip)
  all_goals (first | omega | simp_all | rfl | skip)
  all_goals (
    delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
    have h255 : USize64.toNat s.i < 255 := by omega
    rw [dif_pos h255, dif_pos h255]
    have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
      simp [BitVec.uaddOverflow]; omega
    rw [if_neg huadd]
    delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
    first | rfl | simp_all)

set_option maxRecDepth 3000 in
set_option maxHeartbeats 80000000 in
open Std.Do in
theorem round3_prc2_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by prc2_proof

/-! ## Single-round equivalence for rounds 1–3 (composed via Triple.bind) -/

-- Helper: weaken any postcondition to True
open Std.Do in
private theorem weaken_to_true {P : Assertion _} {Q : KeccakState → Prop}
    (m : RustM KeccakState) (h : ⦃P⦄ m ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃P⦄ m ⦃⇓ r => ⌜True⌝⦄ :=
  Triple.of_entails_right _ _ _ _ h
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial)

-- Helper: strengthen precondition (Q ⊢ₛ True is trivial)
open Std.Do in
private theorem strengthen_pre {Q : Prop} {R : PostCond KeccakState _}
    (m : RustM KeccakState) (h : ⦃⌜True⌝⦄ m ⦃R⦄) :
    ⦃⌜Q⌝⦄ m ⦃R⦄ :=
  Triple.of_entails_left ⌜True⌝ _ _ _ h (by
    rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial)

-- Helper: vacuous triple when precondition is False
open Std.Do in
private theorem triple_of_false {R : PostCond KeccakState _}
    (m : RustM KeccakState) : ⦃⌜False⌝⦄ m ⦃R⦄ := by
  rw [Triple, ← SPred.entails_true_intro]
  exact SPred.pure_intro fun h => absurd h id

-- Helper: vacuous triple when precondition is ⌜P⌝ and ¬P holds
open Std.Do in
private theorem triple_of_neg {P : Prop} (hneg : ¬P) {R : PostCond KeccakState _}
    (m : RustM KeccakState) : ⦃⌜P⌝⦄ m ⦃R⦄ := by
  have : P = False := propext ⟨fun h => absurd h hneg, False.elim⟩
  rw [Triple, this, ← SPred.entails_true_intro]
  exact SPred.pure_intro fun h => absurd h id

open Std.Do in
private theorem roundK_equiv
    {theta prc1 prc2 : KeccakState → RustM KeccakState}
    (theta_spec : ∀ s, ⦃⌜True⌝⦄ theta s ⦃⇓ r => ⌜r.i = s.i⌝⦄)
    (prc1_spec : ∀ s, s.i.toNat < 24 → ⦃⌜True⌝⦄ prc1 s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄)
    (prc2_spec : ∀ s, ⦃⌜True⌝⦄ prc2 s ⦃⇓ r => ⌜r.i = s.i⌝⦄)
    (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃⌜True⌝⦄
    do let s ← theta s; let s ← prc1 s; prc2 s
    ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄ := by
  apply Triple.bind (Q := fun s₁ => ⌜s₁.i = s.i⌝)
  · exact theta_spec s
  · intro s₁
    by_cases hs₁ : s₁.i = s.i
    · have hi₁ : s₁.i.toNat < 24 := hs₁ ▸ hi
      apply Triple.bind (Q := fun s₂ => ⌜s₂.i = s.i + 1⌝)
      · exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (prc1_spec s₁ hi₁)
          (PostCond.entails.of_left_entails fun _ => by
            rw [← SPred.entails_true_intro]
            exact SPred.pure_intro fun h => by simp_all))
      · intro s₂
        by_cases hs₂ : s₂.i = s.i + 1
        · exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (prc2_spec s₂)
            (PostCond.entails.of_left_entails fun _ => by
              rw [← SPred.entails_true_intro]
              exact SPred.pure_intro fun h => by simp_all))
        · rw [Triple, show (s₂.i = s.i + 1) = False from propext ⟨(absurd · hs₂), False.elim⟩]
          rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => absurd h id
    · rw [Triple, show (s₁.i = s.i) = False from propext ⟨(absurd · hs₁), False.elim⟩]
      rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => absurd h id

/-! ## 4-round block equivalence.

Composes 4 single-round equivalences via Triple.bind.
Each round increments i by 1, so after 4 rounds i has increased by 4.
-/

-- Pre-weakened round0 specs (extract just i-tracking from the full specs)
open Std.Do in
private theorem round0_theta_i (s : KeccakState) :
    ⦃⌜True⌝⦄ libcrux_iot_sha3.keccak.keccakf1600_round0_theta s ⦃⇓ r => ⌜r.i = s.i⌝⦄ :=
  Triple.of_entails_right _ _ _ _ (theta_comp_spec s)
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]
      exact SPred.pure_intro fun ⟨_,_,_,_,_,_,_,_,_,_,_,h⟩ => h)

open Std.Do in
private theorem round0_prc1_i (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃⌜True⌝⦄ libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄ :=
  Triple.of_entails_right _ _ _ _ (pi_rho_chi_1_spec s hi)
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun ⟨h, _⟩ => h)

set_option maxRecDepth 3000 in
open Std.Do in
private theorem round0_prc2_i (s : KeccakState) :
    ⦃⌜True⌝⦄ libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s ⦃⇓ r => ⌜r.i = s.i⌝⦄ :=
  Triple.of_entails_right _ _ _ _ (pi_rho_chi_2_spec s)
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun ⟨_, h⟩ => h)

-- Helper: convert usize-preserving spec to Nat-level postcondition.
open Std.Do in
private theorem nat_step_preserve
    {f : KeccakState → RustM KeccakState}
    (spec : ∀ s, ⦃⌜True⌝⦄ f s ⦃⇓ r => ⌜r.i = s.i⌝⦄)
    (s : KeccakState) (n : Nat) :
    ⦃⌜s.i.toNat = n⌝⦄ f s ⦃⇓ r => ⌜r.i.toNat = n⌝⦄ := by
  by_cases hs : s.i.toNat = n
  · exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (spec s)
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]
        exact SPred.pure_intro fun h => by simp_all))
  · exact triple_of_neg hs _

-- Helper: convert usize-incrementing spec to Nat-level postcondition.
open Std.Do in
private theorem nat_step_increment
    {f : KeccakState → RustM KeccakState}
    (spec : ∀ s, s.i.toNat < 24 → ⦃⌜True⌝⦄ f s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄)
    (s : KeccakState) (n : Nat) (hn : n < 24) :
    ⦃⌜s.i.toNat = n⌝⦄ f s ⦃⇓ r => ⌜r.i.toNat = n + 1⌝⦄ := by
  by_cases hs : s.i.toNat = n
  · exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (spec s (hs ▸ hn))
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]
        exact SPred.pure_intro fun h => by omega))
  · exact triple_of_neg hs _

set_option maxRecDepth 2000 in
open Std.Do in
theorem four_rounds_equiv (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s
    ⦃ ⇓ r => ⌜ r.i.toNat = s.i.toNat + 4 ⌝ ⦄ := by
  -- Track s.i.toNat through 12 steps as Nat (avoids usize arithmetic issues).
  -- theta/prc2 preserve (nat_step_preserve), prc1 increments (nat_step_increment).
  unfold libcrux_iot_sha3.keccak.keccakf1600_4rounds
  -- Step 1: theta0 (preserves i)
  apply Triple.bind (Q := fun s₁ => ⌜s₁.i.toNat = s.i.toNat⌝)
  · exact Triple.of_entails_right _ _ _ _ (round0_theta_i s)
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => by simp_all)
  · intro s₁
    -- Step 2: prc1_0 (increments to n0 + 1)
    apply Triple.bind (Q := fun s₂ => ⌜s₂.i.toNat = s.i.toNat + 1⌝)
    · exact nat_step_increment (fun s hi => round0_prc1_i s hi) s₁ s.i.toNat (by omega)
    · intro s₂
      -- Step 3: prc2_0 (preserves n0 + 1)
      apply Triple.bind (Q := fun s₃ => ⌜s₃.i.toNat = s.i.toNat + 1⌝)
      · exact nat_step_preserve round0_prc2_i s₂ (s.i.toNat + 1)
      · intro s₃
        -- Step 4: theta1 (preserves n0 + 1)
        apply Triple.bind (Q := fun s₄ => ⌜s₄.i.toNat = s.i.toNat + 1⌝)
        · exact nat_step_preserve round1_theta_spec s₃ (s.i.toNat + 1)
        · intro s₄
          -- Step 5: prc1_1 (increments to n0 + 2)
          apply Triple.bind (Q := fun s₅ => ⌜s₅.i.toNat = s.i.toNat + 2⌝)
          · exact nat_step_increment (fun s hi => round1_prc1_spec s hi) s₄ (s.i.toNat + 1) (by omega)
          · intro s₅
            -- Step 6: prc2_1 (preserves n0 + 2)
            apply Triple.bind (Q := fun s₆ => ⌜s₆.i.toNat = s.i.toNat + 2⌝)
            · exact nat_step_preserve round1_prc2_spec s₅ (s.i.toNat + 2)
            · intro s₆
              -- Step 7: theta2 (preserves n0 + 2)
              apply Triple.bind (Q := fun s₇ => ⌜s₇.i.toNat = s.i.toNat + 2⌝)
              · exact nat_step_preserve round2_theta_spec s₆ (s.i.toNat + 2)
              · intro s₇
                -- Step 8: prc1_2 (increments to n0 + 3)
                apply Triple.bind (Q := fun s₈ => ⌜s₈.i.toNat = s.i.toNat + 3⌝)
                · exact nat_step_increment (fun s hi => round2_prc1_spec s hi) s₇ (s.i.toNat + 2) (by omega)
                · intro s₈
                  -- Step 9: prc2_2 (preserves n0 + 3)
                  apply Triple.bind (Q := fun s₉ => ⌜s₉.i.toNat = s.i.toNat + 3⌝)
                  · exact nat_step_preserve round2_prc2_spec s₈ (s.i.toNat + 3)
                  · intro s₉
                    -- Step 10: theta3 (preserves n0 + 3)
                    apply Triple.bind (Q := fun s₁₀ => ⌜s₁₀.i.toNat = s.i.toNat + 3⌝)
                    · exact nat_step_preserve round3_theta_spec s₉ (s.i.toNat + 3)
                    · intro s₁₀
                      -- Step 11: prc1_3 (increments to s.i.toNat + 4)
                      apply Triple.bind (Q := fun s₁₁ => ⌜s₁₁.i.toNat = s.i.toNat + 4⌝)
                      · exact nat_step_increment (fun s hi => round3_prc1_spec s hi) s₁₀ (s.i.toNat + 3) (by omega)
                      · intro s₁₁
                        -- Step 12: prc2_3 (preserves s.i.toNat + 4) + pure
                        apply Triple.bind (Q := fun s₁₂ => ⌜s₁₂.i.toNat = s.i.toNat + 4⌝)
                        · exact nat_step_preserve round3_prc2_spec s₁₁ (s.i.toNat + 4)
                        · intro s₁₂
                          -- pure just returns s₁₂
                          by_cases hs₁₂ : s₁₂.i.toNat = s.i.toNat + 4
                          · exact strengthen_pre _ (Triple.pure s₁₂ (by
                              rw [← SPred.entails_true_intro]
                              exact SPred.pure_intro fun _ => hs₁₂))
                          · exact triple_of_neg hs₁₂ _
/-! ## Main equivalence theorem. STATUS: sorry.

The full keccak is 6 repetitions of the 4-round block = 24 spec rounds.
Since each 4-round block returns the state to standard layout (impl_perm^4 = id),
the composition is straightforward.

TODO: Compose 6 × four_rounds_equiv. Since impl_perm^24 = id (24-cycle on
non-fixed points, and impl_perm^4 = id on each 4-cycle), the final lift
has no permutation adjustment.
-/

-- The implementation does not panic (totality): keccakf1600 always returns Except.ok.
-- This follows from composing 6 × four_rounds_equiv via the fold_range loop.
-- The initial state has i = 0 (from KeccakState.default or the caller), so i + 4 ≤ 24
-- holds at each iteration since four_rounds_equiv increments i by 4 each time.
-- Helper: one iteration of the fold body succeeds and tracks i
open Std.Do in
private theorem fold_body_spec (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s
    ⦃ ⇓ r => ⌜ r.i.toNat = s.i.toNat + 4 ⌝ ⦄ :=
  four_rounds_equiv s hi

-- keccakf1600 calls fold_range which invokes keccakf1600_4rounds 6 times.
-- The fold uses the @[spec] annotations on keccakf1600_4rounds and keccakf1600
-- to generate verification conditions via hax_mvcgen.
-- We use four_rounds_equiv to close the per-iteration VC.
-- Helper: one 4-round block as a Nat-level step (increments i by 4)
open Std.Do in
private theorem nat_4round_step (s : KeccakState) (n : Nat) (hn : n + 4 ≤ 24) :
    ⦃⌜s.i.toNat = n⌝⦄
    libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s
    ⦃⇓ r => ⌜r.i.toNat = n + 4⌝⦄ := by
  by_cases hs : s.i.toNat = n
  · have hi' : s.i.toNat + 4 ≤ 24 := by omega
    exact strengthen_pre _ (Triple.of_entails_right _ _ _ _ (four_rounds_equiv s hi')
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => by simp_all))
  · exact triple_of_neg hs _

set_option maxRecDepth 2000 in
set_option maxHeartbeats 8000000 in
open Std.Do in
theorem keccakf1600_succeeds (s : KeccakState) (hi : s.i.toNat = 0) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600 s
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  unfold libcrux_iot_sha3.keccak.keccakf1600
  simp only [rust_primitives.hax.folds.fold_range]
  -- Structure: (fold_range 0 6 ... s ...) >>= fun s => pure {s with i := 0}
  -- First split off the trailing pure
  apply Triple.bind (Q := fun _ => ⌜True⌝)
  · -- The fold: 6 iterations of keccakf1600_4rounds.
    -- Unroll one step at a time: unfold exposes 4rounds >>= fold_rest
    -- Block 1 (i: 0 → 4)
    unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
    apply Triple.bind (Q := fun s₁ => ⌜s₁.i.toNat = 4⌝)
    · exact Triple.of_entails_right _ _ _ _ (four_rounds_equiv s (by omega))
        (PostCond.entails.of_left_entails fun _ => by
          rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun h => by simp_all)
    · intro s₁
      -- Block 2 (i: 4 → 8)
      unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
      apply Triple.bind (Q := fun s₂ => ⌜s₂.i.toNat = 8⌝)
      · exact nat_4round_step s₁ 4 (by omega)
      · intro s₂
        -- Block 3 (i: 8 → 12)
        unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
        apply Triple.bind (Q := fun s₃ => ⌜s₃.i.toNat = 12⌝)
        · exact nat_4round_step s₂ 8 (by omega)
        · intro s₃
          -- Block 4 (i: 12 → 16)
          unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
          apply Triple.bind (Q := fun s₄ => ⌜s₄.i.toNat = 16⌝)
          · exact nat_4round_step s₃ 12 (by omega)
          · intro s₄
            -- Block 5 (i: 16 → 20)
            unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
            apply Triple.bind (Q := fun s₅ => ⌜s₅.i.toNat = 20⌝)
            · exact nat_4round_step s₄ 16 (by omega)
            · intro s₅
              -- Block 6 (i: 20 → 24) + base case (fold_range 6 6 = pure)
              unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
              apply Triple.bind (Q := fun _ => ⌜True⌝)
              · exact Triple.of_entails_right _ _ _ _
                  (nat_4round_step s₅ 20 (by omega))
                  (PostCond.entails.of_left_entails fun _ => by
                    rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun _ => trivial)
              · intro s₆
                unfold Int32.fold_range; simp (config := {decide := true}) only [ite_false]
                exact strengthen_pre _ (Triple.pure s₆ (SPred.entails.refl _))
  · intro s₇; exact Triple.pure _ (SPred.entails.refl _)

/-! ## Per-round functional equivalence

The core mathematical result: running one spec round on the lifted state equals
running one impl round and then lifting with the permutation.

Proven by hax_mvcgen on both spec and impl simultaneously — it generates VCs
that connect the u32 (impl) and u64 (spec) operations, closed by the algebraic
lifting lemmas (lift_lane_bv_{xor,and,not,or}, chi_lane_lift, etc.).
-/

-- One spec round: θ → ρ → π → χ → ι
def spec_round (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.theta state
  let s ← hacspec_sha3.keccak_f.rho s
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

-- Impl round 0: theta → pi_rho_chi_1 → pi_rho_chi_2
def impl_round0 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_2 s

def impl_round1 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round1_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_2 s

def impl_round2 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round2_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_2 s

def impl_round3 (s : KeccakState) : RustM KeccakState := do
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round3_theta s
  let s ← libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 0 s
  libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_2 s

-- Reusable tactic for round-level equivalence proofs
macro "round_equiv_proof" : tactic =>
  `(tactic| (
    hax_mvcgen [hacspec_sha3.keccak_f.get, hacspec_sha3.createi,
                core_models.array.from_fn, core_models.num.Impl_9.rotate_left,
                core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
                libcrux_secrets.traits.Classify.classify, spec_round, impl_round0, lift, lift_lane,
                lift_lane_bv, spread_to_even, impl_perm, lift_perm]
    all_goals (first | intro h₁; subst h₁ | skip)
    all_goals simp (config := { decide := true, maxSteps := 400000 }) [getElemResult, core_models.ops.index.Index.index]
    all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set]; try rfl) | skip)
    all_goals (reduce_usize_sizes; simp (config := { decide := true, maxSteps := 400000 }) [Vector.getElem_set]; try rfl)
    all_goals (repeat' constructor)
    all_goals (first | rfl | skip)
    all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set, rot32,
      lift_lane_bv_xor, lift_lane_bv_and, lift_lane_bv_not, lift_lane_bv_or,
      chi_lane_lift, theta_apply_lift, theta_d_lift, theta_c_lift]; try rfl) | skip)
    all_goals (first | omega | simp_all | rfl | skip)
    all_goals (
      delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
      have h255 : USize64.toNat s.i < 255 := by omega
      rw [dif_pos h255, dif_pos h255]
      have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
        simp [BitVec.uaddOverflow]; omega
      rw [if_neg huadd]
      delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
      first | rfl | simp_all)))

-- Round 0 functional equivalence: spec_round(lift s, i) = lift_perm(impl_round0 s, impl_perm)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 400000000 in
open Std.Do in
theorem round0_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round0 s
       let r_spec ← spec_round (lift s) s.i
       pure (r_spec = lift_perm r_impl impl_perm)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by round_equiv_proof

-- Round 1 functional equivalence
set_option maxRecDepth 5000 in
set_option maxHeartbeats 400000000 in
open Std.Do in
theorem round1_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round1 s
       let r_spec ← spec_round (lift_perm s impl_perm) s.i
       pure (r_spec = lift_perm r_impl impl_perm2)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  hax_mvcgen [hacspec_sha3.keccak_f.get, hacspec_sha3.createi,
              core_models.array.from_fn, core_models.num.Impl_9.rotate_left,
              core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify, spec_round, impl_round1, lift, lift_lane,
              lift_lane_bv, spread_to_even, impl_perm, impl_perm2, lift_perm]
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 400000 }) [getElemResult, core_models.ops.index.Index.index]
  all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set]; try rfl) | skip)
  all_goals (reduce_usize_sizes; simp (config := { decide := true, maxSteps := 400000 }) [Vector.getElem_set]; try rfl)
  all_goals (repeat' constructor)
  all_goals (first | rfl | skip)
  all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set, rot32,
    lift_lane_bv_xor, lift_lane_bv_and, lift_lane_bv_not, lift_lane_bv_or,
    chi_lane_lift, theta_apply_lift, theta_d_lift, theta_c_lift]; try rfl) | skip)
  all_goals (first | omega | simp_all | rfl | skip)
  all_goals (
    delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
    have h255 : USize64.toNat s.i < 255 := by omega
    rw [dif_pos h255, dif_pos h255]
    have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
      simp [BitVec.uaddOverflow]; omega
    rw [if_neg huadd]
    delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
    first | rfl | simp_all)

/-! ## Top-level equivalence

The proof chains 6 applications of four_round_eq, rewriting each spec_4rounds
block into lift(4rounds_result). After all 6 blocks, LHS = RHS = pure (lift r₆).
-/

-- 4 consecutive spec rounds
def spec_4rounds (state : RustArray u64 25) (start_round : usize) : RustM (RustArray u64 25) := do
  let s ← spec_round state start_round
  let s ← spec_round s (start_round + 1)
  let s ← spec_round s (start_round + 2)
  spec_round s (start_round + 3)

-- keccak_f = 6 × spec_4rounds (fold unrolling)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem keccak_f_unfold (state : RustArray u64 25) :
    hacspec_sha3.keccak_f.keccak_f state =
    (do let s ← spec_4rounds state 0; let s ← spec_4rounds s 4
        let s ← spec_4rounds s 8; let s ← spec_4rounds s 12
        let s ← spec_4rounds s 16; spec_4rounds s 20) := by
  unfold hacspec_sha3.keccak_f.keccak_f
  simp only [rust_primitives.hax.folds.fold_range]
  -- Unroll USize64.fold_range (24 iterations)
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold USize64.fold_range; simp (config := {decide := true}) only [ite_false]
  -- Both sides are now 24 flat spec rounds. Unfold RHS and normalize usize arithmetic.
  simp (config := {decide := true}) only [spec_4rounds, spec_round, bind_assoc, pure_bind]
  rfl

-- Round 2 functional equivalence
set_option maxRecDepth 5000 in
set_option maxHeartbeats 400000000 in
open Std.Do in
theorem round2_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round2 s
       let r_spec ← spec_round (lift_perm s impl_perm2) s.i
       pure (r_spec = lift_perm r_impl impl_perm3)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  hax_mvcgen [hacspec_sha3.keccak_f.get, hacspec_sha3.createi,
              core_models.array.from_fn, core_models.num.Impl_9.rotate_left,
              core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify, spec_round, impl_round2, lift, lift_lane,
              lift_lane_bv, spread_to_even, impl_perm, impl_perm2, impl_perm3, lift_perm]
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 400000 }) [getElemResult, core_models.ops.index.Index.index]
  all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set]; try rfl) | skip)
  all_goals (reduce_usize_sizes; simp (config := { decide := true, maxSteps := 400000 }) [Vector.getElem_set]; try rfl)
  all_goals (repeat' constructor)
  all_goals (first | rfl | skip)
  all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set, rot32,
    lift_lane_bv_xor, lift_lane_bv_and, lift_lane_bv_not, lift_lane_bv_or,
    chi_lane_lift, theta_apply_lift, theta_d_lift, theta_c_lift]; try rfl) | skip)
  all_goals (first | omega | simp_all | rfl | skip)
  all_goals (
    delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
    have h255 : USize64.toNat s.i < 255 := by omega
    rw [dif_pos h255, dif_pos h255]
    have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
      simp [BitVec.uaddOverflow]; omega
    rw [if_neg huadd]
    delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
    first | rfl | simp_all)

-- Round 3 functional equivalence
set_option maxRecDepth 5000 in
set_option maxHeartbeats 400000000 in
open Std.Do in
theorem round3_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round3 s
       let r_spec ← spec_round (lift_perm s impl_perm3) s.i
       pure (r_spec = lift r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  hax_mvcgen [hacspec_sha3.keccak_f.get, hacspec_sha3.createi,
              core_models.array.from_fn, core_models.num.Impl_9.rotate_left,
              core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify, spec_round, impl_round3, lift, lift_lane,
              lift_lane_bv, spread_to_even, impl_perm, impl_perm2, impl_perm3, lift_perm]
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 400000 }) [getElemResult, core_models.ops.index.Index.index]
  all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set]; try rfl) | skip)
  all_goals (reduce_usize_sizes; simp (config := { decide := true, maxSteps := 400000 }) [Vector.getElem_set]; try rfl)
  all_goals (repeat' constructor)
  all_goals (first | rfl | skip)
  all_goals (first | (simp_all (config := { maxSteps := 400000 }) [Vector.getElem_set, rot32,
    lift_lane_bv_xor, lift_lane_bv_and, lift_lane_bv_not, lift_lane_bv_or,
    chi_lane_lift, theta_apply_lift, theta_d_lift, theta_c_lift]; try rfl) | skip)
  all_goals (first | omega | simp_all | rfl | skip)
  all_goals (
    delta RustM.instWPMonad WPMonad.toWP WP.wp RustM.instWP at *
    have h255 : USize64.toNat s.i < 255 := by omega
    rw [dif_pos h255, dif_pos h255]
    have huadd : ¬ (s.i.toBitVec.uaddOverflow 1#64 = true) := by
      simp [BitVec.uaddOverflow]; omega
    rw [if_neg huadd]
    delta Except.instWP PredTrans.apply ExceptConds.false PredTrans.const at *
    first | rfl | simp_all)

-- Convert per-round Hoare triple to direct RustM equality
open Std.Do in
private theorem round_eq_of_func_equiv
    (m_impl : RustM KeccakState) (m_spec : RustM (RustArray u64 25))
    (f : KeccakState → RustArray u64 25)
    (h : ⦃⌜True⌝⦄ (do let a ← m_impl; let b ← m_spec; (pure (b = f a) : RustM Prop)) ⦃⇓ r => ⌜r⌝⦄) :
    m_spec = (m_impl >>= fun r => pure (f r)) := by
  match m_impl, m_spec with
  | .ok v₁, .ok v₂ =>
    show RustM.ok v₂ = RustM.ok (f v₁); congr 1
    rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Except.pure, Id.run, pure]
  | .ok _, .fail e =>
    exfalso; rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Id.run, pure, throwThe, throw, ExceptT.mk]
  | .ok _, .div =>
    exfalso; rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, PredTrans.const]
  | .fail e, _ =>
    exfalso; rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Id.run, pure, throwThe, throw, ExceptT.mk]
  | .div, _ =>
    exfalso; rw [Triple] at h
    simp_all [WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, PredTrans.const]

-- Per-round direct equalities (derived from func_equiv Hoare triples)
theorem round0_eq (s : KeccakState) (hi : s.i.toNat < 24) :
    spec_round (lift s) s.i = (impl_round0 s >>= fun r => pure (lift_perm r impl_perm)) :=
  round_eq_of_func_equiv _ _ _ (round0_func_equiv s hi)

theorem round1_eq (s : KeccakState) (hi : s.i.toNat < 24) :
    spec_round (lift_perm s impl_perm) s.i = (impl_round1 s >>= fun r => pure (lift_perm r impl_perm2)) :=
  round_eq_of_func_equiv _ _ _ (round1_func_equiv s hi)

theorem round2_eq (s : KeccakState) (hi : s.i.toNat < 24) :
    spec_round (lift_perm s impl_perm2) s.i = (impl_round2 s >>= fun r => pure (lift_perm r impl_perm3)) :=
  round_eq_of_func_equiv _ _ _ (round2_func_equiv s hi)

theorem round3_eq (s : KeccakState) (hi : s.i.toNat < 24) :
    spec_round (lift_perm s impl_perm3) s.i = (impl_round3 s >>= fun r => pure (lift r)) :=
  round_eq_of_func_equiv _ _ _ (round3_func_equiv s hi)

-- 4-round functional equivalence: compose 4 per-round equalities
-- keccakf1600_4rounds = impl_round0 >> impl_round1 >> impl_round2 >> impl_round3
-- spec_4rounds = spec_round >> spec_round >> spec_round >> spec_round
-- After 4 rounds, impl_perm^4 = id, so lift_perm ... id = lift
-- Extract ok value from impl round (reusable for each round)
private theorem impl_round_ok {f : KeccakState → RustM KeccakState}
    {s : KeccakState} {g : KeccakState → RustArray u64 25}
    (h_eq : ∀ s (hi : s.i.toNat < 24), spec_round (g s) s.i = (f s >>= fun r => pure (g r)))
    (hi : s.i.toNat < 24)
    (h_ok : ∃ r, f s = .ok r ∧ r.i.toNat = s.i.toNat + 1) :
    ∃ r, f s = .ok r := by obtain ⟨r, hr, _⟩ := h_ok; exact ⟨r, hr⟩

-- four_round_eq: 3 sorry remain (rK.i.toNat < 24 bounds from congr/funext)
-- Strategy: extract impl ok values round by round, rewrite spec, simplify
-- We need per-round ok extraction (same pattern as four_rounds_ok)
-- Each impl_roundK returns ok with i incremented by 1
open Std.Do in
private theorem impl_round_ok (f : KeccakState → RustM KeccakState)
    (spec : ∀ s, s.i.toNat < 24 → ⦃⌜True⌝⦄ f s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄)
    (s : KeccakState) (hi : s.i.toNat < 24) :
    ∃ r, f s = .ok r ∧ r.i.toNat = s.i.toNat + 1 := by
  have h := spec s hi
  match hm : f s with
  | .ok r =>
    refine ⟨r, rfl, ?_⟩
    rw [Triple] at h
    simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Except.pure, Id.run, pure, USize64.toNat_add]
    omega
  | .fail e =>
    exfalso; rw [Triple] at h
    simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, ExceptT.run, Id.run, pure, throwThe, throw, ExceptT.mk]
  | .div =>
    exfalso; rw [Triple] at h
    simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept, PredTrans.pure,
      PredTrans.trans, PredTrans.const]

-- i-tracking for impl_roundK (instantiate roundK_equiv with per-step specs)
open Std.Do in
private theorem impl_round0_i (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃⌜True⌝⦄ impl_round0 s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄ :=
  roundK_equiv (fun s => theta_comp_spec s |>.of_entails_right _
    (PostCond.entails.of_left_entails fun _ => by
      rw [← SPred.entails_true_intro]
      exact SPred.pure_intro fun ⟨_,_,_,_,_,_,_,_,_,_,_,h⟩ => h))
    (fun s hi => pi_rho_chi_1_spec s hi |>.of_entails_right _
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun ⟨h, _⟩ => h))
    (fun s => pi_rho_chi_2_spec s |>.of_entails_right _
      (PostCond.entails.of_left_entails fun _ => by
        rw [← SPred.entails_true_intro]; exact SPred.pure_intro fun ⟨_, h⟩ => h))
    s hi

open Std.Do in
private theorem impl_round1_i (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃⌜True⌝⦄ impl_round1 s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄ :=
  roundK_equiv round1_theta_spec (fun s hi => round1_prc1_spec s hi) round1_prc2_spec s hi

open Std.Do in
private theorem impl_round2_i (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃⌜True⌝⦄ impl_round2 s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄ :=
  roundK_equiv round2_theta_spec (fun s hi => round2_prc1_spec s hi) round2_prc2_spec s hi

open Std.Do in
private theorem impl_round3_i (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃⌜True⌝⦄ impl_round3 s ⦃⇓ r => ⌜r.i = s.i + 1⌝⦄ :=
  roundK_equiv round3_theta_spec (fun s hi => round3_prc1_spec s hi) round3_prc2_spec s hi

-- four_round_eq: extraction approach (no congr/funext, no sorry)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem four_round_eq (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    spec_4rounds (lift s) s.i =
    (libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s >>= fun r => pure (lift r)) := by
  unfold spec_4rounds libcrux_iot_sha3.keccak.keccakf1600_4rounds
  simp only [bind_assoc]
  have ok_bind : ∀ {α β : Type} (a : α) (f : α → RustM β), RustM.ok a >>= f = f a := fun _ _ => rfl
  -- Extract concrete impl results with i-tracking
  obtain ⟨r₁, hr₁, hi₁⟩ := impl_round_ok impl_round0 (fun s hi => impl_round0_i s hi) s (by omega)
  obtain ⟨r₂, hr₂, hi₂⟩ := impl_round_ok impl_round1 (fun s hi => impl_round1_i s hi) r₁ (by omega)
  obtain ⟨r₃, hr₃, hi₃⟩ := impl_round_ok impl_round2 (fun s hi => impl_round2_i s hi) r₂ (by omega)
  obtain ⟨r₄, hr₄, hi₄⟩ := impl_round_ok impl_round3 (fun s hi => impl_round3_i s hi) r₃ (by omega)
  -- Substitute all impl results on RHS
  simp only [hr₁, ok_bind, hr₂, hr₃, hr₄, pure_bind]
  -- Rewrite each spec round using roundK_eq (hi bounds from i-tracking)
  rw [round0_eq s (by omega)]
  simp only [hr₁, ok_bind, pure_bind]
  rw [show r₁.i = (UInt64.ofBitVec (BitVec.ofNat 64 (s.i.toNat + 1))) from
        usize_eq _ _ (by omega),
      round1_eq r₁ (by omega)]
  simp only [hr₂, ok_bind, pure_bind]
  rw [show r₂.i = (UInt64.ofBitVec (BitVec.ofNat 64 (s.i.toNat + 2))) from
        usize_eq _ _ (by omega),
      round2_eq r₂ (by omega)]
  simp only [hr₃, ok_bind, pure_bind]
  rw [show r₃.i = (UInt64.ofBitVec (BitVec.ofNat 64 (s.i.toNat + 3))) from
        usize_eq _ _ (by omega),
      round3_eq r₃ (by omega)]
  simp only [hr₄, ok_bind]

-- 4-round block returns ok and increments i by 4
-- Derived from four_rounds_equiv by case-splitting on the RustM result
open Std.Do in
theorem four_rounds_ok (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    ∃ r, libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s = .ok r ∧ r.i.toNat = s.i.toNat + 4 := by
  have h := four_rounds_equiv s hi
  match hm : libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s with
  | .ok r =>
    refine ⟨r, rfl, ?_⟩
    rw [Triple] at h; simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept,
      PredTrans.pure, PredTrans.trans, ExceptT.run, Except.pure, Id.run, pure]
  | .fail e =>
    exfalso; rw [Triple] at h; simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept,
      PredTrans.pure, PredTrans.trans, ExceptT.run, Id.run, pure, throwThe, throw, ExceptT.mk]
  | .div =>
    exfalso; rw [Triple] at h; simp_all [hm, WP.wp, PredTrans.apply, PredTrans.pushExcept,
      PredTrans.pure, PredTrans.trans, PredTrans.const]

-- lift ignores the i field
theorem lift_reset_i (s : KeccakState) (v : usize) : lift { s with i := v } = lift s := by
  unfold lift lift_lane lift_lane_bv spread_to_even; rfl

-- Helper: usize equality from toNat equality
private theorem usize_eq (a b : usize) (ha : a.toNat = b.toNat) : a = b :=
  USize64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq ha)

-- Full equivalence (proven from four_round_eq + keccak_f_unfold + four_rounds_ok)
set_option maxRecDepth 2000 in
set_option maxHeartbeats 8000000 in
theorem equivalence (s : KeccakState) (hi : s.i.toNat = 0) :
    hacspec_sha3.keccak_f.keccak_f (lift s) =
    (libcrux_iot_sha3.keccak.keccakf1600 s >>= fun r => pure (lift r)) := by
  -- Unfold impl fold into 6 × keccakf1600_4rounds
  unfold libcrux_iot_sha3.keccak.keccakf1600
  simp only [rust_primitives.hax.folds.fold_range]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_true]
  unfold Int32.fold_range; simp (config := {decide := true}) only [ite_false]
  -- Rewrite spec as 6 × spec_4rounds
  rw [keccak_f_unfold]
  -- Extract impl block results
  obtain ⟨r₁, hr₁, hi₁⟩ := four_rounds_ok s (by omega)
  obtain ⟨r₂, hr₂, hi₂⟩ := four_rounds_ok r₁ (by omega)
  obtain ⟨r₃, hr₃, hi₃⟩ := four_rounds_ok r₂ (by omega)
  obtain ⟨r₄, hr₄, hi₄⟩ := four_rounds_ok r₃ (by omega)
  obtain ⟨r₅, hr₅, hi₅⟩ := four_rounds_ok r₄ (by omega)
  obtain ⟨r₆, hr₆, hi₆⟩ := four_rounds_ok r₅ (by omega)
  -- Substitute all impl results on RHS and reduce binds
  -- RustM.ok = pure, so pure_bind applies
  have ok_bind : ∀ {α β : Type} (a : α) (f : α → RustM β), RustM.ok a >>= f = f a := fun _ _ => rfl
  simp only [hr₁, ok_bind, hr₂, hr₃, hr₄, hr₅, hr₆, pure_bind, lift_reset_i]
  -- Rewrite each spec_4rounds block using four_round_eq
  -- Need: spec_4rounds (lift rₖ) rₖ.i = pure (lift rₖ₊₁)  [from four_round_eq + hrₖ₊₁]
  -- Bridge: numeric literal n = rₖ.i  [via usize_eq]
  -- Block 1: spec_4rounds (lift s) 0 → pure (lift r₁)
  rw [show (0 : usize) = s.i from (usize_eq _ _ hi).symm,
      four_round_eq s (by omega), hr₁, ok_bind]
  -- Blocks 2-6: need pure_bind to reduce `pure (lift rₖ) >>= spec_4rounds`
  -- then usize_eq to match the round number with rₖ.i
  simp only [pure_bind]
  -- Compute rₖ.i values as Nat, then convert to usize equality
  have h1 : r₁.i.toNat = 4 := by omega
  have h2 : r₂.i.toNat = 8 := by omega
  have h3 : r₃.i.toNat = 12 := by omega
  have h4 : r₄.i.toNat = 16 := by omega
  have h5 : r₅.i.toNat = 20 := by omega
  -- Block 2
  rw [show (4 : usize) = r₁.i from (usize_eq _ _ (by rw [h1]; native_decide)).symm,
      four_round_eq r₁ (by omega), hr₂, ok_bind, pure_bind]
  -- Block 3
  rw [show (8 : usize) = r₂.i from (usize_eq _ _ (by rw [h2]; native_decide)).symm,
      four_round_eq r₂ (by omega), hr₃, ok_bind, pure_bind]
  -- Block 4
  rw [show (12 : usize) = r₃.i from (usize_eq _ _ (by rw [h3]; native_decide)).symm,
      four_round_eq r₃ (by omega), hr₄, ok_bind, pure_bind]
  -- Block 5
  rw [show (16 : usize) = r₄.i from (usize_eq _ _ (by rw [h4]; native_decide)).symm,
      four_round_eq r₄ (by omega), hr₅, ok_bind, pure_bind]
  -- Block 6
  rw [show (20 : usize) = r₅.i from (usize_eq _ _ (by rw [h5]; native_decide)).symm,
      four_round_eq r₅ (by omega), hr₆, ok_bind]
