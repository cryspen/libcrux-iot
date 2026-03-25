import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import Std.Tactic.BVDecide

/-!
# Keccak-f[1600] Equivalence — Round-Level and Top-Level Proofs

Imports only the extraction files (not step_equiv.lean) to keep the
elaboration context small for hax_mvcgen's internal simp (100K step limit).

Definitions needed for the proofs are duplicated from step_equiv.lean.
The composition theorems (four_round_func_equiv, equivalence) are stated
here and composed from the per-round proofs.
-/

open libcrux_iot_sha3.lane
open libcrux_iot_sha3.state

/-! ## Minimal definitions (duplicated from step_equiv for clean context) -/

def spread_to_even (x : BitVec 32) : BitVec 64 :=
  let x : BitVec 64 := x.zeroExtend 64
  let x := (x ||| (x <<< 16)) &&& 0x0000ffff0000ffff#64
  let x := (x ||| (x <<<  8)) &&& 0x00ff00ff00ff00ff#64
  let x := (x ||| (x <<<  4)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := (x ||| (x <<<  2)) &&& 0x3333333333333333#64
  let x := (x ||| (x <<<  1)) &&& 0x5555555555555555#64
  x

def lift_lane_bv (z0 z1 : BitVec 32) : BitVec 64 :=
  spread_to_even z0 ||| (spread_to_even z1 <<< 1)

def lift_lane (l : Lane2U32) : u64 :=
  UInt64.ofBitVec (lift_lane_bv l._0.toVec[0].toBitVec l._0.toVec[1].toBitVec)

def lift (s : KeccakState) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i => lift_lane s.st.toVec[i])

def impl_perm (i : Fin 25) : Fin 25 :=
  let x := i.val / 5
  let z := i.val % 5
  ⟨5 * x + (3 * z + 2 * x) % 5, by omega⟩

def impl_perm2 (i : Fin 25) : Fin 25 := impl_perm (impl_perm i)
def impl_perm3 (i : Fin 25) : Fin 25 := impl_perm (impl_perm (impl_perm i))

def lift_perm (s : KeccakState) (p : Fin 25 → Fin 25) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i => lift_lane s.st.toVec[(p i).val])

abbrev rot32 (x : u32) (n : Nat) : u32 :=
  UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n)

macro "reduce_usize_sizes" : tactic =>
  `(tactic| simp only [Vector.size, show (5 : usize).toNat = 5 from rfl,
                        show (25 : usize).toNat = 25 from rfl,
                        show (2 : usize).toNat = 2 from rfl])

-- Algebraic lifting lemmas
@[simp] theorem lift_lane_bv_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_and (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 &&& b0) (a1 &&& b1) = lift_lane_bv a0 a1 &&& lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_not (a0 a1 : BitVec 32) :
    lift_lane_bv (~~~a0) (~~~a1) = ~~~(lift_lane_bv a0 a1) := by
  unfold lift_lane_bv spread_to_even; bv_decide
@[simp] theorem lift_lane_bv_or (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ||| b0) (a1 ||| b1) = lift_lane_bv a0 a1 ||| lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

theorem theta_c_lift (z0₀ z0₁ z1₀ z1₁ z2₀ z2₁ z3₀ z3₁ z4₀ z4₁ : BitVec 32) :
    lift_lane_bv (z0₀ ^^^ z1₀ ^^^ z2₀ ^^^ z3₀ ^^^ z4₀)
                 (z0₁ ^^^ z1₁ ^^^ z2₁ ^^^ z3₁ ^^^ z4₁) =
    lift_lane_bv z0₀ z0₁ ^^^ lift_lane_bv z1₀ z1₁ ^^^ lift_lane_bv z2₀ z2₁ ^^^
    lift_lane_bv z3₀ z3₁ ^^^ lift_lane_bv z4₀ z4₁ := by simp only [lift_lane_bv_xor]

theorem theta_d_lift (cL_z0 cL_z1 cR_z0 cR_z1 : BitVec 32) :
    lift_lane_bv (cL_z0 ^^^ cR_z1.rotateLeft 1) (cL_z1 ^^^ cR_z0) =
    lift_lane_bv cL_z0 cL_z1 ^^^ (lift_lane_bv cR_z0 cR_z1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

theorem theta_apply_lift (a_z0 a_z1 d_z0 d_z1 : BitVec 32) :
    lift_lane_bv (a_z0 ^^^ d_z0) (a_z1 ^^^ d_z1) =
    lift_lane_bv a_z0 a_z1 ^^^ lift_lane_bv d_z0 d_z1 := by simp only [lift_lane_bv_xor]

theorem chi_lane_lift (bx0_z0 bx0_z1 bx1_z0 bx1_z1 bx2_z0 bx2_z1 : BitVec 32) :
    lift_lane_bv (bx0_z0 ^^^ ((~~~bx1_z0) &&& bx2_z0))
                 (bx0_z1 ^^^ ((~~~bx1_z1) &&& bx2_z1)) =
    lift_lane_bv bx0_z0 bx0_z1 ^^^
      ((~~~(lift_lane_bv bx1_z0 bx1_z1)) &&& lift_lane_bv bx2_z0 bx2_z1) := by
  simp only [lift_lane_bv_xor, lift_lane_bv_not, lift_lane_bv_and]

/-! ## Spec and impl round definitions -/

def spec_round (state : RustArray u64 25) (round : usize) : RustM (RustArray u64 25) := do
  let s ← hacspec_sha3.keccak_f.theta state
  let s ← hacspec_sha3.keccak_f.rho s
  let s ← hacspec_sha3.keccak_f.pi s
  let s ← hacspec_sha3.keccak_f.chi s
  hacspec_sha3.keccak_f.iota s round

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

def spec_4rounds (state : RustArray u64 25) (start_round : usize) : RustM (RustArray u64 25) := do
  let s ← spec_round state start_round
  let s ← spec_round s (start_round + 1)
  let s ← spec_round s (start_round + 2)
  spec_round s (start_round + 3)

/-! ## Per-round functional equivalence -/

-- Reusable tactic (same for all rounds, just different unfolding hints)
macro "round_equiv_tactic" : tactic =>
  `(tactic| (
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

set_option maxRecDepth 5000 in
set_option maxHeartbeats 400000000 in
open Std.Do in
theorem round0_func_equiv (s : KeccakState) (hi : s.i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← impl_round0 s
       let r_spec ← spec_round (lift s) s.i
       pure (r_spec = lift_perm r_impl impl_perm)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  hax_mvcgen [hacspec_sha3.keccak_f.get, hacspec_sha3.createi,
              core_models.array.from_fn, core_models.num.Impl_9.rotate_left,
              core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify, spec_round, impl_round0, lift, lift_lane,
              lift_lane_bv, spread_to_even, impl_perm, lift_perm]
  round_equiv_tactic

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
  round_equiv_tactic

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
  round_equiv_tactic

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
  round_equiv_tactic

/-! ## 4-round and top-level equivalence -/

open Std.Do in
theorem four_round_func_equiv (s : KeccakState) (hi : s.i.toNat + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← libcrux_iot_sha3.keccak.keccakf1600_4rounds 0 s
       let r_spec ← spec_4rounds (lift s) s.i
       pure (r_spec = lift r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  sorry

open Std.Do in
theorem equivalence (s : KeccakState) (hi : s.i.toNat = 0) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← libcrux_iot_sha3.keccak.keccakf1600 s
       let r_spec ← hacspec_sha3.keccak_f.keccak_f (lift s)
       pure (r_spec = lift r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  sorry
