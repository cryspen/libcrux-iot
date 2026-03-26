import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import extraction.spec_decomp
import extraction.lift_defs
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## Theta lifting: pure algebraic bridge

Strategy:
1. theta_comp_spec (in step_equiv, 2M heartbeats) gives d values via Hoare triple
2. Pure algebraic lemma connects d values to spec_theta_unrolled(lift(s))
3. No hax_mvcgen on the combined impl+spec — avoids term blowup

Key: spread_to_even and lift_lane_bv are @[irreducible] after proving lifting
lemmas by bv_decide. All rewriting uses these lemmas, never unfolding the
6-step bit-spreading chain.
-/

-- Lifting lemmas (proven before irreducible)
theorem lift_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

theorem lift_td (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) =
    lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

theorem lift_xor5 (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0 ^^^ c0 ^^^ d0 ^^^ e0) (a1 ^^^ b1 ^^^ c1 ^^^ d1 ^^^ e1) =
    lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 ^^^
    lift_lane_bv c0 c1 ^^^ lift_lane_bv d0 d1 ^^^
    lift_lane_bv e0 e1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

attribute [irreducible] spread_to_even lift_lane_bv

/-- Theta-applied lift: applies d[i/5] to st[i] (interleaved XOR) then lifts each lane. -/
def lift_theta_applied (s : KeccakState) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun (i : Fin 25) =>
    let x : Fin 5 := ⟨i.val / 5, by omega⟩
    UInt64.ofBitVec (lift_lane_bv
      ((s.st.toVec[i]._0.toVec[0] ^^^ s.d.toVec[x]._0.toVec[0]).toBitVec)
      ((s.st.toVec[i]._0.toVec[1] ^^^ s.d.toVec[x]._0.toVec[1]).toBitVec)))

/-! ## Pure algebraic bridge

Given concrete d values (from theta_comp_spec), show that
`spec_theta_unrolled(lift(s)) = .ok(lift_theta_applied({s with d := computed_d}))`.

This is proved WITHOUT hax_mvcgen — just algebraic rewriting with the
lifting lemmas. The key equations:
- `lift_lane_bv((a ⊕ b).toBitVec)((c ⊕ d).toBitVec) = lift_lane_bv(a.bv)(c.bv) ⊕ lift_lane_bv(b.bv)(d.bv)` (lift_xor)
- `lift_lane_bv((cL ⊕ rot(cR,1)).bv)((cL' ⊕ cR').bv) = lift_lane_bv(cL.bv)(cL'.bv) ⊕ rot(lift_lane_bv(cR.bv)(cR'.bv), 1)` (lift_td)
-/

-- TODO: Implement the pure algebraic bridge lemma.
-- The approach:
-- 1. State: for concrete d values matching theta_comp_spec postcondition,
--    spec_theta_unrolled(lift(s)) = .ok(lift_theta_applied({s with d = ...}))
-- 2. Proof: unfold spec_theta_unrolled (pure, no monadic complexity),
--    unfold lift_theta_applied, match lane-by-lane using lift_xor + lift_td
-- 3. Compose with theta_comp_spec via Triple.of_entails_right

-- For now, sorry the theorem to unblock prc_lift development:
set_option maxHeartbeats 800000 in
open Std.Do in
theorem theta_lift_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
       let r_spec ← spec_theta_unrolled (lift s)
       pure (r_spec = lift_theta_applied r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  sorry
