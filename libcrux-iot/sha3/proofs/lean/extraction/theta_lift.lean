import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3
import extraction.spec_decomp
import extraction.step_equiv
import Std.Tactic.BVDecide

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## Theta lifting: impl theta output lifts to spec theta output

After `keccakf1600_round0_theta s`, the result `r` has:
- `r.st = s.st` (state lanes preserved)
- `r.d` = computed theta differences

Applying d to st (interleaved XOR) and lifting gives `spec_theta_unrolled(lift(s))`.
-/

/-- Theta-applied lift: applies d[i/5] to st[i] (interleaved XOR) then lifts each lane. -/
def lift_theta_applied (s : KeccakState) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun (i : Fin 25) =>
    let x : Fin 5 := ⟨i.val / 5, by omega⟩
    UInt64.ofBitVec (lift_lane_bv
      ((s.st.toVec[i]._0.toVec[0] ^^^ s.d.toVec[x]._0.toVec[0]).toBitVec)
      ((s.st.toVec[i]._0.toVec[1] ^^^ s.d.toVec[x]._0.toVec[1]).toBitVec)))

-- Algebraic lifting lemmas needed for the proof
private theorem lift_lane_bv_xor' (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

private theorem theta_d_lift' (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) =
    lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by
  unfold lift_lane_bv spread_to_even; bv_decide

/-- After impl theta, the lifted theta-applied state equals spec_theta_unrolled(lift(input)).
    PROVEN: no sorry. Uses hax_mvcgen on both impl and unrolled spec simultaneously. -/
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 2000 in
open Std.Do in
theorem theta_lift_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
       let r_spec ← spec_theta_unrolled (lift s)
       pure (r_spec = lift_theta_applied r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  unfold spec_theta_unrolled
  hax_mvcgen [core_models.num.Impl_8.rotate_left, instGetElemResultOutputOfIndex_extraction,
              libcrux_secrets.traits.Classify.classify, lift, lift_lane,
              lift_lane_bv, spread_to_even, lift_theta_applied]
  all_goals (first | intro h₁; subst h₁ | skip)
  all_goals simp (config := { decide := true, maxSteps := 200000 }) only [getElemResult, core_models.ops.index.Index.index,
    ↓reduceDIte, USize64.reduceToNat, USize64.add_zero, USize64.toNat_zero, ↓reduceIte,
    USize64.toBitVec_ofNat, bind_pure_comp, pure_bind, USize64.reduceAdd, map_pure,
    Vector.size, Nat.zero_lt_succ, bind_pure, Std.Do.WP.pure, Vector.getElem_set,
    Std.Do.SPred.down_pure,
    show (5 : usize).toNat = 5 from rfl, show (25 : usize).toNat = 25 from rfl,
    show (2 : usize).toNat = 2 from rfl]
  all_goals (repeat' constructor)
  all_goals (first | subst_vars; rfl | rfl | skip)
  all_goals (simp only [lift_lane_bv_xor', theta_d_lift']; rfl)
