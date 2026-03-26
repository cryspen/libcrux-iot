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

Applying d to st (interleaved XOR) and lifting gives `spec_theta(lift(s))`.
-/

/-- Theta-applied lift: applies d[i/5] to st[i] (interleaved XOR) then lifts each lane. -/
def lift_theta_applied (s : KeccakState) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun (i : Fin 25) =>
    let x : Fin 5 := ⟨i.val / 5, by omega⟩
    UInt64.ofBitVec (lift_lane_bv
      ((s.st.toVec[i]._0.toVec[0] ^^^ s.d.toVec[x]._0.toVec[0]).toBitVec)
      ((s.st.toVec[i]._0.toVec[1] ^^^ s.d.toVec[x]._0.toVec[1]).toBitVec)))

/-- After impl theta, the lifted theta-applied state equals spec_theta(lift(input)). -/
set_option maxHeartbeats 2000000 in
open Std.Do in
theorem theta_lift_spec (s : KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜
      r.st = s.st ∧ r.i = s.i ∧
      spec_theta (lift s) = .ok (lift_theta_applied r)
    ⌝ ⦄ := by
  sorry
