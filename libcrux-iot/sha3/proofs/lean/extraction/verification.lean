import extraction.libcrux_iot_sha3
import extraction.spec
import Std.Tactic.BVDecide
#check spec.theta
#check libcrux_iot_sha3.keccak.keccakf1600_round0_theta

open Std.Do
open Std.Tactic.BVDecide

theorem test (a : Vector UInt8 9) : (Vector.set (Vector.set a 0 0) 1 0)[0] = 0 := by
  simp only [Vector.getElem_set]
  bv_decide


@[spec]
theorem getElemResult_spec {s i} (hi : i < 2):
  ⦃ ⌜ True ⌝ ⦄
  @getElemResult libcrux_iot_sha3.lane.Lane2U32 usize u32 instGetElemResultOutputOfIndex_extraction s i
  ⦃ ⇓r => ⌜ r = s._0.toVec[0] ⌝ ⦄ := sorry

-- set_option pp.all true
theorem theta_spec (s : libcrux_iot_sha3.state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c00 s
    ⦃ ⇓r => ⌜
      r.c.toVec[0]._0.toVec[0] == s.st.toVec[0]._0.toVec[0] ^^^ s.st.toVec[1]._0.toVec[0] ^^^ s.st.toVec[2]._0.toVec[0] ^^^ s.st.toVec[3]._0.toVec[0] ^^^ s.st.toVec[4]._0.toVec[0]
     ⌝ ⦄ := by
  -- unfold libcrux_iot_sha3.keccak.keccakf1600_round0_theta_c00
  -- hax_bv_decide
  hax_mvcgen [instGetElemResultOutputOfIndex_extraction]
  expose_names
  unfold s_1
  simp [Vector.getElem_set] at *
  subst_vars
  rfl
  grind
  grind
  bv_decide
  bv_decide
  bv_decide
  bv_decide
  bv_decide
