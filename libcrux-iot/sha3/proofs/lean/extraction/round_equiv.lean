/-!
# Per-round functional equivalence proofs

These are in a separate file to keep the elaboration context lean —
hax_mvcgen's internal simp (100K step limit) fails when the context
has too many definitions/instances loaded.
-/
import extraction.equiv

open libcrux_iot_sha3.lane
open libcrux_iot_sha3.state

-- Round 0 functional equivalence
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
       pure (r_spec = lift r_impl)  -- impl_perm^4 = id
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
