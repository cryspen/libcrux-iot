/-
  θ-step impl/spec lifting — the public spec-coupling theorem.

  Helper definitions (`lift_theta_applied`, per-sub-function `@[spec]`s,
  `theta_comp_spec_local`, and the 25 `lift_getElem_bv_*` peel lemmas)
  live in `ThetaLiftDefs.lean`. This file only contains the final
  spec-coupling theorem `theta_lift_spec`, so editing its proof body
  does not invalidate downstream caches (`PrcLift` etc.) that only need
  the definitions.
-/
import LibcruxIotSha3.Equivalence.ThetaLiftDefs

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

attribute [local irreducible] spread_to_even lift_lane_bv

/-! Spec-coupling Triple for round-0 θ, in `.holds`-in-post form so it can
    be tagged `@[spec]` and used by `hax_mvcgen` whenever a downstream
    function calls `keccakf1600_round0_theta`. The post says: for the
    `r_impl` produced by impl-θ, the spec computation
    `theta_unrolled (lift s)` succeeds with result equal to
    `lift_theta_applied r_impl`. The `r_impl.i = s.i` conjunct lets
    downstream consumers (`prc_lift_spec`, `round0_equiv_spec`) discharge
    their `s.i.val < 24` preconditions on the θ output. -/
set_option maxHeartbeats 16000000 in
@[spec]
theorem theta_lift_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r_impl => ⌜
      r_impl.i = s.i ∧
      (do
        let r_spec ← keccak_f.theta_unrolled (lift s)
        pure (r_spec = lift_theta_applied r_impl)).holds ⌝ ⦄ := by
  apply Triple.of_entails_right _ (theta_comp_spec_local s)
  rw [PostCond.entails_noThrow]
  intro r_impl hpost
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
  refine ⟨hpost.2.1, ?_⟩
  unfold Aeneas.Std.Result.holds
  unfold keccak_f.theta_unrolled
  hax_mvcgen
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  -- all_goals try scalar_tac
  -- Main residual: Array.make 25 [r✝²⁴..r✝] = lift_theta_applied r_impl.
  -- Destructure the 12-conjunct theta_comp_spec_local post and the
  -- spec-side chain, then close 25 lanes pointwise via the lifting
  -- algebra (lift_getElem_bv + lift_xor5 + lift_td + lift_rot1).
  obtain ⟨hst, _, hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
          hd3z0, hd3z1, hd4z0, hd4z1⟩ := hpost
  apply Subtype.ext
  unfold lift_theta_applied
  simp only [Std.Array.make, hst,
             hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
             hd3z0, hd3z1, hd4z0, hd4z1]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  all_goals
    simp_all only [Std.UScalar.bv_xor, rot32,
      show ((0#usize : Std.Usize).val) = 0 from rfl,
      show ((1#usize : Std.Usize).val) = 1 from rfl,
      show ((2#usize : Std.Usize).val) = 2 from rfl,
      show ((3#usize : Std.Usize).val) = 3 from rfl,
      show ((4#usize : Std.Usize).val) = 4 from rfl,
      show ((5#usize : Std.Usize).val) = 5 from rfl,
      show ((6#usize : Std.Usize).val) = 6 from rfl,
      show ((7#usize : Std.Usize).val) = 7 from rfl,
      show ((8#usize : Std.Usize).val) = 8 from rfl,
      show ((9#usize : Std.Usize).val) = 9 from rfl,
      show ((10#usize : Std.Usize).val) = 10 from rfl,
      show ((11#usize : Std.Usize).val) = 11 from rfl,
      show ((12#usize : Std.Usize).val) = 12 from rfl,
      show ((13#usize : Std.Usize).val) = 13 from rfl,
      show ((14#usize : Std.Usize).val) = 14 from rfl,
      show ((15#usize : Std.Usize).val) = 15 from rfl,
      show ((16#usize : Std.Usize).val) = 16 from rfl,
      show ((17#usize : Std.Usize).val) = 17 from rfl,
      show ((18#usize : Std.Usize).val) = 18 from rfl,
      show ((19#usize : Std.Usize).val) = 19 from rfl,
      show ((20#usize : Std.Usize).val) = 20 from rfl,
      show ((21#usize : Std.Usize).val) = 21 from rfl,
      show ((22#usize : Std.Usize).val) = 22 from rfl,
      show ((23#usize : Std.Usize).val) = 23 from rfl,
      show ((24#usize : Std.Usize).val) = 24 from rfl,
      show ((1#u32 : Std.U32).val) = 1 from rfl]
  all_goals
    simp only [lift_getElem_bv_0, lift_getElem_bv_1, lift_getElem_bv_2,
      lift_getElem_bv_3, lift_getElem_bv_4, lift_getElem_bv_5,
      lift_getElem_bv_6, lift_getElem_bv_7, lift_getElem_bv_8,
      lift_getElem_bv_9, lift_getElem_bv_10, lift_getElem_bv_11,
      lift_getElem_bv_12, lift_getElem_bv_13, lift_getElem_bv_14,
      lift_getElem_bv_15, lift_getElem_bv_16, lift_getElem_bv_17,
      lift_getElem_bv_18, lift_getElem_bv_19, lift_getElem_bv_20,
      lift_getElem_bv_21, lift_getElem_bv_22, lift_getElem_bv_23,
      lift_getElem_bv_24]
  all_goals simp only [Std.UScalarTy.U64_numBits_eq, ← lift_xor, ← lift_td]

end libcrux_iot_sha3.Equivalence
