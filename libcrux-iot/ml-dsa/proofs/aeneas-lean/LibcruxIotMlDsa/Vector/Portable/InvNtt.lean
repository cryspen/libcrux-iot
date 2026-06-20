/-
  # `Vector/Portable/InvNtt.lean` — Layer-0 within-SIMD-unit inverse butterflies (ML-DSA)

  Inverse (Gentleman–Sande) analogue of `Vector/Portable/Ntt.lean`
  (`simd_unit_ntt_at_layer_0_fc`). The keystone inverse butterfly FC that sets
  the proof template for the within-`Coefficients` inverse-NTT layers.

  - **`simd_unit_invert_ntt_at_layer_0_fc`** —
    `simd.portable.invntt.simd_unit_invert_ntt_at_layer_0` is a straight-line
    (no loop) sequence of 4 Gentleman–Sande pairs over the lanes
    `(0,1)/(2,3)/(4,5)/(6,7)`, each with its own zeta. For a pair `(lo, hi)` with
    zeta `z`:
    ```
    a_minus_b ← values[hi] - values[lo]                     -- CHECKED i32 sub
    out[lo]   ← values[lo] + values[hi]                     -- CHECKED i32 add
    out[hi]   ← montgomery_multiply_fe_by_fer a_minus_b z   -- t = (hi - lo)·z·R⁻¹
    ```
    Unlike the forward butterfly, the Montgomery multiply is applied to the
    DIFFERENCE, AFTER the checked `±`. Both inputs to each `±` are `B`-bounded,
    so `|result| ≤ 2B`; the no-overflow condition is `2B ≤ 2^31 - 1`. Each output
    lane lifts (Montgomery-strip) to the clean inverse butterfly:
    `liftZ out[lo] = liftZ values[lo] + liftZ values[hi]` (clean ADD) and
    `liftZ out[hi] = (liftZ values[hi] - liftZ values[lo]) · liftZ z`.

  Composition seams (all from `Spec/Lift.lean`):
  * **mont-mul seam** `liftZ_of_mont` — turns the leaf's
    `(t : Z_q) = (a_minus_b)(z)·R⁻¹` into `liftZ t = liftZ a_minus_b · liftZ z`.
  * **additive seams** `liftZ_add` / `liftZ_sub` — push `liftZ` across the
    checked `±` value equations.
-/
import LibcruxIotMlDsa.Vector.Portable.Element

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.InvNtt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_dsa.Util.LoopHelper
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters

/-! ## Local Triple ↔ Result.ok bridges (file-scoped copies of the §13.5 helpers). -/

/-- `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`. -/
private theorem triple_of_ok
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-- Reflect a `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` Triple into an `.ok` witness plus the post. -/
private theorem triple_exists_ok
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- `classify` is the identity (`ok a`). -/
private theorem classify_ok (z : Std.I32) :
    libcrux_secrets.traits.Classify.Blanket.classify z = .ok z := rfl

/-! ## Checked `i32` `±` no-overflow bridges (two `B`-bounded inputs).

The inverse layer-0 body uses the CHECKED `Std.I32` `Sub`/`Add` (monadic, can
panic) on TWO input lanes, each `|·| ≤ B`. Under `2B ≤ 2^31 - 1`, the result is
in bounds, so the op is `.ok` with the exact integer value and `|x ± y| ≤ 2B`. -/

/-- `|x ± y| ≤ 2B` from `|x| ≤ B`, `|y| ≤ B` (triangle ineq.). -/
private theorem sum_abs_bound2 (x y : Int) (B : Nat)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B) :
    (x + y).natAbs ≤ 2 * B ∧ (x - y).natAbs ≤ 2 * B := by
  have h_tri_add : (x + y).natAbs ≤ x.natAbs + y.natAbs := Int.natAbs_add_le _ _
  have h_eq : x - y = x + (-y) := by ring
  have h_tri_sub : (x - y).natAbs ≤ x.natAbs + y.natAbs := by
    rw [h_eq]
    have := Int.natAbs_add_le x (-y)
    rw [Int.natAbs_neg] at this
    exact this
  exact ⟨by omega, by omega⟩

/-- Checked i32 subtraction is `.ok` with value `x - y` under the two-input bound. -/
private theorem checked_sub_ok2 (x y : Std.I32) (B : Nat)
    (hx : x.val.natAbs ≤ B) (hy : y.val.natAbs ≤ B)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1) :
    ∃ z : Std.I32, (x - y : Result Std.I32) = .ok z ∧ z.val = x.val - y.val
      ∧ z.val.natAbs ≤ 2 * B := by
  have h_abs := (sum_abs_bound2 x.val y.val B hx hy).2
  have h_in : Aeneas.Std.IScalar.inBounds Aeneas.Std.IScalarTy.I32 (x.val - y.val) := by
    simp only [Aeneas.Std.IScalar.inBounds, Aeneas.Std.IScalarTy.I32_numBits_eq]
    have h_nat : (x.val - y.val).natAbs ≤ 2 * B := h_abs
    constructor
    · have : -(2 ^ 31 - 1 : Int) ≤ x.val - y.val := by omega
      have h31 : (-(2 : Int) ^ 31) ≤ -(2 ^ 31 - 1) := by norm_num
      omega
    · omega
  have h := Aeneas.Std.IScalar.sub_equiv x y
  cases hz : (x - y : Result Std.I32) with
  | ok z =>
    rw [hz] at h
    refine ⟨z, rfl, h.2.1, ?_⟩
    rw [h.2.1]; exact h_abs
  | fail e =>
    rw [hz] at h
    exact absurd h_in h
  | div =>
    rw [hz] at h
    exact h.elim

/-- Checked i32 addition is `.ok` with value `x + y` under the two-input bound. -/
private theorem checked_add_ok2 (x y : Std.I32) (B : Nat)
    (hx : x.val.natAbs ≤ B) (hy : y.val.natAbs ≤ B)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1) :
    ∃ z : Std.I32, (x + y : Result Std.I32) = .ok z ∧ z.val = x.val + y.val
      ∧ z.val.natAbs ≤ 2 * B := by
  have h_abs := (sum_abs_bound2 x.val y.val B hx hy).1
  have h_in : Aeneas.Std.IScalar.inBounds Aeneas.Std.IScalarTy.I32 (x.val + y.val) := by
    simp only [Aeneas.Std.IScalar.inBounds, Aeneas.Std.IScalarTy.I32_numBits_eq]
    have h_nat : (x.val + y.val).natAbs ≤ 2 * B := h_abs
    constructor
    · have : -(2 ^ 31 - 1 : Int) ≤ x.val + y.val := by omega
      have h31 : (-(2 : Int) ^ 31) ≤ -(2 ^ 31 - 1) := by norm_num
      omega
    · omega
  have h := Aeneas.Std.IScalar.add_equiv x y
  cases hz : (x + y : Result Std.I32) with
  | ok z =>
    rw [hz] at h
    refine ⟨z, rfl, h.2.1, ?_⟩
    rw [h.2.1]; exact h_abs
  | fail e =>
    rw [hz] at h
    exact absurd h_in h
  | div =>
    rw [hz] at h
    exact h.elim

/-! ## The keystone inverse butterfly FC. -/

@[spec]
theorem simd_unit_invert_ntt_at_layer_0_fc
    (simd_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (zeta0 zeta1 zeta2 zeta3 : Std.I32) (B : Nat)
    (hz0 : zeta0.val.natAbs ≤ 8380416) (hz1 : zeta1.val.natAbs ≤ 8380416)
    (hz2 : zeta2.val.natAbs ≤ 8380416) (hz3 : zeta3.val.natAbs ≤ 8380416)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1)
    (hin : ∀ j : Nat, j < 8 → (simd_unit.values.val[j]!).val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.invntt.simd_unit_invert_ntt_at_layer_0 simd_unit zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ (liftZ (r.values.val[0]!).val = liftZ (simd_unit.values.val[0]!).val + liftZ (simd_unit.values.val[1]!).val
              ∧ liftZ (r.values.val[1]!).val = (liftZ (simd_unit.values.val[1]!).val - liftZ (simd_unit.values.val[0]!).val) * liftZ zeta0.val
              ∧ liftZ (r.values.val[2]!).val = liftZ (simd_unit.values.val[2]!).val + liftZ (simd_unit.values.val[3]!).val
              ∧ liftZ (r.values.val[3]!).val = (liftZ (simd_unit.values.val[3]!).val - liftZ (simd_unit.values.val[2]!).val) * liftZ zeta1.val
              ∧ liftZ (r.values.val[4]!).val = liftZ (simd_unit.values.val[4]!).val + liftZ (simd_unit.values.val[5]!).val
              ∧ liftZ (r.values.val[5]!).val = (liftZ (simd_unit.values.val[5]!).val - liftZ (simd_unit.values.val[4]!).val) * liftZ zeta2.val
              ∧ liftZ (r.values.val[6]!).val = liftZ (simd_unit.values.val[6]!).val + liftZ (simd_unit.values.val[7]!).val
              ∧ liftZ (r.values.val[7]!).val = (liftZ (simd_unit.values.val[7]!).val - liftZ (simd_unit.values.val[6]!).val) * liftZ zeta3.val)
            ∧ (∀ j : Nat, j < 8 → (r.values.val[j]!).val.natAbs ≤ 2 * B + 2 ^ 24) ⌝ ⦄ := by
  have h_len : simd_unit.values.length = 8 := Coefficients_values_length simd_unit
  -- Abbreviate the 8 input lanes.
  set v0 : Std.I32 := simd_unit.values.val[0]! with hv0
  set v1 : Std.I32 := simd_unit.values.val[1]! with hv1
  set v2 : Std.I32 := simd_unit.values.val[2]! with hv2
  set v3 : Std.I32 := simd_unit.values.val[3]! with hv3
  set v4 : Std.I32 := simd_unit.values.val[4]! with hv4
  set v5 : Std.I32 := simd_unit.values.val[5]! with hv5
  set v6 : Std.I32 := simd_unit.values.val[6]! with hv6
  set v7 : Std.I32 := simd_unit.values.val[7]! with hv7
  -- Per-lane input bounds.
  have hb0 : v0.val.natAbs ≤ B := hin 0 (by norm_num)
  have hb1 : v1.val.natAbs ≤ B := hin 1 (by norm_num)
  have hb2 : v2.val.natAbs ≤ B := hin 2 (by norm_num)
  have hb3 : v3.val.natAbs ≤ B := hin 3 (by norm_num)
  have hb4 : v4.val.natAbs ≤ B := hin 4 (by norm_num)
  have hb5 : v5.val.natAbs ≤ B := hin 5 (by norm_num)
  have hb6 : v6.val.natAbs ≤ B := hin 6 (by norm_num)
  have hb7 : v7.val.natAbs ≤ B := hin 7 (by norm_num)
  -- Checked SUB (a_minus_b = v_hi - v_lo) and ADD (sum = v_lo + v_hi) per pair.
  obtain ⟨amb0, hamb0_eq, hamb0_val, hamb0_bd⟩ := checked_sub_ok2 v1 v0 B hb1 hb0 hB
  obtain ⟨s0, hs0_eq, hs0_val, hs0_bd⟩ := checked_add_ok2 v0 v1 B hb0 hb1 hB
  obtain ⟨amb1, hamb1_eq, hamb1_val, hamb1_bd⟩ := checked_sub_ok2 v3 v2 B hb3 hb2 hB
  obtain ⟨s1, hs1_eq, hs1_val, hs1_bd⟩ := checked_add_ok2 v2 v3 B hb2 hb3 hB
  obtain ⟨amb2, hamb2_eq, hamb2_val, hamb2_bd⟩ := checked_sub_ok2 v5 v4 B hb5 hb4 hB
  obtain ⟨s2, hs2_eq, hs2_val, hs2_bd⟩ := checked_add_ok2 v4 v5 B hb4 hb5 hB
  obtain ⟨amb3, hamb3_eq, hamb3_val, hamb3_bd⟩ := checked_sub_ok2 v7 v6 B hb7 hb6 hB
  obtain ⟨s3, hs3_eq, hs3_val, hs3_bd⟩ := checked_add_ok2 v6 v7 B hb6 hb7 hB
  -- mont-mul leaves on the DIFFERENCE: t_p = mmfbf amb_p zeta_p.
  obtain ⟨t0, ht0_eq, ht0_lift, ht0_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      amb0 zeta0 hz0)
  obtain ⟨t1, ht1_eq, ht1_lift, ht1_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      amb1 zeta1 hz1)
  obtain ⟨t2, ht2_eq, ht2_lift, ht2_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      amb2 zeta2 hz2)
  obtain ⟨t3, ht3_eq, ht3_lift, ht3_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      amb3 zeta3 hz3)
  -- ===== Index/update bridges (read the EXACT lane each step touches). =====
  -- Pair 0: hi=1, lo=0.  Reads simd_unit[1], simd_unit[0]; update 0 (s0) then update 1 (t0).
  have hi_v1 : Array.index_usize simd_unit.values 1#usize = .ok v1 :=
    array_index_usize_ok_eq simd_unit.values 1#usize (by rw [h_len]; decide)
  have hi_v0 : Array.index_usize simd_unit.values 0#usize = .ok v0 :=
    array_index_usize_ok_eq simd_unit.values 0#usize (by rw [h_len]; decide)
  have hu_a : Array.update simd_unit.values 0#usize s0
      = .ok (simd_unit.values.set 0#usize s0) :=
    array_update_ok_eq simd_unit.values 0#usize s0 (by rw [h_len]; decide)
  set a : CoeffArray := simd_unit.values.set 0#usize s0 with ha
  have ha_len : a.length = 8 := by rw [ha, Std.Array.set_length]; exact h_len
  have hu_a1 : Array.update a 1#usize t0 = .ok (a.set 1#usize t0) :=
    array_update_ok_eq a 1#usize t0 (by rw [ha_len]; decide)
  set a1 : CoeffArray := a.set 1#usize t0 with ha1
  have ha1_len : a1.length = 8 := by rw [ha1, Std.Array.set_length]; exact ha_len
  -- Pair 1: hi=3, lo=2.  a1[3] = v3, a1[2] = v2.
  have ha1_3 : a1.val[3]! = v3 := by
    rw [ha1, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha1_2 : a1.val[2]! = v2 := by
    rw [ha1, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a13 : Array.index_usize a1 3#usize = .ok v3 :=
    (array_index_usize_ok_eq a1 3#usize (by rw [ha1_len]; decide)).trans (congrArg Result.ok ha1_3)
  have hi_a12 : Array.index_usize a1 2#usize = .ok v2 :=
    (array_index_usize_ok_eq a1 2#usize (by rw [ha1_len]; decide)).trans (congrArg Result.ok ha1_2)
  have hu_a2 : Array.update a1 2#usize s1 = .ok (a1.set 2#usize s1) :=
    array_update_ok_eq a1 2#usize s1 (by rw [ha1_len]; decide)
  set a2 : CoeffArray := a1.set 2#usize s1 with ha2
  have ha2_len : a2.length = 8 := by rw [ha2, Std.Array.set_length]; exact ha1_len
  have hu_a3 : Array.update a2 3#usize t1 = .ok (a2.set 3#usize t1) :=
    array_update_ok_eq a2 3#usize t1 (by rw [ha2_len]; decide)
  set a3 : CoeffArray := a2.set 3#usize t1 with ha3
  have ha3_len : a3.length = 8 := by rw [ha3, Std.Array.set_length]; exact ha2_len
  -- Pair 2: hi=5, lo=4.  a3[5] = v5, a3[4] = v4.
  have ha3_5 : a3.val[5]! = v5 := by
    rw [ha3, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha3_4 : a3.val[4]! = v4 := by
    rw [ha3, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a35 : Array.index_usize a3 5#usize = .ok v5 :=
    (array_index_usize_ok_eq a3 5#usize (by rw [ha3_len]; decide)).trans (congrArg Result.ok ha3_5)
  have hi_a34 : Array.index_usize a3 4#usize = .ok v4 :=
    (array_index_usize_ok_eq a3 4#usize (by rw [ha3_len]; decide)).trans (congrArg Result.ok ha3_4)
  have hu_a4 : Array.update a3 4#usize s2 = .ok (a3.set 4#usize s2) :=
    array_update_ok_eq a3 4#usize s2 (by rw [ha3_len]; decide)
  set a4 : CoeffArray := a3.set 4#usize s2 with ha4
  have ha4_len : a4.length = 8 := by rw [ha4, Std.Array.set_length]; exact ha3_len
  have hu_a5 : Array.update a4 5#usize t2 = .ok (a4.set 5#usize t2) :=
    array_update_ok_eq a4 5#usize t2 (by rw [ha4_len]; decide)
  set a5 : CoeffArray := a4.set 5#usize t2 with ha5
  have ha5_len : a5.length = 8 := by rw [ha5, Std.Array.set_length]; exact ha4_len
  -- Pair 3: hi=7, lo=6.  a5[7] = v7, a5[6] = v6.
  have ha5_7 : a5.val[7]! = v7 := by
    rw [ha5, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha5_6 : a5.val[6]! = v6 := by
    rw [ha5, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a57 : Array.index_usize a5 7#usize = .ok v7 :=
    (array_index_usize_ok_eq a5 7#usize (by rw [ha5_len]; decide)).trans (congrArg Result.ok ha5_7)
  have hi_a56 : Array.index_usize a5 6#usize = .ok v6 :=
    (array_index_usize_ok_eq a5 6#usize (by rw [ha5_len]; decide)).trans (congrArg Result.ok ha5_6)
  have hu_a6 : Array.update a5 6#usize s3 = .ok (a5.set 6#usize s3) :=
    array_update_ok_eq a5 6#usize s3 (by rw [ha5_len]; decide)
  set a6 : CoeffArray := a5.set 6#usize s3 with ha6
  have ha6_len : a6.length = 8 := by rw [ha6, Std.Array.set_length]; exact ha5_len
  have hu_a7 : Array.update a6 7#usize t3 = .ok (a6.set 7#usize t3) :=
    array_update_ok_eq a6 7#usize t3 (by rw [ha6_len]; decide)
  set a7 : CoeffArray := a6.set 7#usize t3 with ha7
  have ha7_len : a7.length = 8 := by rw [ha7, Std.Array.set_length]; exact ha6_len
  -- ===== Compose the whole do-block into one `.ok { values := a7 }`. =====
  set final_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    { values := a7 } with hfu
  have h_body :
      libcrux_iot_ml_dsa.simd.portable.invntt.simd_unit_invert_ntt_at_layer_0
        simd_unit zeta0 zeta1 zeta2 zeta3 = .ok final_unit := by
    unfold libcrux_iot_ml_dsa.simd.portable.invntt.simd_unit_invert_ntt_at_layer_0
    rw [hi_v1]; simp only [bind_tc_ok]
    rw [hi_v0]; simp only [bind_tc_ok]
    rw [hamb0_eq]; simp only [bind_tc_ok]
    rw [hs0_eq]; simp only [bind_tc_ok]
    rw [hu_a]; simp only [bind_tc_ok]
    rw [classify_ok zeta0]; simp only [bind_tc_ok]
    rw [ht0_eq]; simp only [bind_tc_ok]
    rw [hu_a1]; simp only [bind_tc_ok]
    rw [hi_a13]; simp only [bind_tc_ok]
    rw [hi_a12]; simp only [bind_tc_ok]
    rw [hamb1_eq]; simp only [bind_tc_ok]
    rw [hs1_eq]; simp only [bind_tc_ok]
    rw [hu_a2]; simp only [bind_tc_ok]
    rw [classify_ok zeta1]; simp only [bind_tc_ok]
    rw [ht1_eq]; simp only [bind_tc_ok]
    rw [hu_a3]; simp only [bind_tc_ok]
    rw [hi_a35]; simp only [bind_tc_ok]
    rw [hi_a34]; simp only [bind_tc_ok]
    rw [hamb2_eq]; simp only [bind_tc_ok]
    rw [hs2_eq]; simp only [bind_tc_ok]
    rw [hu_a4]; simp only [bind_tc_ok]
    rw [classify_ok zeta2]; simp only [bind_tc_ok]
    rw [ht2_eq]; simp only [bind_tc_ok]
    rw [hu_a5]; simp only [bind_tc_ok]
    rw [hi_a57]; simp only [bind_tc_ok]
    rw [hi_a56]; simp only [bind_tc_ok]
    rw [hamb3_eq]; simp only [bind_tc_ok]
    rw [hs3_eq]; simp only [bind_tc_ok]
    rw [hu_a6]; simp only [bind_tc_ok]
    rw [classify_ok zeta3]; simp only [bind_tc_ok]
    rw [ht3_eq]; simp only [bind_tc_ok]
    rw [hu_a7]; simp only [bind_tc_ok]
    rfl
  -- ===== Final lane values of a7 (track through the set chain). =====
  -- a7 = a6.set 7 t3; reads: 0→s0, 1→t0, 2→s1, 3→t1, 4→s2, 5→t2, 6→s3, 7→t3.
  have hr0 : a7.val[0]! = s0 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_eq _ _ 0 _ ⟨rfl, by rw [h_len]; decide⟩]
  have hr1 : a7.val[1]! = t0 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_eq _ _ 1 _ ⟨rfl, by rw [ha_len]; decide⟩]
  have hr2 : a7.val[2]! = s1 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_eq _ _ 2 _ ⟨rfl, by rw [ha1_len]; decide⟩]
  have hr3 : a7.val[3]! = t1 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_eq _ _ 3 _ ⟨rfl, by rw [ha2_len]; decide⟩]
  have hr4 : a7.val[4]! = s2 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_eq _ _ 4 _ ⟨rfl, by rw [ha3_len]; decide⟩]
  have hr5 : a7.val[5]! = t2 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_eq _ _ 5 _ ⟨rfl, by rw [ha4_len]; decide⟩]
  have hr6 : a7.val[6]! = s3 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_eq _ _ 6 _ ⟨rfl, by rw [ha5_len]; decide⟩]
  have hr7 : a7.val[7]! = t3 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq,
        Std.Array.getElem!_Nat_set_eq _ _ 7 _ ⟨rfl, by rw [ha6_len]; decide⟩]
  -- ===== Lift seams: lift each t_p to clean (amb_p)·(z) = (v_hi - v_lo)·z. =====
  have hlift0 : liftZ t0.val = liftZ amb0.val * liftZ zeta0.val := liftZ_of_mont _ _ _ ht0_lift
  have hlift1 : liftZ t1.val = liftZ amb1.val * liftZ zeta1.val := liftZ_of_mont _ _ _ ht1_lift
  have hlift2 : liftZ t2.val = liftZ amb2.val * liftZ zeta2.val := liftZ_of_mont _ _ _ ht2_lift
  have hlift3 : liftZ t3.val = liftZ amb3.val * liftZ zeta3.val := liftZ_of_mont _ _ _ ht3_lift
  -- ===== Close the Triple. =====
  apply triple_of_ok h_body
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- r[0] = v0 + v1  (clean ADD)
    show liftZ (final_unit.values.val[0]!).val = _
    rw [show final_unit.values = a7 from rfl, hr0, hs0_val, liftZ_add]
  · -- r[1] = (v1 - v0)·z0
    show liftZ (final_unit.values.val[1]!).val = _
    rw [show final_unit.values = a7 from rfl, hr1, hlift0,
        show amb0.val = v1.val - v0.val from hamb0_val, liftZ_sub]
  · show liftZ (final_unit.values.val[2]!).val = _
    rw [show final_unit.values = a7 from rfl, hr2, hs1_val, liftZ_add]
  · show liftZ (final_unit.values.val[3]!).val = _
    rw [show final_unit.values = a7 from rfl, hr3, hlift1,
        show amb1.val = v3.val - v2.val from hamb1_val, liftZ_sub]
  · show liftZ (final_unit.values.val[4]!).val = _
    rw [show final_unit.values = a7 from rfl, hr4, hs2_val, liftZ_add]
  · show liftZ (final_unit.values.val[5]!).val = _
    rw [show final_unit.values = a7 from rfl, hr5, hlift2,
        show amb2.val = v5.val - v4.val from hamb2_val, liftZ_sub]
  · show liftZ (final_unit.values.val[6]!).val = _
    rw [show final_unit.values = a7 from rfl, hr6, hs3_val, liftZ_add]
  · show liftZ (final_unit.values.val[7]!).val = _
    rw [show final_unit.values = a7 from rfl, hr7, hlift3,
        show amb3.val = v7.val - v6.val from hamb3_val, liftZ_sub]
  · -- Output bounds on all 8 lanes (lo lanes ≤ 2B, hi lanes ≤ 2^24, both ≤ 2B+2^24).
    intro j hj
    show (final_unit.values.val[j]!).val.natAbs ≤ 2 * B + 2 ^ 24
    rw [show final_unit.values = a7 from rfl]
    match j, hj with
    | 0, _ => rw [hr0]; exact Nat.le_trans hs0_bd (by omega)
    | 1, _ => rw [hr1]; exact Nat.le_trans ht0_bd (by omega)
    | 2, _ => rw [hr2]; exact Nat.le_trans hs1_bd (by omega)
    | 3, _ => rw [hr3]; exact Nat.le_trans ht1_bd (by omega)
    | 4, _ => rw [hr4]; exact Nat.le_trans hs2_bd (by omega)
    | 5, _ => rw [hr5]; exact Nat.le_trans ht2_bd (by omega)
    | 6, _ => rw [hr6]; exact Nat.le_trans hs3_bd (by omega)
    | 7, _ => rw [hr7]; exact Nat.le_trans ht3_bd (by omega)
    | (n + 8), h => exact absurd h (by omega)


end libcrux_iot_ml_dsa.Vector.Portable.InvNtt
