/-
  # `Vector/Portable/NttDriver.lean` — L3 forward NTT layer drivers (ML-DSA)

  The layer drivers (`ntt_at_layer_7 … ntt_at_layer_0`) tie one or more proven
  `outer_3_plus` cross-unit butterflies (Phase-4 keystone `outer_3_plus_fc`) into
  one `Pure.ntt_layer` step on the lifted flat 256-array. They operate on the raw
  `Array Coefficients 32#usize` (the `.simd_units` field), so they speak
  `Lift.lift_units` (the `Array`-level analogue of `lift_poly`).

  **`ntt_at_layer_7_fc`** is the keystone of this family: `ntt_at_layer_7` is
  exactly one `outer_3_plus 0 16 25847` call (`OFFSET=0, STEP_BY=16, ZETA=25847`).
  Since `0 + 2·16 = 32`, the "unchanged" clause is vacuous — every unit is
  butterflied — and the lifted result equals `ntt_layer (lift_units re) 7`
  (`len = 128`, base zeta index `k = 1`, so each lane uses `zeta 1`).

  The bridge `liftZ 25847 = zeta 1` is proven `decide` (KERNEL, axiom-clean;
  spot-checked by the existing `Spec/Lift.lean` `#guard`s) — NOT `native_decide`.
-/
import LibcruxIotMlDsa.Vector.Portable.Ntt
import LibcruxIotMlDsa.Spec.Lift

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.NttDriver
open Aeneas Aeneas.Std Std.Do Result
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Vector.Portable.Ntt

/-- Reflect a `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` Triple into an `.ok` witness plus the post
    (file-scoped copy of the §13.5 helper; the original is `private` in `Ntt`). -/
private theorem triple_exists_ok
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v` (file-scoped §13.5 copy). -/
private theorem triple_of_ok
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

set_option maxRecDepth 4000 in
/-- The layer-7 inline zeta `25847` (Montgomery domain) strips to the clean
    `zeta 1`. KERNEL-checked by `decide` (NOT `native_decide`); the `Spec/Lift`
    `#guard`s validate this exact `liftZ <mont literal> = zeta <idx>` class. -/
private theorem zeta7_bridge : liftZ (25847 : Int) = zeta 1 := by decide

@[spec]
theorem ntt_at_layer_7_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_7 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 7
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_7
  -- Pull the Phase-4 cross-unit keystone at OFFSET=0, STEP_BY=16, ZETA=25847.
  have hzeta : (25847#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
  have hstep : 1 ≤ (16#usize : Std.Usize).val := by decide
  have hbound : (0#usize : Std.Usize).val + 2 * (16#usize : Std.Usize).val ≤ 32 := by decide
  obtain ⟨r, hr_eq, hbutter, hunch, hbd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 16#usize 25847#i32 re B hzeta hB hstep hbound hin)
  apply triple_of_ok hr_eq
  -- Normalize the usize literal coercions in the butterfly post to plain numerals.
  have h0 : (0#usize : Std.Usize).val = 0 := by decide
  have h16 : (16#usize : Std.Usize).val = 16 := by decide
  simp only [h0, h16, Nat.zero_add] at hbutter hunch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct: `lift_units r = ntt_layer (lift_units re) 7`.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    -- Normalize the spec at layer 7: `len = 1<<<7 = 128`, `2*len = 256`,
    -- `k = 128/128 = 1`. For `i < 256`: `round = i/256 = 0`, `idx = i%256 = i`.
    have hround : i / 256 = 0 := by omega
    have hidx : i % 256 = i := by omega
    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
    -- `liftZ ↑25847#i32 = zeta 1` (cast the i32 literal, then the kernel bridge).
    have hzeta_cast : ((25847#i32 : Std.I32).val : Int) = (25847 : Int) := by decide
    have hz : liftZ ((25847#i32 : Std.I32).val : Int) = zeta 1 := by
      rw [hzeta_cast]; exact zeta7_bridge
    by_cases hlt : i < 128
    · -- Low half: butterfly at unit `u = i/8 < 16`, lane `l = i%8`.
      rw [if_pos hlt]
      have hl : i % 8 < 8 := by omega
      have hdiv : (i + 128) / 8 = i / 8 + 16 := by omega
      have hmod : (i + 128) % 8 = i % 8 := by omega
      have hidx2_lt : i + 128 < 256 := by omega
      -- `build_getElem` on both spec lookups (indices `i` and `i+128`).
      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 128) hidx2_lt, hdiv, hmod]
      -- The butterfly low-eq at `j = i/8` (needs `0 ≤ i/8` and `i/8 < 16`).
      obtain ⟨hlow, _hhigh⟩ := hbutter (i / 8) (by omega) (by omega)
      rw [hlow (i % 8) hl, hz, mul_comm]
    · -- High half: butterfly at unit `j = (i-128)/8 < 16`, with `u = i/8 = j+16`.
      rw [if_neg hlt]
      have hl : i % 8 < 8 := by omega
      have hdiv : i / 8 = (i - 128) / 8 + 16 := by omega
      have hmod_lo : (i - 128) % 8 = i % 8 := by omega
      have hidx2_lt : i - 128 < 256 := by omega
      rw [Pure.build_getElem _ (i - 128) hidx2_lt, Pure.build_getElem _ i hi, hmod_lo]
      -- The butterfly high-eq at `j = (i-128)/8` (`j + 16 = i/8`).
      obtain ⟨_hlow, hhigh⟩ := hbutter ((i - 128) / 8) (by omega) (by omega)
      have hhigh' := hhigh (i % 8) hl
      rw [hdiv]  -- goal LHS `r[i/8]` → `r[(i-128)/8 + 16]` to match `hhigh'`
      rw [hhigh', hz, mul_comm]
  · -- Bound conjunct = `hbd` directly.
    exact hbd

/-! ## Layer 6 (`len = 64`, `k = 2`, `STEP_BY = 8`, 2 cross-unit calls)

`ntt_at_layer_6` chains two `outer_3_plus` calls on the disjoint unit blocks
`[0,16)` (call 0, `ZETA = -2608894 → zeta 2`) and `[16,32)` (call 1,
`ZETA = -518909 → zeta 3`). The frame is one step: block-0 units are left
unchanged by call 1 (`OFFSET₁ = 16`), block-1 units are left unchanged by call 0
(`OFFSET₀ + 2·8 = 16`), so each block's butterfly is in terms of `re`. -/

set_option maxRecDepth 4000 in
private theorem zeta6_bridge0 :
    liftZ (((-2608894)#i32 : Std.I32).val : Int) = zeta 2 := by decide
set_option maxRecDepth 4000 in
private theorem zeta6_bridge1 :
    liftZ (((-518909)#i32 : Std.I32).val : Int) = zeta 3 := by decide

/-- i32 zeta-magnitude facts hoisted out of the Triple so the kernel does not
    recheck the (heavy, two's-complement) `decide` terms inside the big proof. -/
private theorem zeta6_mag0 : ((-2608894)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta6_mag1 : ((-518909)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_6_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 2 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_6 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 6
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_6
  -- Shared bound arguments for `outer_3_plus_fc`.
  have hstep : 1 ≤ (8#usize : Std.Usize).val := by scalar_tac
  have hz0 := zeta6_mag0
  have hz1 := zeta6_mag1
  have hbnd0 : (0#usize : Std.Usize).val + 2 * (8#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd1 : (16#usize : Std.Usize).val + 2 * (8#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  have hB0 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  have hB1 : ((B + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  -- Call 0 on block [0,16).
  obtain ⟨r1, hr1_eq, h0butter, h0unch, h0bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 8#usize (-2608894)#i32 re B hz0 hB0 hstep hbnd0 hin)
  -- Call 1 on block [16,32); input bound is `B + 2^24` (from `h0bd`).
  obtain ⟨r2, hr2_eq, h1butter, h1unch, h1bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 16#usize 8#usize (-518909)#i32 r1 (B + 2 ^ 24) hz1 hB1 hstep hbnd1 h0bd)
  simp only [hr1_eq, Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr2_eq
  -- Normalize usize literal coercions in the butterfly/unchanged posts.
  have e0 : (0#usize : Std.Usize).val = 0 := by simp
  have e8 : (8#usize : Std.Usize).val = 8 := by simp
  have e16 : (16#usize : Std.Usize).val = 16 := by simp
  simp only [e0, e8, e16, Nat.zero_add] at h0butter h0unch h1butter h1unch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    -- Spec at layer 6: `len = 64`, `2*len = 128`, `k = 2`.
    have hzv0 : liftZ ((((-2608894)#i32 : Std.I32).val : Int)) = zeta 2 := zeta6_bridge0
    have hzv1 : liftZ ((((-518909)#i32 : Std.I32).val : Int)) = zeta 3 := zeta6_bridge1
    by_cases hround0 : i < 128
    · -- Round 0 (call 0), spec `round = 0`, `idx = i`, `z = zeta 2`.
      have hround : i / 128 = 0 := by omega
      have hidx : i % 128 = i := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
      by_cases hlt : i < 64
      · -- Low half: unit `u = i/8 ∈ [0,8)`, paired `u+8`, coeff `i+64`.
        rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 64) / 8 = i / 8 + 8 := by omega
        have hmod : (i + 64) % 8 = i % 8 := by omega
        have hidx2 : i + 64 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 64) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h0butter (i / 8) (by omega) (by omega)
        -- LHS unit `i/8` is in block 0: call 1 leaves it unchanged (`r2[i/8] = r1[i/8]`).
        rw [h1unch (i / 8) (by omega) (by omega)]
        rw [hlow (i % 8) hl, hzv0, mul_comm]
      · -- High half: paired unit `u-8 = (i-64)/8 ∈ [0,8)`, coeff `i-64`.
        rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 64) / 8 + 8 := by omega
        have hmod : (i - 64) % 8 = i % 8 := by omega
        have hidx2 : i - 64 < 256 := by omega
        rw [Pure.build_getElem _ (i - 64) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h0butter ((i - 64) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [h1unch (i / 8) (by omega) (by omega)]
        rw [hdiv, hhigh', hzv0, mul_comm]
    · -- Round 1 (call 1), spec `round = 1`, `idx = i - 128`, `z = zeta (1+2) = zeta 3`.
      have hround : i / 128 = 1 := by omega
      have hidx : i % 128 = i - 128 := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
      by_cases hlt : i - 128 < 64
      · -- Low half: unit `u = i/8 ∈ [16,24)`, paired `u+8`, coeff `i+64`.
        rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 64) / 8 = i / 8 + 8 := by omega
        have hmod : (i + 64) % 8 = i % 8 := by omega
        have hidx2 : i + 64 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 64) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h1butter (i / 8) (by omega) (by omega)
        -- LHS `r2[i/8]` → butterfly in terms of `r1`; call 0 left block 1 = `re`.
        rw [hlow (i % 8) hl]
        rw [h0unch (i / 8) (by omega) (by omega), h0unch (i / 8 + 8) (by omega) (by omega)]
        rw [hzv1, mul_comm]
      · -- High half: paired unit `u-8 = (i-64)/8 ∈ [16,24)`, coeff `i-64`.
        rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 64) / 8 + 8 := by omega
        have hmod : (i - 64) % 8 = i % 8 := by omega
        have hidx2 : i - 64 < 256 := by omega
        rw [Pure.build_getElem _ (i - 64) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h1butter ((i - 64) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [hdiv, hhigh']
        rw [h0unch ((i - 64) / 8 + 8) (by omega) (by omega),
            h0unch ((i - 64) / 8) (by omega) (by omega)]
        rw [hzv1, mul_comm]
  · -- Bound conjunct: block 1 (units [16,32)) ≤ B+2·2^24 from `h1bd`; block 0 ≤
    -- B+2^24 from `h0bd`, carried through call 1 (`h1unch`), then `≤ B+2·2^24`.
    intro u hu l hl
    by_cases hb : u < 16
    · -- Block 0: unchanged by call 1.
      rw [h1unch u hu (by omega)]
      have h := h0bd u hu l hl
      have hmono : B + 2 ^ 24 ≤ B + 2 * 2 ^ 24 := by omega
      exact Nat.le_trans h hmono
    · -- Block 1: `h1bd` gives ≤ (B+2^24)+2^24; rewrite the target to that shape.
      rw [show B + 2 * 2 ^ 24 = B + 2 ^ 24 + 2 ^ 24 from by ring]
      exact h1bd u hu l hl

end libcrux_iot_ml_dsa.Vector.Portable.NttDriver
