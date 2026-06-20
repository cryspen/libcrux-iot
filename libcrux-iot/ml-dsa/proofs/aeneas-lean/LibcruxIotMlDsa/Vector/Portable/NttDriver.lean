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

end libcrux_iot_ml_dsa.Vector.Portable.NttDriver
