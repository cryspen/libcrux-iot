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

/-! ## Layer 5 (`len = 32`, `k = 4`, `STEP_BY = 4`, 4 cross-unit calls)

`ntt_at_layer_5` chains four `outer_3_plus` calls on disjoint unit blocks
`[0,8)`, `[8,16)`, `[16,24)`, `[24,32)` (`OFFSET = round·8`, `STEP_BY = 4`),
with `ZETA` values `237124→z4`, `-777960→z5`, `-876248→z6`, `466468→z7`. The
locked bound after 4 calls is `B + 4·2^24`. -/

set_option maxRecDepth 4000 in
private theorem zeta5_bridge0 :
    liftZ ((237124#i32 : Std.I32).val : Int) = zeta 4 := by decide
set_option maxRecDepth 4000 in
private theorem zeta5_bridge1 :
    liftZ (((-777960)#i32 : Std.I32).val : Int) = zeta 5 := by decide
set_option maxRecDepth 4000 in
private theorem zeta5_bridge2 :
    liftZ (((-876248)#i32 : Std.I32).val : Int) = zeta 6 := by decide
set_option maxRecDepth 4000 in
private theorem zeta5_bridge3 :
    liftZ ((466468#i32 : Std.I32).val : Int) = zeta 7 := by decide

private theorem zeta5_mag0 : (237124#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta5_mag1 : ((-777960)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta5_mag2 : ((-876248)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta5_mag3 : (466468#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_5_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 4 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_5 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 5
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 4 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_5
  -- Shared bound arguments for `outer_3_plus_fc`.
  have hstep : 1 ≤ (4#usize : Std.Usize).val := by scalar_tac
  have hbnd0 : (0#usize : Std.Usize).val + 2 * (4#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd1 : (8#usize : Std.Usize).val + 2 * (4#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd2 : (16#usize : Std.Usize).val + 2 * (4#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd3 : (24#usize : Std.Usize).val + 2 * (4#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  have hB0 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  -- Call 0 on block [0,8); input bound `B`.
  obtain ⟨r1, hr1_eq, h0butter, h0unch, h0bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 4#usize 237124#i32 re B zeta5_mag0 hB0 hstep hbnd0 hin)
  -- Generalise the running bound `B + 2^24` to a FRESH opaque Nat `B1` before the
  -- next call: a `set`/literal `B + k·2^24` keeps the `2^24` numerals, which the
  -- kernel re-expands and NESTS across calls → "(kernel) deep recursion". A true
  -- `generalize` fvar blocks that. (Same trick at each subsequent call.)
  have hB1raw : ((B + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  generalize hB1def : B + 2 ^ 24 = B1 at h0bd hB1raw
  -- Call 1 on block [8,16); input bound `B1 = B + 2^24`.
  obtain ⟨r2, hr2_eq, h1butter, h1unch, h1bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 8#usize 4#usize (-777960)#i32 r1 B1 zeta5_mag1 hB1raw hstep hbnd1 h0bd)
  have hB2raw : ((B1 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm; push_cast; omega
  generalize hB2def : B1 + 2 ^ 24 = B2 at h1bd hB2raw
  -- Call 2 on block [16,24); input bound `B2 = B + 2·2^24`.
  obtain ⟨r3, hr3_eq, h2butter, h2unch, h2bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 16#usize 4#usize (-876248)#i32 r2 B2 zeta5_mag2 hB2raw hstep hbnd2 h1bd)
  have hB3raw : ((B2 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    push_cast; omega
  generalize hB3def : B2 + 2 ^ 24 = B3 at h2bd hB3raw
  -- Call 3 on block [24,32); input bound `B3 = B + 3·2^24`.
  obtain ⟨r4, hr4_eq, h3butter, h3unch, h3bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 24#usize 4#usize 466468#i32 r3 B3 zeta5_mag3 hB3raw hstep hbnd3 h2bd)
  -- Collapse the bind chain ONE call at a time (keeps each kernel-checked term
  -- shallow; a single `simp only [hr1_eq, hr2_eq, hr3_eq, ...]` builds a deeply
  -- nested `Result` bind that triggers kernel deep recursion).
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr4_eq
  -- Normalize usize literal coercions in the butterfly/unchanged posts.
  have e0 : (0#usize : Std.Usize).val = 0 := by simp
  have e4 : (4#usize : Std.Usize).val = 4 := by simp
  have e8 : (8#usize : Std.Usize).val = 8 := by simp
  have e16 : (16#usize : Std.Usize).val = 16 := by simp
  have e24v : (24#usize : Std.Usize).val = 24 := by simp
  simp only [e0, e4, e8, e16, e24v, Nat.zero_add]
    at h0butter h0unch h1butter h1unch h2butter h2unch h3butter h3unch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    -- Spec at layer 5: `len = 32`, `2*len = 64`, `k = 4`.
    have hzv0 : liftZ (((237124#i32 : Std.I32).val : Int)) = zeta 4 := zeta5_bridge0
    have hzv1 : liftZ ((((-777960)#i32 : Std.I32).val : Int)) = zeta 5 := zeta5_bridge1
    have hzv2 : liftZ ((((-876248)#i32 : Std.I32).val : Int)) = zeta 6 := zeta5_bridge2
    have hzv3 : liftZ (((466468#i32 : Std.I32).val : Int)) = zeta 7 := zeta5_bridge3
    by_cases hr0 : i < 64
    · -- Round 0 (call 0), spec `round = 0`, `idx = i`, `z = zeta 4`.
      have hround : i / 64 = 0 := by omega
      have hidx : i % 64 = i := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
      by_cases hlt : i < 32
      · rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 32) / 8 = i / 8 + 4 := by omega
        have hmod : (i + 32) % 8 = i % 8 := by omega
        have hidx2 : i + 32 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 32) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h0butter (i / 8) (by omega) (by omega)
        -- LHS unit `i/8 ∈ [0,4)` in block 0: calls 1,2,3 leave it unchanged.
        rw [h3unch (i / 8) (by omega) (by omega), h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hlow (i % 8) hl, hzv0, mul_comm]
      · rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 32) / 8 + 4 := by omega
        have hmod : (i - 32) % 8 = i % 8 := by omega
        have hidx2 : i - 32 < 256 := by omega
        rw [Pure.build_getElem _ (i - 32) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h0butter ((i - 32) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [h3unch (i / 8) (by omega) (by omega), h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hdiv, hhigh', hzv0, mul_comm]
    · by_cases hr1 : i < 128
      · -- Round 1 (call 1), spec `round = 1`, `idx = i - 64`, `z = zeta 5`.
        have hround : i / 64 = 1 := by omega
        have hidx : i % 64 = i - 64 := by omega
        simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
        by_cases hlt : i - 64 < 32
        · rw [if_pos hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : (i + 32) / 8 = i / 8 + 4 := by omega
          have hmod : (i + 32) % 8 = i % 8 := by omega
          have hidx2 : i + 32 < 256 := by omega
          rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 32) hidx2, hdiv, hmod]
          obtain ⟨hlow, _⟩ := h1butter (i / 8) (by omega) (by omega)
          -- LHS unit `i/8 ∈ [8,12)` in block 1: calls 2,3 leave it unchanged.
          rw [h3unch (i / 8) (by omega) (by omega), h2unch (i / 8) (by omega) (by omega)]
          rw [hlow (i % 8) hl]
          -- Butterfly in terms of `r1`; call 0 left block 1 = `re`.
          rw [h0unch (i / 8) (by omega) (by omega), h0unch (i / 8 + 4) (by omega) (by omega)]
          rw [hzv1, mul_comm]
        · rw [if_neg hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : i / 8 = (i - 32) / 8 + 4 := by omega
          have hmod : (i - 32) % 8 = i % 8 := by omega
          have hidx2 : i - 32 < 256 := by omega
          rw [Pure.build_getElem _ (i - 32) hidx2, Pure.build_getElem _ i hi, hmod]
          obtain ⟨_, hhigh⟩ := h1butter ((i - 32) / 8) (by omega) (by omega)
          have hhigh' := hhigh (i % 8) hl
          rw [h3unch (i / 8) (by omega) (by omega), h2unch (i / 8) (by omega) (by omega)]
          rw [hdiv, hhigh']
          rw [h0unch ((i - 32) / 8 + 4) (by omega) (by omega),
              h0unch ((i - 32) / 8) (by omega) (by omega)]
          rw [hzv1, mul_comm]
      · by_cases hr2 : i < 192
        · -- Round 2 (call 2), spec `round = 2`, `idx = i - 128`, `z = zeta 6`.
          have hround : i / 64 = 2 := by omega
          have hidx : i % 64 = i - 128 := by omega
          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
          by_cases hlt : i - 128 < 32
          · rw [if_pos hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : (i + 32) / 8 = i / 8 + 4 := by omega
            have hmod : (i + 32) % 8 = i % 8 := by omega
            have hidx2 : i + 32 < 256 := by omega
            rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 32) hidx2, hdiv, hmod]
            obtain ⟨hlow, _⟩ := h2butter (i / 8) (by omega) (by omega)
            rw [h3unch (i / 8) (by omega) (by omega)]
            rw [hlow (i % 8) hl]
            -- Butterfly in terms of `r2`; calls 0,1 left block 2 = `re`.
            rw [h1unch (i / 8) (by omega) (by omega), h0unch (i / 8) (by omega) (by omega),
                h1unch (i / 8 + 4) (by omega) (by omega),
                h0unch (i / 8 + 4) (by omega) (by omega)]
            rw [hzv2, mul_comm]
          · rw [if_neg hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : i / 8 = (i - 32) / 8 + 4 := by omega
            have hmod : (i - 32) % 8 = i % 8 := by omega
            have hidx2 : i - 32 < 256 := by omega
            rw [Pure.build_getElem _ (i - 32) hidx2, Pure.build_getElem _ i hi, hmod]
            obtain ⟨_, hhigh⟩ := h2butter ((i - 32) / 8) (by omega) (by omega)
            have hhigh' := hhigh (i % 8) hl
            rw [h3unch (i / 8) (by omega) (by omega)]
            rw [hdiv, hhigh']
            rw [h1unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h0unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h1unch ((i - 32) / 8) (by omega) (by omega),
                h0unch ((i - 32) / 8) (by omega) (by omega)]
            rw [hzv2, mul_comm]
        · -- Round 3 (call 3), spec `round = 3`, `idx = i - 192`, `z = zeta 7`.
          have hround : i / 64 = 3 := by omega
          have hidx : i % 64 = i - 192 := by omega
          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
          by_cases hlt : i - 192 < 32
          · rw [if_pos hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : (i + 32) / 8 = i / 8 + 4 := by omega
            have hmod : (i + 32) % 8 = i % 8 := by omega
            have hidx2 : i + 32 < 256 := by omega
            rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 32) hidx2, hdiv, hmod]
            obtain ⟨hlow, _⟩ := h3butter (i / 8) (by omega) (by omega)
            rw [hlow (i % 8) hl]
            -- Butterfly in terms of `r3`; calls 0,1,2 left block 3 = `re`.
            rw [h2unch (i / 8) (by omega) (by omega), h1unch (i / 8) (by omega) (by omega),
                h0unch (i / 8) (by omega) (by omega),
                h2unch (i / 8 + 4) (by omega) (by omega),
                h1unch (i / 8 + 4) (by omega) (by omega),
                h0unch (i / 8 + 4) (by omega) (by omega)]
            rw [hzv3, mul_comm]
          · rw [if_neg hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : i / 8 = (i - 32) / 8 + 4 := by omega
            have hmod : (i - 32) % 8 = i % 8 := by omega
            have hidx2 : i - 32 < 256 := by omega
            rw [Pure.build_getElem _ (i - 32) hidx2, Pure.build_getElem _ i hi, hmod]
            obtain ⟨_, hhigh⟩ := h3butter ((i - 32) / 8) (by omega) (by omega)
            have hhigh' := hhigh (i % 8) hl
            rw [hdiv, hhigh']
            rw [h2unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h1unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h0unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h2unch ((i - 32) / 8) (by omega) (by omega),
                h1unch ((i - 32) / 8) (by omega) (by omega),
                h0unch ((i - 32) / 8) (by omega) (by omega)]
            rw [hzv3, mul_comm]
  · -- Bound conjunct: last call's bound `h3bd : |r4| ≤ B3 + 2^24` is already
    -- uniform; recover `B3 + 2^24 = B + 4·2^24` from the generalise equations.
    have heq : B3 + 2 ^ 24 = B + 4 * 2 ^ 24 := by
      rw [← hB3def, ← hB2def, ← hB1def]; ring
    intro u hu l hl
    have := h3bd u hu l hl
    rw [heq] at this
    exact this

/-! ## Layer 4 (`len = 16`, `k = 8`, `STEP_BY = 2`, 8 cross-unit calls)

`ntt_at_layer_4` chains eight `outer_3_plus` calls on disjoint unit blocks
`[4·round, 4·round+2)` (`OFFSET = 4·round`, `STEP_BY = 2`), `ZETA` values
`1826347→z8 … 2680103→z15`. The locked bound after 8 calls is `B + 8·2^24`. -/

set_option maxRecDepth 4000 in
private theorem zeta4_bridge0 :
    liftZ ((1826347#i32 : Std.I32).val : Int) = zeta 8 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge1 :
    liftZ ((2353451#i32 : Std.I32).val : Int) = zeta 9 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge2 :
    liftZ (((-359251)#i32 : Std.I32).val : Int) = zeta 10 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge3 :
    liftZ (((-2091905)#i32 : Std.I32).val : Int) = zeta 11 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge4 :
    liftZ ((3119733#i32 : Std.I32).val : Int) = zeta 12 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge5 :
    liftZ (((-2884855)#i32 : Std.I32).val : Int) = zeta 13 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge6 :
    liftZ ((3111497#i32 : Std.I32).val : Int) = zeta 14 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge7 :
    liftZ ((2680103#i32 : Std.I32).val : Int) = zeta 15 := by decide

private theorem zeta4_mag0 : (1826347#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag1 : (2353451#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag2 : ((-359251)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag3 : ((-2091905)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag4 : (3119733#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag5 : ((-2884855)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag6 : (3111497#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag7 : (2680103#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_4_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 8 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_4 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 4
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 8 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_4
  have hstep : 1 ≤ (2#usize : Std.Usize).val := by scalar_tac
  have hbnd0 : (0#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd1 : (4#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd2 : (8#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd3 : (12#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd4 : (16#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd5 : (20#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd6 : (24#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd7 : (28#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  have hB0 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  obtain ⟨r1, hr1_eq, h0butter, h0unch, h0bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 2#usize 1826347#i32 re B zeta4_mag0 hB0 hstep hbnd0 hin)
  have hB1raw : ((B + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  generalize hB1def : B + 2 ^ 24 = B1 at h0bd hB1raw
  obtain ⟨r2, hr2_eq, h1butter, h1unch, h1bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 4#usize 2#usize 2353451#i32 r1 B1 zeta4_mag1 hB1raw hstep hbnd1 h0bd)
  have hB2raw : ((B1 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    push_cast; omega
  generalize hB2def : B1 + 2 ^ 24 = B2 at h1bd hB2raw
  obtain ⟨r3, hr3_eq, h2butter, h2unch, h2bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 8#usize 2#usize (-359251)#i32 r2 B2 zeta4_mag2 hB2raw hstep hbnd2 h1bd)
  have hB3raw : ((B2 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    push_cast; omega
  generalize hB3def : B2 + 2 ^ 24 = B3 at h2bd hB3raw
  obtain ⟨r4, hr4_eq, h3butter, h3unch, h3bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 12#usize 2#usize (-2091905)#i32 r3 B3 zeta4_mag3 hB3raw hstep hbnd3 h2bd)
  have hB4raw : ((B3 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    push_cast; omega
  generalize hB4def : B3 + 2 ^ 24 = B4 at h3bd hB4raw
  obtain ⟨r5, hr5_eq, h4butter, h4unch, h4bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 16#usize 2#usize 3119733#i32 r4 B4 zeta4_mag4 hB4raw hstep hbnd4 h3bd)
  have hB5raw : ((B4 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    push_cast; omega
  generalize hB5def : B4 + 2 ^ 24 = B5 at h4bd hB5raw
  obtain ⟨r6, hr6_eq, h5butter, h5unch, h5bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 20#usize 2#usize (-2884855)#i32 r5 B5 zeta4_mag5 hB5raw hstep hbnd5 h4bd)
  have hB6raw : ((B5 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    push_cast; omega
  generalize hB6def : B5 + 2 ^ 24 = B6 at h5bd hB6raw
  obtain ⟨r7, hr7_eq, h6butter, h6unch, h6bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 24#usize 2#usize 3111497#i32 r6 B6 zeta4_mag6 hB6raw hstep hbnd6 h5bd)
  have hB7raw : ((B6 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    push_cast; omega
  generalize hB7def : B6 + 2 ^ 24 = B7 at h6bd hB7raw
  obtain ⟨r8, hr8_eq, h7butter, h7unch, h7bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 28#usize 2#usize 2680103#i32 r7 B7 zeta4_mag7 hB7raw hstep hbnd7 h6bd)
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr8_eq
  have e0 : (0#usize : Std.Usize).val = 0 := by simp
  have e2 : (2#usize : Std.Usize).val = 2 := by simp
  have e4 : (4#usize : Std.Usize).val = 4 := by simp
  have e8 : (8#usize : Std.Usize).val = 8 := by simp
  have e12 : (12#usize : Std.Usize).val = 12 := by simp
  have e16 : (16#usize : Std.Usize).val = 16 := by simp
  have e20 : (20#usize : Std.Usize).val = 20 := by simp
  have e24 : (24#usize : Std.Usize).val = 24 := by simp
  have e28 : (28#usize : Std.Usize).val = 28 := by simp
  simp only [e0, e2, e4, e8, e12, e16, e20, e24, e28, Nat.zero_add]
    at h0butter h0unch h1butter h1unch h2butter h2unch h3butter h3unch
       h4butter h4unch h5butter h5unch h6butter h6unch h7butter h7unch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    have hzv0 : liftZ (((1826347#i32 : Std.I32).val : Int)) = zeta 8 := zeta4_bridge0
    have hzv1 : liftZ (((2353451#i32 : Std.I32).val : Int)) = zeta 9 := zeta4_bridge1
    have hzv2 : liftZ ((((-359251)#i32 : Std.I32).val : Int)) = zeta 10 := zeta4_bridge2
    have hzv3 : liftZ ((((-2091905)#i32 : Std.I32).val : Int)) = zeta 11 := zeta4_bridge3
    have hzv4 : liftZ (((3119733#i32 : Std.I32).val : Int)) = zeta 12 := zeta4_bridge4
    have hzv5 : liftZ ((((-2884855)#i32 : Std.I32).val : Int)) = zeta 13 := zeta4_bridge5
    have hzv6 : liftZ (((3111497#i32 : Std.I32).val : Int)) = zeta 14 := zeta4_bridge6
    have hzv7 : liftZ (((2680103#i32 : Std.I32).val : Int)) = zeta 15 := zeta4_bridge7
    by_cases hr0 : i < 32
    · -- Round 0.
      have hround : i / 32 = 0 := by omega
      have hidx : i % 32 = i := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
      by_cases hlt : i < 16
      · rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
        have hmod : (i + 16) % 8 = i % 8 := by omega
        have hidx2 : i + 16 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h0butter (i / 8) (by omega) (by omega)
        rw [h7unch (i / 8) (by omega) (by omega),
            h6unch (i / 8) (by omega) (by omega),
            h5unch (i / 8) (by omega) (by omega),
            h4unch (i / 8) (by omega) (by omega),
            h3unch (i / 8) (by omega) (by omega),
            h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hlow (i % 8) hl]
        rw [hzv0, mul_comm]
      · rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
        have hmod : (i - 16) % 8 = i % 8 := by omega
        have hidx2 : i - 16 < 256 := by omega
        rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h0butter ((i - 16) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [h7unch (i / 8) (by omega) (by omega),
            h6unch (i / 8) (by omega) (by omega),
            h5unch (i / 8) (by omega) (by omega),
            h4unch (i / 8) (by omega) (by omega),
            h3unch (i / 8) (by omega) (by omega),
            h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hdiv, hhigh']
        rw [hzv0, mul_comm]
    · -- Rounds 1+.
      by_cases hr1 : i < 64
      · -- Round 1.
        have hround : i / 32 = 1 := by omega
        have hidx : i % 32 = i - 32 := by omega
        simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
        by_cases hlt : i - 32 < 16
        · rw [if_pos hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
          have hmod : (i + 16) % 8 = i % 8 := by omega
          have hidx2 : i + 16 < 256 := by omega
          rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
          obtain ⟨hlow, _⟩ := h1butter (i / 8) (by omega) (by omega)
          rw [h7unch (i / 8) (by omega) (by omega),
              h6unch (i / 8) (by omega) (by omega),
              h5unch (i / 8) (by omega) (by omega),
              h4unch (i / 8) (by omega) (by omega),
              h3unch (i / 8) (by omega) (by omega),
              h2unch (i / 8) (by omega) (by omega)]
          rw [hlow (i % 8) hl]
          rw [h0unch (i / 8) (by omega) (by omega), h0unch (i / 8 + 2) (by omega) (by omega)]
          rw [hzv1, mul_comm]
        · rw [if_neg hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
          have hmod : (i - 16) % 8 = i % 8 := by omega
          have hidx2 : i - 16 < 256 := by omega
          rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
          obtain ⟨_, hhigh⟩ := h1butter ((i - 16) / 8) (by omega) (by omega)
          have hhigh' := hhigh (i % 8) hl
          rw [h7unch (i / 8) (by omega) (by omega),
              h6unch (i / 8) (by omega) (by omega),
              h5unch (i / 8) (by omega) (by omega),
              h4unch (i / 8) (by omega) (by omega),
              h3unch (i / 8) (by omega) (by omega),
              h2unch (i / 8) (by omega) (by omega)]
          rw [hdiv, hhigh']
          rw [h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
              h0unch ((i - 16) / 8) (by omega) (by omega)]
          rw [hzv1, mul_comm]
      · -- Rounds 2+.
        by_cases hr2 : i < 96
        · -- Round 2.
          have hround : i / 32 = 2 := by omega
          have hidx : i % 32 = i - 64 := by omega
          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
          by_cases hlt : i - 64 < 16
          · rw [if_pos hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
            have hmod : (i + 16) % 8 = i % 8 := by omega
            have hidx2 : i + 16 < 256 := by omega
            rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
            obtain ⟨hlow, _⟩ := h2butter (i / 8) (by omega) (by omega)
            rw [h7unch (i / 8) (by omega) (by omega),
                h6unch (i / 8) (by omega) (by omega),
                h5unch (i / 8) (by omega) (by omega),
                h4unch (i / 8) (by omega) (by omega),
                h3unch (i / 8) (by omega) (by omega)]
            rw [hlow (i % 8) hl]
            rw [h1unch (i / 8) (by omega) (by omega),
                h0unch (i / 8) (by omega) (by omega),
                h1unch (i / 8 + 2) (by omega) (by omega),
                h0unch (i / 8 + 2) (by omega) (by omega)]
            rw [hzv2, mul_comm]
          · rw [if_neg hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
            have hmod : (i - 16) % 8 = i % 8 := by omega
            have hidx2 : i - 16 < 256 := by omega
            rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
            obtain ⟨_, hhigh⟩ := h2butter ((i - 16) / 8) (by omega) (by omega)
            have hhigh' := hhigh (i % 8) hl
            rw [h7unch (i / 8) (by omega) (by omega),
                h6unch (i / 8) (by omega) (by omega),
                h5unch (i / 8) (by omega) (by omega),
                h4unch (i / 8) (by omega) (by omega),
                h3unch (i / 8) (by omega) (by omega)]
            rw [hdiv, hhigh']
            rw [h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                h1unch ((i - 16) / 8) (by omega) (by omega),
                h0unch ((i - 16) / 8) (by omega) (by omega)]
            rw [hzv2, mul_comm]
        · -- Rounds 3+.
          by_cases hr3 : i < 128
          · -- Round 3.
            have hround : i / 32 = 3 := by omega
            have hidx : i % 32 = i - 96 := by omega
            simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
              hround, hidx, Nat.reduceAdd]
            by_cases hlt : i - 96 < 16
            · rw [if_pos hlt]
              have hl : i % 8 < 8 := by omega
              have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
              have hmod : (i + 16) % 8 = i % 8 := by omega
              have hidx2 : i + 16 < 256 := by omega
              rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
              obtain ⟨hlow, _⟩ := h3butter (i / 8) (by omega) (by omega)
              rw [h7unch (i / 8) (by omega) (by omega),
                  h6unch (i / 8) (by omega) (by omega),
                  h5unch (i / 8) (by omega) (by omega),
                  h4unch (i / 8) (by omega) (by omega)]
              rw [hlow (i % 8) hl]
              rw [h2unch (i / 8) (by omega) (by omega),
                  h1unch (i / 8) (by omega) (by omega),
                  h0unch (i / 8) (by omega) (by omega),
                  h2unch (i / 8 + 2) (by omega) (by omega),
                  h1unch (i / 8 + 2) (by omega) (by omega),
                  h0unch (i / 8 + 2) (by omega) (by omega)]
              rw [hzv3, mul_comm]
            · rw [if_neg hlt]
              have hl : i % 8 < 8 := by omega
              have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
              have hmod : (i - 16) % 8 = i % 8 := by omega
              have hidx2 : i - 16 < 256 := by omega
              rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
              obtain ⟨_, hhigh⟩ := h3butter ((i - 16) / 8) (by omega) (by omega)
              have hhigh' := hhigh (i % 8) hl
              rw [h7unch (i / 8) (by omega) (by omega),
                  h6unch (i / 8) (by omega) (by omega),
                  h5unch (i / 8) (by omega) (by omega),
                  h4unch (i / 8) (by omega) (by omega)]
              rw [hdiv, hhigh']
              rw [h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                  h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                  h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                  h2unch ((i - 16) / 8) (by omega) (by omega),
                  h1unch ((i - 16) / 8) (by omega) (by omega),
                  h0unch ((i - 16) / 8) (by omega) (by omega)]
              rw [hzv3, mul_comm]
          · -- Rounds 4+.
            by_cases hr4 : i < 160
            · -- Round 4.
              have hround : i / 32 = 4 := by omega
              have hidx : i % 32 = i - 128 := by omega
              simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                hround, hidx, Nat.reduceAdd]
              by_cases hlt : i - 128 < 16
              · rw [if_pos hlt]
                have hl : i % 8 < 8 := by omega
                have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
                have hmod : (i + 16) % 8 = i % 8 := by omega
                have hidx2 : i + 16 < 256 := by omega
                rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
                obtain ⟨hlow, _⟩ := h4butter (i / 8) (by omega) (by omega)
                rw [h7unch (i / 8) (by omega) (by omega),
                    h6unch (i / 8) (by omega) (by omega),
                    h5unch (i / 8) (by omega) (by omega)]
                rw [hlow (i % 8) hl]
                rw [h3unch (i / 8) (by omega) (by omega),
                    h2unch (i / 8) (by omega) (by omega),
                    h1unch (i / 8) (by omega) (by omega),
                    h0unch (i / 8) (by omega) (by omega),
                    h3unch (i / 8 + 2) (by omega) (by omega),
                    h2unch (i / 8 + 2) (by omega) (by omega),
                    h1unch (i / 8 + 2) (by omega) (by omega),
                    h0unch (i / 8 + 2) (by omega) (by omega)]
                rw [hzv4, mul_comm]
              · rw [if_neg hlt]
                have hl : i % 8 < 8 := by omega
                have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
                have hmod : (i - 16) % 8 = i % 8 := by omega
                have hidx2 : i - 16 < 256 := by omega
                rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
                obtain ⟨_, hhigh⟩ := h4butter ((i - 16) / 8) (by omega) (by omega)
                have hhigh' := hhigh (i % 8) hl
                rw [h7unch (i / 8) (by omega) (by omega),
                    h6unch (i / 8) (by omega) (by omega),
                    h5unch (i / 8) (by omega) (by omega)]
                rw [hdiv, hhigh']
                rw [h3unch ((i - 16) / 8 + 2) (by omega) (by omega),
                    h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                    h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                    h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                    h3unch ((i - 16) / 8) (by omega) (by omega),
                    h2unch ((i - 16) / 8) (by omega) (by omega),
                    h1unch ((i - 16) / 8) (by omega) (by omega),
                    h0unch ((i - 16) / 8) (by omega) (by omega)]
                rw [hzv4, mul_comm]
            · -- Rounds 5+.
              by_cases hr5 : i < 192
              · -- Round 5.
                have hround : i / 32 = 5 := by omega
                have hidx : i % 32 = i - 160 := by omega
                simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                  hround, hidx, Nat.reduceAdd]
                by_cases hlt : i - 160 < 16
                · rw [if_pos hlt]
                  have hl : i % 8 < 8 := by omega
                  have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
                  have hmod : (i + 16) % 8 = i % 8 := by omega
                  have hidx2 : i + 16 < 256 := by omega
                  rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
                  obtain ⟨hlow, _⟩ := h5butter (i / 8) (by omega) (by omega)
                  rw [h7unch (i / 8) (by omega) (by omega), h6unch (i / 8) (by omega) (by omega)]
                  rw [hlow (i % 8) hl]
                  rw [h4unch (i / 8) (by omega) (by omega),
                      h3unch (i / 8) (by omega) (by omega),
                      h2unch (i / 8) (by omega) (by omega),
                      h1unch (i / 8) (by omega) (by omega),
                      h0unch (i / 8) (by omega) (by omega),
                      h4unch (i / 8 + 2) (by omega) (by omega),
                      h3unch (i / 8 + 2) (by omega) (by omega),
                      h2unch (i / 8 + 2) (by omega) (by omega),
                      h1unch (i / 8 + 2) (by omega) (by omega),
                      h0unch (i / 8 + 2) (by omega) (by omega)]
                  rw [hzv5, mul_comm]
                · rw [if_neg hlt]
                  have hl : i % 8 < 8 := by omega
                  have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
                  have hmod : (i - 16) % 8 = i % 8 := by omega
                  have hidx2 : i - 16 < 256 := by omega
                  rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
                  obtain ⟨_, hhigh⟩ := h5butter ((i - 16) / 8) (by omega) (by omega)
                  have hhigh' := hhigh (i % 8) hl
                  rw [h7unch (i / 8) (by omega) (by omega), h6unch (i / 8) (by omega) (by omega)]
                  rw [hdiv, hhigh']
                  rw [h4unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h3unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h4unch ((i - 16) / 8) (by omega) (by omega),
                      h3unch ((i - 16) / 8) (by omega) (by omega),
                      h2unch ((i - 16) / 8) (by omega) (by omega),
                      h1unch ((i - 16) / 8) (by omega) (by omega),
                      h0unch ((i - 16) / 8) (by omega) (by omega)]
                  rw [hzv5, mul_comm]
              · -- Rounds 6+.
                by_cases hr6 : i < 224
                · -- Round 6.
                  have hround : i / 32 = 6 := by omega
                  have hidx : i % 32 = i - 192 := by omega
                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                    hround, hidx, Nat.reduceAdd]
                  by_cases hlt : i - 192 < 16
                  · rw [if_pos hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
                    have hmod : (i + 16) % 8 = i % 8 := by omega
                    have hidx2 : i + 16 < 256 := by omega
                    rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
                    obtain ⟨hlow, _⟩ := h6butter (i / 8) (by omega) (by omega)
                    rw [h7unch (i / 8) (by omega) (by omega)]
                    rw [hlow (i % 8) hl]
                    rw [h5unch (i / 8) (by omega) (by omega),
                        h4unch (i / 8) (by omega) (by omega),
                        h3unch (i / 8) (by omega) (by omega),
                        h2unch (i / 8) (by omega) (by omega),
                        h1unch (i / 8) (by omega) (by omega),
                        h0unch (i / 8) (by omega) (by omega),
                        h5unch (i / 8 + 2) (by omega) (by omega),
                        h4unch (i / 8 + 2) (by omega) (by omega),
                        h3unch (i / 8 + 2) (by omega) (by omega),
                        h2unch (i / 8 + 2) (by omega) (by omega),
                        h1unch (i / 8 + 2) (by omega) (by omega),
                        h0unch (i / 8 + 2) (by omega) (by omega)]
                    rw [hzv6, mul_comm]
                  · rw [if_neg hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
                    have hmod : (i - 16) % 8 = i % 8 := by omega
                    have hidx2 : i - 16 < 256 := by omega
                    rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
                    obtain ⟨_, hhigh⟩ := h6butter ((i - 16) / 8) (by omega) (by omega)
                    have hhigh' := hhigh (i % 8) hl
                    rw [h7unch (i / 8) (by omega) (by omega)]
                    rw [hdiv, hhigh']
                    rw [h5unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h4unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h3unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h5unch ((i - 16) / 8) (by omega) (by omega),
                        h4unch ((i - 16) / 8) (by omega) (by omega),
                        h3unch ((i - 16) / 8) (by omega) (by omega),
                        h2unch ((i - 16) / 8) (by omega) (by omega),
                        h1unch ((i - 16) / 8) (by omega) (by omega),
                        h0unch ((i - 16) / 8) (by omega) (by omega)]
                    rw [hzv6, mul_comm]
                · -- Rounds 7+.
                  have hround : i / 32 = 7 := by omega
                  have hidx : i % 32 = i - 224 := by omega
                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                    hround, hidx, Nat.reduceAdd]
                  by_cases hlt : i - 224 < 16
                  · rw [if_pos hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
                    have hmod : (i + 16) % 8 = i % 8 := by omega
                    have hidx2 : i + 16 < 256 := by omega
                    rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
                    obtain ⟨hlow, _⟩ := h7butter (i / 8) (by omega) (by omega)
                    rw [hlow (i % 8) hl]
                    rw [h6unch (i / 8) (by omega) (by omega),
                        h5unch (i / 8) (by omega) (by omega),
                        h4unch (i / 8) (by omega) (by omega),
                        h3unch (i / 8) (by omega) (by omega),
                        h2unch (i / 8) (by omega) (by omega),
                        h1unch (i / 8) (by omega) (by omega),
                        h0unch (i / 8) (by omega) (by omega),
                        h6unch (i / 8 + 2) (by omega) (by omega),
                        h5unch (i / 8 + 2) (by omega) (by omega),
                        h4unch (i / 8 + 2) (by omega) (by omega),
                        h3unch (i / 8 + 2) (by omega) (by omega),
                        h2unch (i / 8 + 2) (by omega) (by omega),
                        h1unch (i / 8 + 2) (by omega) (by omega),
                        h0unch (i / 8 + 2) (by omega) (by omega)]
                    rw [hzv7, mul_comm]
                  · rw [if_neg hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
                    have hmod : (i - 16) % 8 = i % 8 := by omega
                    have hidx2 : i - 16 < 256 := by omega
                    rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
                    obtain ⟨_, hhigh⟩ := h7butter ((i - 16) / 8) (by omega) (by omega)
                    have hhigh' := hhigh (i % 8) hl
                    rw [hdiv, hhigh']
                    rw [h6unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h5unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h4unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h3unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h6unch ((i - 16) / 8) (by omega) (by omega),
                        h5unch ((i - 16) / 8) (by omega) (by omega),
                        h4unch ((i - 16) / 8) (by omega) (by omega),
                        h3unch ((i - 16) / 8) (by omega) (by omega),
                        h2unch ((i - 16) / 8) (by omega) (by omega),
                        h1unch ((i - 16) / 8) (by omega) (by omega),
                        h0unch ((i - 16) / 8) (by omega) (by omega)]
                    rw [hzv7, mul_comm]
  · -- Bound conjunct.
    have heq : B7 + 2 ^ 24 = B + 8 * 2 ^ 24 := by
      rw [← hB7def, ← hB6def, ← hB5def, ← hB4def, ← hB3def, ← hB2def, ← hB1def]; ring
    intro u hu l hl
    have := h7bd u hu l hl
    rw [heq] at this
    exact this

/-! ## Layer 3 (`len = 8`, `k = 16`, `STEP_BY = 1`, 16 cross-unit calls)

`ntt_at_layer_3` chains sixteen `outer_3_plus` calls on disjoint single-unit
blocks `[2·round, 2·round+1)` (`OFFSET = 2·round`, `STEP_BY = 1`), `ZETA` values
`2725464→z16 … 280005→z31`. The locked bound after 16 calls is `B + 16·2^24`. -/

set_option maxRecDepth 4000 in
private theorem zeta3_bridge0 :
    liftZ ((2725464#i32 : Std.I32).val : Int) = zeta 16 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge1 :
    liftZ ((1024112#i32 : Std.I32).val : Int) = zeta 17 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge2 :
    liftZ (((-1079900)#i32 : Std.I32).val : Int) = zeta 18 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge3 :
    liftZ ((3585928#i32 : Std.I32).val : Int) = zeta 19 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge4 :
    liftZ (((-549488)#i32 : Std.I32).val : Int) = zeta 20 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge5 :
    liftZ (((-1119584)#i32 : Std.I32).val : Int) = zeta 21 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge6 :
    liftZ ((2619752#i32 : Std.I32).val : Int) = zeta 22 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge7 :
    liftZ (((-2108549)#i32 : Std.I32).val : Int) = zeta 23 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge8 :
    liftZ (((-2118186)#i32 : Std.I32).val : Int) = zeta 24 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge9 :
    liftZ (((-3859737)#i32 : Std.I32).val : Int) = zeta 25 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge10 :
    liftZ (((-1399561)#i32 : Std.I32).val : Int) = zeta 26 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge11 :
    liftZ (((-3277672)#i32 : Std.I32).val : Int) = zeta 27 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge12 :
    liftZ ((1757237#i32 : Std.I32).val : Int) = zeta 28 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge13 :
    liftZ (((-19422)#i32 : Std.I32).val : Int) = zeta 29 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge14 :
    liftZ ((4010497#i32 : Std.I32).val : Int) = zeta 30 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge15 :
    liftZ ((280005#i32 : Std.I32).val : Int) = zeta 31 := by decide

private theorem zeta3_mag0 : (2725464#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag1 : (1024112#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag2 : ((-1079900)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag3 : (3585928#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag4 : ((-549488)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag5 : ((-1119584)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag6 : (2619752#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag7 : ((-2108549)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag8 : ((-2118186)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag9 : ((-3859737)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag10 : ((-1399561)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag11 : ((-3277672)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag12 : (1757237#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag13 : ((-19422)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag14 : (4010497#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag15 : (280005#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_3_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 16 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_3 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 3
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 16 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_3
  have hstep : 1 ≤ (1#usize : Std.Usize).val := by scalar_tac
  have hbnd0 : (0#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd1 : (2#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd2 : (4#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd3 : (6#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd4 : (8#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd5 : (10#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd6 : (12#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd7 : (14#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd8 : (16#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd9 : (18#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd10 : (20#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd11 : (22#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd12 : (24#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd13 : (26#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd14 : (28#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd15 : (30#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  have hB0 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  obtain ⟨r1, hr1_eq, h0butter, h0unch, h0bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 1#usize 2725464#i32 re B zeta3_mag0 hB0 hstep hbnd0 hin)
  have hB1raw : ((B + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  generalize hB1def : B + 2 ^ 24 = B1 at h0bd hB1raw
  obtain ⟨r2, hr2_eq, h1butter, h1unch, h1bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 2#usize 1#usize 1024112#i32 r1 B1 zeta3_mag1 hB1raw hstep hbnd1 h0bd)
  have hB2raw : ((B1 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    push_cast; omega
  generalize hB2def : B1 + 2 ^ 24 = B2 at h1bd hB2raw
  obtain ⟨r3, hr3_eq, h2butter, h2unch, h2bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 4#usize 1#usize (-1079900)#i32 r2 B2 zeta3_mag2 hB2raw hstep hbnd2 h1bd)
  have hB3raw : ((B2 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    push_cast; omega
  generalize hB3def : B2 + 2 ^ 24 = B3 at h2bd hB3raw
  obtain ⟨r4, hr4_eq, h3butter, h3unch, h3bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 6#usize 1#usize 3585928#i32 r3 B3 zeta3_mag3 hB3raw hstep hbnd3 h2bd)
  have hB4raw : ((B3 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    push_cast; omega
  generalize hB4def : B3 + 2 ^ 24 = B4 at h3bd hB4raw
  obtain ⟨r5, hr5_eq, h4butter, h4unch, h4bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 8#usize 1#usize (-549488)#i32 r4 B4 zeta3_mag4 hB4raw hstep hbnd4 h3bd)
  have hB5raw : ((B4 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    push_cast; omega
  generalize hB5def : B4 + 2 ^ 24 = B5 at h4bd hB5raw
  obtain ⟨r6, hr6_eq, h5butter, h5unch, h5bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 10#usize 1#usize (-1119584)#i32 r5 B5 zeta3_mag5 hB5raw hstep hbnd5 h4bd)
  have hB6raw : ((B5 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    push_cast; omega
  generalize hB6def : B5 + 2 ^ 24 = B6 at h5bd hB6raw
  obtain ⟨r7, hr7_eq, h6butter, h6unch, h6bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 12#usize 1#usize 2619752#i32 r6 B6 zeta3_mag6 hB6raw hstep hbnd6 h5bd)
  have hB7raw : ((B6 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    push_cast; omega
  generalize hB7def : B6 + 2 ^ 24 = B7 at h6bd hB7raw
  obtain ⟨r8, hr8_eq, h7butter, h7unch, h7bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 14#usize 1#usize (-2108549)#i32 r7 B7 zeta3_mag7 hB7raw hstep hbnd7 h6bd)
  have hB8raw : ((B7 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    push_cast; omega
  generalize hB8def : B7 + 2 ^ 24 = B8 at h7bd hB8raw
  obtain ⟨r9, hr9_eq, h8butter, h8unch, h8bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 16#usize 1#usize (-2118186)#i32 r8 B8 zeta3_mag8 hB8raw hstep hbnd8 h7bd)
  have hB9raw : ((B8 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    push_cast; omega
  generalize hB9def : B8 + 2 ^ 24 = B9 at h8bd hB9raw
  obtain ⟨r10, hr10_eq, h9butter, h9unch, h9bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 18#usize 1#usize (-3859737)#i32 r9 B9 zeta3_mag9 hB9raw hstep hbnd9 h8bd)
  have hB10raw : ((B9 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    push_cast; omega
  generalize hB10def : B9 + 2 ^ 24 = B10 at h9bd hB10raw
  obtain ⟨r11, hr11_eq, h10butter, h10unch, h10bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 20#usize 1#usize (-1399561)#i32 r10 B10
        zeta3_mag10 hB10raw hstep hbnd10 h9bd)
  have hB11raw : ((B10 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    push_cast; omega
  generalize hB11def : B10 + 2 ^ 24 = B11 at h10bd hB11raw
  obtain ⟨r12, hr12_eq, h11butter, h11unch, h11bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 22#usize 1#usize (-3277672)#i32 r11 B11
        zeta3_mag11 hB11raw hstep hbnd11 h10bd)
  have hB12raw : ((B11 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    have e11 : B11 = B10 + 2 ^ 24 := hB11def.symm
    push_cast; omega
  generalize hB12def : B11 + 2 ^ 24 = B12 at h11bd hB12raw
  obtain ⟨r13, hr13_eq, h12butter, h12unch, h12bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 24#usize 1#usize 1757237#i32 r12 B12 zeta3_mag12 hB12raw hstep hbnd12 h11bd)
  have hB13raw : ((B12 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    have e11 : B11 = B10 + 2 ^ 24 := hB11def.symm
    have e12 : B12 = B11 + 2 ^ 24 := hB12def.symm
    push_cast; omega
  generalize hB13def : B12 + 2 ^ 24 = B13 at h12bd hB13raw
  obtain ⟨r14, hr14_eq, h13butter, h13unch, h13bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 26#usize 1#usize (-19422)#i32 r13 B13 zeta3_mag13 hB13raw hstep hbnd13 h12bd)
  have hB14raw : ((B13 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    have e11 : B11 = B10 + 2 ^ 24 := hB11def.symm
    have e12 : B12 = B11 + 2 ^ 24 := hB12def.symm
    have e13 : B13 = B12 + 2 ^ 24 := hB13def.symm
    push_cast; omega
  generalize hB14def : B13 + 2 ^ 24 = B14 at h13bd hB14raw
  obtain ⟨r15, hr15_eq, h14butter, h14unch, h14bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 28#usize 1#usize 4010497#i32 r14 B14 zeta3_mag14 hB14raw hstep hbnd14 h13bd)
  have hB15raw : ((B14 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    have e11 : B11 = B10 + 2 ^ 24 := hB11def.symm
    have e12 : B12 = B11 + 2 ^ 24 := hB12def.symm
    have e13 : B13 = B12 + 2 ^ 24 := hB13def.symm
    have e14 : B14 = B13 + 2 ^ 24 := hB14def.symm
    push_cast; omega
  generalize hB15def : B14 + 2 ^ 24 = B15 at h14bd hB15raw
  obtain ⟨r16, hr16_eq, h15butter, h15unch, h15bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 30#usize 1#usize 280005#i32 r15 B15 zeta3_mag15 hB15raw hstep hbnd15 h14bd)
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr9_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr10_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr11_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr12_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr13_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr14_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr15_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr16_eq
  have e1 : (1#usize : Std.Usize).val = 1 := by simp
  have e0 : (0#usize : Std.Usize).val = 0 := by simp
  have e2 : (2#usize : Std.Usize).val = 2 := by simp
  have e4 : (4#usize : Std.Usize).val = 4 := by simp
  have e6 : (6#usize : Std.Usize).val = 6 := by simp
  have e8 : (8#usize : Std.Usize).val = 8 := by simp
  have e10 : (10#usize : Std.Usize).val = 10 := by simp
  have e12 : (12#usize : Std.Usize).val = 12 := by simp
  have e14 : (14#usize : Std.Usize).val = 14 := by simp
  have e16 : (16#usize : Std.Usize).val = 16 := by simp
  have e18 : (18#usize : Std.Usize).val = 18 := by simp
  have e20 : (20#usize : Std.Usize).val = 20 := by simp
  have e22 : (22#usize : Std.Usize).val = 22 := by simp
  have e24 : (24#usize : Std.Usize).val = 24 := by simp
  have e26 : (26#usize : Std.Usize).val = 26 := by simp
  have e28 : (28#usize : Std.Usize).val = 28 := by simp
  have e30 : (30#usize : Std.Usize).val = 30 := by simp
  simp only [e0, e1, e2, e4, e6, e8, e10, e12, e14, e16,
    e18, e20, e22, e24, e26, e28, e30, Nat.zero_add]
    at h0butter h0unch h1butter h1unch
       h2butter h2unch h3butter h3unch
       h4butter h4unch h5butter h5unch
       h6butter h6unch h7butter h7unch
       h8butter h8unch h9butter h9unch h10butter h10unch h11butter h11unch
       h12butter h12unch h13butter h13unch h14butter h14unch h15butter h15unch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    have hzv0 : liftZ (((2725464#i32 : Std.I32).val : Int)) = zeta 16 := zeta3_bridge0
    have hzv1 : liftZ (((1024112#i32 : Std.I32).val : Int)) = zeta 17 := zeta3_bridge1
    have hzv2 : liftZ ((((-1079900)#i32 : Std.I32).val : Int)) = zeta 18 := zeta3_bridge2
    have hzv3 : liftZ (((3585928#i32 : Std.I32).val : Int)) = zeta 19 := zeta3_bridge3
    have hzv4 : liftZ ((((-549488)#i32 : Std.I32).val : Int)) = zeta 20 := zeta3_bridge4
    have hzv5 : liftZ ((((-1119584)#i32 : Std.I32).val : Int)) = zeta 21 := zeta3_bridge5
    have hzv6 : liftZ (((2619752#i32 : Std.I32).val : Int)) = zeta 22 := zeta3_bridge6
    have hzv7 : liftZ ((((-2108549)#i32 : Std.I32).val : Int)) = zeta 23 := zeta3_bridge7
    have hzv8 : liftZ ((((-2118186)#i32 : Std.I32).val : Int)) = zeta 24 := zeta3_bridge8
    have hzv9 : liftZ ((((-3859737)#i32 : Std.I32).val : Int)) = zeta 25 := zeta3_bridge9
    have hzv10 : liftZ ((((-1399561)#i32 : Std.I32).val : Int)) = zeta 26 := zeta3_bridge10
    have hzv11 : liftZ ((((-3277672)#i32 : Std.I32).val : Int)) = zeta 27 := zeta3_bridge11
    have hzv12 : liftZ (((1757237#i32 : Std.I32).val : Int)) = zeta 28 := zeta3_bridge12
    have hzv13 : liftZ ((((-19422)#i32 : Std.I32).val : Int)) = zeta 29 := zeta3_bridge13
    have hzv14 : liftZ (((4010497#i32 : Std.I32).val : Int)) = zeta 30 := zeta3_bridge14
    have hzv15 : liftZ (((280005#i32 : Std.I32).val : Int)) = zeta 31 := zeta3_bridge15
    by_cases hr0 : i < 16
    · -- Round 0.
      have hround : i / 16 = 0 := by omega
      have hidx : i % 16 = i := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
      by_cases hlt : i < 8
      · rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
        have hmod : (i + 8) % 8 = i % 8 := by omega
        have hidx2 : i + 8 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h0butter (i / 8) (by omega) (by omega)
        rw [h15unch (i / 8) (by omega) (by omega),
            h14unch (i / 8) (by omega) (by omega),
            h13unch (i / 8) (by omega) (by omega),
            h12unch (i / 8) (by omega) (by omega),
            h11unch (i / 8) (by omega) (by omega),
            h10unch (i / 8) (by omega) (by omega),
            h9unch (i / 8) (by omega) (by omega),
            h8unch (i / 8) (by omega) (by omega),
            h7unch (i / 8) (by omega) (by omega),
            h6unch (i / 8) (by omega) (by omega),
            h5unch (i / 8) (by omega) (by omega),
            h4unch (i / 8) (by omega) (by omega),
            h3unch (i / 8) (by omega) (by omega),
            h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hlow (i % 8) hl]
        rw [hzv0, mul_comm]
      · rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
        have hmod : (i - 8) % 8 = i % 8 := by omega
        have hidx2 : i - 8 < 256 := by omega
        rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h0butter ((i - 8) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [h15unch (i / 8) (by omega) (by omega),
            h14unch (i / 8) (by omega) (by omega),
            h13unch (i / 8) (by omega) (by omega),
            h12unch (i / 8) (by omega) (by omega),
            h11unch (i / 8) (by omega) (by omega),
            h10unch (i / 8) (by omega) (by omega),
            h9unch (i / 8) (by omega) (by omega),
            h8unch (i / 8) (by omega) (by omega),
            h7unch (i / 8) (by omega) (by omega),
            h6unch (i / 8) (by omega) (by omega),
            h5unch (i / 8) (by omega) (by omega),
            h4unch (i / 8) (by omega) (by omega),
            h3unch (i / 8) (by omega) (by omega),
            h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hdiv, hhigh']
        rw [hzv0, mul_comm]
    · -- Rounds 1+.
      by_cases hr1 : i < 32
      · -- Round 1.
        have hround : i / 16 = 1 := by omega
        have hidx : i % 16 = i - 16 := by omega
        simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
        by_cases hlt : i - 16 < 8
        · rw [if_pos hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
          have hmod : (i + 8) % 8 = i % 8 := by omega
          have hidx2 : i + 8 < 256 := by omega
          rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
          obtain ⟨hlow, _⟩ := h1butter (i / 8) (by omega) (by omega)
          rw [h15unch (i / 8) (by omega) (by omega),
              h14unch (i / 8) (by omega) (by omega),
              h13unch (i / 8) (by omega) (by omega),
              h12unch (i / 8) (by omega) (by omega),
              h11unch (i / 8) (by omega) (by omega),
              h10unch (i / 8) (by omega) (by omega),
              h9unch (i / 8) (by omega) (by omega),
              h8unch (i / 8) (by omega) (by omega),
              h7unch (i / 8) (by omega) (by omega),
              h6unch (i / 8) (by omega) (by omega),
              h5unch (i / 8) (by omega) (by omega),
              h4unch (i / 8) (by omega) (by omega),
              h3unch (i / 8) (by omega) (by omega),
              h2unch (i / 8) (by omega) (by omega)]
          rw [hlow (i % 8) hl]
          rw [h0unch (i / 8) (by omega) (by omega), h0unch (i / 8 + 1) (by omega) (by omega)]
          rw [hzv1, mul_comm]
        · rw [if_neg hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
          have hmod : (i - 8) % 8 = i % 8 := by omega
          have hidx2 : i - 8 < 256 := by omega
          rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
          obtain ⟨_, hhigh⟩ := h1butter ((i - 8) / 8) (by omega) (by omega)
          have hhigh' := hhigh (i % 8) hl
          rw [h15unch (i / 8) (by omega) (by omega),
              h14unch (i / 8) (by omega) (by omega),
              h13unch (i / 8) (by omega) (by omega),
              h12unch (i / 8) (by omega) (by omega),
              h11unch (i / 8) (by omega) (by omega),
              h10unch (i / 8) (by omega) (by omega),
              h9unch (i / 8) (by omega) (by omega),
              h8unch (i / 8) (by omega) (by omega),
              h7unch (i / 8) (by omega) (by omega),
              h6unch (i / 8) (by omega) (by omega),
              h5unch (i / 8) (by omega) (by omega),
              h4unch (i / 8) (by omega) (by omega),
              h3unch (i / 8) (by omega) (by omega),
              h2unch (i / 8) (by omega) (by omega)]
          rw [hdiv, hhigh']
          rw [h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
              h0unch ((i - 8) / 8) (by omega) (by omega)]
          rw [hzv1, mul_comm]
      · -- Rounds 2+.
        by_cases hr2 : i < 48
        · -- Round 2.
          have hround : i / 16 = 2 := by omega
          have hidx : i % 16 = i - 32 := by omega
          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
          by_cases hlt : i - 32 < 8
          · rw [if_pos hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
            have hmod : (i + 8) % 8 = i % 8 := by omega
            have hidx2 : i + 8 < 256 := by omega
            rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
            obtain ⟨hlow, _⟩ := h2butter (i / 8) (by omega) (by omega)
            rw [h15unch (i / 8) (by omega) (by omega),
                h14unch (i / 8) (by omega) (by omega),
                h13unch (i / 8) (by omega) (by omega),
                h12unch (i / 8) (by omega) (by omega),
                h11unch (i / 8) (by omega) (by omega),
                h10unch (i / 8) (by omega) (by omega),
                h9unch (i / 8) (by omega) (by omega),
                h8unch (i / 8) (by omega) (by omega),
                h7unch (i / 8) (by omega) (by omega),
                h6unch (i / 8) (by omega) (by omega),
                h5unch (i / 8) (by omega) (by omega),
                h4unch (i / 8) (by omega) (by omega),
                h3unch (i / 8) (by omega) (by omega)]
            rw [hlow (i % 8) hl]
            rw [h1unch (i / 8) (by omega) (by omega),
                h0unch (i / 8) (by omega) (by omega),
                h1unch (i / 8 + 1) (by omega) (by omega),
                h0unch (i / 8 + 1) (by omega) (by omega)]
            rw [hzv2, mul_comm]
          · rw [if_neg hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
            have hmod : (i - 8) % 8 = i % 8 := by omega
            have hidx2 : i - 8 < 256 := by omega
            rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
            obtain ⟨_, hhigh⟩ := h2butter ((i - 8) / 8) (by omega) (by omega)
            have hhigh' := hhigh (i % 8) hl
            rw [h15unch (i / 8) (by omega) (by omega),
                h14unch (i / 8) (by omega) (by omega),
                h13unch (i / 8) (by omega) (by omega),
                h12unch (i / 8) (by omega) (by omega),
                h11unch (i / 8) (by omega) (by omega),
                h10unch (i / 8) (by omega) (by omega),
                h9unch (i / 8) (by omega) (by omega),
                h8unch (i / 8) (by omega) (by omega),
                h7unch (i / 8) (by omega) (by omega),
                h6unch (i / 8) (by omega) (by omega),
                h5unch (i / 8) (by omega) (by omega),
                h4unch (i / 8) (by omega) (by omega),
                h3unch (i / 8) (by omega) (by omega)]
            rw [hdiv, hhigh']
            rw [h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                h1unch ((i - 8) / 8) (by omega) (by omega),
                h0unch ((i - 8) / 8) (by omega) (by omega)]
            rw [hzv2, mul_comm]
        · -- Rounds 3+.
          by_cases hr3 : i < 64
          · -- Round 3.
            have hround : i / 16 = 3 := by omega
            have hidx : i % 16 = i - 48 := by omega
            simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
              hround, hidx, Nat.reduceAdd]
            by_cases hlt : i - 48 < 8
            · rw [if_pos hlt]
              have hl : i % 8 < 8 := by omega
              have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
              have hmod : (i + 8) % 8 = i % 8 := by omega
              have hidx2 : i + 8 < 256 := by omega
              rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
              obtain ⟨hlow, _⟩ := h3butter (i / 8) (by omega) (by omega)
              rw [h15unch (i / 8) (by omega) (by omega),
                  h14unch (i / 8) (by omega) (by omega),
                  h13unch (i / 8) (by omega) (by omega),
                  h12unch (i / 8) (by omega) (by omega),
                  h11unch (i / 8) (by omega) (by omega),
                  h10unch (i / 8) (by omega) (by omega),
                  h9unch (i / 8) (by omega) (by omega),
                  h8unch (i / 8) (by omega) (by omega),
                  h7unch (i / 8) (by omega) (by omega),
                  h6unch (i / 8) (by omega) (by omega),
                  h5unch (i / 8) (by omega) (by omega),
                  h4unch (i / 8) (by omega) (by omega)]
              rw [hlow (i % 8) hl]
              rw [h2unch (i / 8) (by omega) (by omega),
                  h1unch (i / 8) (by omega) (by omega),
                  h0unch (i / 8) (by omega) (by omega),
                  h2unch (i / 8 + 1) (by omega) (by omega),
                  h1unch (i / 8 + 1) (by omega) (by omega),
                  h0unch (i / 8 + 1) (by omega) (by omega)]
              rw [hzv3, mul_comm]
            · rw [if_neg hlt]
              have hl : i % 8 < 8 := by omega
              have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
              have hmod : (i - 8) % 8 = i % 8 := by omega
              have hidx2 : i - 8 < 256 := by omega
              rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
              obtain ⟨_, hhigh⟩ := h3butter ((i - 8) / 8) (by omega) (by omega)
              have hhigh' := hhigh (i % 8) hl
              rw [h15unch (i / 8) (by omega) (by omega),
                  h14unch (i / 8) (by omega) (by omega),
                  h13unch (i / 8) (by omega) (by omega),
                  h12unch (i / 8) (by omega) (by omega),
                  h11unch (i / 8) (by omega) (by omega),
                  h10unch (i / 8) (by omega) (by omega),
                  h9unch (i / 8) (by omega) (by omega),
                  h8unch (i / 8) (by omega) (by omega),
                  h7unch (i / 8) (by omega) (by omega),
                  h6unch (i / 8) (by omega) (by omega),
                  h5unch (i / 8) (by omega) (by omega),
                  h4unch (i / 8) (by omega) (by omega)]
              rw [hdiv, hhigh']
              rw [h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                  h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                  h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                  h2unch ((i - 8) / 8) (by omega) (by omega),
                  h1unch ((i - 8) / 8) (by omega) (by omega),
                  h0unch ((i - 8) / 8) (by omega) (by omega)]
              rw [hzv3, mul_comm]
          · -- Rounds 4+.
            by_cases hr4 : i < 80
            · -- Round 4.
              have hround : i / 16 = 4 := by omega
              have hidx : i % 16 = i - 64 := by omega
              simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                hround, hidx, Nat.reduceAdd]
              by_cases hlt : i - 64 < 8
              · rw [if_pos hlt]
                have hl : i % 8 < 8 := by omega
                have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                have hmod : (i + 8) % 8 = i % 8 := by omega
                have hidx2 : i + 8 < 256 := by omega
                rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
                obtain ⟨hlow, _⟩ := h4butter (i / 8) (by omega) (by omega)
                rw [h15unch (i / 8) (by omega) (by omega),
                    h14unch (i / 8) (by omega) (by omega),
                    h13unch (i / 8) (by omega) (by omega),
                    h12unch (i / 8) (by omega) (by omega),
                    h11unch (i / 8) (by omega) (by omega),
                    h10unch (i / 8) (by omega) (by omega),
                    h9unch (i / 8) (by omega) (by omega),
                    h8unch (i / 8) (by omega) (by omega),
                    h7unch (i / 8) (by omega) (by omega),
                    h6unch (i / 8) (by omega) (by omega),
                    h5unch (i / 8) (by omega) (by omega)]
                rw [hlow (i % 8) hl]
                rw [h3unch (i / 8) (by omega) (by omega),
                    h2unch (i / 8) (by omega) (by omega),
                    h1unch (i / 8) (by omega) (by omega),
                    h0unch (i / 8) (by omega) (by omega),
                    h3unch (i / 8 + 1) (by omega) (by omega),
                    h2unch (i / 8 + 1) (by omega) (by omega),
                    h1unch (i / 8 + 1) (by omega) (by omega),
                    h0unch (i / 8 + 1) (by omega) (by omega)]
                rw [hzv4, mul_comm]
              · rw [if_neg hlt]
                have hl : i % 8 < 8 := by omega
                have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                have hmod : (i - 8) % 8 = i % 8 := by omega
                have hidx2 : i - 8 < 256 := by omega
                rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                obtain ⟨_, hhigh⟩ := h4butter ((i - 8) / 8) (by omega) (by omega)
                have hhigh' := hhigh (i % 8) hl
                rw [h15unch (i / 8) (by omega) (by omega),
                    h14unch (i / 8) (by omega) (by omega),
                    h13unch (i / 8) (by omega) (by omega),
                    h12unch (i / 8) (by omega) (by omega),
                    h11unch (i / 8) (by omega) (by omega),
                    h10unch (i / 8) (by omega) (by omega),
                    h9unch (i / 8) (by omega) (by omega),
                    h8unch (i / 8) (by omega) (by omega),
                    h7unch (i / 8) (by omega) (by omega),
                    h6unch (i / 8) (by omega) (by omega),
                    h5unch (i / 8) (by omega) (by omega)]
                rw [hdiv, hhigh']
                rw [h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                    h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                    h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                    h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                    h3unch ((i - 8) / 8) (by omega) (by omega),
                    h2unch ((i - 8) / 8) (by omega) (by omega),
                    h1unch ((i - 8) / 8) (by omega) (by omega),
                    h0unch ((i - 8) / 8) (by omega) (by omega)]
                rw [hzv4, mul_comm]
            · -- Rounds 5+.
              by_cases hr5 : i < 96
              · -- Round 5.
                have hround : i / 16 = 5 := by omega
                have hidx : i % 16 = i - 80 := by omega
                simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                  hround, hidx, Nat.reduceAdd]
                by_cases hlt : i - 80 < 8
                · rw [if_pos hlt]
                  have hl : i % 8 < 8 := by omega
                  have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                  have hmod : (i + 8) % 8 = i % 8 := by omega
                  have hidx2 : i + 8 < 256 := by omega
                  rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
                  obtain ⟨hlow, _⟩ := h5butter (i / 8) (by omega) (by omega)
                  rw [h15unch (i / 8) (by omega) (by omega),
                      h14unch (i / 8) (by omega) (by omega),
                      h13unch (i / 8) (by omega) (by omega),
                      h12unch (i / 8) (by omega) (by omega),
                      h11unch (i / 8) (by omega) (by omega),
                      h10unch (i / 8) (by omega) (by omega),
                      h9unch (i / 8) (by omega) (by omega),
                      h8unch (i / 8) (by omega) (by omega),
                      h7unch (i / 8) (by omega) (by omega),
                      h6unch (i / 8) (by omega) (by omega)]
                  rw [hlow (i % 8) hl]
                  rw [h4unch (i / 8) (by omega) (by omega),
                      h3unch (i / 8) (by omega) (by omega),
                      h2unch (i / 8) (by omega) (by omega),
                      h1unch (i / 8) (by omega) (by omega),
                      h0unch (i / 8) (by omega) (by omega),
                      h4unch (i / 8 + 1) (by omega) (by omega),
                      h3unch (i / 8 + 1) (by omega) (by omega),
                      h2unch (i / 8 + 1) (by omega) (by omega),
                      h1unch (i / 8 + 1) (by omega) (by omega),
                      h0unch (i / 8 + 1) (by omega) (by omega)]
                  rw [hzv5, mul_comm]
                · rw [if_neg hlt]
                  have hl : i % 8 < 8 := by omega
                  have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                  have hmod : (i - 8) % 8 = i % 8 := by omega
                  have hidx2 : i - 8 < 256 := by omega
                  rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                  obtain ⟨_, hhigh⟩ := h5butter ((i - 8) / 8) (by omega) (by omega)
                  have hhigh' := hhigh (i % 8) hl
                  rw [h15unch (i / 8) (by omega) (by omega),
                      h14unch (i / 8) (by omega) (by omega),
                      h13unch (i / 8) (by omega) (by omega),
                      h12unch (i / 8) (by omega) (by omega),
                      h11unch (i / 8) (by omega) (by omega),
                      h10unch (i / 8) (by omega) (by omega),
                      h9unch (i / 8) (by omega) (by omega),
                      h8unch (i / 8) (by omega) (by omega),
                      h7unch (i / 8) (by omega) (by omega),
                      h6unch (i / 8) (by omega) (by omega)]
                  rw [hdiv, hhigh']
                  rw [h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h4unch ((i - 8) / 8) (by omega) (by omega),
                      h3unch ((i - 8) / 8) (by omega) (by omega),
                      h2unch ((i - 8) / 8) (by omega) (by omega),
                      h1unch ((i - 8) / 8) (by omega) (by omega),
                      h0unch ((i - 8) / 8) (by omega) (by omega)]
                  rw [hzv5, mul_comm]
              · -- Rounds 6+.
                by_cases hr6 : i < 112
                · -- Round 6.
                  have hround : i / 16 = 6 := by omega
                  have hidx : i % 16 = i - 96 := by omega
                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                    hround, hidx, Nat.reduceAdd]
                  by_cases hlt : i - 96 < 8
                  · rw [if_pos hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                    have hmod : (i + 8) % 8 = i % 8 := by omega
                    have hidx2 : i + 8 < 256 := by omega
                    rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
                    obtain ⟨hlow, _⟩ := h6butter (i / 8) (by omega) (by omega)
                    rw [h15unch (i / 8) (by omega) (by omega),
                        h14unch (i / 8) (by omega) (by omega),
                        h13unch (i / 8) (by omega) (by omega),
                        h12unch (i / 8) (by omega) (by omega),
                        h11unch (i / 8) (by omega) (by omega),
                        h10unch (i / 8) (by omega) (by omega),
                        h9unch (i / 8) (by omega) (by omega),
                        h8unch (i / 8) (by omega) (by omega),
                        h7unch (i / 8) (by omega) (by omega)]
                    rw [hlow (i % 8) hl]
                    rw [h5unch (i / 8) (by omega) (by omega),
                        h4unch (i / 8) (by omega) (by omega),
                        h3unch (i / 8) (by omega) (by omega),
                        h2unch (i / 8) (by omega) (by omega),
                        h1unch (i / 8) (by omega) (by omega),
                        h0unch (i / 8) (by omega) (by omega),
                        h5unch (i / 8 + 1) (by omega) (by omega),
                        h4unch (i / 8 + 1) (by omega) (by omega),
                        h3unch (i / 8 + 1) (by omega) (by omega),
                        h2unch (i / 8 + 1) (by omega) (by omega),
                        h1unch (i / 8 + 1) (by omega) (by omega),
                        h0unch (i / 8 + 1) (by omega) (by omega)]
                    rw [hzv6, mul_comm]
                  · rw [if_neg hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                    have hmod : (i - 8) % 8 = i % 8 := by omega
                    have hidx2 : i - 8 < 256 := by omega
                    rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                    obtain ⟨_, hhigh⟩ := h6butter ((i - 8) / 8) (by omega) (by omega)
                    have hhigh' := hhigh (i % 8) hl
                    rw [h15unch (i / 8) (by omega) (by omega),
                        h14unch (i / 8) (by omega) (by omega),
                        h13unch (i / 8) (by omega) (by omega),
                        h12unch (i / 8) (by omega) (by omega),
                        h11unch (i / 8) (by omega) (by omega),
                        h10unch (i / 8) (by omega) (by omega),
                        h9unch (i / 8) (by omega) (by omega),
                        h8unch (i / 8) (by omega) (by omega),
                        h7unch (i / 8) (by omega) (by omega)]
                    rw [hdiv, hhigh']
                    rw [h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h5unch ((i - 8) / 8) (by omega) (by omega),
                        h4unch ((i - 8) / 8) (by omega) (by omega),
                        h3unch ((i - 8) / 8) (by omega) (by omega),
                        h2unch ((i - 8) / 8) (by omega) (by omega),
                        h1unch ((i - 8) / 8) (by omega) (by omega),
                        h0unch ((i - 8) / 8) (by omega) (by omega)]
                    rw [hzv6, mul_comm]
                · -- Rounds 7+.
                  by_cases hr7 : i < 128
                  · -- Round 7.
                    have hround : i / 16 = 7 := by omega
                    have hidx : i % 16 = i - 112 := by omega
                    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                      hround, hidx, Nat.reduceAdd]
                    by_cases hlt : i - 112 < 8
                    · rw [if_pos hlt]
                      have hl : i % 8 < 8 := by omega
                      have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                      have hmod : (i + 8) % 8 = i % 8 := by omega
                      have hidx2 : i + 8 < 256 := by omega
                      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
                      obtain ⟨hlow, _⟩ := h7butter (i / 8) (by omega) (by omega)
                      rw [h15unch (i / 8) (by omega) (by omega),
                          h14unch (i / 8) (by omega) (by omega),
                          h13unch (i / 8) (by omega) (by omega),
                          h12unch (i / 8) (by omega) (by omega),
                          h11unch (i / 8) (by omega) (by omega),
                          h10unch (i / 8) (by omega) (by omega),
                          h9unch (i / 8) (by omega) (by omega),
                          h8unch (i / 8) (by omega) (by omega)]
                      rw [hlow (i % 8) hl]
                      rw [h6unch (i / 8) (by omega) (by omega),
                          h5unch (i / 8) (by omega) (by omega),
                          h4unch (i / 8) (by omega) (by omega),
                          h3unch (i / 8) (by omega) (by omega),
                          h2unch (i / 8) (by omega) (by omega),
                          h1unch (i / 8) (by omega) (by omega),
                          h0unch (i / 8) (by omega) (by omega),
                          h6unch (i / 8 + 1) (by omega) (by omega),
                          h5unch (i / 8 + 1) (by omega) (by omega),
                          h4unch (i / 8 + 1) (by omega) (by omega),
                          h3unch (i / 8 + 1) (by omega) (by omega),
                          h2unch (i / 8 + 1) (by omega) (by omega),
                          h1unch (i / 8 + 1) (by omega) (by omega),
                          h0unch (i / 8 + 1) (by omega) (by omega)]
                      rw [hzv7, mul_comm]
                    · rw [if_neg hlt]
                      have hl : i % 8 < 8 := by omega
                      have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                      have hmod : (i - 8) % 8 = i % 8 := by omega
                      have hidx2 : i - 8 < 256 := by omega
                      rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                      obtain ⟨_, hhigh⟩ := h7butter ((i - 8) / 8) (by omega) (by omega)
                      have hhigh' := hhigh (i % 8) hl
                      rw [h15unch (i / 8) (by omega) (by omega),
                          h14unch (i / 8) (by omega) (by omega),
                          h13unch (i / 8) (by omega) (by omega),
                          h12unch (i / 8) (by omega) (by omega),
                          h11unch (i / 8) (by omega) (by omega),
                          h10unch (i / 8) (by omega) (by omega),
                          h9unch (i / 8) (by omega) (by omega),
                          h8unch (i / 8) (by omega) (by omega)]
                      rw [hdiv, hhigh']
                      rw [h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h6unch ((i - 8) / 8) (by omega) (by omega),
                          h5unch ((i - 8) / 8) (by omega) (by omega),
                          h4unch ((i - 8) / 8) (by omega) (by omega),
                          h3unch ((i - 8) / 8) (by omega) (by omega),
                          h2unch ((i - 8) / 8) (by omega) (by omega),
                          h1unch ((i - 8) / 8) (by omega) (by omega),
                          h0unch ((i - 8) / 8) (by omega) (by omega)]
                      rw [hzv7, mul_comm]
                  · -- Rounds 8+.
                    by_cases hr8 : i < 144
                    · -- Round 8.
                      have hround : i / 16 = 8 := by omega
                      have hidx : i % 16 = i - 128 := by omega
                      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                        hround, hidx, Nat.reduceAdd]
                      by_cases hlt : i - 128 < 8
                      · rw [if_pos hlt]
                        have hl : i % 8 < 8 := by omega
                        have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                        have hmod : (i + 8) % 8 = i % 8 := by omega
                        have hidx2 : i + 8 < 256 := by omega
                        rw [Pure.build_getElem _ i hi,
                            Pure.build_getElem _ (i + 8) hidx2,
                            hdiv,
                            hmod]
                        obtain ⟨hlow, _⟩ := h8butter (i / 8) (by omega) (by omega)
                        rw [h15unch (i / 8) (by omega) (by omega),
                            h14unch (i / 8) (by omega) (by omega),
                            h13unch (i / 8) (by omega) (by omega),
                            h12unch (i / 8) (by omega) (by omega),
                            h11unch (i / 8) (by omega) (by omega),
                            h10unch (i / 8) (by omega) (by omega),
                            h9unch (i / 8) (by omega) (by omega)]
                        rw [hlow (i % 8) hl]
                        rw [h7unch (i / 8) (by omega) (by omega),
                            h6unch (i / 8) (by omega) (by omega),
                            h5unch (i / 8) (by omega) (by omega),
                            h4unch (i / 8) (by omega) (by omega),
                            h3unch (i / 8) (by omega) (by omega),
                            h2unch (i / 8) (by omega) (by omega),
                            h1unch (i / 8) (by omega) (by omega),
                            h0unch (i / 8) (by omega) (by omega),
                            h7unch (i / 8 + 1) (by omega) (by omega),
                            h6unch (i / 8 + 1) (by omega) (by omega),
                            h5unch (i / 8 + 1) (by omega) (by omega),
                            h4unch (i / 8 + 1) (by omega) (by omega),
                            h3unch (i / 8 + 1) (by omega) (by omega),
                            h2unch (i / 8 + 1) (by omega) (by omega),
                            h1unch (i / 8 + 1) (by omega) (by omega),
                            h0unch (i / 8 + 1) (by omega) (by omega)]
                        rw [hzv8, mul_comm]
                      · rw [if_neg hlt]
                        have hl : i % 8 < 8 := by omega
                        have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                        have hmod : (i - 8) % 8 = i % 8 := by omega
                        have hidx2 : i - 8 < 256 := by omega
                        rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                        obtain ⟨_, hhigh⟩ := h8butter ((i - 8) / 8) (by omega) (by omega)
                        have hhigh' := hhigh (i % 8) hl
                        rw [h15unch (i / 8) (by omega) (by omega),
                            h14unch (i / 8) (by omega) (by omega),
                            h13unch (i / 8) (by omega) (by omega),
                            h12unch (i / 8) (by omega) (by omega),
                            h11unch (i / 8) (by omega) (by omega),
                            h10unch (i / 8) (by omega) (by omega),
                            h9unch (i / 8) (by omega) (by omega)]
                        rw [hdiv, hhigh']
                        rw [h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h7unch ((i - 8) / 8) (by omega) (by omega),
                            h6unch ((i - 8) / 8) (by omega) (by omega),
                            h5unch ((i - 8) / 8) (by omega) (by omega),
                            h4unch ((i - 8) / 8) (by omega) (by omega),
                            h3unch ((i - 8) / 8) (by omega) (by omega),
                            h2unch ((i - 8) / 8) (by omega) (by omega),
                            h1unch ((i - 8) / 8) (by omega) (by omega),
                            h0unch ((i - 8) / 8) (by omega) (by omega)]
                        rw [hzv8, mul_comm]
                    · -- Rounds 9+.
                      by_cases hr9 : i < 160
                      · -- Round 9.
                        have hround : i / 16 = 9 := by omega
                        have hidx : i % 16 = i - 144 := by omega
                        simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                          hround, hidx, Nat.reduceAdd]
                        by_cases hlt : i - 144 < 8
                        · rw [if_pos hlt]
                          have hl : i % 8 < 8 := by omega
                          have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                          have hmod : (i + 8) % 8 = i % 8 := by omega
                          have hidx2 : i + 8 < 256 := by omega
                          rw [Pure.build_getElem _ i hi,
                              Pure.build_getElem _ (i + 8) hidx2,
                              hdiv,
                              hmod]
                          obtain ⟨hlow, _⟩ := h9butter (i / 8) (by omega) (by omega)
                          rw [h15unch (i / 8) (by omega) (by omega),
                              h14unch (i / 8) (by omega) (by omega),
                              h13unch (i / 8) (by omega) (by omega),
                              h12unch (i / 8) (by omega) (by omega),
                              h11unch (i / 8) (by omega) (by omega),
                              h10unch (i / 8) (by omega) (by omega)]
                          rw [hlow (i % 8) hl]
                          rw [h8unch (i / 8) (by omega) (by omega),
                              h7unch (i / 8) (by omega) (by omega),
                              h6unch (i / 8) (by omega) (by omega),
                              h5unch (i / 8) (by omega) (by omega),
                              h4unch (i / 8) (by omega) (by omega),
                              h3unch (i / 8) (by omega) (by omega),
                              h2unch (i / 8) (by omega) (by omega),
                              h1unch (i / 8) (by omega) (by omega),
                              h0unch (i / 8) (by omega) (by omega),
                              h8unch (i / 8 + 1) (by omega) (by omega),
                              h7unch (i / 8 + 1) (by omega) (by omega),
                              h6unch (i / 8 + 1) (by omega) (by omega),
                              h5unch (i / 8 + 1) (by omega) (by omega),
                              h4unch (i / 8 + 1) (by omega) (by omega),
                              h3unch (i / 8 + 1) (by omega) (by omega),
                              h2unch (i / 8 + 1) (by omega) (by omega),
                              h1unch (i / 8 + 1) (by omega) (by omega),
                              h0unch (i / 8 + 1) (by omega) (by omega)]
                          rw [hzv9, mul_comm]
                        · rw [if_neg hlt]
                          have hl : i % 8 < 8 := by omega
                          have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                          have hmod : (i - 8) % 8 = i % 8 := by omega
                          have hidx2 : i - 8 < 256 := by omega
                          rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                          obtain ⟨_, hhigh⟩ := h9butter ((i - 8) / 8) (by omega) (by omega)
                          have hhigh' := hhigh (i % 8) hl
                          rw [h15unch (i / 8) (by omega) (by omega),
                              h14unch (i / 8) (by omega) (by omega),
                              h13unch (i / 8) (by omega) (by omega),
                              h12unch (i / 8) (by omega) (by omega),
                              h11unch (i / 8) (by omega) (by omega),
                              h10unch (i / 8) (by omega) (by omega)]
                          rw [hdiv, hhigh']
                          rw [h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h8unch ((i - 8) / 8) (by omega) (by omega),
                              h7unch ((i - 8) / 8) (by omega) (by omega),
                              h6unch ((i - 8) / 8) (by omega) (by omega),
                              h5unch ((i - 8) / 8) (by omega) (by omega),
                              h4unch ((i - 8) / 8) (by omega) (by omega),
                              h3unch ((i - 8) / 8) (by omega) (by omega),
                              h2unch ((i - 8) / 8) (by omega) (by omega),
                              h1unch ((i - 8) / 8) (by omega) (by omega),
                              h0unch ((i - 8) / 8) (by omega) (by omega)]
                          rw [hzv9, mul_comm]
                      · -- Rounds 10+.
                        by_cases hr10 : i < 176
                        · -- Round 10.
                          have hround : i / 16 = 10 := by omega
                          have hidx : i % 16 = i - 160 := by omega
                          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                            hround, hidx, Nat.reduceAdd]
                          by_cases hlt : i - 160 < 8
                          · rw [if_pos hlt]
                            have hl : i % 8 < 8 := by omega
                            have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                            have hmod : (i + 8) % 8 = i % 8 := by omega
                            have hidx2 : i + 8 < 256 := by omega
                            rw [Pure.build_getElem _ i hi,
                                Pure.build_getElem _ (i + 8) hidx2,
                                hdiv,
                                hmod]
                            obtain ⟨hlow, _⟩ := h10butter (i / 8) (by omega) (by omega)
                            rw [h15unch (i / 8) (by omega) (by omega),
                                h14unch (i / 8) (by omega) (by omega),
                                h13unch (i / 8) (by omega) (by omega),
                                h12unch (i / 8) (by omega) (by omega),
                                h11unch (i / 8) (by omega) (by omega)]
                            rw [hlow (i % 8) hl]
                            rw [h9unch (i / 8) (by omega) (by omega),
                                h8unch (i / 8) (by omega) (by omega),
                                h7unch (i / 8) (by omega) (by omega),
                                h6unch (i / 8) (by omega) (by omega),
                                h5unch (i / 8) (by omega) (by omega),
                                h4unch (i / 8) (by omega) (by omega),
                                h3unch (i / 8) (by omega) (by omega),
                                h2unch (i / 8) (by omega) (by omega),
                                h1unch (i / 8) (by omega) (by omega),
                                h0unch (i / 8) (by omega) (by omega),
                                h9unch (i / 8 + 1) (by omega) (by omega),
                                h8unch (i / 8 + 1) (by omega) (by omega),
                                h7unch (i / 8 + 1) (by omega) (by omega),
                                h6unch (i / 8 + 1) (by omega) (by omega),
                                h5unch (i / 8 + 1) (by omega) (by omega),
                                h4unch (i / 8 + 1) (by omega) (by omega),
                                h3unch (i / 8 + 1) (by omega) (by omega),
                                h2unch (i / 8 + 1) (by omega) (by omega),
                                h1unch (i / 8 + 1) (by omega) (by omega),
                                h0unch (i / 8 + 1) (by omega) (by omega)]
                            rw [hzv10, mul_comm]
                          · rw [if_neg hlt]
                            have hl : i % 8 < 8 := by omega
                            have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                            have hmod : (i - 8) % 8 = i % 8 := by omega
                            have hidx2 : i - 8 < 256 := by omega
                            rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                            obtain ⟨_, hhigh⟩ := h10butter ((i - 8) / 8) (by omega) (by omega)
                            have hhigh' := hhigh (i % 8) hl
                            rw [h15unch (i / 8) (by omega) (by omega),
                                h14unch (i / 8) (by omega) (by omega),
                                h13unch (i / 8) (by omega) (by omega),
                                h12unch (i / 8) (by omega) (by omega),
                                h11unch (i / 8) (by omega) (by omega)]
                            rw [hdiv, hhigh']
                            rw [h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h9unch ((i - 8) / 8) (by omega) (by omega),
                                h8unch ((i - 8) / 8) (by omega) (by omega),
                                h7unch ((i - 8) / 8) (by omega) (by omega),
                                h6unch ((i - 8) / 8) (by omega) (by omega),
                                h5unch ((i - 8) / 8) (by omega) (by omega),
                                h4unch ((i - 8) / 8) (by omega) (by omega),
                                h3unch ((i - 8) / 8) (by omega) (by omega),
                                h2unch ((i - 8) / 8) (by omega) (by omega),
                                h1unch ((i - 8) / 8) (by omega) (by omega),
                                h0unch ((i - 8) / 8) (by omega) (by omega)]
                            rw [hzv10, mul_comm]
                        · -- Rounds 11+.
                          by_cases hr11 : i < 192
                          · -- Round 11.
                            have hround : i / 16 = 11 := by omega
                            have hidx : i % 16 = i - 176 := by omega
                            simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                              hround, hidx, Nat.reduceAdd]
                            by_cases hlt : i - 176 < 8
                            · rw [if_pos hlt]
                              have hl : i % 8 < 8 := by omega
                              have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                              have hmod : (i + 8) % 8 = i % 8 := by omega
                              have hidx2 : i + 8 < 256 := by omega
                              rw [Pure.build_getElem _ i hi,
                                  Pure.build_getElem _ (i + 8) hidx2,
                                  hdiv,
                                  hmod]
                              obtain ⟨hlow, _⟩ := h11butter (i / 8) (by omega) (by omega)
                              rw [h15unch (i / 8) (by omega) (by omega),
                                  h14unch (i / 8) (by omega) (by omega),
                                  h13unch (i / 8) (by omega) (by omega),
                                  h12unch (i / 8) (by omega) (by omega)]
                              rw [hlow (i % 8) hl]
                              rw [h10unch (i / 8) (by omega) (by omega),
                                  h9unch (i / 8) (by omega) (by omega),
                                  h8unch (i / 8) (by omega) (by omega),
                                  h7unch (i / 8) (by omega) (by omega),
                                  h6unch (i / 8) (by omega) (by omega),
                                  h5unch (i / 8) (by omega) (by omega),
                                  h4unch (i / 8) (by omega) (by omega),
                                  h3unch (i / 8) (by omega) (by omega),
                                  h2unch (i / 8) (by omega) (by omega),
                                  h1unch (i / 8) (by omega) (by omega),
                                  h0unch (i / 8) (by omega) (by omega),
                                  h10unch (i / 8 + 1) (by omega) (by omega),
                                  h9unch (i / 8 + 1) (by omega) (by omega),
                                  h8unch (i / 8 + 1) (by omega) (by omega),
                                  h7unch (i / 8 + 1) (by omega) (by omega),
                                  h6unch (i / 8 + 1) (by omega) (by omega),
                                  h5unch (i / 8 + 1) (by omega) (by omega),
                                  h4unch (i / 8 + 1) (by omega) (by omega),
                                  h3unch (i / 8 + 1) (by omega) (by omega),
                                  h2unch (i / 8 + 1) (by omega) (by omega),
                                  h1unch (i / 8 + 1) (by omega) (by omega),
                                  h0unch (i / 8 + 1) (by omega) (by omega)]
                              rw [hzv11, mul_comm]
                            · rw [if_neg hlt]
                              have hl : i % 8 < 8 := by omega
                              have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                              have hmod : (i - 8) % 8 = i % 8 := by omega
                              have hidx2 : i - 8 < 256 := by omega
                              rw [Pure.build_getElem _ (i - 8) hidx2,
                                  Pure.build_getElem _ i hi,
                                  hmod]
                              obtain ⟨_, hhigh⟩ := h11butter ((i - 8) / 8) (by omega) (by omega)
                              have hhigh' := hhigh (i % 8) hl
                              rw [h15unch (i / 8) (by omega) (by omega),
                                  h14unch (i / 8) (by omega) (by omega),
                                  h13unch (i / 8) (by omega) (by omega),
                                  h12unch (i / 8) (by omega) (by omega)]
                              rw [hdiv, hhigh']
                              rw [h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h10unch ((i - 8) / 8) (by omega) (by omega),
                                  h9unch ((i - 8) / 8) (by omega) (by omega),
                                  h8unch ((i - 8) / 8) (by omega) (by omega),
                                  h7unch ((i - 8) / 8) (by omega) (by omega),
                                  h6unch ((i - 8) / 8) (by omega) (by omega),
                                  h5unch ((i - 8) / 8) (by omega) (by omega),
                                  h4unch ((i - 8) / 8) (by omega) (by omega),
                                  h3unch ((i - 8) / 8) (by omega) (by omega),
                                  h2unch ((i - 8) / 8) (by omega) (by omega),
                                  h1unch ((i - 8) / 8) (by omega) (by omega),
                                  h0unch ((i - 8) / 8) (by omega) (by omega)]
                              rw [hzv11, mul_comm]
                          · -- Rounds 12+.
                            by_cases hr12 : i < 208
                            · -- Round 12.
                              have hround : i / 16 = 12 := by omega
                              have hidx : i % 16 = i - 192 := by omega
                              simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                                hround, hidx, Nat.reduceAdd]
                              by_cases hlt : i - 192 < 8
                              · rw [if_pos hlt]
                                have hl : i % 8 < 8 := by omega
                                have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                                have hmod : (i + 8) % 8 = i % 8 := by omega
                                have hidx2 : i + 8 < 256 := by omega
                                rw [Pure.build_getElem _ i hi,
                                    Pure.build_getElem _ (i + 8) hidx2,
                                    hdiv,
                                    hmod]
                                obtain ⟨hlow, _⟩ := h12butter (i / 8) (by omega) (by omega)
                                rw [h15unch (i / 8) (by omega) (by omega),
                                    h14unch (i / 8) (by omega) (by omega),
                                    h13unch (i / 8) (by omega) (by omega)]
                                rw [hlow (i % 8) hl]
                                rw [h11unch (i / 8) (by omega) (by omega),
                                    h10unch (i / 8) (by omega) (by omega),
                                    h9unch (i / 8) (by omega) (by omega),
                                    h8unch (i / 8) (by omega) (by omega),
                                    h7unch (i / 8) (by omega) (by omega),
                                    h6unch (i / 8) (by omega) (by omega),
                                    h5unch (i / 8) (by omega) (by omega),
                                    h4unch (i / 8) (by omega) (by omega),
                                    h3unch (i / 8) (by omega) (by omega),
                                    h2unch (i / 8) (by omega) (by omega),
                                    h1unch (i / 8) (by omega) (by omega),
                                    h0unch (i / 8) (by omega) (by omega),
                                    h11unch (i / 8 + 1) (by omega) (by omega),
                                    h10unch (i / 8 + 1) (by omega) (by omega),
                                    h9unch (i / 8 + 1) (by omega) (by omega),
                                    h8unch (i / 8 + 1) (by omega) (by omega),
                                    h7unch (i / 8 + 1) (by omega) (by omega),
                                    h6unch (i / 8 + 1) (by omega) (by omega),
                                    h5unch (i / 8 + 1) (by omega) (by omega),
                                    h4unch (i / 8 + 1) (by omega) (by omega),
                                    h3unch (i / 8 + 1) (by omega) (by omega),
                                    h2unch (i / 8 + 1) (by omega) (by omega),
                                    h1unch (i / 8 + 1) (by omega) (by omega),
                                    h0unch (i / 8 + 1) (by omega) (by omega)]
                                rw [hzv12, mul_comm]
                              · rw [if_neg hlt]
                                have hl : i % 8 < 8 := by omega
                                have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                                have hmod : (i - 8) % 8 = i % 8 := by omega
                                have hidx2 : i - 8 < 256 := by omega
                                rw [Pure.build_getElem _ (i - 8) hidx2,
                                    Pure.build_getElem _ i hi,
                                    hmod]
                                obtain ⟨_, hhigh⟩ := h12butter ((i - 8) / 8) (by omega) (by omega)
                                have hhigh' := hhigh (i % 8) hl
                                rw [h15unch (i / 8) (by omega) (by omega),
                                    h14unch (i / 8) (by omega) (by omega),
                                    h13unch (i / 8) (by omega) (by omega)]
                                rw [hdiv, hhigh']
                                rw [h11unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h11unch ((i - 8) / 8) (by omega) (by omega),
                                    h10unch ((i - 8) / 8) (by omega) (by omega),
                                    h9unch ((i - 8) / 8) (by omega) (by omega),
                                    h8unch ((i - 8) / 8) (by omega) (by omega),
                                    h7unch ((i - 8) / 8) (by omega) (by omega),
                                    h6unch ((i - 8) / 8) (by omega) (by omega),
                                    h5unch ((i - 8) / 8) (by omega) (by omega),
                                    h4unch ((i - 8) / 8) (by omega) (by omega),
                                    h3unch ((i - 8) / 8) (by omega) (by omega),
                                    h2unch ((i - 8) / 8) (by omega) (by omega),
                                    h1unch ((i - 8) / 8) (by omega) (by omega),
                                    h0unch ((i - 8) / 8) (by omega) (by omega)]
                                rw [hzv12, mul_comm]
                            · -- Rounds 13+.
                              by_cases hr13 : i < 224
                              · -- Round 13.
                                have hround : i / 16 = 13 := by omega
                                have hidx : i % 16 = i - 208 := by omega
                                simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                                  hround, hidx, Nat.reduceAdd]
                                by_cases hlt : i - 208 < 8
                                · rw [if_pos hlt]
                                  have hl : i % 8 < 8 := by omega
                                  have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                                  have hmod : (i + 8) % 8 = i % 8 := by omega
                                  have hidx2 : i + 8 < 256 := by omega
                                  rw [Pure.build_getElem _ i hi,
                                      Pure.build_getElem _ (i + 8) hidx2,
                                      hdiv,
                                      hmod]
                                  obtain ⟨hlow, _⟩ := h13butter (i / 8) (by omega) (by omega)
                                  rw [h15unch (i / 8) (by omega) (by omega),
                                      h14unch (i / 8) (by omega) (by omega)]
                                  rw [hlow (i % 8) hl]
                                  rw [h12unch (i / 8) (by omega) (by omega),
                                      h11unch (i / 8) (by omega) (by omega),
                                      h10unch (i / 8) (by omega) (by omega),
                                      h9unch (i / 8) (by omega) (by omega),
                                      h8unch (i / 8) (by omega) (by omega),
                                      h7unch (i / 8) (by omega) (by omega),
                                      h6unch (i / 8) (by omega) (by omega),
                                      h5unch (i / 8) (by omega) (by omega),
                                      h4unch (i / 8) (by omega) (by omega),
                                      h3unch (i / 8) (by omega) (by omega),
                                      h2unch (i / 8) (by omega) (by omega),
                                      h1unch (i / 8) (by omega) (by omega),
                                      h0unch (i / 8) (by omega) (by omega),
                                      h12unch (i / 8 + 1) (by omega) (by omega),
                                      h11unch (i / 8 + 1) (by omega) (by omega),
                                      h10unch (i / 8 + 1) (by omega) (by omega),
                                      h9unch (i / 8 + 1) (by omega) (by omega),
                                      h8unch (i / 8 + 1) (by omega) (by omega),
                                      h7unch (i / 8 + 1) (by omega) (by omega),
                                      h6unch (i / 8 + 1) (by omega) (by omega),
                                      h5unch (i / 8 + 1) (by omega) (by omega),
                                      h4unch (i / 8 + 1) (by omega) (by omega),
                                      h3unch (i / 8 + 1) (by omega) (by omega),
                                      h2unch (i / 8 + 1) (by omega) (by omega),
                                      h1unch (i / 8 + 1) (by omega) (by omega),
                                      h0unch (i / 8 + 1) (by omega) (by omega)]
                                  rw [hzv13, mul_comm]
                                · rw [if_neg hlt]
                                  have hl : i % 8 < 8 := by omega
                                  have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                                  have hmod : (i - 8) % 8 = i % 8 := by omega
                                  have hidx2 : i - 8 < 256 := by omega
                                  rw [Pure.build_getElem _ (i - 8) hidx2,
                                      Pure.build_getElem _ i hi,
                                      hmod]
                                  obtain ⟨_, hhigh⟩ := h13butter ((i - 8) / 8) (by omega) (by omega)
                                  have hhigh' := hhigh (i % 8) hl
                                  rw [h15unch (i / 8) (by omega) (by omega),
                                      h14unch (i / 8) (by omega) (by omega)]
                                  rw [hdiv, hhigh']
                                  rw [h12unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h11unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h12unch ((i - 8) / 8) (by omega) (by omega),
                                      h11unch ((i - 8) / 8) (by omega) (by omega),
                                      h10unch ((i - 8) / 8) (by omega) (by omega),
                                      h9unch ((i - 8) / 8) (by omega) (by omega),
                                      h8unch ((i - 8) / 8) (by omega) (by omega),
                                      h7unch ((i - 8) / 8) (by omega) (by omega),
                                      h6unch ((i - 8) / 8) (by omega) (by omega),
                                      h5unch ((i - 8) / 8) (by omega) (by omega),
                                      h4unch ((i - 8) / 8) (by omega) (by omega),
                                      h3unch ((i - 8) / 8) (by omega) (by omega),
                                      h2unch ((i - 8) / 8) (by omega) (by omega),
                                      h1unch ((i - 8) / 8) (by omega) (by omega),
                                      h0unch ((i - 8) / 8) (by omega) (by omega)]
                                  rw [hzv13, mul_comm]
                              · -- Rounds 14+.
                                by_cases hr14 : i < 240
                                · -- Round 14.
                                  have hround : i / 16 = 14 := by omega
                                  have hidx : i % 16 = i - 224 := by omega
                                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                                    hround, hidx, Nat.reduceAdd]
                                  by_cases hlt : i - 224 < 8
                                  · rw [if_pos hlt]
                                    have hl : i % 8 < 8 := by omega
                                    have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                                    have hmod : (i + 8) % 8 = i % 8 := by omega
                                    have hidx2 : i + 8 < 256 := by omega
                                    rw [Pure.build_getElem _ i hi,
                                        Pure.build_getElem _ (i + 8) hidx2,
                                        hdiv,
                                        hmod]
                                    obtain ⟨hlow, _⟩ := h14butter (i / 8) (by omega) (by omega)
                                    rw [h15unch (i / 8) (by omega) (by omega)]
                                    rw [hlow (i % 8) hl]
                                    rw [h13unch (i / 8) (by omega) (by omega),
                                        h12unch (i / 8) (by omega) (by omega),
                                        h11unch (i / 8) (by omega) (by omega),
                                        h10unch (i / 8) (by omega) (by omega),
                                        h9unch (i / 8) (by omega) (by omega),
                                        h8unch (i / 8) (by omega) (by omega),
                                        h7unch (i / 8) (by omega) (by omega),
                                        h6unch (i / 8) (by omega) (by omega),
                                        h5unch (i / 8) (by omega) (by omega),
                                        h4unch (i / 8) (by omega) (by omega),
                                        h3unch (i / 8) (by omega) (by omega),
                                        h2unch (i / 8) (by omega) (by omega),
                                        h1unch (i / 8) (by omega) (by omega),
                                        h0unch (i / 8) (by omega) (by omega),
                                        h13unch (i / 8 + 1) (by omega) (by omega),
                                        h12unch (i / 8 + 1) (by omega) (by omega),
                                        h11unch (i / 8 + 1) (by omega) (by omega),
                                        h10unch (i / 8 + 1) (by omega) (by omega),
                                        h9unch (i / 8 + 1) (by omega) (by omega),
                                        h8unch (i / 8 + 1) (by omega) (by omega),
                                        h7unch (i / 8 + 1) (by omega) (by omega),
                                        h6unch (i / 8 + 1) (by omega) (by omega),
                                        h5unch (i / 8 + 1) (by omega) (by omega),
                                        h4unch (i / 8 + 1) (by omega) (by omega),
                                        h3unch (i / 8 + 1) (by omega) (by omega),
                                        h2unch (i / 8 + 1) (by omega) (by omega),
                                        h1unch (i / 8 + 1) (by omega) (by omega),
                                        h0unch (i / 8 + 1) (by omega) (by omega)]
                                    rw [hzv14, mul_comm]
                                  · rw [if_neg hlt]
                                    have hl : i % 8 < 8 := by omega
                                    have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                                    have hmod : (i - 8) % 8 = i % 8 := by omega
                                    have hidx2 : i - 8 < 256 := by omega
                                    rw [Pure.build_getElem _ (i - 8) hidx2,
                                        Pure.build_getElem _ i hi,
                                        hmod]
                                    obtain ⟨_, hhigh⟩ :=
                                      h14butter ((i - 8) / 8) (by omega) (by omega)
                                    have hhigh' := hhigh (i % 8) hl
                                    rw [h15unch (i / 8) (by omega) (by omega)]
                                    rw [hdiv, hhigh']
                                    rw [h13unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h12unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h11unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h13unch ((i - 8) / 8) (by omega) (by omega),
                                        h12unch ((i - 8) / 8) (by omega) (by omega),
                                        h11unch ((i - 8) / 8) (by omega) (by omega),
                                        h10unch ((i - 8) / 8) (by omega) (by omega),
                                        h9unch ((i - 8) / 8) (by omega) (by omega),
                                        h8unch ((i - 8) / 8) (by omega) (by omega),
                                        h7unch ((i - 8) / 8) (by omega) (by omega),
                                        h6unch ((i - 8) / 8) (by omega) (by omega),
                                        h5unch ((i - 8) / 8) (by omega) (by omega),
                                        h4unch ((i - 8) / 8) (by omega) (by omega),
                                        h3unch ((i - 8) / 8) (by omega) (by omega),
                                        h2unch ((i - 8) / 8) (by omega) (by omega),
                                        h1unch ((i - 8) / 8) (by omega) (by omega),
                                        h0unch ((i - 8) / 8) (by omega) (by omega)]
                                    rw [hzv14, mul_comm]
                                · -- Rounds 15+.
                                  have hround : i / 16 = 15 := by omega
                                  have hidx : i % 16 = i - 240 := by omega
                                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                                    hround, hidx, Nat.reduceAdd]
                                  by_cases hlt : i - 240 < 8
                                  · rw [if_pos hlt]
                                    have hl : i % 8 < 8 := by omega
                                    have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                                    have hmod : (i + 8) % 8 = i % 8 := by omega
                                    have hidx2 : i + 8 < 256 := by omega
                                    rw [Pure.build_getElem _ i hi,
                                        Pure.build_getElem _ (i + 8) hidx2,
                                        hdiv,
                                        hmod]
                                    obtain ⟨hlow, _⟩ := h15butter (i / 8) (by omega) (by omega)
                                    rw [hlow (i % 8) hl]
                                    rw [h14unch (i / 8) (by omega) (by omega),
                                        h13unch (i / 8) (by omega) (by omega),
                                        h12unch (i / 8) (by omega) (by omega),
                                        h11unch (i / 8) (by omega) (by omega),
                                        h10unch (i / 8) (by omega) (by omega),
                                        h9unch (i / 8) (by omega) (by omega),
                                        h8unch (i / 8) (by omega) (by omega),
                                        h7unch (i / 8) (by omega) (by omega),
                                        h6unch (i / 8) (by omega) (by omega),
                                        h5unch (i / 8) (by omega) (by omega),
                                        h4unch (i / 8) (by omega) (by omega),
                                        h3unch (i / 8) (by omega) (by omega),
                                        h2unch (i / 8) (by omega) (by omega),
                                        h1unch (i / 8) (by omega) (by omega),
                                        h0unch (i / 8) (by omega) (by omega),
                                        h14unch (i / 8 + 1) (by omega) (by omega),
                                        h13unch (i / 8 + 1) (by omega) (by omega),
                                        h12unch (i / 8 + 1) (by omega) (by omega),
                                        h11unch (i / 8 + 1) (by omega) (by omega),
                                        h10unch (i / 8 + 1) (by omega) (by omega),
                                        h9unch (i / 8 + 1) (by omega) (by omega),
                                        h8unch (i / 8 + 1) (by omega) (by omega),
                                        h7unch (i / 8 + 1) (by omega) (by omega),
                                        h6unch (i / 8 + 1) (by omega) (by omega),
                                        h5unch (i / 8 + 1) (by omega) (by omega),
                                        h4unch (i / 8 + 1) (by omega) (by omega),
                                        h3unch (i / 8 + 1) (by omega) (by omega),
                                        h2unch (i / 8 + 1) (by omega) (by omega),
                                        h1unch (i / 8 + 1) (by omega) (by omega),
                                        h0unch (i / 8 + 1) (by omega) (by omega)]
                                    rw [hzv15, mul_comm]
                                  · rw [if_neg hlt]
                                    have hl : i % 8 < 8 := by omega
                                    have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                                    have hmod : (i - 8) % 8 = i % 8 := by omega
                                    have hidx2 : i - 8 < 256 := by omega
                                    rw [Pure.build_getElem _ (i - 8) hidx2,
                                        Pure.build_getElem _ i hi,
                                        hmod]
                                    obtain ⟨_, hhigh⟩ :=
                                      h15butter ((i - 8) / 8) (by omega) (by omega)
                                    have hhigh' := hhigh (i % 8) hl
                                    rw [hdiv, hhigh']
                                    rw [h14unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h13unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h12unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h11unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h14unch ((i - 8) / 8) (by omega) (by omega),
                                        h13unch ((i - 8) / 8) (by omega) (by omega),
                                        h12unch ((i - 8) / 8) (by omega) (by omega),
                                        h11unch ((i - 8) / 8) (by omega) (by omega),
                                        h10unch ((i - 8) / 8) (by omega) (by omega),
                                        h9unch ((i - 8) / 8) (by omega) (by omega),
                                        h8unch ((i - 8) / 8) (by omega) (by omega),
                                        h7unch ((i - 8) / 8) (by omega) (by omega),
                                        h6unch ((i - 8) / 8) (by omega) (by omega),
                                        h5unch ((i - 8) / 8) (by omega) (by omega),
                                        h4unch ((i - 8) / 8) (by omega) (by omega),
                                        h3unch ((i - 8) / 8) (by omega) (by omega),
                                        h2unch ((i - 8) / 8) (by omega) (by omega),
                                        h1unch ((i - 8) / 8) (by omega) (by omega),
                                        h0unch ((i - 8) / 8) (by omega) (by omega)]
                                    rw [hzv15, mul_comm]
  · -- Bound conjunct.
    have heq : B15 + 2 ^ 24 = B + 16 * 2 ^ 24 := by
      rw [← hB15def,
          ← hB14def,
          ← hB13def,
          ← hB12def,
          ← hB11def,
          ← hB10def,
          ← hB9def,
          ← hB8def,
          ← hB7def,
          ← hB6def,
          ← hB5def,
          ← hB4def,
          ← hB3def,
          ← hB2def,
          ← hB1def]
      ring
    intro u hu l hl
    have := h15bd u hu l hl
    rw [heq] at this
    exact this

end libcrux_iot_ml_dsa.Vector.Portable.NttDriver
