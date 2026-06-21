/-
  # `Vector/Portable/InvNttDriver.lean` — inverse-NTT within-unit L2 driver (ML-DSA)

  Inverse (Gentleman–Sande) analogue of the forward within-unit L2 keystone
  `NttDriver.ntt_at_layer_2_fc`. `invert_ntt_at_layer_2` chains 32 `round` calls;
  round `u` reads unit `u`, applies the per-unit inverse butterfly
  `simd_unit_invert_ntt_at_layer_2 _ Z_u`, and writes unit `u` back (touching ONLY
  unit `u`). The lifted result equals `Pure.intt_layer (lift_units re) 2`
  (`len = 4`, `k = 256/4 − 1 = 63`; per-unit lane split at lane 4, zeta index
  `63 − u`). Inputs `B`-bounded; precond `2·B ≤ 2^31 − 1`; uniform output bound
  `2·B + 2^24` (each round operates on a distinct unit; the frame keeps every other
  unit at its ORIGINAL `re` value, so the bound does NOT chain/grow).

  Inverse butterfly (leaf `simd_unit_invert_ntt_at_layer_2_fc`):
    lo lanes 0–3 : `liftZ out[l] = liftZ su[l] + liftZ su[l+4]`         (SUM, no zeta)
    hi lanes 4–7 : `liftZ out[l] = (liftZ su[l] − liftZ su[l−4]) · liftZ zeta`
  which equals the spec else-branch `(−zeta(63−u))·(p[i−4]−p[i])` once the zeta
  bridge `liftZ (LIT_u) = zeta (63 − u)` is applied (KERNEL `decide`, NOT
  `native_decide`; the inverse literals are the forward-L2 literals in reversed
  unit order).
-/
import LibcruxIotMlDsa.Vector.Portable.Ntt
import LibcruxIotMlDsa.Vector.Portable.InvNtt
import LibcruxIotMlDsa.Spec.Lift

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.InvNttDriver
open Aeneas Aeneas.Std Std.Do Result
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Vector.Portable.Ntt
open libcrux_iot_ml_dsa.Vector.Portable.InvNtt
open libcrux_iot_ml_dsa.Util.LoopHelper

/-- Reflect a `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` Triple into an `.ok` witness plus the post
    (file-scoped copy of the §13.5 helper). -/
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
private theorem zetaInv2_bridge0 :
    liftZ (((-2797779)#i32 : Std.I32).val : Int) = zeta (63 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge1 :
    liftZ ((2071892#i32 : Std.I32).val : Int) = zeta (63 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge2 :
    liftZ (((-2556880)#i32 : Std.I32).val : Int) = zeta (63 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge3 :
    liftZ ((3900724#i32 : Std.I32).val : Int) = zeta (63 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge4 :
    liftZ ((3881043#i32 : Std.I32).val : Int) = zeta (63 - 4) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge5 :
    liftZ ((954230#i32 : Std.I32).val : Int) = zeta (63 - 5) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge6 :
    liftZ ((531354#i32 : Std.I32).val : Int) = zeta (63 - 6) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge7 :
    liftZ ((811944#i32 : Std.I32).val : Int) = zeta (63 - 7) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge8 :
    liftZ ((3699596#i32 : Std.I32).val : Int) = zeta (63 - 8) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge9 :
    liftZ (((-1600420)#i32 : Std.I32).val : Int) = zeta (63 - 9) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge10 :
    liftZ (((-2140649)#i32 : Std.I32).val : Int) = zeta (63 - 10) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge11 :
    liftZ ((3507263#i32 : Std.I32).val : Int) = zeta (63 - 11) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge12 :
    liftZ (((-3821735)#i32 : Std.I32).val : Int) = zeta (63 - 12) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge13 :
    liftZ ((3505694#i32 : Std.I32).val : Int) = zeta (63 - 13) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge14 :
    liftZ (((-1643818)#i32 : Std.I32).val : Int) = zeta (63 - 14) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge15 :
    liftZ (((-1699267)#i32 : Std.I32).val : Int) = zeta (63 - 15) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge16 :
    liftZ (((-539299)#i32 : Std.I32).val : Int) = zeta (63 - 16) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge17 :
    liftZ ((2348700#i32 : Std.I32).val : Int) = zeta (63 - 17) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge18 :
    liftZ (((-300467)#i32 : Std.I32).val : Int) = zeta (63 - 18) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge19 :
    liftZ ((3539968#i32 : Std.I32).val : Int) = zeta (63 - 19) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge20 :
    liftZ (((-2867647)#i32 : Std.I32).val : Int) = zeta (63 - 20) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge21 :
    liftZ ((3574422#i32 : Std.I32).val : Int) = zeta (63 - 21) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge22 :
    liftZ (((-3043716)#i32 : Std.I32).val : Int) = zeta (63 - 22) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge23 :
    liftZ (((-3861115)#i32 : Std.I32).val : Int) = zeta (63 - 23) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge24 :
    liftZ ((3915439#i32 : Std.I32).val : Int) = zeta (63 - 24) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge25 :
    liftZ (((-2537516)#i32 : Std.I32).val : Int) = zeta (63 - 25) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge26 :
    liftZ (((-3592148)#i32 : Std.I32).val : Int) = zeta (63 - 26) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge27 :
    liftZ (((-1661693)#i32 : Std.I32).val : Int) = zeta (63 - 27) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge28 :
    liftZ ((3530437#i32 : Std.I32).val : Int) = zeta (63 - 28) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge29 :
    liftZ ((3077325#i32 : Std.I32).val : Int) = zeta (63 - 29) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge30 :
    liftZ ((95776#i32 : Std.I32).val : Int) = zeta (63 - 30) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv2_bridge31 :
    liftZ ((2706023#i32 : Std.I32).val : Int) = zeta (63 - 31) := by decide

private theorem zetaInv2_mag0 : ((-2797779)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag1 : (2071892#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag2 : ((-2556880)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag3 : (3900724#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag4 : (3881043#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag5 : (954230#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag6 : (531354#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag7 : (811944#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag8 : (3699596#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag9 : ((-1600420)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag10 : ((-2140649)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag11 : (3507263#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag12 : ((-3821735)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag13 : (3505694#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag14 : ((-1643818)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag15 : ((-1699267)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag16 : ((-539299)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag17 : (2348700#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag18 : ((-300467)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag19 : (3539968#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag20 : ((-2867647)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag21 : (3574422#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag22 : ((-3043716)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag23 : ((-3861115)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag24 : (3915439#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag25 : ((-2537516)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag26 : ((-3592148)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag27 : ((-1661693)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag28 : (3530437#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag29 : (3077325#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag30 : (95776#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv2_mag31 : (2706023#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

/-- One `round` of inverse layer 2: read unit `k`, apply the per-unit inverse
    (Gentleman–Sande) butterfly with `zeta`, write unit `k` back (touching only
    unit `k`). Gives the 8 per-lane lift equations on the new unit `k` (lo lanes
    a SUM with no zeta, hi lanes `(su[hi]−su[lo])·zeta`), the frame
    `out[u] = re[u]` for `u ≠ k`, and the per-lane bound `≤ 2*B + 2^24` on unit
    `k`. Faithful clone of `NttDriver.round2_fc` with the inverse leaf + post. -/
private theorem roundInv2_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (k : Nat) (hk : k < 32) (zeta : Std.I32) (B : Nat)
    (hz : zeta.val.natAbs ≤ 8380416)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1)
    (hin : ∀ l : Nat, l < 8 → ((re.val[k]!).values.val[l]!).val.natAbs ≤ B) :
    ∃ out, libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_2.round re k#usize zeta = .ok out
      ∧ (liftZ ((out.val[k]!).values.val[0]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val + liftZ ((re.val[k]!).values.val[4]!).val
        ∧ liftZ ((out.val[k]!).values.val[1]!).val
            = liftZ ((re.val[k]!).values.val[1]!).val + liftZ ((re.val[k]!).values.val[5]!).val
        ∧ liftZ ((out.val[k]!).values.val[2]!).val
            = liftZ ((re.val[k]!).values.val[2]!).val + liftZ ((re.val[k]!).values.val[6]!).val
        ∧ liftZ ((out.val[k]!).values.val[3]!).val
            = liftZ ((re.val[k]!).values.val[3]!).val + liftZ ((re.val[k]!).values.val[7]!).val
        ∧ liftZ ((out.val[k]!).values.val[4]!).val
            = (liftZ ((re.val[k]!).values.val[4]!).val - liftZ ((re.val[k]!).values.val[0]!).val) * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[5]!).val
            = (liftZ ((re.val[k]!).values.val[5]!).val - liftZ ((re.val[k]!).values.val[1]!).val) * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[6]!).val
            = (liftZ ((re.val[k]!).values.val[6]!).val - liftZ ((re.val[k]!).values.val[2]!).val) * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[7]!).val
            = (liftZ ((re.val[k]!).values.val[7]!).val - liftZ ((re.val[k]!).values.val[3]!).val) * liftZ zeta.val)
      ∧ (∀ u : Nat, u < 32 → u ≠ k → out.val[u]! = re.val[u]!)
      ∧ (∀ l : Nat, l < 8 → ((out.val[k]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24) := by
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_2.round
  have hre_len : re.length = 32 := Std.Array.length_eq _
  have hk_len : (k#usize : Std.Usize).val < re.length := by
    rw [hre_len]; simpa using hk
  have h_idx : Array.index_usize re k#usize = .ok (re.val[k]!) :=
    array_index_usize_ok_eq re k#usize hk_len
  set ak : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    re.val[k]! with hak
  have h_imt : Array.index_mut_usize re k#usize = .ok (ak, re.set k#usize) := by
    unfold Aeneas.Std.Array.index_mut_usize; rw [h_idx]; rfl
  obtain ⟨c1, hc1_eq, hc1_butter, hc1_bd⟩ :=
    triple_exists_ok (simd_unit_invert_ntt_at_layer_2_fc ak zeta B hz hB hin)
  have hset_k : (re.set k#usize c1).val[k]! = c1 := by
    rw [← Std.Array.getElem!_Nat_eq]
    exact Std.Array.getElem!_Nat_set_eq re k#usize k c1 ⟨rfl, by rw [hre_len]; exact hk⟩
  refine ⟨re.set k#usize c1, ?_, ?_, ?_, ?_⟩
  · simp [Aeneas.Std.bind_tc_ok, h_imt, hc1_eq]
  · rw [hset_k]; exact hc1_butter
  · intro u hu hne
    rw [← Std.Array.getElem!_Nat_eq, ← Std.Array.getElem!_Nat_eq (v := re)]
    exact Std.Array.getElem!_Nat_set_ne re k#usize u c1 (fun h => hne h.symm)
  · intro l hl
    rw [hset_k]; exact hc1_bd l hl


set_option maxHeartbeats 16000000 in
@[spec]
theorem invert_ntt_at_layer_2_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_2 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.intt_layer (lift_units re) 2
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ 2 * B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_2
  have hkeep0 : ∀ u, 0 ≤ u → u < 32 → re.val[u]! = re.val[u]! := fun u _ _ => rfl
  obtain ⟨r1, hr1_eq, hbut0, hfr0, hbd0⟩ :=
    roundInv2_fc re 0 (by decide) ((-2797779)#i32) B (zetaInv2_mag0) hB
      (fun l hl => by rw [hkeep0 0 (by omega) (by omega)]; exact hin 0 (by decide) l hl)
  have hkeep1 : ∀ u, 1 ≤ u → u < 32 → r1.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr0 u hu2 (by omega), hkeep0 u (by omega) hu2]
  obtain ⟨r2, hr2_eq, hbut1, hfr1, hbd1⟩ :=
    roundInv2_fc r1 1 (by decide) (2071892#i32) B (zetaInv2_mag1) hB
      (fun l hl => by rw [hkeep1 1 (by omega) (by omega)]; exact hin 1 (by decide) l hl)
  have hkeep2 : ∀ u, 2 ≤ u → u < 32 → r2.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr1 u hu2 (by omega), hkeep1 u (by omega) hu2]
  obtain ⟨r3, hr3_eq, hbut2, hfr2, hbd2⟩ :=
    roundInv2_fc r2 2 (by decide) ((-2556880)#i32) B (zetaInv2_mag2) hB
      (fun l hl => by rw [hkeep2 2 (by omega) (by omega)]; exact hin 2 (by decide) l hl)
  have hkeep3 : ∀ u, 3 ≤ u → u < 32 → r3.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr2 u hu2 (by omega), hkeep2 u (by omega) hu2]
  obtain ⟨r4, hr4_eq, hbut3, hfr3, hbd3⟩ :=
    roundInv2_fc r3 3 (by decide) (3900724#i32) B (zetaInv2_mag3) hB
      (fun l hl => by rw [hkeep3 3 (by omega) (by omega)]; exact hin 3 (by decide) l hl)
  have hkeep4 : ∀ u, 4 ≤ u → u < 32 → r4.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr3 u hu2 (by omega), hkeep3 u (by omega) hu2]
  obtain ⟨r5, hr5_eq, hbut4, hfr4, hbd4⟩ :=
    roundInv2_fc r4 4 (by decide) (3881043#i32) B (zetaInv2_mag4) hB
      (fun l hl => by rw [hkeep4 4 (by omega) (by omega)]; exact hin 4 (by decide) l hl)
  have hkeep5 : ∀ u, 5 ≤ u → u < 32 → r5.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr4 u hu2 (by omega), hkeep4 u (by omega) hu2]
  obtain ⟨r6, hr6_eq, hbut5, hfr5, hbd5⟩ :=
    roundInv2_fc r5 5 (by decide) (954230#i32) B (zetaInv2_mag5) hB
      (fun l hl => by rw [hkeep5 5 (by omega) (by omega)]; exact hin 5 (by decide) l hl)
  have hkeep6 : ∀ u, 6 ≤ u → u < 32 → r6.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr5 u hu2 (by omega), hkeep5 u (by omega) hu2]
  obtain ⟨r7, hr7_eq, hbut6, hfr6, hbd6⟩ :=
    roundInv2_fc r6 6 (by decide) (531354#i32) B (zetaInv2_mag6) hB
      (fun l hl => by rw [hkeep6 6 (by omega) (by omega)]; exact hin 6 (by decide) l hl)
  have hkeep7 : ∀ u, 7 ≤ u → u < 32 → r7.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr6 u hu2 (by omega), hkeep6 u (by omega) hu2]
  obtain ⟨r8, hr8_eq, hbut7, hfr7, hbd7⟩ :=
    roundInv2_fc r7 7 (by decide) (811944#i32) B (zetaInv2_mag7) hB
      (fun l hl => by rw [hkeep7 7 (by omega) (by omega)]; exact hin 7 (by decide) l hl)
  have hkeep8 : ∀ u, 8 ≤ u → u < 32 → r8.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr7 u hu2 (by omega), hkeep7 u (by omega) hu2]
  obtain ⟨r9, hr9_eq, hbut8, hfr8, hbd8⟩ :=
    roundInv2_fc r8 8 (by decide) (3699596#i32) B (zetaInv2_mag8) hB
      (fun l hl => by rw [hkeep8 8 (by omega) (by omega)]; exact hin 8 (by decide) l hl)
  have hkeep9 : ∀ u, 9 ≤ u → u < 32 → r9.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr8 u hu2 (by omega), hkeep8 u (by omega) hu2]
  obtain ⟨r10, hr10_eq, hbut9, hfr9, hbd9⟩ :=
    roundInv2_fc r9 9 (by decide) ((-1600420)#i32) B (zetaInv2_mag9) hB
      (fun l hl => by rw [hkeep9 9 (by omega) (by omega)]; exact hin 9 (by decide) l hl)
  have hkeep10 : ∀ u, 10 ≤ u → u < 32 → r10.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr9 u hu2 (by omega), hkeep9 u (by omega) hu2]
  obtain ⟨r11, hr11_eq, hbut10, hfr10, hbd10⟩ :=
    roundInv2_fc r10 10 (by decide) ((-2140649)#i32) B (zetaInv2_mag10) hB
      (fun l hl => by rw [hkeep10 10 (by omega) (by omega)]; exact hin 10 (by decide) l hl)
  have hkeep11 : ∀ u, 11 ≤ u → u < 32 → r11.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr10 u hu2 (by omega), hkeep10 u (by omega) hu2]
  obtain ⟨r12, hr12_eq, hbut11, hfr11, hbd11⟩ :=
    roundInv2_fc r11 11 (by decide) (3507263#i32) B (zetaInv2_mag11) hB
      (fun l hl => by rw [hkeep11 11 (by omega) (by omega)]; exact hin 11 (by decide) l hl)
  have hkeep12 : ∀ u, 12 ≤ u → u < 32 → r12.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr11 u hu2 (by omega), hkeep11 u (by omega) hu2]
  obtain ⟨r13, hr13_eq, hbut12, hfr12, hbd12⟩ :=
    roundInv2_fc r12 12 (by decide) ((-3821735)#i32) B (zetaInv2_mag12) hB
      (fun l hl => by rw [hkeep12 12 (by omega) (by omega)]; exact hin 12 (by decide) l hl)
  have hkeep13 : ∀ u, 13 ≤ u → u < 32 → r13.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr12 u hu2 (by omega), hkeep12 u (by omega) hu2]
  obtain ⟨r14, hr14_eq, hbut13, hfr13, hbd13⟩ :=
    roundInv2_fc r13 13 (by decide) (3505694#i32) B (zetaInv2_mag13) hB
      (fun l hl => by rw [hkeep13 13 (by omega) (by omega)]; exact hin 13 (by decide) l hl)
  have hkeep14 : ∀ u, 14 ≤ u → u < 32 → r14.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr13 u hu2 (by omega), hkeep13 u (by omega) hu2]
  obtain ⟨r15, hr15_eq, hbut14, hfr14, hbd14⟩ :=
    roundInv2_fc r14 14 (by decide) ((-1643818)#i32) B (zetaInv2_mag14) hB
      (fun l hl => by rw [hkeep14 14 (by omega) (by omega)]; exact hin 14 (by decide) l hl)
  have hkeep15 : ∀ u, 15 ≤ u → u < 32 → r15.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr14 u hu2 (by omega), hkeep14 u (by omega) hu2]
  obtain ⟨r16, hr16_eq, hbut15, hfr15, hbd15⟩ :=
    roundInv2_fc r15 15 (by decide) ((-1699267)#i32) B (zetaInv2_mag15) hB
      (fun l hl => by rw [hkeep15 15 (by omega) (by omega)]; exact hin 15 (by decide) l hl)
  have hkeep16 : ∀ u, 16 ≤ u → u < 32 → r16.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr15 u hu2 (by omega), hkeep15 u (by omega) hu2]
  obtain ⟨r17, hr17_eq, hbut16, hfr16, hbd16⟩ :=
    roundInv2_fc r16 16 (by decide) ((-539299)#i32) B (zetaInv2_mag16) hB
      (fun l hl => by rw [hkeep16 16 (by omega) (by omega)]; exact hin 16 (by decide) l hl)
  have hkeep17 : ∀ u, 17 ≤ u → u < 32 → r17.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr16 u hu2 (by omega), hkeep16 u (by omega) hu2]
  obtain ⟨r18, hr18_eq, hbut17, hfr17, hbd17⟩ :=
    roundInv2_fc r17 17 (by decide) (2348700#i32) B (zetaInv2_mag17) hB
      (fun l hl => by rw [hkeep17 17 (by omega) (by omega)]; exact hin 17 (by decide) l hl)
  have hkeep18 : ∀ u, 18 ≤ u → u < 32 → r18.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr17 u hu2 (by omega), hkeep17 u (by omega) hu2]
  obtain ⟨r19, hr19_eq, hbut18, hfr18, hbd18⟩ :=
    roundInv2_fc r18 18 (by decide) ((-300467)#i32) B (zetaInv2_mag18) hB
      (fun l hl => by rw [hkeep18 18 (by omega) (by omega)]; exact hin 18 (by decide) l hl)
  have hkeep19 : ∀ u, 19 ≤ u → u < 32 → r19.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr18 u hu2 (by omega), hkeep18 u (by omega) hu2]
  obtain ⟨r20, hr20_eq, hbut19, hfr19, hbd19⟩ :=
    roundInv2_fc r19 19 (by decide) (3539968#i32) B (zetaInv2_mag19) hB
      (fun l hl => by rw [hkeep19 19 (by omega) (by omega)]; exact hin 19 (by decide) l hl)
  have hkeep20 : ∀ u, 20 ≤ u → u < 32 → r20.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr19 u hu2 (by omega), hkeep19 u (by omega) hu2]
  obtain ⟨r21, hr21_eq, hbut20, hfr20, hbd20⟩ :=
    roundInv2_fc r20 20 (by decide) ((-2867647)#i32) B (zetaInv2_mag20) hB
      (fun l hl => by rw [hkeep20 20 (by omega) (by omega)]; exact hin 20 (by decide) l hl)
  have hkeep21 : ∀ u, 21 ≤ u → u < 32 → r21.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr20 u hu2 (by omega), hkeep20 u (by omega) hu2]
  obtain ⟨r22, hr22_eq, hbut21, hfr21, hbd21⟩ :=
    roundInv2_fc r21 21 (by decide) (3574422#i32) B (zetaInv2_mag21) hB
      (fun l hl => by rw [hkeep21 21 (by omega) (by omega)]; exact hin 21 (by decide) l hl)
  have hkeep22 : ∀ u, 22 ≤ u → u < 32 → r22.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr21 u hu2 (by omega), hkeep21 u (by omega) hu2]
  obtain ⟨r23, hr23_eq, hbut22, hfr22, hbd22⟩ :=
    roundInv2_fc r22 22 (by decide) ((-3043716)#i32) B (zetaInv2_mag22) hB
      (fun l hl => by rw [hkeep22 22 (by omega) (by omega)]; exact hin 22 (by decide) l hl)
  have hkeep23 : ∀ u, 23 ≤ u → u < 32 → r23.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr22 u hu2 (by omega), hkeep22 u (by omega) hu2]
  obtain ⟨r24, hr24_eq, hbut23, hfr23, hbd23⟩ :=
    roundInv2_fc r23 23 (by decide) ((-3861115)#i32) B (zetaInv2_mag23) hB
      (fun l hl => by rw [hkeep23 23 (by omega) (by omega)]; exact hin 23 (by decide) l hl)
  have hkeep24 : ∀ u, 24 ≤ u → u < 32 → r24.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr23 u hu2 (by omega), hkeep23 u (by omega) hu2]
  obtain ⟨r25, hr25_eq, hbut24, hfr24, hbd24⟩ :=
    roundInv2_fc r24 24 (by decide) (3915439#i32) B (zetaInv2_mag24) hB
      (fun l hl => by rw [hkeep24 24 (by omega) (by omega)]; exact hin 24 (by decide) l hl)
  have hkeep25 : ∀ u, 25 ≤ u → u < 32 → r25.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr24 u hu2 (by omega), hkeep24 u (by omega) hu2]
  obtain ⟨r26, hr26_eq, hbut25, hfr25, hbd25⟩ :=
    roundInv2_fc r25 25 (by decide) ((-2537516)#i32) B (zetaInv2_mag25) hB
      (fun l hl => by rw [hkeep25 25 (by omega) (by omega)]; exact hin 25 (by decide) l hl)
  have hkeep26 : ∀ u, 26 ≤ u → u < 32 → r26.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr25 u hu2 (by omega), hkeep25 u (by omega) hu2]
  obtain ⟨r27, hr27_eq, hbut26, hfr26, hbd26⟩ :=
    roundInv2_fc r26 26 (by decide) ((-3592148)#i32) B (zetaInv2_mag26) hB
      (fun l hl => by rw [hkeep26 26 (by omega) (by omega)]; exact hin 26 (by decide) l hl)
  have hkeep27 : ∀ u, 27 ≤ u → u < 32 → r27.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr26 u hu2 (by omega), hkeep26 u (by omega) hu2]
  obtain ⟨r28, hr28_eq, hbut27, hfr27, hbd27⟩ :=
    roundInv2_fc r27 27 (by decide) ((-1661693)#i32) B (zetaInv2_mag27) hB
      (fun l hl => by rw [hkeep27 27 (by omega) (by omega)]; exact hin 27 (by decide) l hl)
  have hkeep28 : ∀ u, 28 ≤ u → u < 32 → r28.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr27 u hu2 (by omega), hkeep27 u (by omega) hu2]
  obtain ⟨r29, hr29_eq, hbut28, hfr28, hbd28⟩ :=
    roundInv2_fc r28 28 (by decide) (3530437#i32) B (zetaInv2_mag28) hB
      (fun l hl => by rw [hkeep28 28 (by omega) (by omega)]; exact hin 28 (by decide) l hl)
  have hkeep29 : ∀ u, 29 ≤ u → u < 32 → r29.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr28 u hu2 (by omega), hkeep28 u (by omega) hu2]
  obtain ⟨r30, hr30_eq, hbut29, hfr29, hbd29⟩ :=
    roundInv2_fc r29 29 (by decide) (3077325#i32) B (zetaInv2_mag29) hB
      (fun l hl => by rw [hkeep29 29 (by omega) (by omega)]; exact hin 29 (by decide) l hl)
  have hkeep30 : ∀ u, 30 ≤ u → u < 32 → r30.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr29 u hu2 (by omega), hkeep29 u (by omega) hu2]
  obtain ⟨r31, hr31_eq, hbut30, hfr30, hbd30⟩ :=
    roundInv2_fc r30 30 (by decide) (95776#i32) B (zetaInv2_mag30) hB
      (fun l hl => by rw [hkeep30 30 (by omega) (by omega)]; exact hin 30 (by decide) l hl)
  have hkeep31 : ∀ u, 31 ≤ u → u < 32 → r31.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr30 u hu2 (by omega), hkeep30 u (by omega) hu2]
  obtain ⟨r32, hr32_eq, hbut31, hfr31, hbd31⟩ :=
    roundInv2_fc r31 31 (by decide) (2706023#i32) B (zetaInv2_mag31) hB
      (fun l hl => by rw [hkeep31 31 (by omega) (by omega)]; exact hin 31 (by decide) l hl)
  have hkeep32 : ∀ u, 32 ≤ u → u < 32 → r32.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr31 u hu2 (by omega), hkeep31 u (by omega) hu2]
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
  rw [hr16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr17_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr18_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr19_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr20_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr21_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr22_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr23_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr24_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr25_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr26_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr27_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr28_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr29_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr30_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr31_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr32_eq
  have hr32u0 : r32.val[0]! = r1.val[0]! := by
    rw [hfr31 0 (by decide) (by decide), hfr30 0 (by decide) (by decide), hfr29 0 (by decide) (by decide), hfr28 0 (by decide) (by decide), hfr27 0 (by decide) (by decide), hfr26 0 (by decide) (by decide), hfr25 0 (by decide) (by decide), hfr24 0 (by decide) (by decide), hfr23 0 (by decide) (by decide), hfr22 0 (by decide) (by decide), hfr21 0 (by decide) (by decide), hfr20 0 (by decide) (by decide), hfr19 0 (by decide) (by decide), hfr18 0 (by decide) (by decide), hfr17 0 (by decide) (by decide), hfr16 0 (by decide) (by decide), hfr15 0 (by decide) (by decide), hfr14 0 (by decide) (by decide), hfr13 0 (by decide) (by decide), hfr12 0 (by decide) (by decide), hfr11 0 (by decide) (by decide), hfr10 0 (by decide) (by decide), hfr9 0 (by decide) (by decide), hfr8 0 (by decide) (by decide), hfr7 0 (by decide) (by decide), hfr6 0 (by decide) (by decide), hfr5 0 (by decide) (by decide), hfr4 0 (by decide) (by decide), hfr3 0 (by decide) (by decide), hfr2 0 (by decide) (by decide), hfr1 0 (by decide) (by decide)]
  have hr32u1 : r32.val[1]! = r2.val[1]! := by
    rw [hfr31 1 (by decide) (by decide), hfr30 1 (by decide) (by decide), hfr29 1 (by decide) (by decide), hfr28 1 (by decide) (by decide), hfr27 1 (by decide) (by decide), hfr26 1 (by decide) (by decide), hfr25 1 (by decide) (by decide), hfr24 1 (by decide) (by decide), hfr23 1 (by decide) (by decide), hfr22 1 (by decide) (by decide), hfr21 1 (by decide) (by decide), hfr20 1 (by decide) (by decide), hfr19 1 (by decide) (by decide), hfr18 1 (by decide) (by decide), hfr17 1 (by decide) (by decide), hfr16 1 (by decide) (by decide), hfr15 1 (by decide) (by decide), hfr14 1 (by decide) (by decide), hfr13 1 (by decide) (by decide), hfr12 1 (by decide) (by decide), hfr11 1 (by decide) (by decide), hfr10 1 (by decide) (by decide), hfr9 1 (by decide) (by decide), hfr8 1 (by decide) (by decide), hfr7 1 (by decide) (by decide), hfr6 1 (by decide) (by decide), hfr5 1 (by decide) (by decide), hfr4 1 (by decide) (by decide), hfr3 1 (by decide) (by decide), hfr2 1 (by decide) (by decide)]
  rw [hkeep1 1 (by decide) (by decide)] at hbut1
  have hr32u2 : r32.val[2]! = r3.val[2]! := by
    rw [hfr31 2 (by decide) (by decide), hfr30 2 (by decide) (by decide), hfr29 2 (by decide) (by decide), hfr28 2 (by decide) (by decide), hfr27 2 (by decide) (by decide), hfr26 2 (by decide) (by decide), hfr25 2 (by decide) (by decide), hfr24 2 (by decide) (by decide), hfr23 2 (by decide) (by decide), hfr22 2 (by decide) (by decide), hfr21 2 (by decide) (by decide), hfr20 2 (by decide) (by decide), hfr19 2 (by decide) (by decide), hfr18 2 (by decide) (by decide), hfr17 2 (by decide) (by decide), hfr16 2 (by decide) (by decide), hfr15 2 (by decide) (by decide), hfr14 2 (by decide) (by decide), hfr13 2 (by decide) (by decide), hfr12 2 (by decide) (by decide), hfr11 2 (by decide) (by decide), hfr10 2 (by decide) (by decide), hfr9 2 (by decide) (by decide), hfr8 2 (by decide) (by decide), hfr7 2 (by decide) (by decide), hfr6 2 (by decide) (by decide), hfr5 2 (by decide) (by decide), hfr4 2 (by decide) (by decide), hfr3 2 (by decide) (by decide)]
  rw [hkeep2 2 (by decide) (by decide)] at hbut2
  have hr32u3 : r32.val[3]! = r4.val[3]! := by
    rw [hfr31 3 (by decide) (by decide), hfr30 3 (by decide) (by decide), hfr29 3 (by decide) (by decide), hfr28 3 (by decide) (by decide), hfr27 3 (by decide) (by decide), hfr26 3 (by decide) (by decide), hfr25 3 (by decide) (by decide), hfr24 3 (by decide) (by decide), hfr23 3 (by decide) (by decide), hfr22 3 (by decide) (by decide), hfr21 3 (by decide) (by decide), hfr20 3 (by decide) (by decide), hfr19 3 (by decide) (by decide), hfr18 3 (by decide) (by decide), hfr17 3 (by decide) (by decide), hfr16 3 (by decide) (by decide), hfr15 3 (by decide) (by decide), hfr14 3 (by decide) (by decide), hfr13 3 (by decide) (by decide), hfr12 3 (by decide) (by decide), hfr11 3 (by decide) (by decide), hfr10 3 (by decide) (by decide), hfr9 3 (by decide) (by decide), hfr8 3 (by decide) (by decide), hfr7 3 (by decide) (by decide), hfr6 3 (by decide) (by decide), hfr5 3 (by decide) (by decide), hfr4 3 (by decide) (by decide)]
  rw [hkeep3 3 (by decide) (by decide)] at hbut3
  have hr32u4 : r32.val[4]! = r5.val[4]! := by
    rw [hfr31 4 (by decide) (by decide), hfr30 4 (by decide) (by decide), hfr29 4 (by decide) (by decide), hfr28 4 (by decide) (by decide), hfr27 4 (by decide) (by decide), hfr26 4 (by decide) (by decide), hfr25 4 (by decide) (by decide), hfr24 4 (by decide) (by decide), hfr23 4 (by decide) (by decide), hfr22 4 (by decide) (by decide), hfr21 4 (by decide) (by decide), hfr20 4 (by decide) (by decide), hfr19 4 (by decide) (by decide), hfr18 4 (by decide) (by decide), hfr17 4 (by decide) (by decide), hfr16 4 (by decide) (by decide), hfr15 4 (by decide) (by decide), hfr14 4 (by decide) (by decide), hfr13 4 (by decide) (by decide), hfr12 4 (by decide) (by decide), hfr11 4 (by decide) (by decide), hfr10 4 (by decide) (by decide), hfr9 4 (by decide) (by decide), hfr8 4 (by decide) (by decide), hfr7 4 (by decide) (by decide), hfr6 4 (by decide) (by decide), hfr5 4 (by decide) (by decide)]
  rw [hkeep4 4 (by decide) (by decide)] at hbut4
  have hr32u5 : r32.val[5]! = r6.val[5]! := by
    rw [hfr31 5 (by decide) (by decide), hfr30 5 (by decide) (by decide), hfr29 5 (by decide) (by decide), hfr28 5 (by decide) (by decide), hfr27 5 (by decide) (by decide), hfr26 5 (by decide) (by decide), hfr25 5 (by decide) (by decide), hfr24 5 (by decide) (by decide), hfr23 5 (by decide) (by decide), hfr22 5 (by decide) (by decide), hfr21 5 (by decide) (by decide), hfr20 5 (by decide) (by decide), hfr19 5 (by decide) (by decide), hfr18 5 (by decide) (by decide), hfr17 5 (by decide) (by decide), hfr16 5 (by decide) (by decide), hfr15 5 (by decide) (by decide), hfr14 5 (by decide) (by decide), hfr13 5 (by decide) (by decide), hfr12 5 (by decide) (by decide), hfr11 5 (by decide) (by decide), hfr10 5 (by decide) (by decide), hfr9 5 (by decide) (by decide), hfr8 5 (by decide) (by decide), hfr7 5 (by decide) (by decide), hfr6 5 (by decide) (by decide)]
  rw [hkeep5 5 (by decide) (by decide)] at hbut5
  have hr32u6 : r32.val[6]! = r7.val[6]! := by
    rw [hfr31 6 (by decide) (by decide), hfr30 6 (by decide) (by decide), hfr29 6 (by decide) (by decide), hfr28 6 (by decide) (by decide), hfr27 6 (by decide) (by decide), hfr26 6 (by decide) (by decide), hfr25 6 (by decide) (by decide), hfr24 6 (by decide) (by decide), hfr23 6 (by decide) (by decide), hfr22 6 (by decide) (by decide), hfr21 6 (by decide) (by decide), hfr20 6 (by decide) (by decide), hfr19 6 (by decide) (by decide), hfr18 6 (by decide) (by decide), hfr17 6 (by decide) (by decide), hfr16 6 (by decide) (by decide), hfr15 6 (by decide) (by decide), hfr14 6 (by decide) (by decide), hfr13 6 (by decide) (by decide), hfr12 6 (by decide) (by decide), hfr11 6 (by decide) (by decide), hfr10 6 (by decide) (by decide), hfr9 6 (by decide) (by decide), hfr8 6 (by decide) (by decide), hfr7 6 (by decide) (by decide)]
  rw [hkeep6 6 (by decide) (by decide)] at hbut6
  have hr32u7 : r32.val[7]! = r8.val[7]! := by
    rw [hfr31 7 (by decide) (by decide), hfr30 7 (by decide) (by decide), hfr29 7 (by decide) (by decide), hfr28 7 (by decide) (by decide), hfr27 7 (by decide) (by decide), hfr26 7 (by decide) (by decide), hfr25 7 (by decide) (by decide), hfr24 7 (by decide) (by decide), hfr23 7 (by decide) (by decide), hfr22 7 (by decide) (by decide), hfr21 7 (by decide) (by decide), hfr20 7 (by decide) (by decide), hfr19 7 (by decide) (by decide), hfr18 7 (by decide) (by decide), hfr17 7 (by decide) (by decide), hfr16 7 (by decide) (by decide), hfr15 7 (by decide) (by decide), hfr14 7 (by decide) (by decide), hfr13 7 (by decide) (by decide), hfr12 7 (by decide) (by decide), hfr11 7 (by decide) (by decide), hfr10 7 (by decide) (by decide), hfr9 7 (by decide) (by decide), hfr8 7 (by decide) (by decide)]
  rw [hkeep7 7 (by decide) (by decide)] at hbut7
  have hr32u8 : r32.val[8]! = r9.val[8]! := by
    rw [hfr31 8 (by decide) (by decide), hfr30 8 (by decide) (by decide), hfr29 8 (by decide) (by decide), hfr28 8 (by decide) (by decide), hfr27 8 (by decide) (by decide), hfr26 8 (by decide) (by decide), hfr25 8 (by decide) (by decide), hfr24 8 (by decide) (by decide), hfr23 8 (by decide) (by decide), hfr22 8 (by decide) (by decide), hfr21 8 (by decide) (by decide), hfr20 8 (by decide) (by decide), hfr19 8 (by decide) (by decide), hfr18 8 (by decide) (by decide), hfr17 8 (by decide) (by decide), hfr16 8 (by decide) (by decide), hfr15 8 (by decide) (by decide), hfr14 8 (by decide) (by decide), hfr13 8 (by decide) (by decide), hfr12 8 (by decide) (by decide), hfr11 8 (by decide) (by decide), hfr10 8 (by decide) (by decide), hfr9 8 (by decide) (by decide)]
  rw [hkeep8 8 (by decide) (by decide)] at hbut8
  have hr32u9 : r32.val[9]! = r10.val[9]! := by
    rw [hfr31 9 (by decide) (by decide), hfr30 9 (by decide) (by decide), hfr29 9 (by decide) (by decide), hfr28 9 (by decide) (by decide), hfr27 9 (by decide) (by decide), hfr26 9 (by decide) (by decide), hfr25 9 (by decide) (by decide), hfr24 9 (by decide) (by decide), hfr23 9 (by decide) (by decide), hfr22 9 (by decide) (by decide), hfr21 9 (by decide) (by decide), hfr20 9 (by decide) (by decide), hfr19 9 (by decide) (by decide), hfr18 9 (by decide) (by decide), hfr17 9 (by decide) (by decide), hfr16 9 (by decide) (by decide), hfr15 9 (by decide) (by decide), hfr14 9 (by decide) (by decide), hfr13 9 (by decide) (by decide), hfr12 9 (by decide) (by decide), hfr11 9 (by decide) (by decide), hfr10 9 (by decide) (by decide)]
  rw [hkeep9 9 (by decide) (by decide)] at hbut9
  have hr32u10 : r32.val[10]! = r11.val[10]! := by
    rw [hfr31 10 (by decide) (by decide), hfr30 10 (by decide) (by decide), hfr29 10 (by decide) (by decide), hfr28 10 (by decide) (by decide), hfr27 10 (by decide) (by decide), hfr26 10 (by decide) (by decide), hfr25 10 (by decide) (by decide), hfr24 10 (by decide) (by decide), hfr23 10 (by decide) (by decide), hfr22 10 (by decide) (by decide), hfr21 10 (by decide) (by decide), hfr20 10 (by decide) (by decide), hfr19 10 (by decide) (by decide), hfr18 10 (by decide) (by decide), hfr17 10 (by decide) (by decide), hfr16 10 (by decide) (by decide), hfr15 10 (by decide) (by decide), hfr14 10 (by decide) (by decide), hfr13 10 (by decide) (by decide), hfr12 10 (by decide) (by decide), hfr11 10 (by decide) (by decide)]
  rw [hkeep10 10 (by decide) (by decide)] at hbut10
  have hr32u11 : r32.val[11]! = r12.val[11]! := by
    rw [hfr31 11 (by decide) (by decide), hfr30 11 (by decide) (by decide), hfr29 11 (by decide) (by decide), hfr28 11 (by decide) (by decide), hfr27 11 (by decide) (by decide), hfr26 11 (by decide) (by decide), hfr25 11 (by decide) (by decide), hfr24 11 (by decide) (by decide), hfr23 11 (by decide) (by decide), hfr22 11 (by decide) (by decide), hfr21 11 (by decide) (by decide), hfr20 11 (by decide) (by decide), hfr19 11 (by decide) (by decide), hfr18 11 (by decide) (by decide), hfr17 11 (by decide) (by decide), hfr16 11 (by decide) (by decide), hfr15 11 (by decide) (by decide), hfr14 11 (by decide) (by decide), hfr13 11 (by decide) (by decide), hfr12 11 (by decide) (by decide)]
  rw [hkeep11 11 (by decide) (by decide)] at hbut11
  have hr32u12 : r32.val[12]! = r13.val[12]! := by
    rw [hfr31 12 (by decide) (by decide), hfr30 12 (by decide) (by decide), hfr29 12 (by decide) (by decide), hfr28 12 (by decide) (by decide), hfr27 12 (by decide) (by decide), hfr26 12 (by decide) (by decide), hfr25 12 (by decide) (by decide), hfr24 12 (by decide) (by decide), hfr23 12 (by decide) (by decide), hfr22 12 (by decide) (by decide), hfr21 12 (by decide) (by decide), hfr20 12 (by decide) (by decide), hfr19 12 (by decide) (by decide), hfr18 12 (by decide) (by decide), hfr17 12 (by decide) (by decide), hfr16 12 (by decide) (by decide), hfr15 12 (by decide) (by decide), hfr14 12 (by decide) (by decide), hfr13 12 (by decide) (by decide)]
  rw [hkeep12 12 (by decide) (by decide)] at hbut12
  have hr32u13 : r32.val[13]! = r14.val[13]! := by
    rw [hfr31 13 (by decide) (by decide), hfr30 13 (by decide) (by decide), hfr29 13 (by decide) (by decide), hfr28 13 (by decide) (by decide), hfr27 13 (by decide) (by decide), hfr26 13 (by decide) (by decide), hfr25 13 (by decide) (by decide), hfr24 13 (by decide) (by decide), hfr23 13 (by decide) (by decide), hfr22 13 (by decide) (by decide), hfr21 13 (by decide) (by decide), hfr20 13 (by decide) (by decide), hfr19 13 (by decide) (by decide), hfr18 13 (by decide) (by decide), hfr17 13 (by decide) (by decide), hfr16 13 (by decide) (by decide), hfr15 13 (by decide) (by decide), hfr14 13 (by decide) (by decide)]
  rw [hkeep13 13 (by decide) (by decide)] at hbut13
  have hr32u14 : r32.val[14]! = r15.val[14]! := by
    rw [hfr31 14 (by decide) (by decide), hfr30 14 (by decide) (by decide), hfr29 14 (by decide) (by decide), hfr28 14 (by decide) (by decide), hfr27 14 (by decide) (by decide), hfr26 14 (by decide) (by decide), hfr25 14 (by decide) (by decide), hfr24 14 (by decide) (by decide), hfr23 14 (by decide) (by decide), hfr22 14 (by decide) (by decide), hfr21 14 (by decide) (by decide), hfr20 14 (by decide) (by decide), hfr19 14 (by decide) (by decide), hfr18 14 (by decide) (by decide), hfr17 14 (by decide) (by decide), hfr16 14 (by decide) (by decide), hfr15 14 (by decide) (by decide)]
  rw [hkeep14 14 (by decide) (by decide)] at hbut14
  have hr32u15 : r32.val[15]! = r16.val[15]! := by
    rw [hfr31 15 (by decide) (by decide), hfr30 15 (by decide) (by decide), hfr29 15 (by decide) (by decide), hfr28 15 (by decide) (by decide), hfr27 15 (by decide) (by decide), hfr26 15 (by decide) (by decide), hfr25 15 (by decide) (by decide), hfr24 15 (by decide) (by decide), hfr23 15 (by decide) (by decide), hfr22 15 (by decide) (by decide), hfr21 15 (by decide) (by decide), hfr20 15 (by decide) (by decide), hfr19 15 (by decide) (by decide), hfr18 15 (by decide) (by decide), hfr17 15 (by decide) (by decide), hfr16 15 (by decide) (by decide)]
  rw [hkeep15 15 (by decide) (by decide)] at hbut15
  have hr32u16 : r32.val[16]! = r17.val[16]! := by
    rw [hfr31 16 (by decide) (by decide), hfr30 16 (by decide) (by decide), hfr29 16 (by decide) (by decide), hfr28 16 (by decide) (by decide), hfr27 16 (by decide) (by decide), hfr26 16 (by decide) (by decide), hfr25 16 (by decide) (by decide), hfr24 16 (by decide) (by decide), hfr23 16 (by decide) (by decide), hfr22 16 (by decide) (by decide), hfr21 16 (by decide) (by decide), hfr20 16 (by decide) (by decide), hfr19 16 (by decide) (by decide), hfr18 16 (by decide) (by decide), hfr17 16 (by decide) (by decide)]
  rw [hkeep16 16 (by decide) (by decide)] at hbut16
  have hr32u17 : r32.val[17]! = r18.val[17]! := by
    rw [hfr31 17 (by decide) (by decide), hfr30 17 (by decide) (by decide), hfr29 17 (by decide) (by decide), hfr28 17 (by decide) (by decide), hfr27 17 (by decide) (by decide), hfr26 17 (by decide) (by decide), hfr25 17 (by decide) (by decide), hfr24 17 (by decide) (by decide), hfr23 17 (by decide) (by decide), hfr22 17 (by decide) (by decide), hfr21 17 (by decide) (by decide), hfr20 17 (by decide) (by decide), hfr19 17 (by decide) (by decide), hfr18 17 (by decide) (by decide)]
  rw [hkeep17 17 (by decide) (by decide)] at hbut17
  have hr32u18 : r32.val[18]! = r19.val[18]! := by
    rw [hfr31 18 (by decide) (by decide), hfr30 18 (by decide) (by decide), hfr29 18 (by decide) (by decide), hfr28 18 (by decide) (by decide), hfr27 18 (by decide) (by decide), hfr26 18 (by decide) (by decide), hfr25 18 (by decide) (by decide), hfr24 18 (by decide) (by decide), hfr23 18 (by decide) (by decide), hfr22 18 (by decide) (by decide), hfr21 18 (by decide) (by decide), hfr20 18 (by decide) (by decide), hfr19 18 (by decide) (by decide)]
  rw [hkeep18 18 (by decide) (by decide)] at hbut18
  have hr32u19 : r32.val[19]! = r20.val[19]! := by
    rw [hfr31 19 (by decide) (by decide), hfr30 19 (by decide) (by decide), hfr29 19 (by decide) (by decide), hfr28 19 (by decide) (by decide), hfr27 19 (by decide) (by decide), hfr26 19 (by decide) (by decide), hfr25 19 (by decide) (by decide), hfr24 19 (by decide) (by decide), hfr23 19 (by decide) (by decide), hfr22 19 (by decide) (by decide), hfr21 19 (by decide) (by decide), hfr20 19 (by decide) (by decide)]
  rw [hkeep19 19 (by decide) (by decide)] at hbut19
  have hr32u20 : r32.val[20]! = r21.val[20]! := by
    rw [hfr31 20 (by decide) (by decide), hfr30 20 (by decide) (by decide), hfr29 20 (by decide) (by decide), hfr28 20 (by decide) (by decide), hfr27 20 (by decide) (by decide), hfr26 20 (by decide) (by decide), hfr25 20 (by decide) (by decide), hfr24 20 (by decide) (by decide), hfr23 20 (by decide) (by decide), hfr22 20 (by decide) (by decide), hfr21 20 (by decide) (by decide)]
  rw [hkeep20 20 (by decide) (by decide)] at hbut20
  have hr32u21 : r32.val[21]! = r22.val[21]! := by
    rw [hfr31 21 (by decide) (by decide), hfr30 21 (by decide) (by decide), hfr29 21 (by decide) (by decide), hfr28 21 (by decide) (by decide), hfr27 21 (by decide) (by decide), hfr26 21 (by decide) (by decide), hfr25 21 (by decide) (by decide), hfr24 21 (by decide) (by decide), hfr23 21 (by decide) (by decide), hfr22 21 (by decide) (by decide)]
  rw [hkeep21 21 (by decide) (by decide)] at hbut21
  have hr32u22 : r32.val[22]! = r23.val[22]! := by
    rw [hfr31 22 (by decide) (by decide), hfr30 22 (by decide) (by decide), hfr29 22 (by decide) (by decide), hfr28 22 (by decide) (by decide), hfr27 22 (by decide) (by decide), hfr26 22 (by decide) (by decide), hfr25 22 (by decide) (by decide), hfr24 22 (by decide) (by decide), hfr23 22 (by decide) (by decide)]
  rw [hkeep22 22 (by decide) (by decide)] at hbut22
  have hr32u23 : r32.val[23]! = r24.val[23]! := by
    rw [hfr31 23 (by decide) (by decide), hfr30 23 (by decide) (by decide), hfr29 23 (by decide) (by decide), hfr28 23 (by decide) (by decide), hfr27 23 (by decide) (by decide), hfr26 23 (by decide) (by decide), hfr25 23 (by decide) (by decide), hfr24 23 (by decide) (by decide)]
  rw [hkeep23 23 (by decide) (by decide)] at hbut23
  have hr32u24 : r32.val[24]! = r25.val[24]! := by
    rw [hfr31 24 (by decide) (by decide), hfr30 24 (by decide) (by decide), hfr29 24 (by decide) (by decide), hfr28 24 (by decide) (by decide), hfr27 24 (by decide) (by decide), hfr26 24 (by decide) (by decide), hfr25 24 (by decide) (by decide)]
  rw [hkeep24 24 (by decide) (by decide)] at hbut24
  have hr32u25 : r32.val[25]! = r26.val[25]! := by
    rw [hfr31 25 (by decide) (by decide), hfr30 25 (by decide) (by decide), hfr29 25 (by decide) (by decide), hfr28 25 (by decide) (by decide), hfr27 25 (by decide) (by decide), hfr26 25 (by decide) (by decide)]
  rw [hkeep25 25 (by decide) (by decide)] at hbut25
  have hr32u26 : r32.val[26]! = r27.val[26]! := by
    rw [hfr31 26 (by decide) (by decide), hfr30 26 (by decide) (by decide), hfr29 26 (by decide) (by decide), hfr28 26 (by decide) (by decide), hfr27 26 (by decide) (by decide)]
  rw [hkeep26 26 (by decide) (by decide)] at hbut26
  have hr32u27 : r32.val[27]! = r28.val[27]! := by
    rw [hfr31 27 (by decide) (by decide), hfr30 27 (by decide) (by decide), hfr29 27 (by decide) (by decide), hfr28 27 (by decide) (by decide)]
  rw [hkeep27 27 (by decide) (by decide)] at hbut27
  have hr32u28 : r32.val[28]! = r29.val[28]! := by
    rw [hfr31 28 (by decide) (by decide), hfr30 28 (by decide) (by decide), hfr29 28 (by decide) (by decide)]
  rw [hkeep28 28 (by decide) (by decide)] at hbut28
  have hr32u29 : r32.val[29]! = r30.val[29]! := by
    rw [hfr31 29 (by decide) (by decide), hfr30 29 (by decide) (by decide)]
  rw [hkeep29 29 (by decide) (by decide)] at hbut29
  have hr32u30 : r32.val[30]! = r31.val[30]! := by
    rw [hfr31 30 (by decide) (by decide)]
  rw [hkeep30 30 (by decide) (by decide)] at hbut30
  have hr32u31 : r32.val[31]! = r32.val[31]! := by
    rfl
  rw [hkeep31 31 (by decide) (by decide)] at hbut31
  have hbfu0 : ∀ l, l < 8 →
      liftZ ((r32.val[0]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[0]!).values.val[l]!).val
            + liftZ ((re.val[0]!).values.val[l + 4]!).val
         else (- zeta (63 - 0)) * (liftZ ((re.val[0]!).values.val[l - 4]!).val
            - liftZ ((re.val[0]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u0]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut0
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge0]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge0]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge0]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge0]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu1 : ∀ l, l < 8 →
      liftZ ((r32.val[1]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[1]!).values.val[l]!).val
            + liftZ ((re.val[1]!).values.val[l + 4]!).val
         else (- zeta (63 - 1)) * (liftZ ((re.val[1]!).values.val[l - 4]!).val
            - liftZ ((re.val[1]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u1]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut1
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge1]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge1]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge1]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge1]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu2 : ∀ l, l < 8 →
      liftZ ((r32.val[2]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[2]!).values.val[l]!).val
            + liftZ ((re.val[2]!).values.val[l + 4]!).val
         else (- zeta (63 - 2)) * (liftZ ((re.val[2]!).values.val[l - 4]!).val
            - liftZ ((re.val[2]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u2]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut2
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge2]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge2]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge2]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge2]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu3 : ∀ l, l < 8 →
      liftZ ((r32.val[3]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[3]!).values.val[l]!).val
            + liftZ ((re.val[3]!).values.val[l + 4]!).val
         else (- zeta (63 - 3)) * (liftZ ((re.val[3]!).values.val[l - 4]!).val
            - liftZ ((re.val[3]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u3]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut3
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge3]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge3]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge3]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge3]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu4 : ∀ l, l < 8 →
      liftZ ((r32.val[4]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[4]!).values.val[l]!).val
            + liftZ ((re.val[4]!).values.val[l + 4]!).val
         else (- zeta (63 - 4)) * (liftZ ((re.val[4]!).values.val[l - 4]!).val
            - liftZ ((re.val[4]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u4]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut4
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge4]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge4]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge4]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge4]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu5 : ∀ l, l < 8 →
      liftZ ((r32.val[5]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[5]!).values.val[l]!).val
            + liftZ ((re.val[5]!).values.val[l + 4]!).val
         else (- zeta (63 - 5)) * (liftZ ((re.val[5]!).values.val[l - 4]!).val
            - liftZ ((re.val[5]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u5]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut5
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge5]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge5]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge5]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge5]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu6 : ∀ l, l < 8 →
      liftZ ((r32.val[6]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[6]!).values.val[l]!).val
            + liftZ ((re.val[6]!).values.val[l + 4]!).val
         else (- zeta (63 - 6)) * (liftZ ((re.val[6]!).values.val[l - 4]!).val
            - liftZ ((re.val[6]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u6]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut6
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge6]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge6]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge6]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge6]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu7 : ∀ l, l < 8 →
      liftZ ((r32.val[7]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[7]!).values.val[l]!).val
            + liftZ ((re.val[7]!).values.val[l + 4]!).val
         else (- zeta (63 - 7)) * (liftZ ((re.val[7]!).values.val[l - 4]!).val
            - liftZ ((re.val[7]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u7]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut7
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge7]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge7]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge7]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge7]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu8 : ∀ l, l < 8 →
      liftZ ((r32.val[8]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[8]!).values.val[l]!).val
            + liftZ ((re.val[8]!).values.val[l + 4]!).val
         else (- zeta (63 - 8)) * (liftZ ((re.val[8]!).values.val[l - 4]!).val
            - liftZ ((re.val[8]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u8]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut8
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge8]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge8]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge8]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge8]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu9 : ∀ l, l < 8 →
      liftZ ((r32.val[9]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[9]!).values.val[l]!).val
            + liftZ ((re.val[9]!).values.val[l + 4]!).val
         else (- zeta (63 - 9)) * (liftZ ((re.val[9]!).values.val[l - 4]!).val
            - liftZ ((re.val[9]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u9]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut9
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge9]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge9]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge9]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge9]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu10 : ∀ l, l < 8 →
      liftZ ((r32.val[10]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[10]!).values.val[l]!).val
            + liftZ ((re.val[10]!).values.val[l + 4]!).val
         else (- zeta (63 - 10)) * (liftZ ((re.val[10]!).values.val[l - 4]!).val
            - liftZ ((re.val[10]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u10]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut10
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge10]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge10]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge10]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge10]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu11 : ∀ l, l < 8 →
      liftZ ((r32.val[11]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[11]!).values.val[l]!).val
            + liftZ ((re.val[11]!).values.val[l + 4]!).val
         else (- zeta (63 - 11)) * (liftZ ((re.val[11]!).values.val[l - 4]!).val
            - liftZ ((re.val[11]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u11]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut11
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge11]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge11]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge11]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge11]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu12 : ∀ l, l < 8 →
      liftZ ((r32.val[12]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[12]!).values.val[l]!).val
            + liftZ ((re.val[12]!).values.val[l + 4]!).val
         else (- zeta (63 - 12)) * (liftZ ((re.val[12]!).values.val[l - 4]!).val
            - liftZ ((re.val[12]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u12]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut12
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge12]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge12]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge12]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge12]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu13 : ∀ l, l < 8 →
      liftZ ((r32.val[13]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[13]!).values.val[l]!).val
            + liftZ ((re.val[13]!).values.val[l + 4]!).val
         else (- zeta (63 - 13)) * (liftZ ((re.val[13]!).values.val[l - 4]!).val
            - liftZ ((re.val[13]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u13]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut13
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge13]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge13]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge13]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge13]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu14 : ∀ l, l < 8 →
      liftZ ((r32.val[14]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[14]!).values.val[l]!).val
            + liftZ ((re.val[14]!).values.val[l + 4]!).val
         else (- zeta (63 - 14)) * (liftZ ((re.val[14]!).values.val[l - 4]!).val
            - liftZ ((re.val[14]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u14]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut14
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge14]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge14]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge14]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge14]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu15 : ∀ l, l < 8 →
      liftZ ((r32.val[15]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[15]!).values.val[l]!).val
            + liftZ ((re.val[15]!).values.val[l + 4]!).val
         else (- zeta (63 - 15)) * (liftZ ((re.val[15]!).values.val[l - 4]!).val
            - liftZ ((re.val[15]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u15]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut15
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge15]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge15]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge15]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge15]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu16 : ∀ l, l < 8 →
      liftZ ((r32.val[16]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[16]!).values.val[l]!).val
            + liftZ ((re.val[16]!).values.val[l + 4]!).val
         else (- zeta (63 - 16)) * (liftZ ((re.val[16]!).values.val[l - 4]!).val
            - liftZ ((re.val[16]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u16]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut16
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge16]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge16]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge16]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge16]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu17 : ∀ l, l < 8 →
      liftZ ((r32.val[17]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[17]!).values.val[l]!).val
            + liftZ ((re.val[17]!).values.val[l + 4]!).val
         else (- zeta (63 - 17)) * (liftZ ((re.val[17]!).values.val[l - 4]!).val
            - liftZ ((re.val[17]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u17]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut17
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge17]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge17]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge17]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge17]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu18 : ∀ l, l < 8 →
      liftZ ((r32.val[18]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[18]!).values.val[l]!).val
            + liftZ ((re.val[18]!).values.val[l + 4]!).val
         else (- zeta (63 - 18)) * (liftZ ((re.val[18]!).values.val[l - 4]!).val
            - liftZ ((re.val[18]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u18]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut18
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge18]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge18]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge18]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge18]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu19 : ∀ l, l < 8 →
      liftZ ((r32.val[19]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[19]!).values.val[l]!).val
            + liftZ ((re.val[19]!).values.val[l + 4]!).val
         else (- zeta (63 - 19)) * (liftZ ((re.val[19]!).values.val[l - 4]!).val
            - liftZ ((re.val[19]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u19]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut19
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge19]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge19]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge19]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge19]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu20 : ∀ l, l < 8 →
      liftZ ((r32.val[20]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[20]!).values.val[l]!).val
            + liftZ ((re.val[20]!).values.val[l + 4]!).val
         else (- zeta (63 - 20)) * (liftZ ((re.val[20]!).values.val[l - 4]!).val
            - liftZ ((re.val[20]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u20]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut20
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge20]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge20]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge20]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge20]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu21 : ∀ l, l < 8 →
      liftZ ((r32.val[21]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[21]!).values.val[l]!).val
            + liftZ ((re.val[21]!).values.val[l + 4]!).val
         else (- zeta (63 - 21)) * (liftZ ((re.val[21]!).values.val[l - 4]!).val
            - liftZ ((re.val[21]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u21]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut21
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge21]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge21]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge21]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge21]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu22 : ∀ l, l < 8 →
      liftZ ((r32.val[22]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[22]!).values.val[l]!).val
            + liftZ ((re.val[22]!).values.val[l + 4]!).val
         else (- zeta (63 - 22)) * (liftZ ((re.val[22]!).values.val[l - 4]!).val
            - liftZ ((re.val[22]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u22]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut22
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge22]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge22]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge22]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge22]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu23 : ∀ l, l < 8 →
      liftZ ((r32.val[23]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[23]!).values.val[l]!).val
            + liftZ ((re.val[23]!).values.val[l + 4]!).val
         else (- zeta (63 - 23)) * (liftZ ((re.val[23]!).values.val[l - 4]!).val
            - liftZ ((re.val[23]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u23]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut23
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge23]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge23]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge23]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge23]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu24 : ∀ l, l < 8 →
      liftZ ((r32.val[24]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[24]!).values.val[l]!).val
            + liftZ ((re.val[24]!).values.val[l + 4]!).val
         else (- zeta (63 - 24)) * (liftZ ((re.val[24]!).values.val[l - 4]!).val
            - liftZ ((re.val[24]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u24]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut24
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge24]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge24]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge24]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge24]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu25 : ∀ l, l < 8 →
      liftZ ((r32.val[25]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[25]!).values.val[l]!).val
            + liftZ ((re.val[25]!).values.val[l + 4]!).val
         else (- zeta (63 - 25)) * (liftZ ((re.val[25]!).values.val[l - 4]!).val
            - liftZ ((re.val[25]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u25]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut25
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge25]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge25]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge25]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge25]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu26 : ∀ l, l < 8 →
      liftZ ((r32.val[26]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[26]!).values.val[l]!).val
            + liftZ ((re.val[26]!).values.val[l + 4]!).val
         else (- zeta (63 - 26)) * (liftZ ((re.val[26]!).values.val[l - 4]!).val
            - liftZ ((re.val[26]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u26]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut26
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge26]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge26]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge26]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge26]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu27 : ∀ l, l < 8 →
      liftZ ((r32.val[27]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[27]!).values.val[l]!).val
            + liftZ ((re.val[27]!).values.val[l + 4]!).val
         else (- zeta (63 - 27)) * (liftZ ((re.val[27]!).values.val[l - 4]!).val
            - liftZ ((re.val[27]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u27]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut27
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge27]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge27]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge27]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge27]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu28 : ∀ l, l < 8 →
      liftZ ((r32.val[28]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[28]!).values.val[l]!).val
            + liftZ ((re.val[28]!).values.val[l + 4]!).val
         else (- zeta (63 - 28)) * (liftZ ((re.val[28]!).values.val[l - 4]!).val
            - liftZ ((re.val[28]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u28]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut28
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge28]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge28]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge28]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge28]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu29 : ∀ l, l < 8 →
      liftZ ((r32.val[29]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[29]!).values.val[l]!).val
            + liftZ ((re.val[29]!).values.val[l + 4]!).val
         else (- zeta (63 - 29)) * (liftZ ((re.val[29]!).values.val[l - 4]!).val
            - liftZ ((re.val[29]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u29]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut29
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge29]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge29]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge29]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge29]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu30 : ∀ l, l < 8 →
      liftZ ((r32.val[30]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[30]!).values.val[l]!).val
            + liftZ ((re.val[30]!).values.val[l + 4]!).val
         else (- zeta (63 - 30)) * (liftZ ((re.val[30]!).values.val[l - 4]!).val
            - liftZ ((re.val[30]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u30]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut30
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge30]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge30]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge30]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge30]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu31 : ∀ l, l < 8 →
      liftZ ((r32.val[31]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[31]!).values.val[l]!).val
            + liftZ ((re.val[31]!).values.val[l + 4]!).val
         else (- zeta (63 - 31)) * (liftZ ((re.val[31]!).values.val[l - 4]!).val
            - liftZ ((re.val[31]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u31]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut31
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_pos (by decide), b3]
    | 4, _ => rw [if_neg (by decide), b4, zetaInv2_bridge31]; ring
    | 5, _ => rw [if_neg (by decide), b5, zetaInv2_bridge31]; ring
    | 6, _ => rw [if_neg (by decide), b6, zetaInv2_bridge31]; ring
    | 7, _ => rw [if_neg (by decide), b7, zetaInv2_bridge31]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbf : ∀ u, u < 32 → ∀ l, l < 8 →
      liftZ ((r32.val[u]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[u]!).values.val[l]!).val
            + liftZ ((re.val[u]!).values.val[l + 4]!).val
         else (- zeta (63 - u)) * (liftZ ((re.val[u]!).values.val[l - 4]!).val
            - liftZ ((re.val[u]!).values.val[l]!).val)) := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbfu0 l hl
    | 1, _ => exact hbfu1 l hl
    | 2, _ => exact hbfu2 l hl
    | 3, _ => exact hbfu3 l hl
    | 4, _ => exact hbfu4 l hl
    | 5, _ => exact hbfu5 l hl
    | 6, _ => exact hbfu6 l hl
    | 7, _ => exact hbfu7 l hl
    | 8, _ => exact hbfu8 l hl
    | 9, _ => exact hbfu9 l hl
    | 10, _ => exact hbfu10 l hl
    | 11, _ => exact hbfu11 l hl
    | 12, _ => exact hbfu12 l hl
    | 13, _ => exact hbfu13 l hl
    | 14, _ => exact hbfu14 l hl
    | 15, _ => exact hbfu15 l hl
    | 16, _ => exact hbfu16 l hl
    | 17, _ => exact hbfu17 l hl
    | 18, _ => exact hbfu18 l hl
    | 19, _ => exact hbfu19 l hl
    | 20, _ => exact hbfu20 l hl
    | 21, _ => exact hbfu21 l hl
    | 22, _ => exact hbfu22 l hl
    | 23, _ => exact hbfu23 l hl
    | 24, _ => exact hbfu24 l hl
    | 25, _ => exact hbfu25 l hl
    | 26, _ => exact hbfu26 l hl
    | 27, _ => exact hbfu27 l hl
    | 28, _ => exact hbfu28 l hl
    | 29, _ => exact hbfu29 l hl
    | 30, _ => exact hbfu30 l hl
    | 31, _ => exact hbfu31 l hl
    | (n + 32), h => exact absurd h (by omega)
  have hbnd0 : ∀ l, l < 8 → ((r32.val[0]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u0]; exact hbd0 l hl
  have hbnd1 : ∀ l, l < 8 → ((r32.val[1]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u1]; exact hbd1 l hl
  have hbnd2 : ∀ l, l < 8 → ((r32.val[2]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u2]; exact hbd2 l hl
  have hbnd3 : ∀ l, l < 8 → ((r32.val[3]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u3]; exact hbd3 l hl
  have hbnd4 : ∀ l, l < 8 → ((r32.val[4]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u4]; exact hbd4 l hl
  have hbnd5 : ∀ l, l < 8 → ((r32.val[5]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u5]; exact hbd5 l hl
  have hbnd6 : ∀ l, l < 8 → ((r32.val[6]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u6]; exact hbd6 l hl
  have hbnd7 : ∀ l, l < 8 → ((r32.val[7]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u7]; exact hbd7 l hl
  have hbnd8 : ∀ l, l < 8 → ((r32.val[8]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u8]; exact hbd8 l hl
  have hbnd9 : ∀ l, l < 8 → ((r32.val[9]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u9]; exact hbd9 l hl
  have hbnd10 : ∀ l, l < 8 → ((r32.val[10]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u10]; exact hbd10 l hl
  have hbnd11 : ∀ l, l < 8 → ((r32.val[11]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u11]; exact hbd11 l hl
  have hbnd12 : ∀ l, l < 8 → ((r32.val[12]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u12]; exact hbd12 l hl
  have hbnd13 : ∀ l, l < 8 → ((r32.val[13]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u13]; exact hbd13 l hl
  have hbnd14 : ∀ l, l < 8 → ((r32.val[14]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u14]; exact hbd14 l hl
  have hbnd15 : ∀ l, l < 8 → ((r32.val[15]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u15]; exact hbd15 l hl
  have hbnd16 : ∀ l, l < 8 → ((r32.val[16]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u16]; exact hbd16 l hl
  have hbnd17 : ∀ l, l < 8 → ((r32.val[17]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u17]; exact hbd17 l hl
  have hbnd18 : ∀ l, l < 8 → ((r32.val[18]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u18]; exact hbd18 l hl
  have hbnd19 : ∀ l, l < 8 → ((r32.val[19]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u19]; exact hbd19 l hl
  have hbnd20 : ∀ l, l < 8 → ((r32.val[20]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u20]; exact hbd20 l hl
  have hbnd21 : ∀ l, l < 8 → ((r32.val[21]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u21]; exact hbd21 l hl
  have hbnd22 : ∀ l, l < 8 → ((r32.val[22]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u22]; exact hbd22 l hl
  have hbnd23 : ∀ l, l < 8 → ((r32.val[23]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u23]; exact hbd23 l hl
  have hbnd24 : ∀ l, l < 8 → ((r32.val[24]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u24]; exact hbd24 l hl
  have hbnd25 : ∀ l, l < 8 → ((r32.val[25]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u25]; exact hbd25 l hl
  have hbnd26 : ∀ l, l < 8 → ((r32.val[26]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u26]; exact hbd26 l hl
  have hbnd27 : ∀ l, l < 8 → ((r32.val[27]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u27]; exact hbd27 l hl
  have hbnd28 : ∀ l, l < 8 → ((r32.val[28]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u28]; exact hbd28 l hl
  have hbnd29 : ∀ l, l < 8 → ((r32.val[29]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u29]; exact hbd29 l hl
  have hbnd30 : ∀ l, l < 8 → ((r32.val[30]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u30]; exact hbd30 l hl
  have hbnd31 : ∀ l, l < 8 → ((r32.val[31]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u31]; exact hbd31 l hl
  have hbnd : ∀ u, u < 32 → ∀ l, l < 8 →
      ((r32.val[u]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbnd0 l hl
    | 1, _ => exact hbnd1 l hl
    | 2, _ => exact hbnd2 l hl
    | 3, _ => exact hbnd3 l hl
    | 4, _ => exact hbnd4 l hl
    | 5, _ => exact hbnd5 l hl
    | 6, _ => exact hbnd6 l hl
    | 7, _ => exact hbnd7 l hl
    | 8, _ => exact hbnd8 l hl
    | 9, _ => exact hbnd9 l hl
    | 10, _ => exact hbnd10 l hl
    | 11, _ => exact hbnd11 l hl
    | 12, _ => exact hbnd12 l hl
    | 13, _ => exact hbnd13 l hl
    | 14, _ => exact hbnd14 l hl
    | 15, _ => exact hbnd15 l hl
    | 16, _ => exact hbnd16 l hl
    | 17, _ => exact hbnd17 l hl
    | 18, _ => exact hbnd18 l hl
    | 19, _ => exact hbnd19 l hl
    | 20, _ => exact hbnd20 l hl
    | 21, _ => exact hbnd21 l hl
    | 22, _ => exact hbnd22 l hl
    | 23, _ => exact hbnd23 l hl
    | 24, _ => exact hbnd24 l hl
    | 25, _ => exact hbnd25 l hl
    | 26, _ => exact hbnd26 l hl
    | 27, _ => exact hbnd27 l hl
    | 28, _ => exact hbnd28 l hl
    | 29, _ => exact hbnd29 l hl
    | 30, _ => exact hbnd30 l hl
    | 31, _ => exact hbnd31 l hl
    | (n + 32), h => exact absurd h (by omega)
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub]
    have huu : i / 8 < 32 := by omega
    have hll : i % 8 < 8 := by omega
    have hb := hbf (i / 8) huu (i % 8) hll
    by_cases hlt : i % 8 < 4
    · rw [if_pos hlt]
      rw [if_pos hlt] at hb
      have hdiv : (i + 4) / 8 = i / 8 := by omega
      have hmod : (i + 4) % 8 = i % 8 + 4 := by omega
      have hidx2 : i + 4 < 256 := by omega
      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 4) hidx2, hdiv, hmod]
      exact hb
    · rw [if_neg hlt]
      rw [if_neg hlt] at hb
      have hdiv : (i - 4) / 8 = i / 8 := by omega
      have hmod : (i - 4) % 8 = i % 8 - 4 := by omega
      have hidx2 : i - 4 < 256 := by omega
      rw [Pure.build_getElem _ (i - 4) hidx2, Pure.build_getElem _ i hi, hdiv, hmod]
      exact hb
  · -- Bound conjunct.
    exact hbnd



/-! ### Layer-1 within-unit inverse driver `invert_ntt_at_layer_1_fc`.

    `invert_ntt_at_layer_1` chains 32 `round` calls; round `u` reads unit `u`,
    applies the per-unit inverse butterfly `simd_unit_invert_ntt_at_layer_1 _ Z0 Z1`
    (sub-block {0-3} uses `zeta0`, {4-7} uses `zeta1`), and writes unit `u` back
    (touching ONLY unit `u`). The lifted result equals
    `Pure.intt_layer (lift_units re) 1` (`len = 2`, `k = 127`; within each unit the
    lane split is at `l % 4 < 2`, hi-lane zeta index `127 - (2u + l/4)`). Uniform
    bound `2·B + 2^24`. Faithful clone of `roundInv2_fc` with the L1 leaf (2 zetas)
    + the forward-L1 within-unit lane-split arithmetic. -/

set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_0 :
    liftZ ((3839961#i32 : Std.I32).val : Int) = zeta (127 - 2 * 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_0 :
    liftZ (((-3628969)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_1 :
    liftZ (((-3881060)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_1 :
    liftZ (((-3019102)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_2 :
    liftZ (((-1439742)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_2 :
    liftZ (((-812732)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_3 :
    liftZ (((-1584928)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_3 :
    liftZ ((1285669#i32 : Std.I32).val : Int) = zeta (126 - 2 * 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_4 :
    liftZ ((1341330#i32 : Std.I32).val : Int) = zeta (127 - 2 * 4) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_4 :
    liftZ ((1315589#i32 : Std.I32).val : Int) = zeta (126 - 2 * 4) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_5 :
    liftZ (((-177440)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 5) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_5 :
    liftZ (((-2409325)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 5) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_6 :
    liftZ (((-1851402)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 6) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_6 :
    liftZ ((3159746#i32 : Std.I32).val : Int) = zeta (126 - 2 * 6) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_7 :
    liftZ (((-3553272)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 7) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_7 :
    liftZ ((189548#i32 : Std.I32).val : Int) = zeta (126 - 2 * 7) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_8 :
    liftZ (((-1316856)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 8) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_8 :
    liftZ ((759969#i32 : Std.I32).val : Int) = zeta (126 - 2 * 8) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_9 :
    liftZ (((-210977)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 9) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_9 :
    liftZ ((2389356#i32 : Std.I32).val : Int) = zeta (126 - 2 * 9) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_10 :
    liftZ (((-3249728)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 10) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_10 :
    liftZ ((1653064#i32 : Std.I32).val : Int) = zeta (126 - 2 * 10) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_11 :
    liftZ (((-8578)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 11) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_11 :
    liftZ (((-3724342)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 11) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_12 :
    liftZ ((3958618#i32 : Std.I32).val : Int) = zeta (127 - 2 * 12) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_12 :
    liftZ ((904516#i32 : Std.I32).val : Int) = zeta (126 - 2 * 12) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_13 :
    liftZ (((-1100098)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 13) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_13 :
    liftZ ((44288#i32 : Std.I32).val : Int) = zeta (126 - 2 * 13) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_14 :
    liftZ ((3097992#i32 : Std.I32).val : Int) = zeta (127 - 2 * 14) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_14 :
    liftZ ((508951#i32 : Std.I32).val : Int) = zeta (126 - 2 * 14) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_15 :
    liftZ ((264944#i32 : Std.I32).val : Int) = zeta (127 - 2 * 15) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_15 :
    liftZ (((-3343383)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 15) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_16 :
    liftZ (((-1430430)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 16) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_16 :
    liftZ ((1852771#i32 : Std.I32).val : Int) = zeta (126 - 2 * 16) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_17 :
    liftZ ((1349076#i32 : Std.I32).val : Int) = zeta (127 - 2 * 17) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_17 :
    liftZ (((-381987)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 17) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_18 :
    liftZ (((-1308169)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 18) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_18 :
    liftZ (((-22981)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 18) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_19 :
    liftZ (((-1228525)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 19) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_19 :
    liftZ (((-671102)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 19) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_20 :
    liftZ (((-2477047)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 20) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_20 :
    liftZ (((-411027)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 20) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_21 :
    liftZ (((-3693493)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 21) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_21 :
    liftZ (((-2967645)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 21) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_22 :
    liftZ ((2715295#i32 : Std.I32).val : Int) = zeta (127 - 2 * 22) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_22 :
    liftZ ((2147896#i32 : Std.I32).val : Int) = zeta (126 - 2 * 22) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_23 :
    liftZ (((-983419)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 23) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_23 :
    liftZ ((3412210#i32 : Std.I32).val : Int) = zeta (126 - 2 * 23) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_24 :
    liftZ ((126922#i32 : Std.I32).val : Int) = zeta (127 - 2 * 24) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_24 :
    liftZ (((-3632928)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 24) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_25 :
    liftZ (((-3157330)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 25) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_25 :
    liftZ (((-3190144)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 25) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_26 :
    liftZ (((-1000202)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 26) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_26 :
    liftZ (((-4083598)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 26) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_27 :
    liftZ ((1939314#i32 : Std.I32).val : Int) = zeta (127 - 2 * 27) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_27 :
    liftZ (((-1257611)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 27) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_28 :
    liftZ (((-1585221)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 28) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_28 :
    liftZ ((2176455#i32 : Std.I32).val : Int) = zeta (126 - 2 * 28) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_29 :
    liftZ ((3475950#i32 : Std.I32).val : Int) = zeta (127 - 2 * 29) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_29 :
    liftZ (((-1452451)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 29) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_30 :
    liftZ (((-3041255)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 30) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_30 :
    liftZ (((-3677745)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 30) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge0_31 :
    liftZ (((-1528703)#i32 : Std.I32).val : Int) = zeta (127 - 2 * 31) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv1_bridge1_31 :
    liftZ (((-3930395)#i32 : Std.I32).val : Int) = zeta (126 - 2 * 31) := by decide

private theorem zetaInv1_mag0_0 : (3839961#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_0 : ((-3628969)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_1 : ((-3881060)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_1 : ((-3019102)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_2 : ((-1439742)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_2 : ((-812732)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_3 : ((-1584928)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_3 : (1285669#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_4 : (1341330#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_4 : (1315589#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_5 : ((-177440)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_5 : ((-2409325)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_6 : ((-1851402)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_6 : (3159746#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_7 : ((-3553272)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_7 : (189548#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_8 : ((-1316856)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_8 : (759969#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_9 : ((-210977)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_9 : (2389356#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_10 : ((-3249728)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_10 : (1653064#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_11 : ((-8578)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_11 : ((-3724342)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_12 : (3958618#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_12 : (904516#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_13 : ((-1100098)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_13 : (44288#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_14 : (3097992#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_14 : (508951#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_15 : (264944#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_15 : ((-3343383)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_16 : ((-1430430)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_16 : (1852771#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_17 : (1349076#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_17 : ((-381987)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_18 : ((-1308169)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_18 : ((-22981)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_19 : ((-1228525)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_19 : ((-671102)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_20 : ((-2477047)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_20 : ((-411027)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_21 : ((-3693493)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_21 : ((-2967645)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_22 : (2715295#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_22 : (2147896#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_23 : ((-983419)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_23 : (3412210#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_24 : (126922#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_24 : ((-3632928)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_25 : ((-3157330)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_25 : ((-3190144)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_26 : ((-1000202)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_26 : ((-4083598)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_27 : (1939314#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_27 : ((-1257611)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_28 : ((-1585221)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_28 : (2176455#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_29 : (3475950#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_29 : ((-1452451)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_30 : ((-3041255)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_30 : ((-3677745)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag0_31 : ((-1528703)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv1_mag1_31 : ((-3930395)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

/-- One `round` of inverse layer 1: read unit `k`, apply the per-unit inverse
    (Gentleman–Sande) butterfly with `zeta0` (sub-block {0-3}) and `zeta1`
    (sub-block {4-7}), write unit `k` back (touching only unit `k`). Faithful clone
    of `roundInv2_fc` with the L1 leaf + post. -/
private theorem roundInv1_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (k : Nat) (hk : k < 32) (zeta0 zeta1 : Std.I32) (B : Nat)
    (hz0 : zeta0.val.natAbs ≤ 8380416) (hz1 : zeta1.val.natAbs ≤ 8380416)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1)
    (hin : ∀ l : Nat, l < 8 → ((re.val[k]!).values.val[l]!).val.natAbs ≤ B) :
    ∃ out, libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_1.round re k#usize zeta0 zeta1 = .ok out
      ∧ (liftZ ((out.val[k]!).values.val[0]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val + liftZ ((re.val[k]!).values.val[2]!).val
        ∧ liftZ ((out.val[k]!).values.val[1]!).val
            = liftZ ((re.val[k]!).values.val[1]!).val + liftZ ((re.val[k]!).values.val[3]!).val
        ∧ liftZ ((out.val[k]!).values.val[2]!).val
            = (liftZ ((re.val[k]!).values.val[2]!).val - liftZ ((re.val[k]!).values.val[0]!).val) * liftZ zeta0.val
        ∧ liftZ ((out.val[k]!).values.val[3]!).val
            = (liftZ ((re.val[k]!).values.val[3]!).val - liftZ ((re.val[k]!).values.val[1]!).val) * liftZ zeta0.val
        ∧ liftZ ((out.val[k]!).values.val[4]!).val
            = liftZ ((re.val[k]!).values.val[4]!).val + liftZ ((re.val[k]!).values.val[6]!).val
        ∧ liftZ ((out.val[k]!).values.val[5]!).val
            = liftZ ((re.val[k]!).values.val[5]!).val + liftZ ((re.val[k]!).values.val[7]!).val
        ∧ liftZ ((out.val[k]!).values.val[6]!).val
            = (liftZ ((re.val[k]!).values.val[6]!).val - liftZ ((re.val[k]!).values.val[4]!).val) * liftZ zeta1.val
        ∧ liftZ ((out.val[k]!).values.val[7]!).val
            = (liftZ ((re.val[k]!).values.val[7]!).val - liftZ ((re.val[k]!).values.val[5]!).val) * liftZ zeta1.val)
      ∧ (∀ u : Nat, u < 32 → u ≠ k → out.val[u]! = re.val[u]!)
      ∧ (∀ l : Nat, l < 8 → ((out.val[k]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24) := by
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_1.round
  have hre_len : re.length = 32 := Std.Array.length_eq _
  have hk_len : (k#usize : Std.Usize).val < re.length := by
    rw [hre_len]; simpa using hk
  have h_idx : Array.index_usize re k#usize = .ok (re.val[k]!) :=
    array_index_usize_ok_eq re k#usize hk_len
  set ak : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    re.val[k]! with hak
  have h_imt : Array.index_mut_usize re k#usize = .ok (ak, re.set k#usize) := by
    unfold Aeneas.Std.Array.index_mut_usize; rw [h_idx]; rfl
  obtain ⟨c1, hc1_eq, hc1_butter, hc1_bd⟩ :=
    triple_exists_ok (simd_unit_invert_ntt_at_layer_1_fc ak zeta0 zeta1 B hz0 hz1 hB hin)
  have hset_k : (re.set k#usize c1).val[k]! = c1 := by
    rw [← Std.Array.getElem!_Nat_eq]
    exact Std.Array.getElem!_Nat_set_eq re k#usize k c1 ⟨rfl, by rw [hre_len]; exact hk⟩
  refine ⟨re.set k#usize c1, ?_, ?_, ?_, ?_⟩
  · simp [Aeneas.Std.bind_tc_ok, h_imt, hc1_eq]
  · rw [hset_k]; exact hc1_butter
  · intro u hu hne
    rw [← Std.Array.getElem!_Nat_eq, ← Std.Array.getElem!_Nat_eq (v := re)]
    exact Std.Array.getElem!_Nat_set_ne re k#usize u c1 (fun h => hne h.symm)
  · intro l hl
    rw [hset_k]; exact hc1_bd l hl


set_option maxHeartbeats 16000000 in
@[spec]
theorem invert_ntt_at_layer_1_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_1 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.intt_layer (lift_units re) 1
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ 2 * B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_1
  have hkeep0 : ∀ u, 0 ≤ u → u < 32 → re.val[u]! = re.val[u]! := fun u _ _ => rfl
  obtain ⟨r1, hr1_eq, hbut0, hfr0, hbd0⟩ :=
    roundInv1_fc re 0 (by decide) (3839961#i32) ((-3628969)#i32) B (zetaInv1_mag0_0) (zetaInv1_mag1_0) hB
      (fun l hl => by rw [hkeep0 0 (by omega) (by omega)]; exact hin 0 (by decide) l hl)
  have hkeep1 : ∀ u, 1 ≤ u → u < 32 → r1.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr0 u hu2 (by omega), hkeep0 u (by omega) hu2]
  obtain ⟨r2, hr2_eq, hbut1, hfr1, hbd1⟩ :=
    roundInv1_fc r1 1 (by decide) ((-3881060)#i32) ((-3019102)#i32) B (zetaInv1_mag0_1) (zetaInv1_mag1_1) hB
      (fun l hl => by rw [hkeep1 1 (by omega) (by omega)]; exact hin 1 (by decide) l hl)
  have hkeep2 : ∀ u, 2 ≤ u → u < 32 → r2.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr1 u hu2 (by omega), hkeep1 u (by omega) hu2]
  obtain ⟨r3, hr3_eq, hbut2, hfr2, hbd2⟩ :=
    roundInv1_fc r2 2 (by decide) ((-1439742)#i32) ((-812732)#i32) B (zetaInv1_mag0_2) (zetaInv1_mag1_2) hB
      (fun l hl => by rw [hkeep2 2 (by omega) (by omega)]; exact hin 2 (by decide) l hl)
  have hkeep3 : ∀ u, 3 ≤ u → u < 32 → r3.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr2 u hu2 (by omega), hkeep2 u (by omega) hu2]
  obtain ⟨r4, hr4_eq, hbut3, hfr3, hbd3⟩ :=
    roundInv1_fc r3 3 (by decide) ((-1584928)#i32) (1285669#i32) B (zetaInv1_mag0_3) (zetaInv1_mag1_3) hB
      (fun l hl => by rw [hkeep3 3 (by omega) (by omega)]; exact hin 3 (by decide) l hl)
  have hkeep4 : ∀ u, 4 ≤ u → u < 32 → r4.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr3 u hu2 (by omega), hkeep3 u (by omega) hu2]
  obtain ⟨r5, hr5_eq, hbut4, hfr4, hbd4⟩ :=
    roundInv1_fc r4 4 (by decide) (1341330#i32) (1315589#i32) B (zetaInv1_mag0_4) (zetaInv1_mag1_4) hB
      (fun l hl => by rw [hkeep4 4 (by omega) (by omega)]; exact hin 4 (by decide) l hl)
  have hkeep5 : ∀ u, 5 ≤ u → u < 32 → r5.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr4 u hu2 (by omega), hkeep4 u (by omega) hu2]
  obtain ⟨r6, hr6_eq, hbut5, hfr5, hbd5⟩ :=
    roundInv1_fc r5 5 (by decide) ((-177440)#i32) ((-2409325)#i32) B (zetaInv1_mag0_5) (zetaInv1_mag1_5) hB
      (fun l hl => by rw [hkeep5 5 (by omega) (by omega)]; exact hin 5 (by decide) l hl)
  have hkeep6 : ∀ u, 6 ≤ u → u < 32 → r6.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr5 u hu2 (by omega), hkeep5 u (by omega) hu2]
  obtain ⟨r7, hr7_eq, hbut6, hfr6, hbd6⟩ :=
    roundInv1_fc r6 6 (by decide) ((-1851402)#i32) (3159746#i32) B (zetaInv1_mag0_6) (zetaInv1_mag1_6) hB
      (fun l hl => by rw [hkeep6 6 (by omega) (by omega)]; exact hin 6 (by decide) l hl)
  have hkeep7 : ∀ u, 7 ≤ u → u < 32 → r7.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr6 u hu2 (by omega), hkeep6 u (by omega) hu2]
  obtain ⟨r8, hr8_eq, hbut7, hfr7, hbd7⟩ :=
    roundInv1_fc r7 7 (by decide) ((-3553272)#i32) (189548#i32) B (zetaInv1_mag0_7) (zetaInv1_mag1_7) hB
      (fun l hl => by rw [hkeep7 7 (by omega) (by omega)]; exact hin 7 (by decide) l hl)
  have hkeep8 : ∀ u, 8 ≤ u → u < 32 → r8.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr7 u hu2 (by omega), hkeep7 u (by omega) hu2]
  obtain ⟨r9, hr9_eq, hbut8, hfr8, hbd8⟩ :=
    roundInv1_fc r8 8 (by decide) ((-1316856)#i32) (759969#i32) B (zetaInv1_mag0_8) (zetaInv1_mag1_8) hB
      (fun l hl => by rw [hkeep8 8 (by omega) (by omega)]; exact hin 8 (by decide) l hl)
  have hkeep9 : ∀ u, 9 ≤ u → u < 32 → r9.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr8 u hu2 (by omega), hkeep8 u (by omega) hu2]
  obtain ⟨r10, hr10_eq, hbut9, hfr9, hbd9⟩ :=
    roundInv1_fc r9 9 (by decide) ((-210977)#i32) (2389356#i32) B (zetaInv1_mag0_9) (zetaInv1_mag1_9) hB
      (fun l hl => by rw [hkeep9 9 (by omega) (by omega)]; exact hin 9 (by decide) l hl)
  have hkeep10 : ∀ u, 10 ≤ u → u < 32 → r10.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr9 u hu2 (by omega), hkeep9 u (by omega) hu2]
  obtain ⟨r11, hr11_eq, hbut10, hfr10, hbd10⟩ :=
    roundInv1_fc r10 10 (by decide) ((-3249728)#i32) (1653064#i32) B (zetaInv1_mag0_10) (zetaInv1_mag1_10) hB
      (fun l hl => by rw [hkeep10 10 (by omega) (by omega)]; exact hin 10 (by decide) l hl)
  have hkeep11 : ∀ u, 11 ≤ u → u < 32 → r11.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr10 u hu2 (by omega), hkeep10 u (by omega) hu2]
  obtain ⟨r12, hr12_eq, hbut11, hfr11, hbd11⟩ :=
    roundInv1_fc r11 11 (by decide) ((-8578)#i32) ((-3724342)#i32) B (zetaInv1_mag0_11) (zetaInv1_mag1_11) hB
      (fun l hl => by rw [hkeep11 11 (by omega) (by omega)]; exact hin 11 (by decide) l hl)
  have hkeep12 : ∀ u, 12 ≤ u → u < 32 → r12.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr11 u hu2 (by omega), hkeep11 u (by omega) hu2]
  obtain ⟨r13, hr13_eq, hbut12, hfr12, hbd12⟩ :=
    roundInv1_fc r12 12 (by decide) (3958618#i32) (904516#i32) B (zetaInv1_mag0_12) (zetaInv1_mag1_12) hB
      (fun l hl => by rw [hkeep12 12 (by omega) (by omega)]; exact hin 12 (by decide) l hl)
  have hkeep13 : ∀ u, 13 ≤ u → u < 32 → r13.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr12 u hu2 (by omega), hkeep12 u (by omega) hu2]
  obtain ⟨r14, hr14_eq, hbut13, hfr13, hbd13⟩ :=
    roundInv1_fc r13 13 (by decide) ((-1100098)#i32) (44288#i32) B (zetaInv1_mag0_13) (zetaInv1_mag1_13) hB
      (fun l hl => by rw [hkeep13 13 (by omega) (by omega)]; exact hin 13 (by decide) l hl)
  have hkeep14 : ∀ u, 14 ≤ u → u < 32 → r14.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr13 u hu2 (by omega), hkeep13 u (by omega) hu2]
  obtain ⟨r15, hr15_eq, hbut14, hfr14, hbd14⟩ :=
    roundInv1_fc r14 14 (by decide) (3097992#i32) (508951#i32) B (zetaInv1_mag0_14) (zetaInv1_mag1_14) hB
      (fun l hl => by rw [hkeep14 14 (by omega) (by omega)]; exact hin 14 (by decide) l hl)
  have hkeep15 : ∀ u, 15 ≤ u → u < 32 → r15.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr14 u hu2 (by omega), hkeep14 u (by omega) hu2]
  obtain ⟨r16, hr16_eq, hbut15, hfr15, hbd15⟩ :=
    roundInv1_fc r15 15 (by decide) (264944#i32) ((-3343383)#i32) B (zetaInv1_mag0_15) (zetaInv1_mag1_15) hB
      (fun l hl => by rw [hkeep15 15 (by omega) (by omega)]; exact hin 15 (by decide) l hl)
  have hkeep16 : ∀ u, 16 ≤ u → u < 32 → r16.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr15 u hu2 (by omega), hkeep15 u (by omega) hu2]
  obtain ⟨r17, hr17_eq, hbut16, hfr16, hbd16⟩ :=
    roundInv1_fc r16 16 (by decide) ((-1430430)#i32) (1852771#i32) B (zetaInv1_mag0_16) (zetaInv1_mag1_16) hB
      (fun l hl => by rw [hkeep16 16 (by omega) (by omega)]; exact hin 16 (by decide) l hl)
  have hkeep17 : ∀ u, 17 ≤ u → u < 32 → r17.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr16 u hu2 (by omega), hkeep16 u (by omega) hu2]
  obtain ⟨r18, hr18_eq, hbut17, hfr17, hbd17⟩ :=
    roundInv1_fc r17 17 (by decide) (1349076#i32) ((-381987)#i32) B (zetaInv1_mag0_17) (zetaInv1_mag1_17) hB
      (fun l hl => by rw [hkeep17 17 (by omega) (by omega)]; exact hin 17 (by decide) l hl)
  have hkeep18 : ∀ u, 18 ≤ u → u < 32 → r18.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr17 u hu2 (by omega), hkeep17 u (by omega) hu2]
  obtain ⟨r19, hr19_eq, hbut18, hfr18, hbd18⟩ :=
    roundInv1_fc r18 18 (by decide) ((-1308169)#i32) ((-22981)#i32) B (zetaInv1_mag0_18) (zetaInv1_mag1_18) hB
      (fun l hl => by rw [hkeep18 18 (by omega) (by omega)]; exact hin 18 (by decide) l hl)
  have hkeep19 : ∀ u, 19 ≤ u → u < 32 → r19.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr18 u hu2 (by omega), hkeep18 u (by omega) hu2]
  obtain ⟨r20, hr20_eq, hbut19, hfr19, hbd19⟩ :=
    roundInv1_fc r19 19 (by decide) ((-1228525)#i32) ((-671102)#i32) B (zetaInv1_mag0_19) (zetaInv1_mag1_19) hB
      (fun l hl => by rw [hkeep19 19 (by omega) (by omega)]; exact hin 19 (by decide) l hl)
  have hkeep20 : ∀ u, 20 ≤ u → u < 32 → r20.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr19 u hu2 (by omega), hkeep19 u (by omega) hu2]
  obtain ⟨r21, hr21_eq, hbut20, hfr20, hbd20⟩ :=
    roundInv1_fc r20 20 (by decide) ((-2477047)#i32) ((-411027)#i32) B (zetaInv1_mag0_20) (zetaInv1_mag1_20) hB
      (fun l hl => by rw [hkeep20 20 (by omega) (by omega)]; exact hin 20 (by decide) l hl)
  have hkeep21 : ∀ u, 21 ≤ u → u < 32 → r21.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr20 u hu2 (by omega), hkeep20 u (by omega) hu2]
  obtain ⟨r22, hr22_eq, hbut21, hfr21, hbd21⟩ :=
    roundInv1_fc r21 21 (by decide) ((-3693493)#i32) ((-2967645)#i32) B (zetaInv1_mag0_21) (zetaInv1_mag1_21) hB
      (fun l hl => by rw [hkeep21 21 (by omega) (by omega)]; exact hin 21 (by decide) l hl)
  have hkeep22 : ∀ u, 22 ≤ u → u < 32 → r22.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr21 u hu2 (by omega), hkeep21 u (by omega) hu2]
  obtain ⟨r23, hr23_eq, hbut22, hfr22, hbd22⟩ :=
    roundInv1_fc r22 22 (by decide) (2715295#i32) (2147896#i32) B (zetaInv1_mag0_22) (zetaInv1_mag1_22) hB
      (fun l hl => by rw [hkeep22 22 (by omega) (by omega)]; exact hin 22 (by decide) l hl)
  have hkeep23 : ∀ u, 23 ≤ u → u < 32 → r23.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr22 u hu2 (by omega), hkeep22 u (by omega) hu2]
  obtain ⟨r24, hr24_eq, hbut23, hfr23, hbd23⟩ :=
    roundInv1_fc r23 23 (by decide) ((-983419)#i32) (3412210#i32) B (zetaInv1_mag0_23) (zetaInv1_mag1_23) hB
      (fun l hl => by rw [hkeep23 23 (by omega) (by omega)]; exact hin 23 (by decide) l hl)
  have hkeep24 : ∀ u, 24 ≤ u → u < 32 → r24.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr23 u hu2 (by omega), hkeep23 u (by omega) hu2]
  obtain ⟨r25, hr25_eq, hbut24, hfr24, hbd24⟩ :=
    roundInv1_fc r24 24 (by decide) (126922#i32) ((-3632928)#i32) B (zetaInv1_mag0_24) (zetaInv1_mag1_24) hB
      (fun l hl => by rw [hkeep24 24 (by omega) (by omega)]; exact hin 24 (by decide) l hl)
  have hkeep25 : ∀ u, 25 ≤ u → u < 32 → r25.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr24 u hu2 (by omega), hkeep24 u (by omega) hu2]
  obtain ⟨r26, hr26_eq, hbut25, hfr25, hbd25⟩ :=
    roundInv1_fc r25 25 (by decide) ((-3157330)#i32) ((-3190144)#i32) B (zetaInv1_mag0_25) (zetaInv1_mag1_25) hB
      (fun l hl => by rw [hkeep25 25 (by omega) (by omega)]; exact hin 25 (by decide) l hl)
  have hkeep26 : ∀ u, 26 ≤ u → u < 32 → r26.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr25 u hu2 (by omega), hkeep25 u (by omega) hu2]
  obtain ⟨r27, hr27_eq, hbut26, hfr26, hbd26⟩ :=
    roundInv1_fc r26 26 (by decide) ((-1000202)#i32) ((-4083598)#i32) B (zetaInv1_mag0_26) (zetaInv1_mag1_26) hB
      (fun l hl => by rw [hkeep26 26 (by omega) (by omega)]; exact hin 26 (by decide) l hl)
  have hkeep27 : ∀ u, 27 ≤ u → u < 32 → r27.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr26 u hu2 (by omega), hkeep26 u (by omega) hu2]
  obtain ⟨r28, hr28_eq, hbut27, hfr27, hbd27⟩ :=
    roundInv1_fc r27 27 (by decide) (1939314#i32) ((-1257611)#i32) B (zetaInv1_mag0_27) (zetaInv1_mag1_27) hB
      (fun l hl => by rw [hkeep27 27 (by omega) (by omega)]; exact hin 27 (by decide) l hl)
  have hkeep28 : ∀ u, 28 ≤ u → u < 32 → r28.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr27 u hu2 (by omega), hkeep27 u (by omega) hu2]
  obtain ⟨r29, hr29_eq, hbut28, hfr28, hbd28⟩ :=
    roundInv1_fc r28 28 (by decide) ((-1585221)#i32) (2176455#i32) B (zetaInv1_mag0_28) (zetaInv1_mag1_28) hB
      (fun l hl => by rw [hkeep28 28 (by omega) (by omega)]; exact hin 28 (by decide) l hl)
  have hkeep29 : ∀ u, 29 ≤ u → u < 32 → r29.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr28 u hu2 (by omega), hkeep28 u (by omega) hu2]
  obtain ⟨r30, hr30_eq, hbut29, hfr29, hbd29⟩ :=
    roundInv1_fc r29 29 (by decide) (3475950#i32) ((-1452451)#i32) B (zetaInv1_mag0_29) (zetaInv1_mag1_29) hB
      (fun l hl => by rw [hkeep29 29 (by omega) (by omega)]; exact hin 29 (by decide) l hl)
  have hkeep30 : ∀ u, 30 ≤ u → u < 32 → r30.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr29 u hu2 (by omega), hkeep29 u (by omega) hu2]
  obtain ⟨r31, hr31_eq, hbut30, hfr30, hbd30⟩ :=
    roundInv1_fc r30 30 (by decide) ((-3041255)#i32) ((-3677745)#i32) B (zetaInv1_mag0_30) (zetaInv1_mag1_30) hB
      (fun l hl => by rw [hkeep30 30 (by omega) (by omega)]; exact hin 30 (by decide) l hl)
  have hkeep31 : ∀ u, 31 ≤ u → u < 32 → r31.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr30 u hu2 (by omega), hkeep30 u (by omega) hu2]
  obtain ⟨r32, hr32_eq, hbut31, hfr31, hbd31⟩ :=
    roundInv1_fc r31 31 (by decide) ((-1528703)#i32) ((-3930395)#i32) B (zetaInv1_mag0_31) (zetaInv1_mag1_31) hB
      (fun l hl => by rw [hkeep31 31 (by omega) (by omega)]; exact hin 31 (by decide) l hl)
  have hkeep32 : ∀ u, 32 ≤ u → u < 32 → r32.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr31 u hu2 (by omega), hkeep31 u (by omega) hu2]
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
  rw [hr16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr17_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr18_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr19_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr20_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr21_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr22_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr23_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr24_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr25_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr26_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr27_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr28_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr29_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr30_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr31_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr32_eq
  have hr32u0 : r32.val[0]! = r1.val[0]! := by
    rw [hfr31 0 (by decide) (by decide), hfr30 0 (by decide) (by decide), hfr29 0 (by decide) (by decide), hfr28 0 (by decide) (by decide), hfr27 0 (by decide) (by decide), hfr26 0 (by decide) (by decide), hfr25 0 (by decide) (by decide), hfr24 0 (by decide) (by decide), hfr23 0 (by decide) (by decide), hfr22 0 (by decide) (by decide), hfr21 0 (by decide) (by decide), hfr20 0 (by decide) (by decide), hfr19 0 (by decide) (by decide), hfr18 0 (by decide) (by decide), hfr17 0 (by decide) (by decide), hfr16 0 (by decide) (by decide), hfr15 0 (by decide) (by decide), hfr14 0 (by decide) (by decide), hfr13 0 (by decide) (by decide), hfr12 0 (by decide) (by decide), hfr11 0 (by decide) (by decide), hfr10 0 (by decide) (by decide), hfr9 0 (by decide) (by decide), hfr8 0 (by decide) (by decide), hfr7 0 (by decide) (by decide), hfr6 0 (by decide) (by decide), hfr5 0 (by decide) (by decide), hfr4 0 (by decide) (by decide), hfr3 0 (by decide) (by decide), hfr2 0 (by decide) (by decide), hfr1 0 (by decide) (by decide)]
  have hr32u1 : r32.val[1]! = r2.val[1]! := by
    rw [hfr31 1 (by decide) (by decide), hfr30 1 (by decide) (by decide), hfr29 1 (by decide) (by decide), hfr28 1 (by decide) (by decide), hfr27 1 (by decide) (by decide), hfr26 1 (by decide) (by decide), hfr25 1 (by decide) (by decide), hfr24 1 (by decide) (by decide), hfr23 1 (by decide) (by decide), hfr22 1 (by decide) (by decide), hfr21 1 (by decide) (by decide), hfr20 1 (by decide) (by decide), hfr19 1 (by decide) (by decide), hfr18 1 (by decide) (by decide), hfr17 1 (by decide) (by decide), hfr16 1 (by decide) (by decide), hfr15 1 (by decide) (by decide), hfr14 1 (by decide) (by decide), hfr13 1 (by decide) (by decide), hfr12 1 (by decide) (by decide), hfr11 1 (by decide) (by decide), hfr10 1 (by decide) (by decide), hfr9 1 (by decide) (by decide), hfr8 1 (by decide) (by decide), hfr7 1 (by decide) (by decide), hfr6 1 (by decide) (by decide), hfr5 1 (by decide) (by decide), hfr4 1 (by decide) (by decide), hfr3 1 (by decide) (by decide), hfr2 1 (by decide) (by decide)]
  rw [hkeep1 1 (by decide) (by decide)] at hbut1
  have hr32u2 : r32.val[2]! = r3.val[2]! := by
    rw [hfr31 2 (by decide) (by decide), hfr30 2 (by decide) (by decide), hfr29 2 (by decide) (by decide), hfr28 2 (by decide) (by decide), hfr27 2 (by decide) (by decide), hfr26 2 (by decide) (by decide), hfr25 2 (by decide) (by decide), hfr24 2 (by decide) (by decide), hfr23 2 (by decide) (by decide), hfr22 2 (by decide) (by decide), hfr21 2 (by decide) (by decide), hfr20 2 (by decide) (by decide), hfr19 2 (by decide) (by decide), hfr18 2 (by decide) (by decide), hfr17 2 (by decide) (by decide), hfr16 2 (by decide) (by decide), hfr15 2 (by decide) (by decide), hfr14 2 (by decide) (by decide), hfr13 2 (by decide) (by decide), hfr12 2 (by decide) (by decide), hfr11 2 (by decide) (by decide), hfr10 2 (by decide) (by decide), hfr9 2 (by decide) (by decide), hfr8 2 (by decide) (by decide), hfr7 2 (by decide) (by decide), hfr6 2 (by decide) (by decide), hfr5 2 (by decide) (by decide), hfr4 2 (by decide) (by decide), hfr3 2 (by decide) (by decide)]
  rw [hkeep2 2 (by decide) (by decide)] at hbut2
  have hr32u3 : r32.val[3]! = r4.val[3]! := by
    rw [hfr31 3 (by decide) (by decide), hfr30 3 (by decide) (by decide), hfr29 3 (by decide) (by decide), hfr28 3 (by decide) (by decide), hfr27 3 (by decide) (by decide), hfr26 3 (by decide) (by decide), hfr25 3 (by decide) (by decide), hfr24 3 (by decide) (by decide), hfr23 3 (by decide) (by decide), hfr22 3 (by decide) (by decide), hfr21 3 (by decide) (by decide), hfr20 3 (by decide) (by decide), hfr19 3 (by decide) (by decide), hfr18 3 (by decide) (by decide), hfr17 3 (by decide) (by decide), hfr16 3 (by decide) (by decide), hfr15 3 (by decide) (by decide), hfr14 3 (by decide) (by decide), hfr13 3 (by decide) (by decide), hfr12 3 (by decide) (by decide), hfr11 3 (by decide) (by decide), hfr10 3 (by decide) (by decide), hfr9 3 (by decide) (by decide), hfr8 3 (by decide) (by decide), hfr7 3 (by decide) (by decide), hfr6 3 (by decide) (by decide), hfr5 3 (by decide) (by decide), hfr4 3 (by decide) (by decide)]
  rw [hkeep3 3 (by decide) (by decide)] at hbut3
  have hr32u4 : r32.val[4]! = r5.val[4]! := by
    rw [hfr31 4 (by decide) (by decide), hfr30 4 (by decide) (by decide), hfr29 4 (by decide) (by decide), hfr28 4 (by decide) (by decide), hfr27 4 (by decide) (by decide), hfr26 4 (by decide) (by decide), hfr25 4 (by decide) (by decide), hfr24 4 (by decide) (by decide), hfr23 4 (by decide) (by decide), hfr22 4 (by decide) (by decide), hfr21 4 (by decide) (by decide), hfr20 4 (by decide) (by decide), hfr19 4 (by decide) (by decide), hfr18 4 (by decide) (by decide), hfr17 4 (by decide) (by decide), hfr16 4 (by decide) (by decide), hfr15 4 (by decide) (by decide), hfr14 4 (by decide) (by decide), hfr13 4 (by decide) (by decide), hfr12 4 (by decide) (by decide), hfr11 4 (by decide) (by decide), hfr10 4 (by decide) (by decide), hfr9 4 (by decide) (by decide), hfr8 4 (by decide) (by decide), hfr7 4 (by decide) (by decide), hfr6 4 (by decide) (by decide), hfr5 4 (by decide) (by decide)]
  rw [hkeep4 4 (by decide) (by decide)] at hbut4
  have hr32u5 : r32.val[5]! = r6.val[5]! := by
    rw [hfr31 5 (by decide) (by decide), hfr30 5 (by decide) (by decide), hfr29 5 (by decide) (by decide), hfr28 5 (by decide) (by decide), hfr27 5 (by decide) (by decide), hfr26 5 (by decide) (by decide), hfr25 5 (by decide) (by decide), hfr24 5 (by decide) (by decide), hfr23 5 (by decide) (by decide), hfr22 5 (by decide) (by decide), hfr21 5 (by decide) (by decide), hfr20 5 (by decide) (by decide), hfr19 5 (by decide) (by decide), hfr18 5 (by decide) (by decide), hfr17 5 (by decide) (by decide), hfr16 5 (by decide) (by decide), hfr15 5 (by decide) (by decide), hfr14 5 (by decide) (by decide), hfr13 5 (by decide) (by decide), hfr12 5 (by decide) (by decide), hfr11 5 (by decide) (by decide), hfr10 5 (by decide) (by decide), hfr9 5 (by decide) (by decide), hfr8 5 (by decide) (by decide), hfr7 5 (by decide) (by decide), hfr6 5 (by decide) (by decide)]
  rw [hkeep5 5 (by decide) (by decide)] at hbut5
  have hr32u6 : r32.val[6]! = r7.val[6]! := by
    rw [hfr31 6 (by decide) (by decide), hfr30 6 (by decide) (by decide), hfr29 6 (by decide) (by decide), hfr28 6 (by decide) (by decide), hfr27 6 (by decide) (by decide), hfr26 6 (by decide) (by decide), hfr25 6 (by decide) (by decide), hfr24 6 (by decide) (by decide), hfr23 6 (by decide) (by decide), hfr22 6 (by decide) (by decide), hfr21 6 (by decide) (by decide), hfr20 6 (by decide) (by decide), hfr19 6 (by decide) (by decide), hfr18 6 (by decide) (by decide), hfr17 6 (by decide) (by decide), hfr16 6 (by decide) (by decide), hfr15 6 (by decide) (by decide), hfr14 6 (by decide) (by decide), hfr13 6 (by decide) (by decide), hfr12 6 (by decide) (by decide), hfr11 6 (by decide) (by decide), hfr10 6 (by decide) (by decide), hfr9 6 (by decide) (by decide), hfr8 6 (by decide) (by decide), hfr7 6 (by decide) (by decide)]
  rw [hkeep6 6 (by decide) (by decide)] at hbut6
  have hr32u7 : r32.val[7]! = r8.val[7]! := by
    rw [hfr31 7 (by decide) (by decide), hfr30 7 (by decide) (by decide), hfr29 7 (by decide) (by decide), hfr28 7 (by decide) (by decide), hfr27 7 (by decide) (by decide), hfr26 7 (by decide) (by decide), hfr25 7 (by decide) (by decide), hfr24 7 (by decide) (by decide), hfr23 7 (by decide) (by decide), hfr22 7 (by decide) (by decide), hfr21 7 (by decide) (by decide), hfr20 7 (by decide) (by decide), hfr19 7 (by decide) (by decide), hfr18 7 (by decide) (by decide), hfr17 7 (by decide) (by decide), hfr16 7 (by decide) (by decide), hfr15 7 (by decide) (by decide), hfr14 7 (by decide) (by decide), hfr13 7 (by decide) (by decide), hfr12 7 (by decide) (by decide), hfr11 7 (by decide) (by decide), hfr10 7 (by decide) (by decide), hfr9 7 (by decide) (by decide), hfr8 7 (by decide) (by decide)]
  rw [hkeep7 7 (by decide) (by decide)] at hbut7
  have hr32u8 : r32.val[8]! = r9.val[8]! := by
    rw [hfr31 8 (by decide) (by decide), hfr30 8 (by decide) (by decide), hfr29 8 (by decide) (by decide), hfr28 8 (by decide) (by decide), hfr27 8 (by decide) (by decide), hfr26 8 (by decide) (by decide), hfr25 8 (by decide) (by decide), hfr24 8 (by decide) (by decide), hfr23 8 (by decide) (by decide), hfr22 8 (by decide) (by decide), hfr21 8 (by decide) (by decide), hfr20 8 (by decide) (by decide), hfr19 8 (by decide) (by decide), hfr18 8 (by decide) (by decide), hfr17 8 (by decide) (by decide), hfr16 8 (by decide) (by decide), hfr15 8 (by decide) (by decide), hfr14 8 (by decide) (by decide), hfr13 8 (by decide) (by decide), hfr12 8 (by decide) (by decide), hfr11 8 (by decide) (by decide), hfr10 8 (by decide) (by decide), hfr9 8 (by decide) (by decide)]
  rw [hkeep8 8 (by decide) (by decide)] at hbut8
  have hr32u9 : r32.val[9]! = r10.val[9]! := by
    rw [hfr31 9 (by decide) (by decide), hfr30 9 (by decide) (by decide), hfr29 9 (by decide) (by decide), hfr28 9 (by decide) (by decide), hfr27 9 (by decide) (by decide), hfr26 9 (by decide) (by decide), hfr25 9 (by decide) (by decide), hfr24 9 (by decide) (by decide), hfr23 9 (by decide) (by decide), hfr22 9 (by decide) (by decide), hfr21 9 (by decide) (by decide), hfr20 9 (by decide) (by decide), hfr19 9 (by decide) (by decide), hfr18 9 (by decide) (by decide), hfr17 9 (by decide) (by decide), hfr16 9 (by decide) (by decide), hfr15 9 (by decide) (by decide), hfr14 9 (by decide) (by decide), hfr13 9 (by decide) (by decide), hfr12 9 (by decide) (by decide), hfr11 9 (by decide) (by decide), hfr10 9 (by decide) (by decide)]
  rw [hkeep9 9 (by decide) (by decide)] at hbut9
  have hr32u10 : r32.val[10]! = r11.val[10]! := by
    rw [hfr31 10 (by decide) (by decide), hfr30 10 (by decide) (by decide), hfr29 10 (by decide) (by decide), hfr28 10 (by decide) (by decide), hfr27 10 (by decide) (by decide), hfr26 10 (by decide) (by decide), hfr25 10 (by decide) (by decide), hfr24 10 (by decide) (by decide), hfr23 10 (by decide) (by decide), hfr22 10 (by decide) (by decide), hfr21 10 (by decide) (by decide), hfr20 10 (by decide) (by decide), hfr19 10 (by decide) (by decide), hfr18 10 (by decide) (by decide), hfr17 10 (by decide) (by decide), hfr16 10 (by decide) (by decide), hfr15 10 (by decide) (by decide), hfr14 10 (by decide) (by decide), hfr13 10 (by decide) (by decide), hfr12 10 (by decide) (by decide), hfr11 10 (by decide) (by decide)]
  rw [hkeep10 10 (by decide) (by decide)] at hbut10
  have hr32u11 : r32.val[11]! = r12.val[11]! := by
    rw [hfr31 11 (by decide) (by decide), hfr30 11 (by decide) (by decide), hfr29 11 (by decide) (by decide), hfr28 11 (by decide) (by decide), hfr27 11 (by decide) (by decide), hfr26 11 (by decide) (by decide), hfr25 11 (by decide) (by decide), hfr24 11 (by decide) (by decide), hfr23 11 (by decide) (by decide), hfr22 11 (by decide) (by decide), hfr21 11 (by decide) (by decide), hfr20 11 (by decide) (by decide), hfr19 11 (by decide) (by decide), hfr18 11 (by decide) (by decide), hfr17 11 (by decide) (by decide), hfr16 11 (by decide) (by decide), hfr15 11 (by decide) (by decide), hfr14 11 (by decide) (by decide), hfr13 11 (by decide) (by decide), hfr12 11 (by decide) (by decide)]
  rw [hkeep11 11 (by decide) (by decide)] at hbut11
  have hr32u12 : r32.val[12]! = r13.val[12]! := by
    rw [hfr31 12 (by decide) (by decide), hfr30 12 (by decide) (by decide), hfr29 12 (by decide) (by decide), hfr28 12 (by decide) (by decide), hfr27 12 (by decide) (by decide), hfr26 12 (by decide) (by decide), hfr25 12 (by decide) (by decide), hfr24 12 (by decide) (by decide), hfr23 12 (by decide) (by decide), hfr22 12 (by decide) (by decide), hfr21 12 (by decide) (by decide), hfr20 12 (by decide) (by decide), hfr19 12 (by decide) (by decide), hfr18 12 (by decide) (by decide), hfr17 12 (by decide) (by decide), hfr16 12 (by decide) (by decide), hfr15 12 (by decide) (by decide), hfr14 12 (by decide) (by decide), hfr13 12 (by decide) (by decide)]
  rw [hkeep12 12 (by decide) (by decide)] at hbut12
  have hr32u13 : r32.val[13]! = r14.val[13]! := by
    rw [hfr31 13 (by decide) (by decide), hfr30 13 (by decide) (by decide), hfr29 13 (by decide) (by decide), hfr28 13 (by decide) (by decide), hfr27 13 (by decide) (by decide), hfr26 13 (by decide) (by decide), hfr25 13 (by decide) (by decide), hfr24 13 (by decide) (by decide), hfr23 13 (by decide) (by decide), hfr22 13 (by decide) (by decide), hfr21 13 (by decide) (by decide), hfr20 13 (by decide) (by decide), hfr19 13 (by decide) (by decide), hfr18 13 (by decide) (by decide), hfr17 13 (by decide) (by decide), hfr16 13 (by decide) (by decide), hfr15 13 (by decide) (by decide), hfr14 13 (by decide) (by decide)]
  rw [hkeep13 13 (by decide) (by decide)] at hbut13
  have hr32u14 : r32.val[14]! = r15.val[14]! := by
    rw [hfr31 14 (by decide) (by decide), hfr30 14 (by decide) (by decide), hfr29 14 (by decide) (by decide), hfr28 14 (by decide) (by decide), hfr27 14 (by decide) (by decide), hfr26 14 (by decide) (by decide), hfr25 14 (by decide) (by decide), hfr24 14 (by decide) (by decide), hfr23 14 (by decide) (by decide), hfr22 14 (by decide) (by decide), hfr21 14 (by decide) (by decide), hfr20 14 (by decide) (by decide), hfr19 14 (by decide) (by decide), hfr18 14 (by decide) (by decide), hfr17 14 (by decide) (by decide), hfr16 14 (by decide) (by decide), hfr15 14 (by decide) (by decide)]
  rw [hkeep14 14 (by decide) (by decide)] at hbut14
  have hr32u15 : r32.val[15]! = r16.val[15]! := by
    rw [hfr31 15 (by decide) (by decide), hfr30 15 (by decide) (by decide), hfr29 15 (by decide) (by decide), hfr28 15 (by decide) (by decide), hfr27 15 (by decide) (by decide), hfr26 15 (by decide) (by decide), hfr25 15 (by decide) (by decide), hfr24 15 (by decide) (by decide), hfr23 15 (by decide) (by decide), hfr22 15 (by decide) (by decide), hfr21 15 (by decide) (by decide), hfr20 15 (by decide) (by decide), hfr19 15 (by decide) (by decide), hfr18 15 (by decide) (by decide), hfr17 15 (by decide) (by decide), hfr16 15 (by decide) (by decide)]
  rw [hkeep15 15 (by decide) (by decide)] at hbut15
  have hr32u16 : r32.val[16]! = r17.val[16]! := by
    rw [hfr31 16 (by decide) (by decide), hfr30 16 (by decide) (by decide), hfr29 16 (by decide) (by decide), hfr28 16 (by decide) (by decide), hfr27 16 (by decide) (by decide), hfr26 16 (by decide) (by decide), hfr25 16 (by decide) (by decide), hfr24 16 (by decide) (by decide), hfr23 16 (by decide) (by decide), hfr22 16 (by decide) (by decide), hfr21 16 (by decide) (by decide), hfr20 16 (by decide) (by decide), hfr19 16 (by decide) (by decide), hfr18 16 (by decide) (by decide), hfr17 16 (by decide) (by decide)]
  rw [hkeep16 16 (by decide) (by decide)] at hbut16
  have hr32u17 : r32.val[17]! = r18.val[17]! := by
    rw [hfr31 17 (by decide) (by decide), hfr30 17 (by decide) (by decide), hfr29 17 (by decide) (by decide), hfr28 17 (by decide) (by decide), hfr27 17 (by decide) (by decide), hfr26 17 (by decide) (by decide), hfr25 17 (by decide) (by decide), hfr24 17 (by decide) (by decide), hfr23 17 (by decide) (by decide), hfr22 17 (by decide) (by decide), hfr21 17 (by decide) (by decide), hfr20 17 (by decide) (by decide), hfr19 17 (by decide) (by decide), hfr18 17 (by decide) (by decide)]
  rw [hkeep17 17 (by decide) (by decide)] at hbut17
  have hr32u18 : r32.val[18]! = r19.val[18]! := by
    rw [hfr31 18 (by decide) (by decide), hfr30 18 (by decide) (by decide), hfr29 18 (by decide) (by decide), hfr28 18 (by decide) (by decide), hfr27 18 (by decide) (by decide), hfr26 18 (by decide) (by decide), hfr25 18 (by decide) (by decide), hfr24 18 (by decide) (by decide), hfr23 18 (by decide) (by decide), hfr22 18 (by decide) (by decide), hfr21 18 (by decide) (by decide), hfr20 18 (by decide) (by decide), hfr19 18 (by decide) (by decide)]
  rw [hkeep18 18 (by decide) (by decide)] at hbut18
  have hr32u19 : r32.val[19]! = r20.val[19]! := by
    rw [hfr31 19 (by decide) (by decide), hfr30 19 (by decide) (by decide), hfr29 19 (by decide) (by decide), hfr28 19 (by decide) (by decide), hfr27 19 (by decide) (by decide), hfr26 19 (by decide) (by decide), hfr25 19 (by decide) (by decide), hfr24 19 (by decide) (by decide), hfr23 19 (by decide) (by decide), hfr22 19 (by decide) (by decide), hfr21 19 (by decide) (by decide), hfr20 19 (by decide) (by decide)]
  rw [hkeep19 19 (by decide) (by decide)] at hbut19
  have hr32u20 : r32.val[20]! = r21.val[20]! := by
    rw [hfr31 20 (by decide) (by decide), hfr30 20 (by decide) (by decide), hfr29 20 (by decide) (by decide), hfr28 20 (by decide) (by decide), hfr27 20 (by decide) (by decide), hfr26 20 (by decide) (by decide), hfr25 20 (by decide) (by decide), hfr24 20 (by decide) (by decide), hfr23 20 (by decide) (by decide), hfr22 20 (by decide) (by decide), hfr21 20 (by decide) (by decide)]
  rw [hkeep20 20 (by decide) (by decide)] at hbut20
  have hr32u21 : r32.val[21]! = r22.val[21]! := by
    rw [hfr31 21 (by decide) (by decide), hfr30 21 (by decide) (by decide), hfr29 21 (by decide) (by decide), hfr28 21 (by decide) (by decide), hfr27 21 (by decide) (by decide), hfr26 21 (by decide) (by decide), hfr25 21 (by decide) (by decide), hfr24 21 (by decide) (by decide), hfr23 21 (by decide) (by decide), hfr22 21 (by decide) (by decide)]
  rw [hkeep21 21 (by decide) (by decide)] at hbut21
  have hr32u22 : r32.val[22]! = r23.val[22]! := by
    rw [hfr31 22 (by decide) (by decide), hfr30 22 (by decide) (by decide), hfr29 22 (by decide) (by decide), hfr28 22 (by decide) (by decide), hfr27 22 (by decide) (by decide), hfr26 22 (by decide) (by decide), hfr25 22 (by decide) (by decide), hfr24 22 (by decide) (by decide), hfr23 22 (by decide) (by decide)]
  rw [hkeep22 22 (by decide) (by decide)] at hbut22
  have hr32u23 : r32.val[23]! = r24.val[23]! := by
    rw [hfr31 23 (by decide) (by decide), hfr30 23 (by decide) (by decide), hfr29 23 (by decide) (by decide), hfr28 23 (by decide) (by decide), hfr27 23 (by decide) (by decide), hfr26 23 (by decide) (by decide), hfr25 23 (by decide) (by decide), hfr24 23 (by decide) (by decide)]
  rw [hkeep23 23 (by decide) (by decide)] at hbut23
  have hr32u24 : r32.val[24]! = r25.val[24]! := by
    rw [hfr31 24 (by decide) (by decide), hfr30 24 (by decide) (by decide), hfr29 24 (by decide) (by decide), hfr28 24 (by decide) (by decide), hfr27 24 (by decide) (by decide), hfr26 24 (by decide) (by decide), hfr25 24 (by decide) (by decide)]
  rw [hkeep24 24 (by decide) (by decide)] at hbut24
  have hr32u25 : r32.val[25]! = r26.val[25]! := by
    rw [hfr31 25 (by decide) (by decide), hfr30 25 (by decide) (by decide), hfr29 25 (by decide) (by decide), hfr28 25 (by decide) (by decide), hfr27 25 (by decide) (by decide), hfr26 25 (by decide) (by decide)]
  rw [hkeep25 25 (by decide) (by decide)] at hbut25
  have hr32u26 : r32.val[26]! = r27.val[26]! := by
    rw [hfr31 26 (by decide) (by decide), hfr30 26 (by decide) (by decide), hfr29 26 (by decide) (by decide), hfr28 26 (by decide) (by decide), hfr27 26 (by decide) (by decide)]
  rw [hkeep26 26 (by decide) (by decide)] at hbut26
  have hr32u27 : r32.val[27]! = r28.val[27]! := by
    rw [hfr31 27 (by decide) (by decide), hfr30 27 (by decide) (by decide), hfr29 27 (by decide) (by decide), hfr28 27 (by decide) (by decide)]
  rw [hkeep27 27 (by decide) (by decide)] at hbut27
  have hr32u28 : r32.val[28]! = r29.val[28]! := by
    rw [hfr31 28 (by decide) (by decide), hfr30 28 (by decide) (by decide), hfr29 28 (by decide) (by decide)]
  rw [hkeep28 28 (by decide) (by decide)] at hbut28
  have hr32u29 : r32.val[29]! = r30.val[29]! := by
    rw [hfr31 29 (by decide) (by decide), hfr30 29 (by decide) (by decide)]
  rw [hkeep29 29 (by decide) (by decide)] at hbut29
  have hr32u30 : r32.val[30]! = r31.val[30]! := by
    rw [hfr31 30 (by decide) (by decide)]
  rw [hkeep30 30 (by decide) (by decide)] at hbut30
  have hr32u31 : r32.val[31]! = r32.val[31]! := by
    rfl
  rw [hkeep31 31 (by decide) (by decide)] at hbut31
  have hbfu0 : ∀ l, l < 8 →
      liftZ ((r32.val[0]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[0]!).values.val[l]!).val
            + liftZ ((re.val[0]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 0 + l / 4))) * (liftZ ((re.val[0]!).values.val[l - 2]!).val
            - liftZ ((re.val[0]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u0]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut0
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 0 + 2 / 4)) = (127 - 2 * 0) from by decide, zetaInv1_bridge0_0]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 0 + 3 / 4)) = (127 - 2 * 0) from by decide, zetaInv1_bridge0_0]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 0 + 6 / 4)) = (126 - 2 * 0) from by decide, zetaInv1_bridge1_0]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 0 + 7 / 4)) = (126 - 2 * 0) from by decide, zetaInv1_bridge1_0]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu1 : ∀ l, l < 8 →
      liftZ ((r32.val[1]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[1]!).values.val[l]!).val
            + liftZ ((re.val[1]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 1 + l / 4))) * (liftZ ((re.val[1]!).values.val[l - 2]!).val
            - liftZ ((re.val[1]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u1]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut1
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 1 + 2 / 4)) = (127 - 2 * 1) from by decide, zetaInv1_bridge0_1]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 1 + 3 / 4)) = (127 - 2 * 1) from by decide, zetaInv1_bridge0_1]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 1 + 6 / 4)) = (126 - 2 * 1) from by decide, zetaInv1_bridge1_1]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 1 + 7 / 4)) = (126 - 2 * 1) from by decide, zetaInv1_bridge1_1]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu2 : ∀ l, l < 8 →
      liftZ ((r32.val[2]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[2]!).values.val[l]!).val
            + liftZ ((re.val[2]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 2 + l / 4))) * (liftZ ((re.val[2]!).values.val[l - 2]!).val
            - liftZ ((re.val[2]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u2]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut2
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 2 + 2 / 4)) = (127 - 2 * 2) from by decide, zetaInv1_bridge0_2]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 2 + 3 / 4)) = (127 - 2 * 2) from by decide, zetaInv1_bridge0_2]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 2 + 6 / 4)) = (126 - 2 * 2) from by decide, zetaInv1_bridge1_2]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 2 + 7 / 4)) = (126 - 2 * 2) from by decide, zetaInv1_bridge1_2]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu3 : ∀ l, l < 8 →
      liftZ ((r32.val[3]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[3]!).values.val[l]!).val
            + liftZ ((re.val[3]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 3 + l / 4))) * (liftZ ((re.val[3]!).values.val[l - 2]!).val
            - liftZ ((re.val[3]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u3]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut3
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 3 + 2 / 4)) = (127 - 2 * 3) from by decide, zetaInv1_bridge0_3]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 3 + 3 / 4)) = (127 - 2 * 3) from by decide, zetaInv1_bridge0_3]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 3 + 6 / 4)) = (126 - 2 * 3) from by decide, zetaInv1_bridge1_3]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 3 + 7 / 4)) = (126 - 2 * 3) from by decide, zetaInv1_bridge1_3]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu4 : ∀ l, l < 8 →
      liftZ ((r32.val[4]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[4]!).values.val[l]!).val
            + liftZ ((re.val[4]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 4 + l / 4))) * (liftZ ((re.val[4]!).values.val[l - 2]!).val
            - liftZ ((re.val[4]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u4]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut4
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 4 + 2 / 4)) = (127 - 2 * 4) from by decide, zetaInv1_bridge0_4]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 4 + 3 / 4)) = (127 - 2 * 4) from by decide, zetaInv1_bridge0_4]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 4 + 6 / 4)) = (126 - 2 * 4) from by decide, zetaInv1_bridge1_4]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 4 + 7 / 4)) = (126 - 2 * 4) from by decide, zetaInv1_bridge1_4]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu5 : ∀ l, l < 8 →
      liftZ ((r32.val[5]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[5]!).values.val[l]!).val
            + liftZ ((re.val[5]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 5 + l / 4))) * (liftZ ((re.val[5]!).values.val[l - 2]!).val
            - liftZ ((re.val[5]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u5]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut5
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 5 + 2 / 4)) = (127 - 2 * 5) from by decide, zetaInv1_bridge0_5]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 5 + 3 / 4)) = (127 - 2 * 5) from by decide, zetaInv1_bridge0_5]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 5 + 6 / 4)) = (126 - 2 * 5) from by decide, zetaInv1_bridge1_5]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 5 + 7 / 4)) = (126 - 2 * 5) from by decide, zetaInv1_bridge1_5]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu6 : ∀ l, l < 8 →
      liftZ ((r32.val[6]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[6]!).values.val[l]!).val
            + liftZ ((re.val[6]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 6 + l / 4))) * (liftZ ((re.val[6]!).values.val[l - 2]!).val
            - liftZ ((re.val[6]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u6]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut6
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 6 + 2 / 4)) = (127 - 2 * 6) from by decide, zetaInv1_bridge0_6]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 6 + 3 / 4)) = (127 - 2 * 6) from by decide, zetaInv1_bridge0_6]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 6 + 6 / 4)) = (126 - 2 * 6) from by decide, zetaInv1_bridge1_6]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 6 + 7 / 4)) = (126 - 2 * 6) from by decide, zetaInv1_bridge1_6]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu7 : ∀ l, l < 8 →
      liftZ ((r32.val[7]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[7]!).values.val[l]!).val
            + liftZ ((re.val[7]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 7 + l / 4))) * (liftZ ((re.val[7]!).values.val[l - 2]!).val
            - liftZ ((re.val[7]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u7]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut7
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 7 + 2 / 4)) = (127 - 2 * 7) from by decide, zetaInv1_bridge0_7]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 7 + 3 / 4)) = (127 - 2 * 7) from by decide, zetaInv1_bridge0_7]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 7 + 6 / 4)) = (126 - 2 * 7) from by decide, zetaInv1_bridge1_7]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 7 + 7 / 4)) = (126 - 2 * 7) from by decide, zetaInv1_bridge1_7]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu8 : ∀ l, l < 8 →
      liftZ ((r32.val[8]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[8]!).values.val[l]!).val
            + liftZ ((re.val[8]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 8 + l / 4))) * (liftZ ((re.val[8]!).values.val[l - 2]!).val
            - liftZ ((re.val[8]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u8]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut8
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 8 + 2 / 4)) = (127 - 2 * 8) from by decide, zetaInv1_bridge0_8]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 8 + 3 / 4)) = (127 - 2 * 8) from by decide, zetaInv1_bridge0_8]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 8 + 6 / 4)) = (126 - 2 * 8) from by decide, zetaInv1_bridge1_8]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 8 + 7 / 4)) = (126 - 2 * 8) from by decide, zetaInv1_bridge1_8]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu9 : ∀ l, l < 8 →
      liftZ ((r32.val[9]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[9]!).values.val[l]!).val
            + liftZ ((re.val[9]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 9 + l / 4))) * (liftZ ((re.val[9]!).values.val[l - 2]!).val
            - liftZ ((re.val[9]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u9]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut9
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 9 + 2 / 4)) = (127 - 2 * 9) from by decide, zetaInv1_bridge0_9]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 9 + 3 / 4)) = (127 - 2 * 9) from by decide, zetaInv1_bridge0_9]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 9 + 6 / 4)) = (126 - 2 * 9) from by decide, zetaInv1_bridge1_9]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 9 + 7 / 4)) = (126 - 2 * 9) from by decide, zetaInv1_bridge1_9]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu10 : ∀ l, l < 8 →
      liftZ ((r32.val[10]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[10]!).values.val[l]!).val
            + liftZ ((re.val[10]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 10 + l / 4))) * (liftZ ((re.val[10]!).values.val[l - 2]!).val
            - liftZ ((re.val[10]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u10]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut10
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 10 + 2 / 4)) = (127 - 2 * 10) from by decide, zetaInv1_bridge0_10]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 10 + 3 / 4)) = (127 - 2 * 10) from by decide, zetaInv1_bridge0_10]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 10 + 6 / 4)) = (126 - 2 * 10) from by decide, zetaInv1_bridge1_10]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 10 + 7 / 4)) = (126 - 2 * 10) from by decide, zetaInv1_bridge1_10]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu11 : ∀ l, l < 8 →
      liftZ ((r32.val[11]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[11]!).values.val[l]!).val
            + liftZ ((re.val[11]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 11 + l / 4))) * (liftZ ((re.val[11]!).values.val[l - 2]!).val
            - liftZ ((re.val[11]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u11]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut11
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 11 + 2 / 4)) = (127 - 2 * 11) from by decide, zetaInv1_bridge0_11]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 11 + 3 / 4)) = (127 - 2 * 11) from by decide, zetaInv1_bridge0_11]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 11 + 6 / 4)) = (126 - 2 * 11) from by decide, zetaInv1_bridge1_11]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 11 + 7 / 4)) = (126 - 2 * 11) from by decide, zetaInv1_bridge1_11]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu12 : ∀ l, l < 8 →
      liftZ ((r32.val[12]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[12]!).values.val[l]!).val
            + liftZ ((re.val[12]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 12 + l / 4))) * (liftZ ((re.val[12]!).values.val[l - 2]!).val
            - liftZ ((re.val[12]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u12]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut12
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 12 + 2 / 4)) = (127 - 2 * 12) from by decide, zetaInv1_bridge0_12]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 12 + 3 / 4)) = (127 - 2 * 12) from by decide, zetaInv1_bridge0_12]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 12 + 6 / 4)) = (126 - 2 * 12) from by decide, zetaInv1_bridge1_12]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 12 + 7 / 4)) = (126 - 2 * 12) from by decide, zetaInv1_bridge1_12]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu13 : ∀ l, l < 8 →
      liftZ ((r32.val[13]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[13]!).values.val[l]!).val
            + liftZ ((re.val[13]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 13 + l / 4))) * (liftZ ((re.val[13]!).values.val[l - 2]!).val
            - liftZ ((re.val[13]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u13]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut13
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 13 + 2 / 4)) = (127 - 2 * 13) from by decide, zetaInv1_bridge0_13]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 13 + 3 / 4)) = (127 - 2 * 13) from by decide, zetaInv1_bridge0_13]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 13 + 6 / 4)) = (126 - 2 * 13) from by decide, zetaInv1_bridge1_13]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 13 + 7 / 4)) = (126 - 2 * 13) from by decide, zetaInv1_bridge1_13]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu14 : ∀ l, l < 8 →
      liftZ ((r32.val[14]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[14]!).values.val[l]!).val
            + liftZ ((re.val[14]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 14 + l / 4))) * (liftZ ((re.val[14]!).values.val[l - 2]!).val
            - liftZ ((re.val[14]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u14]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut14
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 14 + 2 / 4)) = (127 - 2 * 14) from by decide, zetaInv1_bridge0_14]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 14 + 3 / 4)) = (127 - 2 * 14) from by decide, zetaInv1_bridge0_14]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 14 + 6 / 4)) = (126 - 2 * 14) from by decide, zetaInv1_bridge1_14]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 14 + 7 / 4)) = (126 - 2 * 14) from by decide, zetaInv1_bridge1_14]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu15 : ∀ l, l < 8 →
      liftZ ((r32.val[15]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[15]!).values.val[l]!).val
            + liftZ ((re.val[15]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 15 + l / 4))) * (liftZ ((re.val[15]!).values.val[l - 2]!).val
            - liftZ ((re.val[15]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u15]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut15
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 15 + 2 / 4)) = (127 - 2 * 15) from by decide, zetaInv1_bridge0_15]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 15 + 3 / 4)) = (127 - 2 * 15) from by decide, zetaInv1_bridge0_15]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 15 + 6 / 4)) = (126 - 2 * 15) from by decide, zetaInv1_bridge1_15]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 15 + 7 / 4)) = (126 - 2 * 15) from by decide, zetaInv1_bridge1_15]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu16 : ∀ l, l < 8 →
      liftZ ((r32.val[16]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[16]!).values.val[l]!).val
            + liftZ ((re.val[16]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 16 + l / 4))) * (liftZ ((re.val[16]!).values.val[l - 2]!).val
            - liftZ ((re.val[16]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u16]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut16
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 16 + 2 / 4)) = (127 - 2 * 16) from by decide, zetaInv1_bridge0_16]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 16 + 3 / 4)) = (127 - 2 * 16) from by decide, zetaInv1_bridge0_16]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 16 + 6 / 4)) = (126 - 2 * 16) from by decide, zetaInv1_bridge1_16]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 16 + 7 / 4)) = (126 - 2 * 16) from by decide, zetaInv1_bridge1_16]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu17 : ∀ l, l < 8 →
      liftZ ((r32.val[17]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[17]!).values.val[l]!).val
            + liftZ ((re.val[17]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 17 + l / 4))) * (liftZ ((re.val[17]!).values.val[l - 2]!).val
            - liftZ ((re.val[17]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u17]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut17
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 17 + 2 / 4)) = (127 - 2 * 17) from by decide, zetaInv1_bridge0_17]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 17 + 3 / 4)) = (127 - 2 * 17) from by decide, zetaInv1_bridge0_17]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 17 + 6 / 4)) = (126 - 2 * 17) from by decide, zetaInv1_bridge1_17]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 17 + 7 / 4)) = (126 - 2 * 17) from by decide, zetaInv1_bridge1_17]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu18 : ∀ l, l < 8 →
      liftZ ((r32.val[18]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[18]!).values.val[l]!).val
            + liftZ ((re.val[18]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 18 + l / 4))) * (liftZ ((re.val[18]!).values.val[l - 2]!).val
            - liftZ ((re.val[18]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u18]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut18
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 18 + 2 / 4)) = (127 - 2 * 18) from by decide, zetaInv1_bridge0_18]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 18 + 3 / 4)) = (127 - 2 * 18) from by decide, zetaInv1_bridge0_18]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 18 + 6 / 4)) = (126 - 2 * 18) from by decide, zetaInv1_bridge1_18]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 18 + 7 / 4)) = (126 - 2 * 18) from by decide, zetaInv1_bridge1_18]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu19 : ∀ l, l < 8 →
      liftZ ((r32.val[19]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[19]!).values.val[l]!).val
            + liftZ ((re.val[19]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 19 + l / 4))) * (liftZ ((re.val[19]!).values.val[l - 2]!).val
            - liftZ ((re.val[19]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u19]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut19
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 19 + 2 / 4)) = (127 - 2 * 19) from by decide, zetaInv1_bridge0_19]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 19 + 3 / 4)) = (127 - 2 * 19) from by decide, zetaInv1_bridge0_19]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 19 + 6 / 4)) = (126 - 2 * 19) from by decide, zetaInv1_bridge1_19]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 19 + 7 / 4)) = (126 - 2 * 19) from by decide, zetaInv1_bridge1_19]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu20 : ∀ l, l < 8 →
      liftZ ((r32.val[20]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[20]!).values.val[l]!).val
            + liftZ ((re.val[20]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 20 + l / 4))) * (liftZ ((re.val[20]!).values.val[l - 2]!).val
            - liftZ ((re.val[20]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u20]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut20
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 20 + 2 / 4)) = (127 - 2 * 20) from by decide, zetaInv1_bridge0_20]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 20 + 3 / 4)) = (127 - 2 * 20) from by decide, zetaInv1_bridge0_20]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 20 + 6 / 4)) = (126 - 2 * 20) from by decide, zetaInv1_bridge1_20]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 20 + 7 / 4)) = (126 - 2 * 20) from by decide, zetaInv1_bridge1_20]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu21 : ∀ l, l < 8 →
      liftZ ((r32.val[21]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[21]!).values.val[l]!).val
            + liftZ ((re.val[21]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 21 + l / 4))) * (liftZ ((re.val[21]!).values.val[l - 2]!).val
            - liftZ ((re.val[21]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u21]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut21
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 21 + 2 / 4)) = (127 - 2 * 21) from by decide, zetaInv1_bridge0_21]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 21 + 3 / 4)) = (127 - 2 * 21) from by decide, zetaInv1_bridge0_21]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 21 + 6 / 4)) = (126 - 2 * 21) from by decide, zetaInv1_bridge1_21]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 21 + 7 / 4)) = (126 - 2 * 21) from by decide, zetaInv1_bridge1_21]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu22 : ∀ l, l < 8 →
      liftZ ((r32.val[22]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[22]!).values.val[l]!).val
            + liftZ ((re.val[22]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 22 + l / 4))) * (liftZ ((re.val[22]!).values.val[l - 2]!).val
            - liftZ ((re.val[22]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u22]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut22
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 22 + 2 / 4)) = (127 - 2 * 22) from by decide, zetaInv1_bridge0_22]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 22 + 3 / 4)) = (127 - 2 * 22) from by decide, zetaInv1_bridge0_22]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 22 + 6 / 4)) = (126 - 2 * 22) from by decide, zetaInv1_bridge1_22]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 22 + 7 / 4)) = (126 - 2 * 22) from by decide, zetaInv1_bridge1_22]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu23 : ∀ l, l < 8 →
      liftZ ((r32.val[23]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[23]!).values.val[l]!).val
            + liftZ ((re.val[23]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 23 + l / 4))) * (liftZ ((re.val[23]!).values.val[l - 2]!).val
            - liftZ ((re.val[23]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u23]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut23
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 23 + 2 / 4)) = (127 - 2 * 23) from by decide, zetaInv1_bridge0_23]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 23 + 3 / 4)) = (127 - 2 * 23) from by decide, zetaInv1_bridge0_23]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 23 + 6 / 4)) = (126 - 2 * 23) from by decide, zetaInv1_bridge1_23]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 23 + 7 / 4)) = (126 - 2 * 23) from by decide, zetaInv1_bridge1_23]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu24 : ∀ l, l < 8 →
      liftZ ((r32.val[24]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[24]!).values.val[l]!).val
            + liftZ ((re.val[24]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 24 + l / 4))) * (liftZ ((re.val[24]!).values.val[l - 2]!).val
            - liftZ ((re.val[24]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u24]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut24
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 24 + 2 / 4)) = (127 - 2 * 24) from by decide, zetaInv1_bridge0_24]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 24 + 3 / 4)) = (127 - 2 * 24) from by decide, zetaInv1_bridge0_24]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 24 + 6 / 4)) = (126 - 2 * 24) from by decide, zetaInv1_bridge1_24]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 24 + 7 / 4)) = (126 - 2 * 24) from by decide, zetaInv1_bridge1_24]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu25 : ∀ l, l < 8 →
      liftZ ((r32.val[25]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[25]!).values.val[l]!).val
            + liftZ ((re.val[25]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 25 + l / 4))) * (liftZ ((re.val[25]!).values.val[l - 2]!).val
            - liftZ ((re.val[25]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u25]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut25
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 25 + 2 / 4)) = (127 - 2 * 25) from by decide, zetaInv1_bridge0_25]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 25 + 3 / 4)) = (127 - 2 * 25) from by decide, zetaInv1_bridge0_25]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 25 + 6 / 4)) = (126 - 2 * 25) from by decide, zetaInv1_bridge1_25]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 25 + 7 / 4)) = (126 - 2 * 25) from by decide, zetaInv1_bridge1_25]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu26 : ∀ l, l < 8 →
      liftZ ((r32.val[26]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[26]!).values.val[l]!).val
            + liftZ ((re.val[26]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 26 + l / 4))) * (liftZ ((re.val[26]!).values.val[l - 2]!).val
            - liftZ ((re.val[26]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u26]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut26
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 26 + 2 / 4)) = (127 - 2 * 26) from by decide, zetaInv1_bridge0_26]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 26 + 3 / 4)) = (127 - 2 * 26) from by decide, zetaInv1_bridge0_26]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 26 + 6 / 4)) = (126 - 2 * 26) from by decide, zetaInv1_bridge1_26]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 26 + 7 / 4)) = (126 - 2 * 26) from by decide, zetaInv1_bridge1_26]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu27 : ∀ l, l < 8 →
      liftZ ((r32.val[27]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[27]!).values.val[l]!).val
            + liftZ ((re.val[27]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 27 + l / 4))) * (liftZ ((re.val[27]!).values.val[l - 2]!).val
            - liftZ ((re.val[27]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u27]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut27
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 27 + 2 / 4)) = (127 - 2 * 27) from by decide, zetaInv1_bridge0_27]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 27 + 3 / 4)) = (127 - 2 * 27) from by decide, zetaInv1_bridge0_27]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 27 + 6 / 4)) = (126 - 2 * 27) from by decide, zetaInv1_bridge1_27]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 27 + 7 / 4)) = (126 - 2 * 27) from by decide, zetaInv1_bridge1_27]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu28 : ∀ l, l < 8 →
      liftZ ((r32.val[28]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[28]!).values.val[l]!).val
            + liftZ ((re.val[28]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 28 + l / 4))) * (liftZ ((re.val[28]!).values.val[l - 2]!).val
            - liftZ ((re.val[28]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u28]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut28
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 28 + 2 / 4)) = (127 - 2 * 28) from by decide, zetaInv1_bridge0_28]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 28 + 3 / 4)) = (127 - 2 * 28) from by decide, zetaInv1_bridge0_28]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 28 + 6 / 4)) = (126 - 2 * 28) from by decide, zetaInv1_bridge1_28]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 28 + 7 / 4)) = (126 - 2 * 28) from by decide, zetaInv1_bridge1_28]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu29 : ∀ l, l < 8 →
      liftZ ((r32.val[29]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[29]!).values.val[l]!).val
            + liftZ ((re.val[29]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 29 + l / 4))) * (liftZ ((re.val[29]!).values.val[l - 2]!).val
            - liftZ ((re.val[29]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u29]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut29
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 29 + 2 / 4)) = (127 - 2 * 29) from by decide, zetaInv1_bridge0_29]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 29 + 3 / 4)) = (127 - 2 * 29) from by decide, zetaInv1_bridge0_29]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 29 + 6 / 4)) = (126 - 2 * 29) from by decide, zetaInv1_bridge1_29]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 29 + 7 / 4)) = (126 - 2 * 29) from by decide, zetaInv1_bridge1_29]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu30 : ∀ l, l < 8 →
      liftZ ((r32.val[30]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[30]!).values.val[l]!).val
            + liftZ ((re.val[30]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 30 + l / 4))) * (liftZ ((re.val[30]!).values.val[l - 2]!).val
            - liftZ ((re.val[30]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u30]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut30
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 30 + 2 / 4)) = (127 - 2 * 30) from by decide, zetaInv1_bridge0_30]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 30 + 3 / 4)) = (127 - 2 * 30) from by decide, zetaInv1_bridge0_30]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 30 + 6 / 4)) = (126 - 2 * 30) from by decide, zetaInv1_bridge1_30]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 30 + 7 / 4)) = (126 - 2 * 30) from by decide, zetaInv1_bridge1_30]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu31 : ∀ l, l < 8 →
      liftZ ((r32.val[31]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[31]!).values.val[l]!).val
            + liftZ ((re.val[31]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * 31 + l / 4))) * (liftZ ((re.val[31]!).values.val[l - 2]!).val
            - liftZ ((re.val[31]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u31]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut31
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_pos (by decide), b1]
    | 2, _ => rw [if_neg (by decide), b2, show (127 - (2 * 31 + 2 / 4)) = (127 - 2 * 31) from by decide, zetaInv1_bridge0_31]; ring
    | 3, _ => rw [if_neg (by decide), b3, show (127 - (2 * 31 + 3 / 4)) = (127 - 2 * 31) from by decide, zetaInv1_bridge0_31]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_pos (by decide), b5]
    | 6, _ => rw [if_neg (by decide), b6, show (127 - (2 * 31 + 6 / 4)) = (126 - 2 * 31) from by decide, zetaInv1_bridge1_31]; ring
    | 7, _ => rw [if_neg (by decide), b7, show (127 - (2 * 31 + 7 / 4)) = (126 - 2 * 31) from by decide, zetaInv1_bridge1_31]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbf : ∀ u, u < 32 → ∀ l, l < 8 →
      liftZ ((r32.val[u]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[u]!).values.val[l]!).val
            + liftZ ((re.val[u]!).values.val[l + 2]!).val
         else (- zeta (127 - (2 * u + l / 4))) * (liftZ ((re.val[u]!).values.val[l - 2]!).val
            - liftZ ((re.val[u]!).values.val[l]!).val)) := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbfu0 l hl
    | 1, _ => exact hbfu1 l hl
    | 2, _ => exact hbfu2 l hl
    | 3, _ => exact hbfu3 l hl
    | 4, _ => exact hbfu4 l hl
    | 5, _ => exact hbfu5 l hl
    | 6, _ => exact hbfu6 l hl
    | 7, _ => exact hbfu7 l hl
    | 8, _ => exact hbfu8 l hl
    | 9, _ => exact hbfu9 l hl
    | 10, _ => exact hbfu10 l hl
    | 11, _ => exact hbfu11 l hl
    | 12, _ => exact hbfu12 l hl
    | 13, _ => exact hbfu13 l hl
    | 14, _ => exact hbfu14 l hl
    | 15, _ => exact hbfu15 l hl
    | 16, _ => exact hbfu16 l hl
    | 17, _ => exact hbfu17 l hl
    | 18, _ => exact hbfu18 l hl
    | 19, _ => exact hbfu19 l hl
    | 20, _ => exact hbfu20 l hl
    | 21, _ => exact hbfu21 l hl
    | 22, _ => exact hbfu22 l hl
    | 23, _ => exact hbfu23 l hl
    | 24, _ => exact hbfu24 l hl
    | 25, _ => exact hbfu25 l hl
    | 26, _ => exact hbfu26 l hl
    | 27, _ => exact hbfu27 l hl
    | 28, _ => exact hbfu28 l hl
    | 29, _ => exact hbfu29 l hl
    | 30, _ => exact hbfu30 l hl
    | 31, _ => exact hbfu31 l hl
    | (n + 32), h => exact absurd h (by omega)
  have hbnd0 : ∀ l, l < 8 → ((r32.val[0]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u0]; exact hbd0 l hl
  have hbnd1 : ∀ l, l < 8 → ((r32.val[1]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u1]; exact hbd1 l hl
  have hbnd2 : ∀ l, l < 8 → ((r32.val[2]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u2]; exact hbd2 l hl
  have hbnd3 : ∀ l, l < 8 → ((r32.val[3]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u3]; exact hbd3 l hl
  have hbnd4 : ∀ l, l < 8 → ((r32.val[4]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u4]; exact hbd4 l hl
  have hbnd5 : ∀ l, l < 8 → ((r32.val[5]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u5]; exact hbd5 l hl
  have hbnd6 : ∀ l, l < 8 → ((r32.val[6]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u6]; exact hbd6 l hl
  have hbnd7 : ∀ l, l < 8 → ((r32.val[7]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u7]; exact hbd7 l hl
  have hbnd8 : ∀ l, l < 8 → ((r32.val[8]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u8]; exact hbd8 l hl
  have hbnd9 : ∀ l, l < 8 → ((r32.val[9]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u9]; exact hbd9 l hl
  have hbnd10 : ∀ l, l < 8 → ((r32.val[10]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u10]; exact hbd10 l hl
  have hbnd11 : ∀ l, l < 8 → ((r32.val[11]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u11]; exact hbd11 l hl
  have hbnd12 : ∀ l, l < 8 → ((r32.val[12]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u12]; exact hbd12 l hl
  have hbnd13 : ∀ l, l < 8 → ((r32.val[13]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u13]; exact hbd13 l hl
  have hbnd14 : ∀ l, l < 8 → ((r32.val[14]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u14]; exact hbd14 l hl
  have hbnd15 : ∀ l, l < 8 → ((r32.val[15]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u15]; exact hbd15 l hl
  have hbnd16 : ∀ l, l < 8 → ((r32.val[16]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u16]; exact hbd16 l hl
  have hbnd17 : ∀ l, l < 8 → ((r32.val[17]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u17]; exact hbd17 l hl
  have hbnd18 : ∀ l, l < 8 → ((r32.val[18]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u18]; exact hbd18 l hl
  have hbnd19 : ∀ l, l < 8 → ((r32.val[19]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u19]; exact hbd19 l hl
  have hbnd20 : ∀ l, l < 8 → ((r32.val[20]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u20]; exact hbd20 l hl
  have hbnd21 : ∀ l, l < 8 → ((r32.val[21]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u21]; exact hbd21 l hl
  have hbnd22 : ∀ l, l < 8 → ((r32.val[22]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u22]; exact hbd22 l hl
  have hbnd23 : ∀ l, l < 8 → ((r32.val[23]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u23]; exact hbd23 l hl
  have hbnd24 : ∀ l, l < 8 → ((r32.val[24]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u24]; exact hbd24 l hl
  have hbnd25 : ∀ l, l < 8 → ((r32.val[25]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u25]; exact hbd25 l hl
  have hbnd26 : ∀ l, l < 8 → ((r32.val[26]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u26]; exact hbd26 l hl
  have hbnd27 : ∀ l, l < 8 → ((r32.val[27]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u27]; exact hbd27 l hl
  have hbnd28 : ∀ l, l < 8 → ((r32.val[28]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u28]; exact hbd28 l hl
  have hbnd29 : ∀ l, l < 8 → ((r32.val[29]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u29]; exact hbd29 l hl
  have hbnd30 : ∀ l, l < 8 → ((r32.val[30]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u30]; exact hbd30 l hl
  have hbnd31 : ∀ l, l < 8 → ((r32.val[31]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u31]; exact hbd31 l hl
  have hbnd : ∀ u, u < 32 → ∀ l, l < 8 →
      ((r32.val[u]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbnd0 l hl
    | 1, _ => exact hbnd1 l hl
    | 2, _ => exact hbnd2 l hl
    | 3, _ => exact hbnd3 l hl
    | 4, _ => exact hbnd4 l hl
    | 5, _ => exact hbnd5 l hl
    | 6, _ => exact hbnd6 l hl
    | 7, _ => exact hbnd7 l hl
    | 8, _ => exact hbnd8 l hl
    | 9, _ => exact hbnd9 l hl
    | 10, _ => exact hbnd10 l hl
    | 11, _ => exact hbnd11 l hl
    | 12, _ => exact hbnd12 l hl
    | 13, _ => exact hbnd13 l hl
    | 14, _ => exact hbnd14 l hl
    | 15, _ => exact hbnd15 l hl
    | 16, _ => exact hbnd16 l hl
    | 17, _ => exact hbnd17 l hl
    | 18, _ => exact hbnd18 l hl
    | 19, _ => exact hbnd19 l hl
    | 20, _ => exact hbnd20 l hl
    | 21, _ => exact hbnd21 l hl
    | 22, _ => exact hbnd22 l hl
    | 23, _ => exact hbnd23 l hl
    | 24, _ => exact hbnd24 l hl
    | 25, _ => exact hbnd25 l hl
    | 26, _ => exact hbnd26 l hl
    | 27, _ => exact hbnd27 l hl
    | 28, _ => exact hbnd28 l hl
    | 29, _ => exact hbnd29 l hl
    | 30, _ => exact hbnd30 l hl
    | 31, _ => exact hbnd31 l hl
    | (n + 32), h => exact absurd h (by omega)
  refine ⟨?_, ?_⟩
  · unfold lift_units
    apply Pure.build_congr
    intro i hi
    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub]
    have huu : i / 8 < 32 := by omega
    have hll : i % 8 < 8 := by omega
    have hb := hbf (i / 8) huu (i % 8) hll
    by_cases hlt : i % 4 < 2
    · have hcond : i % 8 % 4 < 2 := by omega
      rw [if_pos hlt]
      rw [if_pos hcond] at hb
      have hdiv : (i + 2) / 8 = i / 8 := by omega
      have hmod : (i + 2) % 8 = i % 8 + 2 := by omega
      have hidx2 : i + 2 < 256 := by omega
      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 2) hidx2, hdiv, hmod]
      exact hb
    · have hcond : ¬ i % 8 % 4 < 2 := by omega
      rw [if_neg hlt]
      rw [if_neg hcond] at hb
      have hdiv : (i - 2) / 8 = i / 8 := by omega
      have hmod : (i - 2) % 8 = i % 8 - 2 := by omega
      have hidx2 : i - 2 < 256 := by omega
      have hz : 127 - (2 * (i / 8) + i % 8 / 4) = 127 - i / 4 := by omega
      rw [Pure.build_getElem _ (i - 2) hidx2, Pure.build_getElem _ i hi, hdiv, hmod]
      rw [hz] at hb
      exact hb
  · exact hbnd




/-! ### Layer-0 within-unit inverse driver `invert_ntt_at_layer_0_fc`.

    `invert_ntt_at_layer_0` chains 32 `round` calls; round `u` reads unit `u`,
    applies the per-unit inverse butterfly `simd_unit_invert_ntt_at_layer_0 _ Z0 Z1 Z2 Z3`
    (adjacent pairs (0,1)(2,3)(4,5)(6,7); even lane = SUM, odd lane = mont-mul
    difference with `zeta{p}`), and writes unit `u` back (touching ONLY unit `u`).
    The lifted result equals `Pure.intt_layer (lift_units re) 0` (`len = 1`, `k = 255`;
    within each unit the lane split is at `l % 2 < 1`, hi-lane zeta index
    `255 - (4u + l/2)`). Uniform bound `2·B + 2^24`. Faithful clone of `roundInv2_fc`
    with the L0 leaf (4 zetas) + the forward-L0 within-unit lane-split arithmetic. -/

set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_0 :
    liftZ ((1976782#i32 : Std.I32).val : Int) = zeta (255 - 4 * 0 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_0 :
    liftZ (((-846154)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 0 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_0 :
    liftZ ((1400424#i32 : Std.I32).val : Int) = zeta (255 - 4 * 0 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_0 :
    liftZ ((3937738#i32 : Std.I32).val : Int) = zeta (255 - 4 * 0 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_1 :
    liftZ (((-1362209)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 1 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_1 :
    liftZ (((-48306)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 1 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_1 :
    liftZ ((3919660#i32 : Std.I32).val : Int) = zeta (255 - 4 * 1 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_1 :
    liftZ (((-554416)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 1 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_2 :
    liftZ (((-3545687)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 2 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_2 :
    liftZ ((1612842#i32 : Std.I32).val : Int) = zeta (255 - 4 * 2 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_2 :
    liftZ (((-976891)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 2 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_2 :
    liftZ ((183443#i32 : Std.I32).val : Int) = zeta (255 - 4 * 2 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_3 :
    liftZ (((-2286327)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 3 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_3 :
    liftZ (((-420899)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 3 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_3 :
    liftZ (((-2235985)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 3 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_3 :
    liftZ (((-2939036)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 3 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_4 :
    liftZ (((-3833893)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 4 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_4 :
    liftZ (((-260646)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 4 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_4 :
    liftZ (((-1104333)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 4 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_4 :
    liftZ (((-1667432)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 4 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_5 :
    liftZ ((1910376#i32 : Std.I32).val : Int) = zeta (255 - 4 * 5 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_5 :
    liftZ (((-1803090)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 5 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_5 :
    liftZ ((1723600#i32 : Std.I32).val : Int) = zeta (255 - 4 * 5 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_5 :
    liftZ (((-426683)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 5 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_6 :
    liftZ ((472078#i32 : Std.I32).val : Int) = zeta (255 - 4 * 6 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_6 :
    liftZ ((1717735#i32 : Std.I32).val : Int) = zeta (255 - 4 * 6 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_6 :
    liftZ (((-975884)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 6 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_6 :
    liftZ ((2213111#i32 : Std.I32).val : Int) = zeta (255 - 4 * 6 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_7 :
    liftZ ((269760#i32 : Std.I32).val : Int) = zeta (255 - 4 * 7 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_7 :
    liftZ ((3866901#i32 : Std.I32).val : Int) = zeta (255 - 4 * 7 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_7 :
    liftZ ((3523897#i32 : Std.I32).val : Int) = zeta (255 - 4 * 7 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_7 :
    liftZ (((-3038916)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 7 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_8 :
    liftZ (((-1799107)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 8 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_8 :
    liftZ (((-3694233)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 8 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_8 :
    liftZ ((1652634#i32 : Std.I32).val : Int) = zeta (255 - 4 * 8 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_8 :
    liftZ ((810149#i32 : Std.I32).val : Int) = zeta (255 - 4 * 8 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_9 :
    liftZ ((3014001#i32 : Std.I32).val : Int) = zeta (255 - 4 * 9 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_9 :
    liftZ ((1616392#i32 : Std.I32).val : Int) = zeta (255 - 4 * 9 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_9 :
    liftZ ((162844#i32 : Std.I32).val : Int) = zeta (255 - 4 * 9 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_9 :
    liftZ (((-3183426)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 9 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_10 :
    liftZ (((-1207385)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 10 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_10 :
    liftZ ((185531#i32 : Std.I32).val : Int) = zeta (255 - 4 * 10 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_10 :
    liftZ ((3369112#i32 : Std.I32).val : Int) = zeta (255 - 4 * 10 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_10 :
    liftZ ((1957272#i32 : Std.I32).val : Int) = zeta (255 - 4 * 10 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_11 :
    liftZ (((-164721)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 11 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_11 :
    liftZ ((2454455#i32 : Std.I32).val : Int) = zeta (255 - 4 * 11 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_11 :
    liftZ ((2432395#i32 : Std.I32).val : Int) = zeta (255 - 4 * 11 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_11 :
    liftZ (((-2013608)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 11 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_12 :
    liftZ (((-3776993)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 12 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_12 :
    liftZ ((594136#i32 : Std.I32).val : Int) = zeta (255 - 4 * 12 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_12 :
    liftZ (((-3724270)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 12 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_12 :
    liftZ (((-2584293)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 12 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_13 :
    liftZ (((-1846953)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 13 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_13 :
    liftZ (((-1671176)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 13 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_13 :
    liftZ (((-2831860)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 13 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_13 :
    liftZ (((-542412)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 13 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_14 :
    liftZ ((3406031#i32 : Std.I32).val : Int) = zeta (255 - 4 * 14 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_14 :
    liftZ ((2235880#i32 : Std.I32).val : Int) = zeta (255 - 4 * 14 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_14 :
    liftZ ((777191#i32 : Std.I32).val : Int) = zeta (255 - 4 * 14 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_14 :
    liftZ ((1500165#i32 : Std.I32).val : Int) = zeta (255 - 4 * 14 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_15 :
    liftZ (((-1374803)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 15 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_15 :
    liftZ (((-2546312)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 15 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_15 :
    liftZ ((1917081#i32 : Std.I32).val : Int) = zeta (255 - 4 * 15 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_15 :
    liftZ (((-1279661)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 15 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_16 :
    liftZ (((-1962642)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 16 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_16 :
    liftZ ((3306115#i32 : Std.I32).val : Int) = zeta (255 - 4 * 16 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_16 :
    liftZ ((1312455#i32 : Std.I32).val : Int) = zeta (255 - 4 * 16 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_16 :
    liftZ (((-451100)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 16 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_17 :
    liftZ (((-1430225)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 17 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_17 :
    liftZ (((-3318210)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 17 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_17 :
    liftZ ((1237275#i32 : Std.I32).val : Int) = zeta (255 - 4 * 17 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_17 :
    liftZ (((-1333058)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 17 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_18 :
    liftZ (((-1050970)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 18 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_18 :
    liftZ ((1903435#i32 : Std.I32).val : Int) = zeta (255 - 4 * 18 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_18 :
    liftZ ((1869119#i32 : Std.I32).val : Int) = zeta (255 - 4 * 18 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_18 :
    liftZ (((-2994039)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 18 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_19 :
    liftZ (((-3548272)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 19 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_19 :
    liftZ ((2635921#i32 : Std.I32).val : Int) = zeta (255 - 4 * 19 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_19 :
    liftZ ((1250494#i32 : Std.I32).val : Int) = zeta (255 - 4 * 19 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_19 :
    liftZ (((-3767016)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 19 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_20 :
    liftZ ((1595974#i32 : Std.I32).val : Int) = zeta (255 - 4 * 20 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_20 :
    liftZ ((2486353#i32 : Std.I32).val : Int) = zeta (255 - 4 * 20 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_20 :
    liftZ ((1247620#i32 : Std.I32).val : Int) = zeta (255 - 4 * 20 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_20 :
    liftZ ((4055324#i32 : Std.I32).val : Int) = zeta (255 - 4 * 20 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_21 :
    liftZ ((1265009#i32 : Std.I32).val : Int) = zeta (255 - 4 * 21 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_21 :
    liftZ (((-2590150)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 21 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_21 :
    liftZ ((2691481#i32 : Std.I32).val : Int) = zeta (255 - 4 * 21 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_21 :
    liftZ ((2842341#i32 : Std.I32).val : Int) = zeta (255 - 4 * 21 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_22 :
    liftZ ((203044#i32 : Std.I32).val : Int) = zeta (255 - 4 * 22 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_22 :
    liftZ ((1735879#i32 : Std.I32).val : Int) = zeta (255 - 4 * 22 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_22 :
    liftZ (((-3342277)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 22 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_22 :
    liftZ ((3437287#i32 : Std.I32).val : Int) = zeta (255 - 4 * 22 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_23 :
    liftZ ((4108315#i32 : Std.I32).val : Int) = zeta (255 - 4 * 23 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_23 :
    liftZ (((-2437823)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 23 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_23 :
    liftZ ((286988#i32 : Std.I32).val : Int) = zeta (255 - 4 * 23 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_23 :
    liftZ ((342297#i32 : Std.I32).val : Int) = zeta (255 - 4 * 23 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_24 :
    liftZ (((-3595838)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 24 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_24 :
    liftZ (((-768622)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 24 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_24 :
    liftZ (((-525098)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 24 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_24 :
    liftZ (((-3556995)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 24 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_25 :
    liftZ ((3207046#i32 : Std.I32).val : Int) = zeta (255 - 4 * 25 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_25 :
    liftZ ((2031748#i32 : Std.I32).val : Int) = zeta (255 - 4 * 25 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_25 :
    liftZ (((-3122442)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 25 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_25 :
    liftZ (((-655327)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 25 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_26 :
    liftZ (((-522500)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 26 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_26 :
    liftZ (((-43260)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 26 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_26 :
    liftZ (((-1613174)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 26 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_26 :
    liftZ ((495491#i32 : Std.I32).val : Int) = zeta (255 - 4 * 26 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_27 :
    liftZ ((819034#i32 : Std.I32).val : Int) = zeta (255 - 4 * 27 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_27 :
    liftZ ((909542#i32 : Std.I32).val : Int) = zeta (255 - 4 * 27 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_27 :
    liftZ ((1859098#i32 : Std.I32).val : Int) = zeta (255 - 4 * 27 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_27 :
    liftZ ((900702#i32 : Std.I32).val : Int) = zeta (255 - 4 * 27 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_28 :
    liftZ (((-3193378)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 28 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_28 :
    liftZ (((-1197226)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 28 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_28 :
    liftZ (((-3759364)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 28 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_28 :
    liftZ (((-3520352)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 28 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_29 :
    liftZ ((3513181#i32 : Std.I32).val : Int) = zeta (255 - 4 * 29 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_29 :
    liftZ (((-1235728)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 29 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_29 :
    liftZ ((2434439#i32 : Std.I32).val : Int) = zeta (255 - 4 * 29 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_29 :
    liftZ ((266997#i32 : Std.I32).val : Int) = zeta (255 - 4 * 29 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_30 :
    liftZ (((-3562462)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 30 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_30 :
    liftZ (((-2446433)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 30 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_30 :
    liftZ ((2244091#i32 : Std.I32).val : Int) = zeta (255 - 4 * 30 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_30 :
    liftZ (((-3342478)#i32 : Std.I32).val : Int) = zeta (255 - 4 * 30 - 3) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge0_31 :
    liftZ ((3817976#i32 : Std.I32).val : Int) = zeta (255 - 4 * 31 - 0) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge1_31 :
    liftZ ((2316500#i32 : Std.I32).val : Int) = zeta (255 - 4 * 31 - 1) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge2_31 :
    liftZ ((3407706#i32 : Std.I32).val : Int) = zeta (255 - 4 * 31 - 2) := by decide
set_option maxRecDepth 4000 in
private theorem zetaInv0_bridge3_31 :
    liftZ ((2091667#i32 : Std.I32).val : Int) = zeta (255 - 4 * 31 - 3) := by decide

private theorem zetaInv0_mag0_0 : (1976782#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_0 : ((-846154)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_0 : (1400424#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_0 : (3937738#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_1 : ((-1362209)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_1 : ((-48306)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_1 : (3919660#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_1 : ((-554416)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_2 : ((-3545687)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_2 : (1612842#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_2 : ((-976891)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_2 : (183443#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_3 : ((-2286327)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_3 : ((-420899)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_3 : ((-2235985)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_3 : ((-2939036)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_4 : ((-3833893)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_4 : ((-260646)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_4 : ((-1104333)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_4 : ((-1667432)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_5 : (1910376#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_5 : ((-1803090)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_5 : (1723600#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_5 : ((-426683)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_6 : (472078#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_6 : (1717735#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_6 : ((-975884)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_6 : (2213111#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_7 : (269760#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_7 : (3866901#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_7 : (3523897#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_7 : ((-3038916)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_8 : ((-1799107)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_8 : ((-3694233)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_8 : (1652634#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_8 : (810149#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_9 : (3014001#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_9 : (1616392#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_9 : (162844#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_9 : ((-3183426)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_10 : ((-1207385)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_10 : (185531#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_10 : (3369112#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_10 : (1957272#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_11 : ((-164721)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_11 : (2454455#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_11 : (2432395#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_11 : ((-2013608)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_12 : ((-3776993)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_12 : (594136#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_12 : ((-3724270)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_12 : ((-2584293)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_13 : ((-1846953)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_13 : ((-1671176)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_13 : ((-2831860)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_13 : ((-542412)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_14 : (3406031#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_14 : (2235880#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_14 : (777191#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_14 : (1500165#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_15 : ((-1374803)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_15 : ((-2546312)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_15 : (1917081#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_15 : ((-1279661)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_16 : ((-1962642)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_16 : (3306115#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_16 : (1312455#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_16 : ((-451100)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_17 : ((-1430225)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_17 : ((-3318210)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_17 : (1237275#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_17 : ((-1333058)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_18 : ((-1050970)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_18 : (1903435#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_18 : (1869119#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_18 : ((-2994039)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_19 : ((-3548272)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_19 : (2635921#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_19 : (1250494#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_19 : ((-3767016)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_20 : (1595974#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_20 : (2486353#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_20 : (1247620#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_20 : (4055324#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_21 : (1265009#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_21 : ((-2590150)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_21 : (2691481#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_21 : (2842341#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_22 : (203044#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_22 : (1735879#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_22 : ((-3342277)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_22 : (3437287#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_23 : (4108315#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_23 : ((-2437823)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_23 : (286988#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_23 : (342297#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_24 : ((-3595838)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_24 : ((-768622)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_24 : ((-525098)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_24 : ((-3556995)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_25 : (3207046#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_25 : (2031748#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_25 : ((-3122442)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_25 : ((-655327)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_26 : ((-522500)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_26 : ((-43260)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_26 : ((-1613174)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_26 : (495491#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_27 : (819034#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_27 : (909542#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_27 : (1859098#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_27 : (900702#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_28 : ((-3193378)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_28 : ((-1197226)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_28 : ((-3759364)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_28 : ((-3520352)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_29 : (3513181#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_29 : ((-1235728)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_29 : (2434439#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_29 : (266997#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_30 : ((-3562462)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_30 : ((-2446433)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_30 : (2244091#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_30 : ((-3342478)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag0_31 : (3817976#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag1_31 : (2316500#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag2_31 : (3407706#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zetaInv0_mag3_31 : (2091667#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

/-- One `round` of inverse layer 0: read unit `k`, apply the per-unit inverse
    (Gentleman–Sande) stride-1 butterfly with `zeta0..zeta3` (pairs (0,1)(2,3)(4,5)(6,7)),
    write unit `k` back (touching only unit `k`). Faithful clone of `roundInv2_fc`
    with the L0 leaf + post. -/
private theorem roundInv0_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (k : Nat) (hk : k < 32) (zeta0 zeta1 zeta2 zeta3 : Std.I32) (B : Nat)
    (hz0 : zeta0.val.natAbs ≤ 8380416) (hz1 : zeta1.val.natAbs ≤ 8380416)
    (hz2 : zeta2.val.natAbs ≤ 8380416) (hz3 : zeta3.val.natAbs ≤ 8380416)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1)
    (hin : ∀ l : Nat, l < 8 → ((re.val[k]!).values.val[l]!).val.natAbs ≤ B) :
    ∃ out, libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_0.round re k#usize zeta0 zeta1 zeta2 zeta3 = .ok out
      ∧ (liftZ ((out.val[k]!).values.val[0]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val + liftZ ((re.val[k]!).values.val[1]!).val
        ∧ liftZ ((out.val[k]!).values.val[1]!).val
            = (liftZ ((re.val[k]!).values.val[1]!).val - liftZ ((re.val[k]!).values.val[0]!).val) * liftZ zeta0.val
        ∧ liftZ ((out.val[k]!).values.val[2]!).val
            = liftZ ((re.val[k]!).values.val[2]!).val + liftZ ((re.val[k]!).values.val[3]!).val
        ∧ liftZ ((out.val[k]!).values.val[3]!).val
            = (liftZ ((re.val[k]!).values.val[3]!).val - liftZ ((re.val[k]!).values.val[2]!).val) * liftZ zeta1.val
        ∧ liftZ ((out.val[k]!).values.val[4]!).val
            = liftZ ((re.val[k]!).values.val[4]!).val + liftZ ((re.val[k]!).values.val[5]!).val
        ∧ liftZ ((out.val[k]!).values.val[5]!).val
            = (liftZ ((re.val[k]!).values.val[5]!).val - liftZ ((re.val[k]!).values.val[4]!).val) * liftZ zeta2.val
        ∧ liftZ ((out.val[k]!).values.val[6]!).val
            = liftZ ((re.val[k]!).values.val[6]!).val + liftZ ((re.val[k]!).values.val[7]!).val
        ∧ liftZ ((out.val[k]!).values.val[7]!).val
            = (liftZ ((re.val[k]!).values.val[7]!).val - liftZ ((re.val[k]!).values.val[6]!).val) * liftZ zeta3.val)
      ∧ (∀ u : Nat, u < 32 → u ≠ k → out.val[u]! = re.val[u]!)
      ∧ (∀ l : Nat, l < 8 → ((out.val[k]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24) := by
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_0.round
  have hre_len : re.length = 32 := Std.Array.length_eq _
  have hk_len : (k#usize : Std.Usize).val < re.length := by
    rw [hre_len]; simpa using hk
  have h_idx : Array.index_usize re k#usize = .ok (re.val[k]!) :=
    array_index_usize_ok_eq re k#usize hk_len
  set ak : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    re.val[k]! with hak
  have h_imt : Array.index_mut_usize re k#usize = .ok (ak, re.set k#usize) := by
    unfold Aeneas.Std.Array.index_mut_usize; rw [h_idx]; rfl
  obtain ⟨c1, hc1_eq, hc1_butter, hc1_bd⟩ :=
    triple_exists_ok (simd_unit_invert_ntt_at_layer_0_fc ak zeta0 zeta1 zeta2 zeta3 B hz0 hz1 hz2 hz3 hB hin)
  have hset_k : (re.set k#usize c1).val[k]! = c1 := by
    rw [← Std.Array.getElem!_Nat_eq]
    exact Std.Array.getElem!_Nat_set_eq re k#usize k c1 ⟨rfl, by rw [hre_len]; exact hk⟩
  refine ⟨re.set k#usize c1, ?_, ?_, ?_, ?_⟩
  · simp [Aeneas.Std.bind_tc_ok, h_imt, hc1_eq]
  · rw [hset_k]; exact hc1_butter
  · intro u hu hne
    rw [← Std.Array.getElem!_Nat_eq, ← Std.Array.getElem!_Nat_eq (v := re)]
    exact Std.Array.getElem!_Nat_set_ne re k#usize u c1 (fun h => hne h.symm)
  · intro l hl
    rw [hset_k]; exact hc1_bd l hl


set_option maxHeartbeats 16000000 in
@[spec]
theorem invert_ntt_at_layer_0_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (2 : Int) * B ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_0 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.intt_layer (lift_units re) 0
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ 2 * B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_at_layer_0
  have hkeep0 : ∀ u, 0 ≤ u → u < 32 → re.val[u]! = re.val[u]! := fun u _ _ => rfl
  obtain ⟨r1, hr1_eq, hbut0, hfr0, hbd0⟩ :=
    roundInv0_fc re 0 (by decide) (1976782#i32) ((-846154)#i32) (1400424#i32) (3937738#i32) B (zetaInv0_mag0_0) (zetaInv0_mag1_0) (zetaInv0_mag2_0) (zetaInv0_mag3_0) hB
      (fun l hl => by rw [hkeep0 0 (by omega) (by omega)]; exact hin 0 (by decide) l hl)
  have hkeep1 : ∀ u, 1 ≤ u → u < 32 → r1.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr0 u hu2 (by omega), hkeep0 u (by omega) hu2]
  obtain ⟨r2, hr2_eq, hbut1, hfr1, hbd1⟩ :=
    roundInv0_fc r1 1 (by decide) ((-1362209)#i32) ((-48306)#i32) (3919660#i32) ((-554416)#i32) B (zetaInv0_mag0_1) (zetaInv0_mag1_1) (zetaInv0_mag2_1) (zetaInv0_mag3_1) hB
      (fun l hl => by rw [hkeep1 1 (by omega) (by omega)]; exact hin 1 (by decide) l hl)
  have hkeep2 : ∀ u, 2 ≤ u → u < 32 → r2.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr1 u hu2 (by omega), hkeep1 u (by omega) hu2]
  obtain ⟨r3, hr3_eq, hbut2, hfr2, hbd2⟩ :=
    roundInv0_fc r2 2 (by decide) ((-3545687)#i32) (1612842#i32) ((-976891)#i32) (183443#i32) B (zetaInv0_mag0_2) (zetaInv0_mag1_2) (zetaInv0_mag2_2) (zetaInv0_mag3_2) hB
      (fun l hl => by rw [hkeep2 2 (by omega) (by omega)]; exact hin 2 (by decide) l hl)
  have hkeep3 : ∀ u, 3 ≤ u → u < 32 → r3.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr2 u hu2 (by omega), hkeep2 u (by omega) hu2]
  obtain ⟨r4, hr4_eq, hbut3, hfr3, hbd3⟩ :=
    roundInv0_fc r3 3 (by decide) ((-2286327)#i32) ((-420899)#i32) ((-2235985)#i32) ((-2939036)#i32) B (zetaInv0_mag0_3) (zetaInv0_mag1_3) (zetaInv0_mag2_3) (zetaInv0_mag3_3) hB
      (fun l hl => by rw [hkeep3 3 (by omega) (by omega)]; exact hin 3 (by decide) l hl)
  have hkeep4 : ∀ u, 4 ≤ u → u < 32 → r4.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr3 u hu2 (by omega), hkeep3 u (by omega) hu2]
  obtain ⟨r5, hr5_eq, hbut4, hfr4, hbd4⟩ :=
    roundInv0_fc r4 4 (by decide) ((-3833893)#i32) ((-260646)#i32) ((-1104333)#i32) ((-1667432)#i32) B (zetaInv0_mag0_4) (zetaInv0_mag1_4) (zetaInv0_mag2_4) (zetaInv0_mag3_4) hB
      (fun l hl => by rw [hkeep4 4 (by omega) (by omega)]; exact hin 4 (by decide) l hl)
  have hkeep5 : ∀ u, 5 ≤ u → u < 32 → r5.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr4 u hu2 (by omega), hkeep4 u (by omega) hu2]
  obtain ⟨r6, hr6_eq, hbut5, hfr5, hbd5⟩ :=
    roundInv0_fc r5 5 (by decide) (1910376#i32) ((-1803090)#i32) (1723600#i32) ((-426683)#i32) B (zetaInv0_mag0_5) (zetaInv0_mag1_5) (zetaInv0_mag2_5) (zetaInv0_mag3_5) hB
      (fun l hl => by rw [hkeep5 5 (by omega) (by omega)]; exact hin 5 (by decide) l hl)
  have hkeep6 : ∀ u, 6 ≤ u → u < 32 → r6.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr5 u hu2 (by omega), hkeep5 u (by omega) hu2]
  obtain ⟨r7, hr7_eq, hbut6, hfr6, hbd6⟩ :=
    roundInv0_fc r6 6 (by decide) (472078#i32) (1717735#i32) ((-975884)#i32) (2213111#i32) B (zetaInv0_mag0_6) (zetaInv0_mag1_6) (zetaInv0_mag2_6) (zetaInv0_mag3_6) hB
      (fun l hl => by rw [hkeep6 6 (by omega) (by omega)]; exact hin 6 (by decide) l hl)
  have hkeep7 : ∀ u, 7 ≤ u → u < 32 → r7.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr6 u hu2 (by omega), hkeep6 u (by omega) hu2]
  obtain ⟨r8, hr8_eq, hbut7, hfr7, hbd7⟩ :=
    roundInv0_fc r7 7 (by decide) (269760#i32) (3866901#i32) (3523897#i32) ((-3038916)#i32) B (zetaInv0_mag0_7) (zetaInv0_mag1_7) (zetaInv0_mag2_7) (zetaInv0_mag3_7) hB
      (fun l hl => by rw [hkeep7 7 (by omega) (by omega)]; exact hin 7 (by decide) l hl)
  have hkeep8 : ∀ u, 8 ≤ u → u < 32 → r8.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr7 u hu2 (by omega), hkeep7 u (by omega) hu2]
  obtain ⟨r9, hr9_eq, hbut8, hfr8, hbd8⟩ :=
    roundInv0_fc r8 8 (by decide) ((-1799107)#i32) ((-3694233)#i32) (1652634#i32) (810149#i32) B (zetaInv0_mag0_8) (zetaInv0_mag1_8) (zetaInv0_mag2_8) (zetaInv0_mag3_8) hB
      (fun l hl => by rw [hkeep8 8 (by omega) (by omega)]; exact hin 8 (by decide) l hl)
  have hkeep9 : ∀ u, 9 ≤ u → u < 32 → r9.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr8 u hu2 (by omega), hkeep8 u (by omega) hu2]
  obtain ⟨r10, hr10_eq, hbut9, hfr9, hbd9⟩ :=
    roundInv0_fc r9 9 (by decide) (3014001#i32) (1616392#i32) (162844#i32) ((-3183426)#i32) B (zetaInv0_mag0_9) (zetaInv0_mag1_9) (zetaInv0_mag2_9) (zetaInv0_mag3_9) hB
      (fun l hl => by rw [hkeep9 9 (by omega) (by omega)]; exact hin 9 (by decide) l hl)
  have hkeep10 : ∀ u, 10 ≤ u → u < 32 → r10.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr9 u hu2 (by omega), hkeep9 u (by omega) hu2]
  obtain ⟨r11, hr11_eq, hbut10, hfr10, hbd10⟩ :=
    roundInv0_fc r10 10 (by decide) ((-1207385)#i32) (185531#i32) (3369112#i32) (1957272#i32) B (zetaInv0_mag0_10) (zetaInv0_mag1_10) (zetaInv0_mag2_10) (zetaInv0_mag3_10) hB
      (fun l hl => by rw [hkeep10 10 (by omega) (by omega)]; exact hin 10 (by decide) l hl)
  have hkeep11 : ∀ u, 11 ≤ u → u < 32 → r11.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr10 u hu2 (by omega), hkeep10 u (by omega) hu2]
  obtain ⟨r12, hr12_eq, hbut11, hfr11, hbd11⟩ :=
    roundInv0_fc r11 11 (by decide) ((-164721)#i32) (2454455#i32) (2432395#i32) ((-2013608)#i32) B (zetaInv0_mag0_11) (zetaInv0_mag1_11) (zetaInv0_mag2_11) (zetaInv0_mag3_11) hB
      (fun l hl => by rw [hkeep11 11 (by omega) (by omega)]; exact hin 11 (by decide) l hl)
  have hkeep12 : ∀ u, 12 ≤ u → u < 32 → r12.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr11 u hu2 (by omega), hkeep11 u (by omega) hu2]
  obtain ⟨r13, hr13_eq, hbut12, hfr12, hbd12⟩ :=
    roundInv0_fc r12 12 (by decide) ((-3776993)#i32) (594136#i32) ((-3724270)#i32) ((-2584293)#i32) B (zetaInv0_mag0_12) (zetaInv0_mag1_12) (zetaInv0_mag2_12) (zetaInv0_mag3_12) hB
      (fun l hl => by rw [hkeep12 12 (by omega) (by omega)]; exact hin 12 (by decide) l hl)
  have hkeep13 : ∀ u, 13 ≤ u → u < 32 → r13.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr12 u hu2 (by omega), hkeep12 u (by omega) hu2]
  obtain ⟨r14, hr14_eq, hbut13, hfr13, hbd13⟩ :=
    roundInv0_fc r13 13 (by decide) ((-1846953)#i32) ((-1671176)#i32) ((-2831860)#i32) ((-542412)#i32) B (zetaInv0_mag0_13) (zetaInv0_mag1_13) (zetaInv0_mag2_13) (zetaInv0_mag3_13) hB
      (fun l hl => by rw [hkeep13 13 (by omega) (by omega)]; exact hin 13 (by decide) l hl)
  have hkeep14 : ∀ u, 14 ≤ u → u < 32 → r14.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr13 u hu2 (by omega), hkeep13 u (by omega) hu2]
  obtain ⟨r15, hr15_eq, hbut14, hfr14, hbd14⟩ :=
    roundInv0_fc r14 14 (by decide) (3406031#i32) (2235880#i32) (777191#i32) (1500165#i32) B (zetaInv0_mag0_14) (zetaInv0_mag1_14) (zetaInv0_mag2_14) (zetaInv0_mag3_14) hB
      (fun l hl => by rw [hkeep14 14 (by omega) (by omega)]; exact hin 14 (by decide) l hl)
  have hkeep15 : ∀ u, 15 ≤ u → u < 32 → r15.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr14 u hu2 (by omega), hkeep14 u (by omega) hu2]
  obtain ⟨r16, hr16_eq, hbut15, hfr15, hbd15⟩ :=
    roundInv0_fc r15 15 (by decide) ((-1374803)#i32) ((-2546312)#i32) (1917081#i32) ((-1279661)#i32) B (zetaInv0_mag0_15) (zetaInv0_mag1_15) (zetaInv0_mag2_15) (zetaInv0_mag3_15) hB
      (fun l hl => by rw [hkeep15 15 (by omega) (by omega)]; exact hin 15 (by decide) l hl)
  have hkeep16 : ∀ u, 16 ≤ u → u < 32 → r16.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr15 u hu2 (by omega), hkeep15 u (by omega) hu2]
  obtain ⟨r17, hr17_eq, hbut16, hfr16, hbd16⟩ :=
    roundInv0_fc r16 16 (by decide) ((-1962642)#i32) (3306115#i32) (1312455#i32) ((-451100)#i32) B (zetaInv0_mag0_16) (zetaInv0_mag1_16) (zetaInv0_mag2_16) (zetaInv0_mag3_16) hB
      (fun l hl => by rw [hkeep16 16 (by omega) (by omega)]; exact hin 16 (by decide) l hl)
  have hkeep17 : ∀ u, 17 ≤ u → u < 32 → r17.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr16 u hu2 (by omega), hkeep16 u (by omega) hu2]
  obtain ⟨r18, hr18_eq, hbut17, hfr17, hbd17⟩ :=
    roundInv0_fc r17 17 (by decide) ((-1430225)#i32) ((-3318210)#i32) (1237275#i32) ((-1333058)#i32) B (zetaInv0_mag0_17) (zetaInv0_mag1_17) (zetaInv0_mag2_17) (zetaInv0_mag3_17) hB
      (fun l hl => by rw [hkeep17 17 (by omega) (by omega)]; exact hin 17 (by decide) l hl)
  have hkeep18 : ∀ u, 18 ≤ u → u < 32 → r18.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr17 u hu2 (by omega), hkeep17 u (by omega) hu2]
  obtain ⟨r19, hr19_eq, hbut18, hfr18, hbd18⟩ :=
    roundInv0_fc r18 18 (by decide) ((-1050970)#i32) (1903435#i32) (1869119#i32) ((-2994039)#i32) B (zetaInv0_mag0_18) (zetaInv0_mag1_18) (zetaInv0_mag2_18) (zetaInv0_mag3_18) hB
      (fun l hl => by rw [hkeep18 18 (by omega) (by omega)]; exact hin 18 (by decide) l hl)
  have hkeep19 : ∀ u, 19 ≤ u → u < 32 → r19.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr18 u hu2 (by omega), hkeep18 u (by omega) hu2]
  obtain ⟨r20, hr20_eq, hbut19, hfr19, hbd19⟩ :=
    roundInv0_fc r19 19 (by decide) ((-3548272)#i32) (2635921#i32) (1250494#i32) ((-3767016)#i32) B (zetaInv0_mag0_19) (zetaInv0_mag1_19) (zetaInv0_mag2_19) (zetaInv0_mag3_19) hB
      (fun l hl => by rw [hkeep19 19 (by omega) (by omega)]; exact hin 19 (by decide) l hl)
  have hkeep20 : ∀ u, 20 ≤ u → u < 32 → r20.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr19 u hu2 (by omega), hkeep19 u (by omega) hu2]
  obtain ⟨r21, hr21_eq, hbut20, hfr20, hbd20⟩ :=
    roundInv0_fc r20 20 (by decide) (1595974#i32) (2486353#i32) (1247620#i32) (4055324#i32) B (zetaInv0_mag0_20) (zetaInv0_mag1_20) (zetaInv0_mag2_20) (zetaInv0_mag3_20) hB
      (fun l hl => by rw [hkeep20 20 (by omega) (by omega)]; exact hin 20 (by decide) l hl)
  have hkeep21 : ∀ u, 21 ≤ u → u < 32 → r21.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr20 u hu2 (by omega), hkeep20 u (by omega) hu2]
  obtain ⟨r22, hr22_eq, hbut21, hfr21, hbd21⟩ :=
    roundInv0_fc r21 21 (by decide) (1265009#i32) ((-2590150)#i32) (2691481#i32) (2842341#i32) B (zetaInv0_mag0_21) (zetaInv0_mag1_21) (zetaInv0_mag2_21) (zetaInv0_mag3_21) hB
      (fun l hl => by rw [hkeep21 21 (by omega) (by omega)]; exact hin 21 (by decide) l hl)
  have hkeep22 : ∀ u, 22 ≤ u → u < 32 → r22.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr21 u hu2 (by omega), hkeep21 u (by omega) hu2]
  obtain ⟨r23, hr23_eq, hbut22, hfr22, hbd22⟩ :=
    roundInv0_fc r22 22 (by decide) (203044#i32) (1735879#i32) ((-3342277)#i32) (3437287#i32) B (zetaInv0_mag0_22) (zetaInv0_mag1_22) (zetaInv0_mag2_22) (zetaInv0_mag3_22) hB
      (fun l hl => by rw [hkeep22 22 (by omega) (by omega)]; exact hin 22 (by decide) l hl)
  have hkeep23 : ∀ u, 23 ≤ u → u < 32 → r23.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr22 u hu2 (by omega), hkeep22 u (by omega) hu2]
  obtain ⟨r24, hr24_eq, hbut23, hfr23, hbd23⟩ :=
    roundInv0_fc r23 23 (by decide) (4108315#i32) ((-2437823)#i32) (286988#i32) (342297#i32) B (zetaInv0_mag0_23) (zetaInv0_mag1_23) (zetaInv0_mag2_23) (zetaInv0_mag3_23) hB
      (fun l hl => by rw [hkeep23 23 (by omega) (by omega)]; exact hin 23 (by decide) l hl)
  have hkeep24 : ∀ u, 24 ≤ u → u < 32 → r24.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr23 u hu2 (by omega), hkeep23 u (by omega) hu2]
  obtain ⟨r25, hr25_eq, hbut24, hfr24, hbd24⟩ :=
    roundInv0_fc r24 24 (by decide) ((-3595838)#i32) ((-768622)#i32) ((-525098)#i32) ((-3556995)#i32) B (zetaInv0_mag0_24) (zetaInv0_mag1_24) (zetaInv0_mag2_24) (zetaInv0_mag3_24) hB
      (fun l hl => by rw [hkeep24 24 (by omega) (by omega)]; exact hin 24 (by decide) l hl)
  have hkeep25 : ∀ u, 25 ≤ u → u < 32 → r25.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr24 u hu2 (by omega), hkeep24 u (by omega) hu2]
  obtain ⟨r26, hr26_eq, hbut25, hfr25, hbd25⟩ :=
    roundInv0_fc r25 25 (by decide) (3207046#i32) (2031748#i32) ((-3122442)#i32) ((-655327)#i32) B (zetaInv0_mag0_25) (zetaInv0_mag1_25) (zetaInv0_mag2_25) (zetaInv0_mag3_25) hB
      (fun l hl => by rw [hkeep25 25 (by omega) (by omega)]; exact hin 25 (by decide) l hl)
  have hkeep26 : ∀ u, 26 ≤ u → u < 32 → r26.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr25 u hu2 (by omega), hkeep25 u (by omega) hu2]
  obtain ⟨r27, hr27_eq, hbut26, hfr26, hbd26⟩ :=
    roundInv0_fc r26 26 (by decide) ((-522500)#i32) ((-43260)#i32) ((-1613174)#i32) (495491#i32) B (zetaInv0_mag0_26) (zetaInv0_mag1_26) (zetaInv0_mag2_26) (zetaInv0_mag3_26) hB
      (fun l hl => by rw [hkeep26 26 (by omega) (by omega)]; exact hin 26 (by decide) l hl)
  have hkeep27 : ∀ u, 27 ≤ u → u < 32 → r27.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr26 u hu2 (by omega), hkeep26 u (by omega) hu2]
  obtain ⟨r28, hr28_eq, hbut27, hfr27, hbd27⟩ :=
    roundInv0_fc r27 27 (by decide) (819034#i32) (909542#i32) (1859098#i32) (900702#i32) B (zetaInv0_mag0_27) (zetaInv0_mag1_27) (zetaInv0_mag2_27) (zetaInv0_mag3_27) hB
      (fun l hl => by rw [hkeep27 27 (by omega) (by omega)]; exact hin 27 (by decide) l hl)
  have hkeep28 : ∀ u, 28 ≤ u → u < 32 → r28.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr27 u hu2 (by omega), hkeep27 u (by omega) hu2]
  obtain ⟨r29, hr29_eq, hbut28, hfr28, hbd28⟩ :=
    roundInv0_fc r28 28 (by decide) ((-3193378)#i32) ((-1197226)#i32) ((-3759364)#i32) ((-3520352)#i32) B (zetaInv0_mag0_28) (zetaInv0_mag1_28) (zetaInv0_mag2_28) (zetaInv0_mag3_28) hB
      (fun l hl => by rw [hkeep28 28 (by omega) (by omega)]; exact hin 28 (by decide) l hl)
  have hkeep29 : ∀ u, 29 ≤ u → u < 32 → r29.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr28 u hu2 (by omega), hkeep28 u (by omega) hu2]
  obtain ⟨r30, hr30_eq, hbut29, hfr29, hbd29⟩ :=
    roundInv0_fc r29 29 (by decide) (3513181#i32) ((-1235728)#i32) (2434439#i32) (266997#i32) B (zetaInv0_mag0_29) (zetaInv0_mag1_29) (zetaInv0_mag2_29) (zetaInv0_mag3_29) hB
      (fun l hl => by rw [hkeep29 29 (by omega) (by omega)]; exact hin 29 (by decide) l hl)
  have hkeep30 : ∀ u, 30 ≤ u → u < 32 → r30.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr29 u hu2 (by omega), hkeep29 u (by omega) hu2]
  obtain ⟨r31, hr31_eq, hbut30, hfr30, hbd30⟩ :=
    roundInv0_fc r30 30 (by decide) ((-3562462)#i32) ((-2446433)#i32) (2244091#i32) ((-3342478)#i32) B (zetaInv0_mag0_30) (zetaInv0_mag1_30) (zetaInv0_mag2_30) (zetaInv0_mag3_30) hB
      (fun l hl => by rw [hkeep30 30 (by omega) (by omega)]; exact hin 30 (by decide) l hl)
  have hkeep31 : ∀ u, 31 ≤ u → u < 32 → r31.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr30 u hu2 (by omega), hkeep30 u (by omega) hu2]
  obtain ⟨r32, hr32_eq, hbut31, hfr31, hbd31⟩ :=
    roundInv0_fc r31 31 (by decide) (3817976#i32) (2316500#i32) (3407706#i32) (2091667#i32) B (zetaInv0_mag0_31) (zetaInv0_mag1_31) (zetaInv0_mag2_31) (zetaInv0_mag3_31) hB
      (fun l hl => by rw [hkeep31 31 (by omega) (by omega)]; exact hin 31 (by decide) l hl)
  have hkeep32 : ∀ u, 32 ≤ u → u < 32 → r32.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr31 u hu2 (by omega), hkeep31 u (by omega) hu2]
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
  rw [hr16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr17_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr18_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr19_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr20_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr21_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr22_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr23_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr24_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr25_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr26_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr27_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr28_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr29_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr30_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr31_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr32_eq
  have hr32u0 : r32.val[0]! = r1.val[0]! := by
    rw [hfr31 0 (by decide) (by decide), hfr30 0 (by decide) (by decide), hfr29 0 (by decide) (by decide), hfr28 0 (by decide) (by decide), hfr27 0 (by decide) (by decide), hfr26 0 (by decide) (by decide), hfr25 0 (by decide) (by decide), hfr24 0 (by decide) (by decide), hfr23 0 (by decide) (by decide), hfr22 0 (by decide) (by decide), hfr21 0 (by decide) (by decide), hfr20 0 (by decide) (by decide), hfr19 0 (by decide) (by decide), hfr18 0 (by decide) (by decide), hfr17 0 (by decide) (by decide), hfr16 0 (by decide) (by decide), hfr15 0 (by decide) (by decide), hfr14 0 (by decide) (by decide), hfr13 0 (by decide) (by decide), hfr12 0 (by decide) (by decide), hfr11 0 (by decide) (by decide), hfr10 0 (by decide) (by decide), hfr9 0 (by decide) (by decide), hfr8 0 (by decide) (by decide), hfr7 0 (by decide) (by decide), hfr6 0 (by decide) (by decide), hfr5 0 (by decide) (by decide), hfr4 0 (by decide) (by decide), hfr3 0 (by decide) (by decide), hfr2 0 (by decide) (by decide), hfr1 0 (by decide) (by decide)]
  have hr32u1 : r32.val[1]! = r2.val[1]! := by
    rw [hfr31 1 (by decide) (by decide), hfr30 1 (by decide) (by decide), hfr29 1 (by decide) (by decide), hfr28 1 (by decide) (by decide), hfr27 1 (by decide) (by decide), hfr26 1 (by decide) (by decide), hfr25 1 (by decide) (by decide), hfr24 1 (by decide) (by decide), hfr23 1 (by decide) (by decide), hfr22 1 (by decide) (by decide), hfr21 1 (by decide) (by decide), hfr20 1 (by decide) (by decide), hfr19 1 (by decide) (by decide), hfr18 1 (by decide) (by decide), hfr17 1 (by decide) (by decide), hfr16 1 (by decide) (by decide), hfr15 1 (by decide) (by decide), hfr14 1 (by decide) (by decide), hfr13 1 (by decide) (by decide), hfr12 1 (by decide) (by decide), hfr11 1 (by decide) (by decide), hfr10 1 (by decide) (by decide), hfr9 1 (by decide) (by decide), hfr8 1 (by decide) (by decide), hfr7 1 (by decide) (by decide), hfr6 1 (by decide) (by decide), hfr5 1 (by decide) (by decide), hfr4 1 (by decide) (by decide), hfr3 1 (by decide) (by decide), hfr2 1 (by decide) (by decide)]
  rw [hkeep1 1 (by decide) (by decide)] at hbut1
  have hr32u2 : r32.val[2]! = r3.val[2]! := by
    rw [hfr31 2 (by decide) (by decide), hfr30 2 (by decide) (by decide), hfr29 2 (by decide) (by decide), hfr28 2 (by decide) (by decide), hfr27 2 (by decide) (by decide), hfr26 2 (by decide) (by decide), hfr25 2 (by decide) (by decide), hfr24 2 (by decide) (by decide), hfr23 2 (by decide) (by decide), hfr22 2 (by decide) (by decide), hfr21 2 (by decide) (by decide), hfr20 2 (by decide) (by decide), hfr19 2 (by decide) (by decide), hfr18 2 (by decide) (by decide), hfr17 2 (by decide) (by decide), hfr16 2 (by decide) (by decide), hfr15 2 (by decide) (by decide), hfr14 2 (by decide) (by decide), hfr13 2 (by decide) (by decide), hfr12 2 (by decide) (by decide), hfr11 2 (by decide) (by decide), hfr10 2 (by decide) (by decide), hfr9 2 (by decide) (by decide), hfr8 2 (by decide) (by decide), hfr7 2 (by decide) (by decide), hfr6 2 (by decide) (by decide), hfr5 2 (by decide) (by decide), hfr4 2 (by decide) (by decide), hfr3 2 (by decide) (by decide)]
  rw [hkeep2 2 (by decide) (by decide)] at hbut2
  have hr32u3 : r32.val[3]! = r4.val[3]! := by
    rw [hfr31 3 (by decide) (by decide), hfr30 3 (by decide) (by decide), hfr29 3 (by decide) (by decide), hfr28 3 (by decide) (by decide), hfr27 3 (by decide) (by decide), hfr26 3 (by decide) (by decide), hfr25 3 (by decide) (by decide), hfr24 3 (by decide) (by decide), hfr23 3 (by decide) (by decide), hfr22 3 (by decide) (by decide), hfr21 3 (by decide) (by decide), hfr20 3 (by decide) (by decide), hfr19 3 (by decide) (by decide), hfr18 3 (by decide) (by decide), hfr17 3 (by decide) (by decide), hfr16 3 (by decide) (by decide), hfr15 3 (by decide) (by decide), hfr14 3 (by decide) (by decide), hfr13 3 (by decide) (by decide), hfr12 3 (by decide) (by decide), hfr11 3 (by decide) (by decide), hfr10 3 (by decide) (by decide), hfr9 3 (by decide) (by decide), hfr8 3 (by decide) (by decide), hfr7 3 (by decide) (by decide), hfr6 3 (by decide) (by decide), hfr5 3 (by decide) (by decide), hfr4 3 (by decide) (by decide)]
  rw [hkeep3 3 (by decide) (by decide)] at hbut3
  have hr32u4 : r32.val[4]! = r5.val[4]! := by
    rw [hfr31 4 (by decide) (by decide), hfr30 4 (by decide) (by decide), hfr29 4 (by decide) (by decide), hfr28 4 (by decide) (by decide), hfr27 4 (by decide) (by decide), hfr26 4 (by decide) (by decide), hfr25 4 (by decide) (by decide), hfr24 4 (by decide) (by decide), hfr23 4 (by decide) (by decide), hfr22 4 (by decide) (by decide), hfr21 4 (by decide) (by decide), hfr20 4 (by decide) (by decide), hfr19 4 (by decide) (by decide), hfr18 4 (by decide) (by decide), hfr17 4 (by decide) (by decide), hfr16 4 (by decide) (by decide), hfr15 4 (by decide) (by decide), hfr14 4 (by decide) (by decide), hfr13 4 (by decide) (by decide), hfr12 4 (by decide) (by decide), hfr11 4 (by decide) (by decide), hfr10 4 (by decide) (by decide), hfr9 4 (by decide) (by decide), hfr8 4 (by decide) (by decide), hfr7 4 (by decide) (by decide), hfr6 4 (by decide) (by decide), hfr5 4 (by decide) (by decide)]
  rw [hkeep4 4 (by decide) (by decide)] at hbut4
  have hr32u5 : r32.val[5]! = r6.val[5]! := by
    rw [hfr31 5 (by decide) (by decide), hfr30 5 (by decide) (by decide), hfr29 5 (by decide) (by decide), hfr28 5 (by decide) (by decide), hfr27 5 (by decide) (by decide), hfr26 5 (by decide) (by decide), hfr25 5 (by decide) (by decide), hfr24 5 (by decide) (by decide), hfr23 5 (by decide) (by decide), hfr22 5 (by decide) (by decide), hfr21 5 (by decide) (by decide), hfr20 5 (by decide) (by decide), hfr19 5 (by decide) (by decide), hfr18 5 (by decide) (by decide), hfr17 5 (by decide) (by decide), hfr16 5 (by decide) (by decide), hfr15 5 (by decide) (by decide), hfr14 5 (by decide) (by decide), hfr13 5 (by decide) (by decide), hfr12 5 (by decide) (by decide), hfr11 5 (by decide) (by decide), hfr10 5 (by decide) (by decide), hfr9 5 (by decide) (by decide), hfr8 5 (by decide) (by decide), hfr7 5 (by decide) (by decide), hfr6 5 (by decide) (by decide)]
  rw [hkeep5 5 (by decide) (by decide)] at hbut5
  have hr32u6 : r32.val[6]! = r7.val[6]! := by
    rw [hfr31 6 (by decide) (by decide), hfr30 6 (by decide) (by decide), hfr29 6 (by decide) (by decide), hfr28 6 (by decide) (by decide), hfr27 6 (by decide) (by decide), hfr26 6 (by decide) (by decide), hfr25 6 (by decide) (by decide), hfr24 6 (by decide) (by decide), hfr23 6 (by decide) (by decide), hfr22 6 (by decide) (by decide), hfr21 6 (by decide) (by decide), hfr20 6 (by decide) (by decide), hfr19 6 (by decide) (by decide), hfr18 6 (by decide) (by decide), hfr17 6 (by decide) (by decide), hfr16 6 (by decide) (by decide), hfr15 6 (by decide) (by decide), hfr14 6 (by decide) (by decide), hfr13 6 (by decide) (by decide), hfr12 6 (by decide) (by decide), hfr11 6 (by decide) (by decide), hfr10 6 (by decide) (by decide), hfr9 6 (by decide) (by decide), hfr8 6 (by decide) (by decide), hfr7 6 (by decide) (by decide)]
  rw [hkeep6 6 (by decide) (by decide)] at hbut6
  have hr32u7 : r32.val[7]! = r8.val[7]! := by
    rw [hfr31 7 (by decide) (by decide), hfr30 7 (by decide) (by decide), hfr29 7 (by decide) (by decide), hfr28 7 (by decide) (by decide), hfr27 7 (by decide) (by decide), hfr26 7 (by decide) (by decide), hfr25 7 (by decide) (by decide), hfr24 7 (by decide) (by decide), hfr23 7 (by decide) (by decide), hfr22 7 (by decide) (by decide), hfr21 7 (by decide) (by decide), hfr20 7 (by decide) (by decide), hfr19 7 (by decide) (by decide), hfr18 7 (by decide) (by decide), hfr17 7 (by decide) (by decide), hfr16 7 (by decide) (by decide), hfr15 7 (by decide) (by decide), hfr14 7 (by decide) (by decide), hfr13 7 (by decide) (by decide), hfr12 7 (by decide) (by decide), hfr11 7 (by decide) (by decide), hfr10 7 (by decide) (by decide), hfr9 7 (by decide) (by decide), hfr8 7 (by decide) (by decide)]
  rw [hkeep7 7 (by decide) (by decide)] at hbut7
  have hr32u8 : r32.val[8]! = r9.val[8]! := by
    rw [hfr31 8 (by decide) (by decide), hfr30 8 (by decide) (by decide), hfr29 8 (by decide) (by decide), hfr28 8 (by decide) (by decide), hfr27 8 (by decide) (by decide), hfr26 8 (by decide) (by decide), hfr25 8 (by decide) (by decide), hfr24 8 (by decide) (by decide), hfr23 8 (by decide) (by decide), hfr22 8 (by decide) (by decide), hfr21 8 (by decide) (by decide), hfr20 8 (by decide) (by decide), hfr19 8 (by decide) (by decide), hfr18 8 (by decide) (by decide), hfr17 8 (by decide) (by decide), hfr16 8 (by decide) (by decide), hfr15 8 (by decide) (by decide), hfr14 8 (by decide) (by decide), hfr13 8 (by decide) (by decide), hfr12 8 (by decide) (by decide), hfr11 8 (by decide) (by decide), hfr10 8 (by decide) (by decide), hfr9 8 (by decide) (by decide)]
  rw [hkeep8 8 (by decide) (by decide)] at hbut8
  have hr32u9 : r32.val[9]! = r10.val[9]! := by
    rw [hfr31 9 (by decide) (by decide), hfr30 9 (by decide) (by decide), hfr29 9 (by decide) (by decide), hfr28 9 (by decide) (by decide), hfr27 9 (by decide) (by decide), hfr26 9 (by decide) (by decide), hfr25 9 (by decide) (by decide), hfr24 9 (by decide) (by decide), hfr23 9 (by decide) (by decide), hfr22 9 (by decide) (by decide), hfr21 9 (by decide) (by decide), hfr20 9 (by decide) (by decide), hfr19 9 (by decide) (by decide), hfr18 9 (by decide) (by decide), hfr17 9 (by decide) (by decide), hfr16 9 (by decide) (by decide), hfr15 9 (by decide) (by decide), hfr14 9 (by decide) (by decide), hfr13 9 (by decide) (by decide), hfr12 9 (by decide) (by decide), hfr11 9 (by decide) (by decide), hfr10 9 (by decide) (by decide)]
  rw [hkeep9 9 (by decide) (by decide)] at hbut9
  have hr32u10 : r32.val[10]! = r11.val[10]! := by
    rw [hfr31 10 (by decide) (by decide), hfr30 10 (by decide) (by decide), hfr29 10 (by decide) (by decide), hfr28 10 (by decide) (by decide), hfr27 10 (by decide) (by decide), hfr26 10 (by decide) (by decide), hfr25 10 (by decide) (by decide), hfr24 10 (by decide) (by decide), hfr23 10 (by decide) (by decide), hfr22 10 (by decide) (by decide), hfr21 10 (by decide) (by decide), hfr20 10 (by decide) (by decide), hfr19 10 (by decide) (by decide), hfr18 10 (by decide) (by decide), hfr17 10 (by decide) (by decide), hfr16 10 (by decide) (by decide), hfr15 10 (by decide) (by decide), hfr14 10 (by decide) (by decide), hfr13 10 (by decide) (by decide), hfr12 10 (by decide) (by decide), hfr11 10 (by decide) (by decide)]
  rw [hkeep10 10 (by decide) (by decide)] at hbut10
  have hr32u11 : r32.val[11]! = r12.val[11]! := by
    rw [hfr31 11 (by decide) (by decide), hfr30 11 (by decide) (by decide), hfr29 11 (by decide) (by decide), hfr28 11 (by decide) (by decide), hfr27 11 (by decide) (by decide), hfr26 11 (by decide) (by decide), hfr25 11 (by decide) (by decide), hfr24 11 (by decide) (by decide), hfr23 11 (by decide) (by decide), hfr22 11 (by decide) (by decide), hfr21 11 (by decide) (by decide), hfr20 11 (by decide) (by decide), hfr19 11 (by decide) (by decide), hfr18 11 (by decide) (by decide), hfr17 11 (by decide) (by decide), hfr16 11 (by decide) (by decide), hfr15 11 (by decide) (by decide), hfr14 11 (by decide) (by decide), hfr13 11 (by decide) (by decide), hfr12 11 (by decide) (by decide)]
  rw [hkeep11 11 (by decide) (by decide)] at hbut11
  have hr32u12 : r32.val[12]! = r13.val[12]! := by
    rw [hfr31 12 (by decide) (by decide), hfr30 12 (by decide) (by decide), hfr29 12 (by decide) (by decide), hfr28 12 (by decide) (by decide), hfr27 12 (by decide) (by decide), hfr26 12 (by decide) (by decide), hfr25 12 (by decide) (by decide), hfr24 12 (by decide) (by decide), hfr23 12 (by decide) (by decide), hfr22 12 (by decide) (by decide), hfr21 12 (by decide) (by decide), hfr20 12 (by decide) (by decide), hfr19 12 (by decide) (by decide), hfr18 12 (by decide) (by decide), hfr17 12 (by decide) (by decide), hfr16 12 (by decide) (by decide), hfr15 12 (by decide) (by decide), hfr14 12 (by decide) (by decide), hfr13 12 (by decide) (by decide)]
  rw [hkeep12 12 (by decide) (by decide)] at hbut12
  have hr32u13 : r32.val[13]! = r14.val[13]! := by
    rw [hfr31 13 (by decide) (by decide), hfr30 13 (by decide) (by decide), hfr29 13 (by decide) (by decide), hfr28 13 (by decide) (by decide), hfr27 13 (by decide) (by decide), hfr26 13 (by decide) (by decide), hfr25 13 (by decide) (by decide), hfr24 13 (by decide) (by decide), hfr23 13 (by decide) (by decide), hfr22 13 (by decide) (by decide), hfr21 13 (by decide) (by decide), hfr20 13 (by decide) (by decide), hfr19 13 (by decide) (by decide), hfr18 13 (by decide) (by decide), hfr17 13 (by decide) (by decide), hfr16 13 (by decide) (by decide), hfr15 13 (by decide) (by decide), hfr14 13 (by decide) (by decide)]
  rw [hkeep13 13 (by decide) (by decide)] at hbut13
  have hr32u14 : r32.val[14]! = r15.val[14]! := by
    rw [hfr31 14 (by decide) (by decide), hfr30 14 (by decide) (by decide), hfr29 14 (by decide) (by decide), hfr28 14 (by decide) (by decide), hfr27 14 (by decide) (by decide), hfr26 14 (by decide) (by decide), hfr25 14 (by decide) (by decide), hfr24 14 (by decide) (by decide), hfr23 14 (by decide) (by decide), hfr22 14 (by decide) (by decide), hfr21 14 (by decide) (by decide), hfr20 14 (by decide) (by decide), hfr19 14 (by decide) (by decide), hfr18 14 (by decide) (by decide), hfr17 14 (by decide) (by decide), hfr16 14 (by decide) (by decide), hfr15 14 (by decide) (by decide)]
  rw [hkeep14 14 (by decide) (by decide)] at hbut14
  have hr32u15 : r32.val[15]! = r16.val[15]! := by
    rw [hfr31 15 (by decide) (by decide), hfr30 15 (by decide) (by decide), hfr29 15 (by decide) (by decide), hfr28 15 (by decide) (by decide), hfr27 15 (by decide) (by decide), hfr26 15 (by decide) (by decide), hfr25 15 (by decide) (by decide), hfr24 15 (by decide) (by decide), hfr23 15 (by decide) (by decide), hfr22 15 (by decide) (by decide), hfr21 15 (by decide) (by decide), hfr20 15 (by decide) (by decide), hfr19 15 (by decide) (by decide), hfr18 15 (by decide) (by decide), hfr17 15 (by decide) (by decide), hfr16 15 (by decide) (by decide)]
  rw [hkeep15 15 (by decide) (by decide)] at hbut15
  have hr32u16 : r32.val[16]! = r17.val[16]! := by
    rw [hfr31 16 (by decide) (by decide), hfr30 16 (by decide) (by decide), hfr29 16 (by decide) (by decide), hfr28 16 (by decide) (by decide), hfr27 16 (by decide) (by decide), hfr26 16 (by decide) (by decide), hfr25 16 (by decide) (by decide), hfr24 16 (by decide) (by decide), hfr23 16 (by decide) (by decide), hfr22 16 (by decide) (by decide), hfr21 16 (by decide) (by decide), hfr20 16 (by decide) (by decide), hfr19 16 (by decide) (by decide), hfr18 16 (by decide) (by decide), hfr17 16 (by decide) (by decide)]
  rw [hkeep16 16 (by decide) (by decide)] at hbut16
  have hr32u17 : r32.val[17]! = r18.val[17]! := by
    rw [hfr31 17 (by decide) (by decide), hfr30 17 (by decide) (by decide), hfr29 17 (by decide) (by decide), hfr28 17 (by decide) (by decide), hfr27 17 (by decide) (by decide), hfr26 17 (by decide) (by decide), hfr25 17 (by decide) (by decide), hfr24 17 (by decide) (by decide), hfr23 17 (by decide) (by decide), hfr22 17 (by decide) (by decide), hfr21 17 (by decide) (by decide), hfr20 17 (by decide) (by decide), hfr19 17 (by decide) (by decide), hfr18 17 (by decide) (by decide)]
  rw [hkeep17 17 (by decide) (by decide)] at hbut17
  have hr32u18 : r32.val[18]! = r19.val[18]! := by
    rw [hfr31 18 (by decide) (by decide), hfr30 18 (by decide) (by decide), hfr29 18 (by decide) (by decide), hfr28 18 (by decide) (by decide), hfr27 18 (by decide) (by decide), hfr26 18 (by decide) (by decide), hfr25 18 (by decide) (by decide), hfr24 18 (by decide) (by decide), hfr23 18 (by decide) (by decide), hfr22 18 (by decide) (by decide), hfr21 18 (by decide) (by decide), hfr20 18 (by decide) (by decide), hfr19 18 (by decide) (by decide)]
  rw [hkeep18 18 (by decide) (by decide)] at hbut18
  have hr32u19 : r32.val[19]! = r20.val[19]! := by
    rw [hfr31 19 (by decide) (by decide), hfr30 19 (by decide) (by decide), hfr29 19 (by decide) (by decide), hfr28 19 (by decide) (by decide), hfr27 19 (by decide) (by decide), hfr26 19 (by decide) (by decide), hfr25 19 (by decide) (by decide), hfr24 19 (by decide) (by decide), hfr23 19 (by decide) (by decide), hfr22 19 (by decide) (by decide), hfr21 19 (by decide) (by decide), hfr20 19 (by decide) (by decide)]
  rw [hkeep19 19 (by decide) (by decide)] at hbut19
  have hr32u20 : r32.val[20]! = r21.val[20]! := by
    rw [hfr31 20 (by decide) (by decide), hfr30 20 (by decide) (by decide), hfr29 20 (by decide) (by decide), hfr28 20 (by decide) (by decide), hfr27 20 (by decide) (by decide), hfr26 20 (by decide) (by decide), hfr25 20 (by decide) (by decide), hfr24 20 (by decide) (by decide), hfr23 20 (by decide) (by decide), hfr22 20 (by decide) (by decide), hfr21 20 (by decide) (by decide)]
  rw [hkeep20 20 (by decide) (by decide)] at hbut20
  have hr32u21 : r32.val[21]! = r22.val[21]! := by
    rw [hfr31 21 (by decide) (by decide), hfr30 21 (by decide) (by decide), hfr29 21 (by decide) (by decide), hfr28 21 (by decide) (by decide), hfr27 21 (by decide) (by decide), hfr26 21 (by decide) (by decide), hfr25 21 (by decide) (by decide), hfr24 21 (by decide) (by decide), hfr23 21 (by decide) (by decide), hfr22 21 (by decide) (by decide)]
  rw [hkeep21 21 (by decide) (by decide)] at hbut21
  have hr32u22 : r32.val[22]! = r23.val[22]! := by
    rw [hfr31 22 (by decide) (by decide), hfr30 22 (by decide) (by decide), hfr29 22 (by decide) (by decide), hfr28 22 (by decide) (by decide), hfr27 22 (by decide) (by decide), hfr26 22 (by decide) (by decide), hfr25 22 (by decide) (by decide), hfr24 22 (by decide) (by decide), hfr23 22 (by decide) (by decide)]
  rw [hkeep22 22 (by decide) (by decide)] at hbut22
  have hr32u23 : r32.val[23]! = r24.val[23]! := by
    rw [hfr31 23 (by decide) (by decide), hfr30 23 (by decide) (by decide), hfr29 23 (by decide) (by decide), hfr28 23 (by decide) (by decide), hfr27 23 (by decide) (by decide), hfr26 23 (by decide) (by decide), hfr25 23 (by decide) (by decide), hfr24 23 (by decide) (by decide)]
  rw [hkeep23 23 (by decide) (by decide)] at hbut23
  have hr32u24 : r32.val[24]! = r25.val[24]! := by
    rw [hfr31 24 (by decide) (by decide), hfr30 24 (by decide) (by decide), hfr29 24 (by decide) (by decide), hfr28 24 (by decide) (by decide), hfr27 24 (by decide) (by decide), hfr26 24 (by decide) (by decide), hfr25 24 (by decide) (by decide)]
  rw [hkeep24 24 (by decide) (by decide)] at hbut24
  have hr32u25 : r32.val[25]! = r26.val[25]! := by
    rw [hfr31 25 (by decide) (by decide), hfr30 25 (by decide) (by decide), hfr29 25 (by decide) (by decide), hfr28 25 (by decide) (by decide), hfr27 25 (by decide) (by decide), hfr26 25 (by decide) (by decide)]
  rw [hkeep25 25 (by decide) (by decide)] at hbut25
  have hr32u26 : r32.val[26]! = r27.val[26]! := by
    rw [hfr31 26 (by decide) (by decide), hfr30 26 (by decide) (by decide), hfr29 26 (by decide) (by decide), hfr28 26 (by decide) (by decide), hfr27 26 (by decide) (by decide)]
  rw [hkeep26 26 (by decide) (by decide)] at hbut26
  have hr32u27 : r32.val[27]! = r28.val[27]! := by
    rw [hfr31 27 (by decide) (by decide), hfr30 27 (by decide) (by decide), hfr29 27 (by decide) (by decide), hfr28 27 (by decide) (by decide)]
  rw [hkeep27 27 (by decide) (by decide)] at hbut27
  have hr32u28 : r32.val[28]! = r29.val[28]! := by
    rw [hfr31 28 (by decide) (by decide), hfr30 28 (by decide) (by decide), hfr29 28 (by decide) (by decide)]
  rw [hkeep28 28 (by decide) (by decide)] at hbut28
  have hr32u29 : r32.val[29]! = r30.val[29]! := by
    rw [hfr31 29 (by decide) (by decide), hfr30 29 (by decide) (by decide)]
  rw [hkeep29 29 (by decide) (by decide)] at hbut29
  have hr32u30 : r32.val[30]! = r31.val[30]! := by
    rw [hfr31 30 (by decide) (by decide)]
  rw [hkeep30 30 (by decide) (by decide)] at hbut30
  have hr32u31 : r32.val[31]! = r32.val[31]! := by
    rfl
  rw [hkeep31 31 (by decide) (by decide)] at hbut31
  have hbfu0 : ∀ l, l < 8 →
      liftZ ((r32.val[0]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[0]!).values.val[l]!).val
            + liftZ ((re.val[0]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 0 + l / 2))) * (liftZ ((re.val[0]!).values.val[l - 1]!).val
            - liftZ ((re.val[0]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u0]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut0
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 0 + 1 / 2)) = (255 - 4 * 0 - 0) from by decide, zetaInv0_bridge0_0]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 0 + 3 / 2)) = (255 - 4 * 0 - 1) from by decide, zetaInv0_bridge1_0]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 0 + 5 / 2)) = (255 - 4 * 0 - 2) from by decide, zetaInv0_bridge2_0]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 0 + 7 / 2)) = (255 - 4 * 0 - 3) from by decide, zetaInv0_bridge3_0]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu1 : ∀ l, l < 8 →
      liftZ ((r32.val[1]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[1]!).values.val[l]!).val
            + liftZ ((re.val[1]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 1 + l / 2))) * (liftZ ((re.val[1]!).values.val[l - 1]!).val
            - liftZ ((re.val[1]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u1]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut1
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 1 + 1 / 2)) = (255 - 4 * 1 - 0) from by decide, zetaInv0_bridge0_1]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 1 + 3 / 2)) = (255 - 4 * 1 - 1) from by decide, zetaInv0_bridge1_1]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 1 + 5 / 2)) = (255 - 4 * 1 - 2) from by decide, zetaInv0_bridge2_1]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 1 + 7 / 2)) = (255 - 4 * 1 - 3) from by decide, zetaInv0_bridge3_1]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu2 : ∀ l, l < 8 →
      liftZ ((r32.val[2]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[2]!).values.val[l]!).val
            + liftZ ((re.val[2]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 2 + l / 2))) * (liftZ ((re.val[2]!).values.val[l - 1]!).val
            - liftZ ((re.val[2]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u2]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut2
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 2 + 1 / 2)) = (255 - 4 * 2 - 0) from by decide, zetaInv0_bridge0_2]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 2 + 3 / 2)) = (255 - 4 * 2 - 1) from by decide, zetaInv0_bridge1_2]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 2 + 5 / 2)) = (255 - 4 * 2 - 2) from by decide, zetaInv0_bridge2_2]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 2 + 7 / 2)) = (255 - 4 * 2 - 3) from by decide, zetaInv0_bridge3_2]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu3 : ∀ l, l < 8 →
      liftZ ((r32.val[3]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[3]!).values.val[l]!).val
            + liftZ ((re.val[3]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 3 + l / 2))) * (liftZ ((re.val[3]!).values.val[l - 1]!).val
            - liftZ ((re.val[3]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u3]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut3
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 3 + 1 / 2)) = (255 - 4 * 3 - 0) from by decide, zetaInv0_bridge0_3]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 3 + 3 / 2)) = (255 - 4 * 3 - 1) from by decide, zetaInv0_bridge1_3]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 3 + 5 / 2)) = (255 - 4 * 3 - 2) from by decide, zetaInv0_bridge2_3]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 3 + 7 / 2)) = (255 - 4 * 3 - 3) from by decide, zetaInv0_bridge3_3]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu4 : ∀ l, l < 8 →
      liftZ ((r32.val[4]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[4]!).values.val[l]!).val
            + liftZ ((re.val[4]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 4 + l / 2))) * (liftZ ((re.val[4]!).values.val[l - 1]!).val
            - liftZ ((re.val[4]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u4]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut4
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 4 + 1 / 2)) = (255 - 4 * 4 - 0) from by decide, zetaInv0_bridge0_4]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 4 + 3 / 2)) = (255 - 4 * 4 - 1) from by decide, zetaInv0_bridge1_4]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 4 + 5 / 2)) = (255 - 4 * 4 - 2) from by decide, zetaInv0_bridge2_4]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 4 + 7 / 2)) = (255 - 4 * 4 - 3) from by decide, zetaInv0_bridge3_4]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu5 : ∀ l, l < 8 →
      liftZ ((r32.val[5]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[5]!).values.val[l]!).val
            + liftZ ((re.val[5]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 5 + l / 2))) * (liftZ ((re.val[5]!).values.val[l - 1]!).val
            - liftZ ((re.val[5]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u5]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut5
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 5 + 1 / 2)) = (255 - 4 * 5 - 0) from by decide, zetaInv0_bridge0_5]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 5 + 3 / 2)) = (255 - 4 * 5 - 1) from by decide, zetaInv0_bridge1_5]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 5 + 5 / 2)) = (255 - 4 * 5 - 2) from by decide, zetaInv0_bridge2_5]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 5 + 7 / 2)) = (255 - 4 * 5 - 3) from by decide, zetaInv0_bridge3_5]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu6 : ∀ l, l < 8 →
      liftZ ((r32.val[6]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[6]!).values.val[l]!).val
            + liftZ ((re.val[6]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 6 + l / 2))) * (liftZ ((re.val[6]!).values.val[l - 1]!).val
            - liftZ ((re.val[6]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u6]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut6
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 6 + 1 / 2)) = (255 - 4 * 6 - 0) from by decide, zetaInv0_bridge0_6]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 6 + 3 / 2)) = (255 - 4 * 6 - 1) from by decide, zetaInv0_bridge1_6]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 6 + 5 / 2)) = (255 - 4 * 6 - 2) from by decide, zetaInv0_bridge2_6]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 6 + 7 / 2)) = (255 - 4 * 6 - 3) from by decide, zetaInv0_bridge3_6]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu7 : ∀ l, l < 8 →
      liftZ ((r32.val[7]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[7]!).values.val[l]!).val
            + liftZ ((re.val[7]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 7 + l / 2))) * (liftZ ((re.val[7]!).values.val[l - 1]!).val
            - liftZ ((re.val[7]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u7]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut7
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 7 + 1 / 2)) = (255 - 4 * 7 - 0) from by decide, zetaInv0_bridge0_7]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 7 + 3 / 2)) = (255 - 4 * 7 - 1) from by decide, zetaInv0_bridge1_7]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 7 + 5 / 2)) = (255 - 4 * 7 - 2) from by decide, zetaInv0_bridge2_7]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 7 + 7 / 2)) = (255 - 4 * 7 - 3) from by decide, zetaInv0_bridge3_7]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu8 : ∀ l, l < 8 →
      liftZ ((r32.val[8]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[8]!).values.val[l]!).val
            + liftZ ((re.val[8]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 8 + l / 2))) * (liftZ ((re.val[8]!).values.val[l - 1]!).val
            - liftZ ((re.val[8]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u8]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut8
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 8 + 1 / 2)) = (255 - 4 * 8 - 0) from by decide, zetaInv0_bridge0_8]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 8 + 3 / 2)) = (255 - 4 * 8 - 1) from by decide, zetaInv0_bridge1_8]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 8 + 5 / 2)) = (255 - 4 * 8 - 2) from by decide, zetaInv0_bridge2_8]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 8 + 7 / 2)) = (255 - 4 * 8 - 3) from by decide, zetaInv0_bridge3_8]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu9 : ∀ l, l < 8 →
      liftZ ((r32.val[9]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[9]!).values.val[l]!).val
            + liftZ ((re.val[9]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 9 + l / 2))) * (liftZ ((re.val[9]!).values.val[l - 1]!).val
            - liftZ ((re.val[9]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u9]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut9
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 9 + 1 / 2)) = (255 - 4 * 9 - 0) from by decide, zetaInv0_bridge0_9]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 9 + 3 / 2)) = (255 - 4 * 9 - 1) from by decide, zetaInv0_bridge1_9]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 9 + 5 / 2)) = (255 - 4 * 9 - 2) from by decide, zetaInv0_bridge2_9]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 9 + 7 / 2)) = (255 - 4 * 9 - 3) from by decide, zetaInv0_bridge3_9]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu10 : ∀ l, l < 8 →
      liftZ ((r32.val[10]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[10]!).values.val[l]!).val
            + liftZ ((re.val[10]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 10 + l / 2))) * (liftZ ((re.val[10]!).values.val[l - 1]!).val
            - liftZ ((re.val[10]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u10]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut10
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 10 + 1 / 2)) = (255 - 4 * 10 - 0) from by decide, zetaInv0_bridge0_10]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 10 + 3 / 2)) = (255 - 4 * 10 - 1) from by decide, zetaInv0_bridge1_10]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 10 + 5 / 2)) = (255 - 4 * 10 - 2) from by decide, zetaInv0_bridge2_10]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 10 + 7 / 2)) = (255 - 4 * 10 - 3) from by decide, zetaInv0_bridge3_10]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu11 : ∀ l, l < 8 →
      liftZ ((r32.val[11]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[11]!).values.val[l]!).val
            + liftZ ((re.val[11]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 11 + l / 2))) * (liftZ ((re.val[11]!).values.val[l - 1]!).val
            - liftZ ((re.val[11]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u11]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut11
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 11 + 1 / 2)) = (255 - 4 * 11 - 0) from by decide, zetaInv0_bridge0_11]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 11 + 3 / 2)) = (255 - 4 * 11 - 1) from by decide, zetaInv0_bridge1_11]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 11 + 5 / 2)) = (255 - 4 * 11 - 2) from by decide, zetaInv0_bridge2_11]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 11 + 7 / 2)) = (255 - 4 * 11 - 3) from by decide, zetaInv0_bridge3_11]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu12 : ∀ l, l < 8 →
      liftZ ((r32.val[12]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[12]!).values.val[l]!).val
            + liftZ ((re.val[12]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 12 + l / 2))) * (liftZ ((re.val[12]!).values.val[l - 1]!).val
            - liftZ ((re.val[12]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u12]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut12
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 12 + 1 / 2)) = (255 - 4 * 12 - 0) from by decide, zetaInv0_bridge0_12]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 12 + 3 / 2)) = (255 - 4 * 12 - 1) from by decide, zetaInv0_bridge1_12]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 12 + 5 / 2)) = (255 - 4 * 12 - 2) from by decide, zetaInv0_bridge2_12]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 12 + 7 / 2)) = (255 - 4 * 12 - 3) from by decide, zetaInv0_bridge3_12]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu13 : ∀ l, l < 8 →
      liftZ ((r32.val[13]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[13]!).values.val[l]!).val
            + liftZ ((re.val[13]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 13 + l / 2))) * (liftZ ((re.val[13]!).values.val[l - 1]!).val
            - liftZ ((re.val[13]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u13]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut13
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 13 + 1 / 2)) = (255 - 4 * 13 - 0) from by decide, zetaInv0_bridge0_13]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 13 + 3 / 2)) = (255 - 4 * 13 - 1) from by decide, zetaInv0_bridge1_13]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 13 + 5 / 2)) = (255 - 4 * 13 - 2) from by decide, zetaInv0_bridge2_13]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 13 + 7 / 2)) = (255 - 4 * 13 - 3) from by decide, zetaInv0_bridge3_13]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu14 : ∀ l, l < 8 →
      liftZ ((r32.val[14]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[14]!).values.val[l]!).val
            + liftZ ((re.val[14]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 14 + l / 2))) * (liftZ ((re.val[14]!).values.val[l - 1]!).val
            - liftZ ((re.val[14]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u14]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut14
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 14 + 1 / 2)) = (255 - 4 * 14 - 0) from by decide, zetaInv0_bridge0_14]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 14 + 3 / 2)) = (255 - 4 * 14 - 1) from by decide, zetaInv0_bridge1_14]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 14 + 5 / 2)) = (255 - 4 * 14 - 2) from by decide, zetaInv0_bridge2_14]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 14 + 7 / 2)) = (255 - 4 * 14 - 3) from by decide, zetaInv0_bridge3_14]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu15 : ∀ l, l < 8 →
      liftZ ((r32.val[15]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[15]!).values.val[l]!).val
            + liftZ ((re.val[15]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 15 + l / 2))) * (liftZ ((re.val[15]!).values.val[l - 1]!).val
            - liftZ ((re.val[15]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u15]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut15
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 15 + 1 / 2)) = (255 - 4 * 15 - 0) from by decide, zetaInv0_bridge0_15]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 15 + 3 / 2)) = (255 - 4 * 15 - 1) from by decide, zetaInv0_bridge1_15]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 15 + 5 / 2)) = (255 - 4 * 15 - 2) from by decide, zetaInv0_bridge2_15]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 15 + 7 / 2)) = (255 - 4 * 15 - 3) from by decide, zetaInv0_bridge3_15]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu16 : ∀ l, l < 8 →
      liftZ ((r32.val[16]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[16]!).values.val[l]!).val
            + liftZ ((re.val[16]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 16 + l / 2))) * (liftZ ((re.val[16]!).values.val[l - 1]!).val
            - liftZ ((re.val[16]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u16]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut16
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 16 + 1 / 2)) = (255 - 4 * 16 - 0) from by decide, zetaInv0_bridge0_16]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 16 + 3 / 2)) = (255 - 4 * 16 - 1) from by decide, zetaInv0_bridge1_16]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 16 + 5 / 2)) = (255 - 4 * 16 - 2) from by decide, zetaInv0_bridge2_16]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 16 + 7 / 2)) = (255 - 4 * 16 - 3) from by decide, zetaInv0_bridge3_16]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu17 : ∀ l, l < 8 →
      liftZ ((r32.val[17]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[17]!).values.val[l]!).val
            + liftZ ((re.val[17]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 17 + l / 2))) * (liftZ ((re.val[17]!).values.val[l - 1]!).val
            - liftZ ((re.val[17]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u17]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut17
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 17 + 1 / 2)) = (255 - 4 * 17 - 0) from by decide, zetaInv0_bridge0_17]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 17 + 3 / 2)) = (255 - 4 * 17 - 1) from by decide, zetaInv0_bridge1_17]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 17 + 5 / 2)) = (255 - 4 * 17 - 2) from by decide, zetaInv0_bridge2_17]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 17 + 7 / 2)) = (255 - 4 * 17 - 3) from by decide, zetaInv0_bridge3_17]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu18 : ∀ l, l < 8 →
      liftZ ((r32.val[18]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[18]!).values.val[l]!).val
            + liftZ ((re.val[18]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 18 + l / 2))) * (liftZ ((re.val[18]!).values.val[l - 1]!).val
            - liftZ ((re.val[18]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u18]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut18
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 18 + 1 / 2)) = (255 - 4 * 18 - 0) from by decide, zetaInv0_bridge0_18]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 18 + 3 / 2)) = (255 - 4 * 18 - 1) from by decide, zetaInv0_bridge1_18]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 18 + 5 / 2)) = (255 - 4 * 18 - 2) from by decide, zetaInv0_bridge2_18]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 18 + 7 / 2)) = (255 - 4 * 18 - 3) from by decide, zetaInv0_bridge3_18]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu19 : ∀ l, l < 8 →
      liftZ ((r32.val[19]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[19]!).values.val[l]!).val
            + liftZ ((re.val[19]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 19 + l / 2))) * (liftZ ((re.val[19]!).values.val[l - 1]!).val
            - liftZ ((re.val[19]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u19]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut19
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 19 + 1 / 2)) = (255 - 4 * 19 - 0) from by decide, zetaInv0_bridge0_19]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 19 + 3 / 2)) = (255 - 4 * 19 - 1) from by decide, zetaInv0_bridge1_19]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 19 + 5 / 2)) = (255 - 4 * 19 - 2) from by decide, zetaInv0_bridge2_19]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 19 + 7 / 2)) = (255 - 4 * 19 - 3) from by decide, zetaInv0_bridge3_19]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu20 : ∀ l, l < 8 →
      liftZ ((r32.val[20]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[20]!).values.val[l]!).val
            + liftZ ((re.val[20]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 20 + l / 2))) * (liftZ ((re.val[20]!).values.val[l - 1]!).val
            - liftZ ((re.val[20]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u20]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut20
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 20 + 1 / 2)) = (255 - 4 * 20 - 0) from by decide, zetaInv0_bridge0_20]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 20 + 3 / 2)) = (255 - 4 * 20 - 1) from by decide, zetaInv0_bridge1_20]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 20 + 5 / 2)) = (255 - 4 * 20 - 2) from by decide, zetaInv0_bridge2_20]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 20 + 7 / 2)) = (255 - 4 * 20 - 3) from by decide, zetaInv0_bridge3_20]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu21 : ∀ l, l < 8 →
      liftZ ((r32.val[21]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[21]!).values.val[l]!).val
            + liftZ ((re.val[21]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 21 + l / 2))) * (liftZ ((re.val[21]!).values.val[l - 1]!).val
            - liftZ ((re.val[21]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u21]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut21
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 21 + 1 / 2)) = (255 - 4 * 21 - 0) from by decide, zetaInv0_bridge0_21]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 21 + 3 / 2)) = (255 - 4 * 21 - 1) from by decide, zetaInv0_bridge1_21]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 21 + 5 / 2)) = (255 - 4 * 21 - 2) from by decide, zetaInv0_bridge2_21]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 21 + 7 / 2)) = (255 - 4 * 21 - 3) from by decide, zetaInv0_bridge3_21]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu22 : ∀ l, l < 8 →
      liftZ ((r32.val[22]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[22]!).values.val[l]!).val
            + liftZ ((re.val[22]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 22 + l / 2))) * (liftZ ((re.val[22]!).values.val[l - 1]!).val
            - liftZ ((re.val[22]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u22]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut22
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 22 + 1 / 2)) = (255 - 4 * 22 - 0) from by decide, zetaInv0_bridge0_22]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 22 + 3 / 2)) = (255 - 4 * 22 - 1) from by decide, zetaInv0_bridge1_22]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 22 + 5 / 2)) = (255 - 4 * 22 - 2) from by decide, zetaInv0_bridge2_22]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 22 + 7 / 2)) = (255 - 4 * 22 - 3) from by decide, zetaInv0_bridge3_22]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu23 : ∀ l, l < 8 →
      liftZ ((r32.val[23]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[23]!).values.val[l]!).val
            + liftZ ((re.val[23]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 23 + l / 2))) * (liftZ ((re.val[23]!).values.val[l - 1]!).val
            - liftZ ((re.val[23]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u23]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut23
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 23 + 1 / 2)) = (255 - 4 * 23 - 0) from by decide, zetaInv0_bridge0_23]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 23 + 3 / 2)) = (255 - 4 * 23 - 1) from by decide, zetaInv0_bridge1_23]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 23 + 5 / 2)) = (255 - 4 * 23 - 2) from by decide, zetaInv0_bridge2_23]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 23 + 7 / 2)) = (255 - 4 * 23 - 3) from by decide, zetaInv0_bridge3_23]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu24 : ∀ l, l < 8 →
      liftZ ((r32.val[24]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[24]!).values.val[l]!).val
            + liftZ ((re.val[24]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 24 + l / 2))) * (liftZ ((re.val[24]!).values.val[l - 1]!).val
            - liftZ ((re.val[24]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u24]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut24
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 24 + 1 / 2)) = (255 - 4 * 24 - 0) from by decide, zetaInv0_bridge0_24]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 24 + 3 / 2)) = (255 - 4 * 24 - 1) from by decide, zetaInv0_bridge1_24]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 24 + 5 / 2)) = (255 - 4 * 24 - 2) from by decide, zetaInv0_bridge2_24]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 24 + 7 / 2)) = (255 - 4 * 24 - 3) from by decide, zetaInv0_bridge3_24]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu25 : ∀ l, l < 8 →
      liftZ ((r32.val[25]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[25]!).values.val[l]!).val
            + liftZ ((re.val[25]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 25 + l / 2))) * (liftZ ((re.val[25]!).values.val[l - 1]!).val
            - liftZ ((re.val[25]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u25]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut25
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 25 + 1 / 2)) = (255 - 4 * 25 - 0) from by decide, zetaInv0_bridge0_25]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 25 + 3 / 2)) = (255 - 4 * 25 - 1) from by decide, zetaInv0_bridge1_25]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 25 + 5 / 2)) = (255 - 4 * 25 - 2) from by decide, zetaInv0_bridge2_25]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 25 + 7 / 2)) = (255 - 4 * 25 - 3) from by decide, zetaInv0_bridge3_25]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu26 : ∀ l, l < 8 →
      liftZ ((r32.val[26]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[26]!).values.val[l]!).val
            + liftZ ((re.val[26]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 26 + l / 2))) * (liftZ ((re.val[26]!).values.val[l - 1]!).val
            - liftZ ((re.val[26]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u26]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut26
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 26 + 1 / 2)) = (255 - 4 * 26 - 0) from by decide, zetaInv0_bridge0_26]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 26 + 3 / 2)) = (255 - 4 * 26 - 1) from by decide, zetaInv0_bridge1_26]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 26 + 5 / 2)) = (255 - 4 * 26 - 2) from by decide, zetaInv0_bridge2_26]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 26 + 7 / 2)) = (255 - 4 * 26 - 3) from by decide, zetaInv0_bridge3_26]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu27 : ∀ l, l < 8 →
      liftZ ((r32.val[27]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[27]!).values.val[l]!).val
            + liftZ ((re.val[27]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 27 + l / 2))) * (liftZ ((re.val[27]!).values.val[l - 1]!).val
            - liftZ ((re.val[27]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u27]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut27
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 27 + 1 / 2)) = (255 - 4 * 27 - 0) from by decide, zetaInv0_bridge0_27]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 27 + 3 / 2)) = (255 - 4 * 27 - 1) from by decide, zetaInv0_bridge1_27]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 27 + 5 / 2)) = (255 - 4 * 27 - 2) from by decide, zetaInv0_bridge2_27]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 27 + 7 / 2)) = (255 - 4 * 27 - 3) from by decide, zetaInv0_bridge3_27]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu28 : ∀ l, l < 8 →
      liftZ ((r32.val[28]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[28]!).values.val[l]!).val
            + liftZ ((re.val[28]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 28 + l / 2))) * (liftZ ((re.val[28]!).values.val[l - 1]!).val
            - liftZ ((re.val[28]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u28]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut28
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 28 + 1 / 2)) = (255 - 4 * 28 - 0) from by decide, zetaInv0_bridge0_28]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 28 + 3 / 2)) = (255 - 4 * 28 - 1) from by decide, zetaInv0_bridge1_28]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 28 + 5 / 2)) = (255 - 4 * 28 - 2) from by decide, zetaInv0_bridge2_28]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 28 + 7 / 2)) = (255 - 4 * 28 - 3) from by decide, zetaInv0_bridge3_28]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu29 : ∀ l, l < 8 →
      liftZ ((r32.val[29]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[29]!).values.val[l]!).val
            + liftZ ((re.val[29]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 29 + l / 2))) * (liftZ ((re.val[29]!).values.val[l - 1]!).val
            - liftZ ((re.val[29]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u29]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut29
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 29 + 1 / 2)) = (255 - 4 * 29 - 0) from by decide, zetaInv0_bridge0_29]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 29 + 3 / 2)) = (255 - 4 * 29 - 1) from by decide, zetaInv0_bridge1_29]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 29 + 5 / 2)) = (255 - 4 * 29 - 2) from by decide, zetaInv0_bridge2_29]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 29 + 7 / 2)) = (255 - 4 * 29 - 3) from by decide, zetaInv0_bridge3_29]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu30 : ∀ l, l < 8 →
      liftZ ((r32.val[30]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[30]!).values.val[l]!).val
            + liftZ ((re.val[30]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 30 + l / 2))) * (liftZ ((re.val[30]!).values.val[l - 1]!).val
            - liftZ ((re.val[30]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u30]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut30
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 30 + 1 / 2)) = (255 - 4 * 30 - 0) from by decide, zetaInv0_bridge0_30]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 30 + 3 / 2)) = (255 - 4 * 30 - 1) from by decide, zetaInv0_bridge1_30]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 30 + 5 / 2)) = (255 - 4 * 30 - 2) from by decide, zetaInv0_bridge2_30]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 30 + 7 / 2)) = (255 - 4 * 30 - 3) from by decide, zetaInv0_bridge3_30]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbfu31 : ∀ l, l < 8 →
      liftZ ((r32.val[31]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[31]!).values.val[l]!).val
            + liftZ ((re.val[31]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * 31 + l / 2))) * (liftZ ((re.val[31]!).values.val[l - 1]!).val
            - liftZ ((re.val[31]!).values.val[l]!).val)) := by
    intro l hl; rw [hr32u31]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut31
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]
    | 1, _ => rw [if_neg (by decide), b1, show (255 - (4 * 31 + 1 / 2)) = (255 - 4 * 31 - 0) from by decide, zetaInv0_bridge0_31]; ring
    | 2, _ => rw [if_pos (by decide), b2]
    | 3, _ => rw [if_neg (by decide), b3, show (255 - (4 * 31 + 3 / 2)) = (255 - 4 * 31 - 1) from by decide, zetaInv0_bridge1_31]; ring
    | 4, _ => rw [if_pos (by decide), b4]
    | 5, _ => rw [if_neg (by decide), b5, show (255 - (4 * 31 + 5 / 2)) = (255 - 4 * 31 - 2) from by decide, zetaInv0_bridge2_31]; ring
    | 6, _ => rw [if_pos (by decide), b6]
    | 7, _ => rw [if_neg (by decide), b7, show (255 - (4 * 31 + 7 / 2)) = (255 - 4 * 31 - 3) from by decide, zetaInv0_bridge3_31]; ring
    | (n + 8), h => exact absurd h (by omega)
  have hbf : ∀ u, u < 32 → ∀ l, l < 8 →
      liftZ ((r32.val[u]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[u]!).values.val[l]!).val
            + liftZ ((re.val[u]!).values.val[l + 1]!).val
         else (- zeta (255 - (4 * u + l / 2))) * (liftZ ((re.val[u]!).values.val[l - 1]!).val
            - liftZ ((re.val[u]!).values.val[l]!).val)) := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbfu0 l hl
    | 1, _ => exact hbfu1 l hl
    | 2, _ => exact hbfu2 l hl
    | 3, _ => exact hbfu3 l hl
    | 4, _ => exact hbfu4 l hl
    | 5, _ => exact hbfu5 l hl
    | 6, _ => exact hbfu6 l hl
    | 7, _ => exact hbfu7 l hl
    | 8, _ => exact hbfu8 l hl
    | 9, _ => exact hbfu9 l hl
    | 10, _ => exact hbfu10 l hl
    | 11, _ => exact hbfu11 l hl
    | 12, _ => exact hbfu12 l hl
    | 13, _ => exact hbfu13 l hl
    | 14, _ => exact hbfu14 l hl
    | 15, _ => exact hbfu15 l hl
    | 16, _ => exact hbfu16 l hl
    | 17, _ => exact hbfu17 l hl
    | 18, _ => exact hbfu18 l hl
    | 19, _ => exact hbfu19 l hl
    | 20, _ => exact hbfu20 l hl
    | 21, _ => exact hbfu21 l hl
    | 22, _ => exact hbfu22 l hl
    | 23, _ => exact hbfu23 l hl
    | 24, _ => exact hbfu24 l hl
    | 25, _ => exact hbfu25 l hl
    | 26, _ => exact hbfu26 l hl
    | 27, _ => exact hbfu27 l hl
    | 28, _ => exact hbfu28 l hl
    | 29, _ => exact hbfu29 l hl
    | 30, _ => exact hbfu30 l hl
    | 31, _ => exact hbfu31 l hl
    | (n + 32), h => exact absurd h (by omega)
  have hbnd0 : ∀ l, l < 8 → ((r32.val[0]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u0]; exact hbd0 l hl
  have hbnd1 : ∀ l, l < 8 → ((r32.val[1]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u1]; exact hbd1 l hl
  have hbnd2 : ∀ l, l < 8 → ((r32.val[2]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u2]; exact hbd2 l hl
  have hbnd3 : ∀ l, l < 8 → ((r32.val[3]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u3]; exact hbd3 l hl
  have hbnd4 : ∀ l, l < 8 → ((r32.val[4]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u4]; exact hbd4 l hl
  have hbnd5 : ∀ l, l < 8 → ((r32.val[5]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u5]; exact hbd5 l hl
  have hbnd6 : ∀ l, l < 8 → ((r32.val[6]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u6]; exact hbd6 l hl
  have hbnd7 : ∀ l, l < 8 → ((r32.val[7]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u7]; exact hbd7 l hl
  have hbnd8 : ∀ l, l < 8 → ((r32.val[8]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u8]; exact hbd8 l hl
  have hbnd9 : ∀ l, l < 8 → ((r32.val[9]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u9]; exact hbd9 l hl
  have hbnd10 : ∀ l, l < 8 → ((r32.val[10]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u10]; exact hbd10 l hl
  have hbnd11 : ∀ l, l < 8 → ((r32.val[11]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u11]; exact hbd11 l hl
  have hbnd12 : ∀ l, l < 8 → ((r32.val[12]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u12]; exact hbd12 l hl
  have hbnd13 : ∀ l, l < 8 → ((r32.val[13]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u13]; exact hbd13 l hl
  have hbnd14 : ∀ l, l < 8 → ((r32.val[14]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u14]; exact hbd14 l hl
  have hbnd15 : ∀ l, l < 8 → ((r32.val[15]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u15]; exact hbd15 l hl
  have hbnd16 : ∀ l, l < 8 → ((r32.val[16]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u16]; exact hbd16 l hl
  have hbnd17 : ∀ l, l < 8 → ((r32.val[17]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u17]; exact hbd17 l hl
  have hbnd18 : ∀ l, l < 8 → ((r32.val[18]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u18]; exact hbd18 l hl
  have hbnd19 : ∀ l, l < 8 → ((r32.val[19]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u19]; exact hbd19 l hl
  have hbnd20 : ∀ l, l < 8 → ((r32.val[20]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u20]; exact hbd20 l hl
  have hbnd21 : ∀ l, l < 8 → ((r32.val[21]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u21]; exact hbd21 l hl
  have hbnd22 : ∀ l, l < 8 → ((r32.val[22]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u22]; exact hbd22 l hl
  have hbnd23 : ∀ l, l < 8 → ((r32.val[23]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u23]; exact hbd23 l hl
  have hbnd24 : ∀ l, l < 8 → ((r32.val[24]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u24]; exact hbd24 l hl
  have hbnd25 : ∀ l, l < 8 → ((r32.val[25]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u25]; exact hbd25 l hl
  have hbnd26 : ∀ l, l < 8 → ((r32.val[26]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u26]; exact hbd26 l hl
  have hbnd27 : ∀ l, l < 8 → ((r32.val[27]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u27]; exact hbd27 l hl
  have hbnd28 : ∀ l, l < 8 → ((r32.val[28]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u28]; exact hbd28 l hl
  have hbnd29 : ∀ l, l < 8 → ((r32.val[29]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u29]; exact hbd29 l hl
  have hbnd30 : ∀ l, l < 8 → ((r32.val[30]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u30]; exact hbd30 l hl
  have hbnd31 : ∀ l, l < 8 → ((r32.val[31]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro l hl; rw [hr32u31]; exact hbd31 l hl
  have hbnd : ∀ u, u < 32 → ∀ l, l < 8 →
      ((r32.val[u]!).values.val[l]!).val.natAbs ≤ 2 * B + 2 ^ 24 := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbnd0 l hl
    | 1, _ => exact hbnd1 l hl
    | 2, _ => exact hbnd2 l hl
    | 3, _ => exact hbnd3 l hl
    | 4, _ => exact hbnd4 l hl
    | 5, _ => exact hbnd5 l hl
    | 6, _ => exact hbnd6 l hl
    | 7, _ => exact hbnd7 l hl
    | 8, _ => exact hbnd8 l hl
    | 9, _ => exact hbnd9 l hl
    | 10, _ => exact hbnd10 l hl
    | 11, _ => exact hbnd11 l hl
    | 12, _ => exact hbnd12 l hl
    | 13, _ => exact hbnd13 l hl
    | 14, _ => exact hbnd14 l hl
    | 15, _ => exact hbnd15 l hl
    | 16, _ => exact hbnd16 l hl
    | 17, _ => exact hbnd17 l hl
    | 18, _ => exact hbnd18 l hl
    | 19, _ => exact hbnd19 l hl
    | 20, _ => exact hbnd20 l hl
    | 21, _ => exact hbnd21 l hl
    | 22, _ => exact hbnd22 l hl
    | 23, _ => exact hbnd23 l hl
    | 24, _ => exact hbnd24 l hl
    | 25, _ => exact hbnd25 l hl
    | 26, _ => exact hbnd26 l hl
    | 27, _ => exact hbnd27 l hl
    | 28, _ => exact hbnd28 l hl
    | 29, _ => exact hbnd29 l hl
    | 30, _ => exact hbnd30 l hl
    | 31, _ => exact hbnd31 l hl
    | (n + 32), h => exact absurd h (by omega)
  refine ⟨?_, ?_⟩
  · unfold lift_units
    apply Pure.build_congr
    intro i hi
    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub]
    have huu : i / 8 < 32 := by omega
    have hll : i % 8 < 8 := by omega
    have hb := hbf (i / 8) huu (i % 8) hll
    by_cases hlt : i % 2 < 1
    · have hcond : i % 8 % 2 < 1 := by omega
      rw [if_pos hlt]
      rw [if_pos hcond] at hb
      have hdiv : (i + 1) / 8 = i / 8 := by omega
      have hmod : (i + 1) % 8 = i % 8 + 1 := by omega
      have hidx2 : i + 1 < 256 := by omega
      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 1) hidx2, hdiv, hmod]
      exact hb
    · have hcond : ¬ i % 8 % 2 < 1 := by omega
      rw [if_neg hlt]
      rw [if_neg hcond] at hb
      have hdiv : (i - 1) / 8 = i / 8 := by omega
      have hmod : (i - 1) % 8 = i % 8 - 1 := by omega
      have hidx2 : i - 1 < 256 := by omega
      have hz : 255 - (4 * (i / 8) + i % 8 / 2) = 255 - i / 2 := by omega
      rw [Pure.build_getElem _ (i - 1) hidx2, Pure.build_getElem _ i hi, hdiv, hmod]
      rw [hz] at hb
      exact hb
  · exact hbnd


end libcrux_iot_ml_dsa.Vector.Portable.InvNttDriver
