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

end libcrux_iot_ml_dsa.Vector.Portable.InvNttDriver
