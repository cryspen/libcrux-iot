/-
  Projection simp-lemma bridge between `Lane.fromAeneas l .zζ` and
  `l.val[ζ]!.bv` for `ζ ∈ {0, 1}`. After applying these as `simp`, the
  per-lane equalities reduce to pure `BitVec 32` equations closable by
  `bv_decide`.
-/
import LibcruxIotSha3.BitKeccak.StateIso

namespace libcrux_iot_sha3.BitKeccak

open Aeneas Aeneas.Std libcrux_iot_sha3

/-- A `Lane2U32` always has two elements; destructure to expose them. -/
private theorem Lane2U32.shape (l : lane.Lane2U32) :
    ∃ a b, l.val = [a, b] := by
  obtain ⟨vs, hlen⟩ := l
  have hu2 : ((2#usize : Std.Usize).val) = 2 := by simp [Std.UScalar.ofNatCore_val_eq]
  have h2 : vs.length = 2 := by rw [hu2] at hlen; exact hlen
  match vs, h2 with
  | [a, b], _ => exact ⟨a, b, rfl⟩

@[simp]
theorem Lane.fromAeneas_z0 (l : lane.Lane2U32) :
    (Lane.fromAeneas l).z0 = l.val[0]!.bv := by
  obtain ⟨a, b, hl⟩ := Lane2U32.shape l
  simp [Lane.fromAeneas, hl]

@[simp]
theorem Lane.fromAeneas_z1 (l : lane.Lane2U32) :
    (Lane.fromAeneas l).z1 = l.val[1]!.bv := by
  obtain ⟨a, b, hl⟩ := Lane2U32.shape l
  simp [Lane.fromAeneas, hl]

/-! ## `stateArray*FromAeneas` indexed reads — bridge to underlying `.val[k]` -/

@[simp]
theorem stateArray25FromAeneas_getElem
    (a : Std.Array lane.Lane2U32 25#usize) (k : Nat) (hk : k < 25) :
    (stateArray25FromAeneas a)[k] = Lane.fromAeneas (a.val[k]'(by
      have h25u : ((25#usize : Std.Usize).val) = 25 := by
        simp [Std.UScalar.ofNatCore_val_eq]
      have := a.property; omega)) := by
  show ((a.val.map Lane.fromAeneas).toArray)[k]'_ = _
  simp [List.getElem_map]

@[simp]
theorem stateArray5FromAeneas_getElem
    (a : Std.Array lane.Lane2U32 5#usize) (k : Nat) (hk : k < 5) :
    (stateArray5FromAeneas a)[k] = Lane.fromAeneas (a.val[k]'(by
      have h5u : ((5#usize : Std.Usize).val) = 5 := by
        simp [Std.UScalar.ofNatCore_val_eq]
      have := a.property; omega)) := by
  show ((a.val.map Lane.fromAeneas).toArray)[k]'_ = _
  simp [List.getElem_map]

end libcrux_iot_sha3.BitKeccak
