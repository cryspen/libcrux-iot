/-
  Rosetta-stone Campaign-1 equivalence: one sub-fn at a time.

  Proves `keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0` is observationally
  equal to the pure-Lean `bit_pi_rho_chi_y0_zeta0` under `KState.fromAeneas`.

  Strategy (per the "minimize unfolding" rule):
  - Consume the existing `@[spec]`-tagged FC lemma `pi_rho_chi_y0_zeta0_spec_fc`
    from `PrcLift.lean` via `mvcgen` — no need to re-do its bv chain locally.
  - The residual `KState.fromAeneas r = bit_pi_rho_chi_y0_zeta0 ...` splits
    into 4 field equalities. The `st` field collapses by `simp` once the
    iso-projection lemmas (`Lane.fromAeneas_*`, `stateArray*FromAeneas_getElem`
    in `Project.lean`) are in scope; `c`/`d`/`i` are trivial chain rewrites.
-/
import LibcruxIotSha3.BitKeccak.Spec
import LibcruxIotSha3.BitKeccak.StateIso
import LibcruxIotSha3.BitKeccak.Project
import LibcruxIotSha3.Equivalence.PrcLift
import Hax

namespace libcrux_iot_sha3.BitKeccak

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3

set_option mvcgen.warning false

/-- Bridge: when `r.i.val = s.i.val + 1` and `s.i.val < 24`, recover the
    UScalar-level equality `r.i = ⟨s.i.bv + 1⟩`. Used in every PrcLift FC
    sub-fn that increments `s.i` (the `_zeta1` family with RC). -/
private theorem usize_succ_eq
    {r s : Aeneas.Std.Usize} (hi_eq : r.val = s.val + 1) (hi : s.val < 24) :
    r = ⟨s.bv + (1 : BitVec System.Platform.numBits)⟩ := by
  apply Std.UScalar.eq_of_val_eq
  rw [hi_eq]
  show s.val + 1 = (s.bv + (1 : BitVec System.Platform.numBits)).toNat
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq
    omega
  have hpow : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) h32
  have hone : (1 : BitVec System.Platform.numBits).toNat = 1 := by
    have h1 : (1 : Nat) % 2 ^ System.Platform.numBits = 1 := by
      apply Nat.mod_eq_of_lt; omega
    simp [BitVec.toNat_ofNat, h1]
  rw [BitVec.toNat_add, hone]
  have hsv : s.bv.toNat = s.val := rfl
  have hmod : (s.bv.toNat + 1) % 2 ^ System.Platform.numBits = s.bv.toNat + 1 := by
    apply Nat.mod_eq_of_lt
    rw [hsv]; omega
  rw [hmod, hsv]

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y0_zeta0_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y0_zeta0 BR (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · -- st: structural collapse via the iso projection lemmas + bit-side unfold
    apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · -- c
    show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · -- d
    show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · -- i
    show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y0_zeta1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y0_zeta1 BR (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · exact usize_succ_eq hi_eq hi

/-! ## No-RC PrcLift sub-fns (y1..y4 × ζ0/ζ1) — preserve `s.i`. -/

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y1_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y1_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y1_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y1_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y2_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y2_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y2_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y2_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y3_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y3_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y3_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y3_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y4_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y4_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec]
theorem bit_pi_rho_chi_y4_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y4_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

end libcrux_iot_sha3.BitKeccak
