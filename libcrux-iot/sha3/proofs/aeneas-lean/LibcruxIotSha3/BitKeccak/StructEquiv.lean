/-
  Rosetta-stone Campaign-1 equivalence: one sub-fn at a time.

  Proves `keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0` is observationally
  equal to the pure-Lean `bit_pi_rho_chi_y0_zeta0` under `KState.fromAeneas`.

  Strategy (per the "minimize unfolding" rule):
  - Consume the existing `@[spec high]`-tagged FC lemma `pi_rho_chi_y0_zeta0_spec_fc`
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
import LibcruxIotSha3.Equivalence.ThetaLiftDefs
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
@[spec high]
theorem bit_pi_rho_chi_y0_zeta0_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y0_zeta0 BR (KState.fromAeneas s) ∧
      r.i = s.i ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
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
@[spec high]
theorem bit_pi_rho_chi_y0_zeta1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y0_zeta1 BR (KState.fromAeneas s) ∧
      r.i.val = s.i.val + 1 ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
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
@[spec high]
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
@[spec high]
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
@[spec high]
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
@[spec high]
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
@[spec high]
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
@[spec high]
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
@[spec high]
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
@[spec high]
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

/-! ## θ-stage c-cell sub-fns -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x0_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x0_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x0_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x0_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x1_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x1_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x1_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x1_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x2_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x2_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x2_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x2_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x3_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x3_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x3_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x3_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x4_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x4_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x4_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x4_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem,
      stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

/-! ## θ-stage d-cell sub-fn

The FC `theta_d_spec` gives a 10-conjunct postcondition (one per
`r.d[i]!.val[j]!` cell), unlike the c-family which gives a single
`r.c = s.c.set …` equation. We therefore can't fold the result with
`rw [hd]` + `List.map_set`; we instead reduce to a 5-way
`Vector.ext` and discharge each lane via `Lane.mk.injEq` on z0/z1.
-/

set_option maxHeartbeats 8000000 in
@[spec high]
theorem bit_theta_d_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_d (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hc hd00 hd01 hd10 hd11 hd20 hd21 hd30 hd31 hd40 hd41
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · -- d: 10 cell equalities determine 5 lanes; case-split on i.
    show stateArray5FromAeneas r.d = _
    apply Vector.ext
    intro i hi
    rw [stateArray5FromAeneas_getElem! r.d i hi]
    match i, hi with
    | 0, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd00]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!, Equivalence.rot32]
      · rw [hd01]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!]
    | 1, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd10]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!, Equivalence.rot32]
      · rw [hd11]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!]
    | 2, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd20]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!, Equivalence.rot32]
      · rw [hd21]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!]
    | 3, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd30]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!, Equivalence.rot32]
      · rw [hd31]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!]
    | 4, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd40]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!, Equivalence.rot32]
      · rw [hd41]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          stateArray5FromAeneas_getElem!]
  · show r.i = s.i
    exact hi_eq

/-! ## θ-step composition (round 0)

With the 11 sub-fn equivalences tagged `@[spec high]`, `mvcgen` threads
them through the 11-step do-chain of `keccak.keccakf1600_round0_theta`
(the `high` priority overrides the FC default-priority `@[spec]`s in
`Equivalence/ThetaLiftDefs.lean` that target the same sub-fns). The
residual after `mvcgen` is the definitional unfolding of
`bit_keccakf1600_round0_theta` applied to `KState.fromAeneas s`. -/

section ThetaComp
/-! Same `attribute [local irreducible]` pattern as `PrcLiftComp`
    below — keeps `mvcgen` from whnf-reducing the ~5-line nested set
    chain in each `bit_theta_c_*` sub-fn while threading the 11-bind
    chain. With them irreducible, the chain threads in default
    heartbeats; without, ~4M are needed. -/
attribute [local irreducible]
  bit_theta_c_x0_z0 bit_theta_c_x0_z1
  bit_theta_c_x1_z0 bit_theta_c_x1_z1
  bit_theta_c_x2_z0 bit_theta_c_x2_z1
  bit_theta_c_x3_z0 bit_theta_c_x3_z1
  bit_theta_c_x4_z0 bit_theta_c_x4_z1
  bit_theta_d

@[spec high]
theorem keccakf1600_round0_theta_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_theta (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_theta
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_9, h_8, h_7, h_6, h_5, h_4, h_3, h_2, h_1, h]
  rfl

end ThetaComp

/-! ## PrcLift compositions (round 0)

Same threading pattern as `keccakf1600_round0_theta_eq` — `mvcgen`
uses the `@[spec high]`-tagged bit-side per-sub-fn equivalences. -/

section PrcLiftComp
/-! `attribute [local irreducible]` on the per-sub-fn bit-side defs is
    crucial: without it, `mvcgen` whnf-reduces them while processing the
    bind chain — each contains ~30 lines of nested `Vector.set` /
    `BitVec` operations, and four nested expansions blow well past 4M
    heartbeats. With them irreducible, the chain threads in <200K. -/
attribute [local irreducible]
  bit_pi_rho_chi_y0_zeta0 bit_pi_rho_chi_y0_zeta1
  bit_pi_rho_chi_y1_zeta0 bit_pi_rho_chi_y1_zeta1
  bit_pi_rho_chi_y2_zeta0 bit_pi_rho_chi_y2_zeta1
  bit_pi_rho_chi_y3_zeta0 bit_pi_rho_chi_y3_zeta1
  bit_pi_rho_chi_y4_zeta0 bit_pi_rho_chi_y4_zeta1

@[spec high]
theorem keccakf1600_round0_pi_rho_chi_1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_pi_rho_chi_1 BR (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_1
  mvcgen
  -- vc2.hi: y0_zeta1's precondition `r.i.val < 24` from the conjunctive
  -- post of y0_zeta0_eq. `scalar_tac` reads `r.i = s.i ∧ s.i.val < 24`.
  · scalar_tac
  -- Main chain: thread the 4 hypotheses + close the bit composition.
  · expose_names
    intro h_y1z1
    rw [h_y1z1, h_2, h_1.1, h.1]
    rfl

@[spec high]
theorem keccakf1600_round0_pi_rho_chi_2_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_pi_rho_chi_2 (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_2
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_4, h_3, h_2, h_1, h]
  rfl

end PrcLiftComp

end libcrux_iot_sha3.BitKeccak
