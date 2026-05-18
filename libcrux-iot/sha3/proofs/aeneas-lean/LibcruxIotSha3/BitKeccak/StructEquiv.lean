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

/-! # Round 1 sub-fn equivalences

Same template as the round-0 proofs above, but on the round-1
sub-functions, whose lane addressing follows `impl_perm` (see
`BitKeccak/Spec.lean` round-1 defs for the per-sub-fn mapping). No
round-1 FC `@[spec]` lemmas exist in `Equivalence/`, so `mvcgen` chains
the primitive `get_with_zeta_spec` / `set_with_zeta_spec` /
`set_lane_value_spec` / `rotate_left_u32_spec` / etc. as it threads the
body. -/

/-! ## θ-stage c-cell sub-fns (round 1)

Same proof shape as the round-0 theta_c equivalences. `mvcgen` chains
the FC-default `set_lane_value_spec` and the local `theta_c_x{X}_z{Z}_spec`
in `ThetaLiftDefs.lean`... no wait, those are round-0-specific. For
round 1 mvcgen chains `set_lane_value_spec` + `get_with_zeta_spec` +
`lift`/xor primitives directly through the body. The resulting
hypothesis set is identical in shape to round 0 (since theta_c_x{X}_z{Z}
both end with the same `set_lane_value`). -/

/- Proof template for a round-1 `theta_c_x{X}_z{Z}` equivalence: after
   `hax_mvcgen` on the manually-unfolded body, close the index-bound VCs
   with `scalar_tac`, then `rename_i` the post-conjuncts (`hst, hi_eq,
   hd, hc`) and decompose the bit-side `KState.fromAeneas` equality field
   by field, using `simp [*]` to thread the chain of XOR hypotheses on
   the c-cell. Hygiene disabled so the `rename_i`-introduced names
   (`r`, `hst`, `hi_eq`, `hd`, `hc`) and the theorem's outer `s` resolve
   against the runtime context. -/
set_option hygiene false in
local macro "round1_theta_c_proof" subfun:ident : tactic => `(tactic|
  (unfold $subfun
   hax_mvcgen
   all_goals try scalar_tac
   rename_i r hst hi_eq hd hc
   refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
   · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
     rw [hst]
   · apply Vector.toArray_inj.mp
     simp [stateArray5FromAeneas, hc, List.map_set,
       Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1, KState.fromAeneas,
       stateArray25FromAeneas_getElem, Std.UScalar.bv_xor, *]
   · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
     rw [hd]
   · show r.i = s.i
     exact hi_eq))

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x0_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x0_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x0_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x0_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x0_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x0_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x1_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x1_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x1_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x1_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x1_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x1_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x2_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x2_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x2_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x2_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x2_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x2_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x3_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x3_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x3_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x3_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x3_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x3_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x4_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x4_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x4_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x4_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x4_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x4_z1

/-! ## θ-stage d-cell sub-fn (round 1)

Round 1's `keccakf1600_round1_theta_d` body is a long Array-update chain
(no FC sub-fn `@[spec]` exists in `Equivalence/`); we publish a local
FC `@[spec]` mirroring `Equivalence/ThetaLiftDefs.lean:theta_d_spec` so
the `bit_round1_theta_d_eq` proof can reuse the round-0 template. The
formulas are identical to round 0 (same XOR-rotate-1 pattern on `s.c`);
only the function name differs. -/

set_option maxHeartbeats 1600000 in
@[spec]
private theorem round1_theta_d_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ Equivalence.rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ Equivalence.rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ Equivalence.rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ Equivalence.rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ Equivalence.rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_theta_d
  hax_mvcgen
  all_goals first
    | scalar_tac
    | trivial
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       all_goals first | trivial | assumption | (
         simp only [Std.WP.predn] at *
         try apply Std.U32.bv_eq_imp_eq
         simp_all [Std.UScalar.bv_xor, Equivalence.rot32]))

set_option maxHeartbeats 8000000 in
@[spec high]
theorem bit_round1_theta_d_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_d s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_d (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hc hd00 hd01 hd10 hd11 hd20 hd21 hd30 hd31 hd40 hd41
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = _
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

/-! ## PrcLift sub-fns (round 1)

Round-1 PrcLift sub-fns have no FC `@[spec]` in `Equivalence/PrcLift.lean`,
so we publish private FC specs locally (mirroring the R1-chained-set form
in PrcLift.lean) and then prove the bit-side equivalences using those
FCs as the `mvcgen` consumers. -/

/-- Local copy of `Equivalence.PrcLift.apply_5_writes` (which is `private`
    and not re-exported). Used by the round-1 PrcLift FC posts to express
    the 5-write chain compactly. -/
@[reducible]
private def apply_5_writes
    (l : List lane.Lane2U32)
    (lane0 lane1 lane2 lane3 lane4 : Nat)
    (half0 half1 half2 half3 half4 : Std.Usize)
    (v0 v1 v2 v3 v4 : Std.U32) : List lane.Lane2U32 :=
  let l := l.set lane0 ((l[lane0]!).set half0 v0)
  let l := l.set lane1 ((l[lane1]!).set half1 v1)
  let l := l.set lane2 ((l[lane2]!).set half2 v2)
  let l := l.set lane3 ((l[lane3]!).set half3 v3)
  l.set lane4 ((l[lane4]!).set half4 v4)

/-! ### Round-1 FC specs and bit-side equivalences

Each round-1 PrcLift sub-fn has the same control flow as its round-0
counterpart (5 lane reads, 5 d-cell reads, 5 lift+rotate, 5 chi values,
5 writes), so `hax_mvcgen` produces the same h_25..h_62 names. The
proof bodies of the FC specs below are byte-identical to round 0's
PrcLift.lean templates except for `_round0_` → `_round1_` and the
constants in the post (lanes/halves/rotations). -/

/- Local copy of `Equivalence.PrcLift`'s `prc_y_zeta_no_rc_proof` macro
   (which is `private` and not re-exported). Discharges the 4-conjunct
   FC post for any round's y1..y4 PrcLift sub-fn (no RC step, preserves
   `s.i`). Hygiene disabled so the `h_25..h_55` names produced by
   `hax_mvcgen` resolve. -/
set_option hygiene false in
local macro "round1_prc_y_zeta_no_rc_proof" subfun:ident : tactic => `(tactic|
  (unfold $subfun
   hax_mvcgen
   all_goals try scalar_tac
   expose_names
   refine ⟨?_, ?_, ?_, ?_⟩
   · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
   · exact h_57.trans (h_50.trans (h_43.trans (h_36.trans h_29)))
   · exact h_56.trans (h_49.trans (h_42.trans (h_35.trans h_28)))
   · rw [h_59, h_52, h_45, h_38, h_31]
     norm_num [apply_5_writes]
     congr 6
     all_goals try apply Std.U32.bv_eq_imp_eq
     all_goals (
       simp only [
         h_27.2, h_26.2, h_25,
         h_34.2, h_33.2, h_32,
         h_41.2, h_40.2, h_39,
         h_48.2, h_47.2, h_46,
         h_55.2, h_54.2, h_53,
         h_7, h_9, h_20, h_22, h_24,
         h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
         h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
         Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Equivalence.rot32]
       norm_num)))

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y0_zeta0_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[0]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 0
      let bx1 := Equivalence.rot32 (s.st.val[8]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx2 := Equivalence.rot32 (s.st.val[11]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 22
      let bx3 := Equivalence.rot32 (s.st.val[19]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 11
      let bx4 := Equivalence.rot32 (s.st.val[22]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        0 8 11 19 22
        0#usize 1#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · exact h_59.trans (h_52.trans (h_45.trans (h_38.trans h_31)))
  · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
  · rw [h_61, h_54, h_47, h_40, h_33]
    norm_num [apply_5_writes]
    congr 6
    all_goals try apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        h_29.2, h_27.2, h_26.2, h_25,
        h_36.2, h_35.2, h_34,
        h_43.2, h_42.2, h_41,
        h_50.2, h_49.2, h_48,
        h_57.2, h_56.2, h_55,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Equivalence.rot32]
      norm_num)

/- Round-1 y0_zeta1 FC (RC + s.i++): same proof shape as round-0's
   `pi_rho_chi_y0_zeta1_spec_fc`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y0_zeta1_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[0]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 0
      let bx1 := Equivalence.rot32 (s.st.val[8]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 22
      let bx2 := Equivalence.rot32 (s.st.val[11]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 21
      let bx3 := Equivalence.rot32 (s.st.val[19]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 10
      let bx4 := Equivalence.rot32 (s.st.val[22]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ∧
      r.st.val = apply_5_writes s.st.val
        0 8 11 19 22
        1#usize 0#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_61.trans (h_54.trans (h_47.trans (h_40.trans h_33)))
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · rw [h_59, h_52, h_45, h_38, h_31, h_30]
    rfl
  · rw [h_62, h_55, h_48, h_41, h_34]
    norm_num [apply_5_writes]
    congr 6
    all_goals try apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        h_29.2, h_27.2, h_26.2, h_25,
        h_37.2, h_36.2, h_35,
        h_44.2, h_43.2, h_42,
        h_51.2, h_50.2, h_49,
        h_58.2, h_57.2, h_56,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Equivalence.rot32]
      norm_num)

/-! Round-1 y1..y4 × ζ0/ζ1 FCs (no RC; preserve `s.i`). -/

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y1_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[18]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 14
      let bx1 := Equivalence.rot32 (s.st.val[21]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 10
      let bx2 := Equivalence.rot32 (s.st.val[4]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 2
      let bx3 := Equivalence.rot32 (s.st.val[7]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 23
      let bx4 := Equivalence.rot32 (s.st.val[10]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 31
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 7 10 18 21
        1#usize 1#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y1_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[18]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 14
      let bx1 := Equivalence.rot32 (s.st.val[21]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 10
      let bx2 := Equivalence.rot32 (s.st.val[4]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 1
      let bx3 := Equivalence.rot32 (s.st.val[7]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx4 := Equivalence.rot32 (s.st.val[10]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 30
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 7 10 18 21
        0#usize 0#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y2_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[6]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      let bx1 := Equivalence.rot32 (s.st.val[14]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 3
      let bx2 := Equivalence.rot32 (s.st.val[17]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 13
      let bx3 := Equivalence.rot32 (s.st.val[20]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 4
      let bx4 := Equivalence.rot32 (s.st.val[3]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 6 14 17 20
        1#usize 1#usize 1#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y2_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[6]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 0
      let bx1 := Equivalence.rot32 (s.st.val[14]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 3
      let bx2 := Equivalence.rot32 (s.st.val[17]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 12
      let bx3 := Equivalence.rot32 (s.st.val[20]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 4
      let bx4 := Equivalence.rot32 (s.st.val[3]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 6 14 17 20
        0#usize 0#usize 0#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y3_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[24]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 14
      let bx1 := Equivalence.rot32 (s.st.val[2]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 18
      let bx2 := Equivalence.rot32 (s.st.val[5]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 5
      let bx3 := Equivalence.rot32 (s.st.val[13]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 8
      let bx4 := Equivalence.rot32 (s.st.val[16]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 5 13 16 24
        1#usize 1#usize 0#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y3_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[24]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 13
      let bx1 := Equivalence.rot32 (s.st.val[2]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 18
      let bx2 := Equivalence.rot32 (s.st.val[5]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 5
      let bx3 := Equivalence.rot32 (s.st.val[13]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 7
      let bx4 := Equivalence.rot32 (s.st.val[16]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 5 13 16 24
        0#usize 0#usize 1#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y4_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[12]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 31
      let bx1 := Equivalence.rot32 (s.st.val[15]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 28
      let bx2 := Equivalence.rot32 (s.st.val[23]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 20
      let bx3 := Equivalence.rot32 (s.st.val[1]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 21
      let bx4 := Equivalence.rot32 (s.st.val[9]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 9 12 15 23
        1#usize 0#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y4_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[12]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      let bx1 := Equivalence.rot32 (s.st.val[15]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 27
      let bx2 := Equivalence.rot32 (s.st.val[23]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 19
      let bx3 := Equivalence.rot32 (s.st.val[1]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 20
      let bx4 := Equivalence.rot32 (s.st.val[9]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 9 12 15 23
        0#usize 1#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1

/-! ### Round-1 PrcLift bit-side equivalences

With the 10 FC `@[spec]`s above registered, `mvcgen` threads the
conjunctive post into `hd, hc, hi_eq, hst` exactly as for round 0.
The proof shape mirrors round-0's `bit_pi_rho_chi_*_eq`. -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y0_zeta0_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y0_zeta0 BR (KState.fromAeneas s) ∧
      r.i = s.i ⌝ ⦄ := by
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
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y0_zeta1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y0_zeta1 BR (KState.fromAeneas s) ∧
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

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y1_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y1_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round1_pi_rho_chi_y1_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y1_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round1_pi_rho_chi_y2_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y2_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round1_pi_rho_chi_y2_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y2_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round1_pi_rho_chi_y3_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y3_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round1_pi_rho_chi_y3_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y3_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round1_pi_rho_chi_y4_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y4_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round1_pi_rho_chi_y4_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y4_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
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

/-! ## Compositions (round 1)

Same idiom as round-0's `ThetaComp` / `PrcLiftComp`: `attribute [local
irreducible]` on the round-1 bit-side sub-fn defs keeps `mvcgen` from
whnf-reducing them while threading the bind chain. -/

section Round1ThetaComp
attribute [local irreducible]
  bit_round1_theta_c_x0_z0 bit_round1_theta_c_x0_z1
  bit_round1_theta_c_x1_z0 bit_round1_theta_c_x1_z1
  bit_round1_theta_c_x2_z0 bit_round1_theta_c_x2_z1
  bit_round1_theta_c_x3_z0 bit_round1_theta_c_x3_z1
  bit_round1_theta_c_x4_z0 bit_round1_theta_c_x4_z1
  bit_round1_theta_d

@[spec high]
theorem keccakf1600_round1_theta_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_theta (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_theta
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_9, h_8, h_7, h_6, h_5, h_4, h_3, h_2, h_1, h]
  rfl

end Round1ThetaComp

section Round1PrcLiftComp
attribute [local irreducible]
  bit_round1_pi_rho_chi_y0_zeta0 bit_round1_pi_rho_chi_y0_zeta1
  bit_round1_pi_rho_chi_y1_zeta0 bit_round1_pi_rho_chi_y1_zeta1
  bit_round1_pi_rho_chi_y2_zeta0 bit_round1_pi_rho_chi_y2_zeta1
  bit_round1_pi_rho_chi_y3_zeta0 bit_round1_pi_rho_chi_y3_zeta1
  bit_round1_pi_rho_chi_y4_zeta0 bit_round1_pi_rho_chi_y4_zeta1

@[spec high]
theorem keccakf1600_round1_pi_rho_chi_1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_pi_rho_chi_1 BR (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_1
  mvcgen
  · scalar_tac
  · expose_names
    intro h_y1z1
    rw [h_y1z1, h_2, h_1.1, h.1]
    rfl

@[spec high]
theorem keccakf1600_round1_pi_rho_chi_2_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_pi_rho_chi_2 (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_2
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_4, h_3, h_2, h_1, h]
  rfl

end Round1PrcLiftComp

/-! # Round 2 -/

/-! ## θ-stage c-cell sub-fns (round 2)

Same control flow as round 1 (5 XOR-reads + 1 set_lane_value); the only
differences are the zeta-pattern (the impl_perm²-image of round-0's
column-read pattern) and the function name. So `round1_theta_c_proof`
is reusable. -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x0_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x0_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x0_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x0_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x0_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x0_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x1_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x1_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x1_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x1_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x1_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x1_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x2_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x2_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x2_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x2_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x2_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x2_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x3_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x3_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x3_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x3_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x3_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x3_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x4_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x4_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x4_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x4_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x4_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x4_z1

/-! ## θ-stage d-cell sub-fn (round 2)

Identical formulas to rounds 0/1; only the function name differs. -/

set_option maxHeartbeats 1600000 in
@[spec]
private theorem round2_theta_d_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ Equivalence.rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ Equivalence.rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ Equivalence.rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ Equivalence.rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ Equivalence.rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_theta_d
  hax_mvcgen
  all_goals first
    | scalar_tac
    | trivial
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       all_goals first | trivial | assumption | (
         simp only [Std.WP.predn] at *
         try apply Std.U32.bv_eq_imp_eq
         simp_all [Std.UScalar.bv_xor, Equivalence.rot32]))

set_option maxHeartbeats 8000000 in
@[spec high]
theorem bit_round2_theta_d_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_d s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_d (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hc hd00 hd01 hd10 hd11 hd20 hd21 hd30 hd31 hd40 hd41
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = _
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

/-! ## PrcLift sub-fns (round 2)

Same control flow as round 1, so the round-1 macros `round1_prc_y_zeta_no_rc_proof`
and the FC spec template are reusable. -/

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y0_zeta0_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[0]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 0
      let bx1 := Equivalence.rot32 (s.st.val[7]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx2 := Equivalence.rot32 (s.st.val[14]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 22
      let bx3 := Equivalence.rot32 (s.st.val[16]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 11
      let bx4 := Equivalence.rot32 (s.st.val[23]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        0 7 14 16 23
        0#usize 1#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · exact h_59.trans (h_52.trans (h_45.trans (h_38.trans h_31)))
  · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
  · rw [h_61, h_54, h_47, h_40, h_33]
    norm_num [apply_5_writes]
    congr 6
    all_goals try apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        h_29.2, h_27.2, h_26.2, h_25,
        h_36.2, h_35.2, h_34,
        h_43.2, h_42.2, h_41,
        h_50.2, h_49.2, h_48,
        h_57.2, h_56.2, h_55,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Equivalence.rot32]
      norm_num)

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y0_zeta1_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[0]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 0
      let bx1 := Equivalence.rot32 (s.st.val[7]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 22
      let bx2 := Equivalence.rot32 (s.st.val[14]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 21
      let bx3 := Equivalence.rot32 (s.st.val[16]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 10
      let bx4 := Equivalence.rot32 (s.st.val[23]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ∧
      r.st.val = apply_5_writes s.st.val
        0 7 14 16 23
        1#usize 0#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_61.trans (h_54.trans (h_47.trans (h_40.trans h_33)))
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · rw [h_59, h_52, h_45, h_38, h_31, h_30]
    rfl
  · rw [h_62, h_55, h_48, h_41, h_34]
    norm_num [apply_5_writes]
    congr 6
    all_goals try apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        h_29.2, h_27.2, h_26.2, h_25,
        h_37.2, h_36.2, h_35,
        h_44.2, h_43.2, h_42,
        h_51.2, h_50.2, h_49,
        h_58.2, h_57.2, h_56,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Equivalence.rot32]
      norm_num)

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y1_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[19]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 14
      let bx1 := Equivalence.rot32 (s.st.val[21]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 10
      let bx2 := Equivalence.rot32 (s.st.val[3]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 2
      let bx3 := Equivalence.rot32 (s.st.val[5]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 23
      let bx4 := Equivalence.rot32 (s.st.val[12]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 5 12 19 21
        0#usize 0#usize 0#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y1_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[19]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 14
      let bx1 := Equivalence.rot32 (s.st.val[21]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 10
      let bx2 := Equivalence.rot32 (s.st.val[3]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 1
      let bx3 := Equivalence.rot32 (s.st.val[5]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx4 := Equivalence.rot32 (s.st.val[12]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 30
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 5 12 19 21
        1#usize 1#usize 1#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y2_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[8]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 1
      let bx1 := Equivalence.rot32 (s.st.val[10]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 3
      let bx2 := Equivalence.rot32 (s.st.val[17]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 13
      let bx3 := Equivalence.rot32 (s.st.val[24]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 4
      let bx4 := Equivalence.rot32 (s.st.val[1]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 8 10 17 24
        1#usize 0#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y2_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[8]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 0
      let bx1 := Equivalence.rot32 (s.st.val[10]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 3
      let bx2 := Equivalence.rot32 (s.st.val[17]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 12
      let bx3 := Equivalence.rot32 (s.st.val[24]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 4
      let bx4 := Equivalence.rot32 (s.st.val[1]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 8 10 17 24
        0#usize 1#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y3_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[22]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 14
      let bx1 := Equivalence.rot32 (s.st.val[4]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 18
      let bx2 := Equivalence.rot32 (s.st.val[6]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 5
      let bx3 := Equivalence.rot32 (s.st.val[13]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 8
      let bx4 := Equivalence.rot32 (s.st.val[15]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 6 13 15 22
        1#usize 1#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y3_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[22]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 13
      let bx1 := Equivalence.rot32 (s.st.val[4]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 18
      let bx2 := Equivalence.rot32 (s.st.val[6]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 5
      let bx3 := Equivalence.rot32 (s.st.val[13]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 7
      let bx4 := Equivalence.rot32 (s.st.val[15]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 6 13 15 22
        0#usize 0#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y4_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[11]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 31
      let bx1 := Equivalence.rot32 (s.st.val[18]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      let bx2 := Equivalence.rot32 (s.st.val[20]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 20
      let bx3 := Equivalence.rot32 (s.st.val[2]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 21
      let bx4 := Equivalence.rot32 (s.st.val[9]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 9 11 18 20
        0#usize 0#usize 1#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y4_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Equivalence.rot32 (s.st.val[11]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      let bx1 := Equivalence.rot32 (s.st.val[18]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 27
      let bx2 := Equivalence.rot32 (s.st.val[20]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 19
      let bx3 := Equivalence.rot32 (s.st.val[2]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 20
      let bx4 := Equivalence.rot32 (s.st.val[9]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 9 11 18 20
        1#usize 1#usize 0#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1

/-! ### Round-2 PrcLift bit-side equivalences -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y0_zeta0_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y0_zeta0 BR (KState.fromAeneas s) ∧
      r.i = s.i ⌝ ⦄ := by
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
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y0_zeta1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y0_zeta1 BR (KState.fromAeneas s) ∧
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

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y1_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y1_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round2_pi_rho_chi_y1_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y1_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round2_pi_rho_chi_y2_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y2_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round2_pi_rho_chi_y2_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y2_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round2_pi_rho_chi_y3_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y3_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round2_pi_rho_chi_y3_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y3_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round2_pi_rho_chi_y4_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y4_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
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
theorem bit_round2_pi_rho_chi_y4_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y4_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
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

/-! ## Compositions (round 2) -/

section Round2ThetaComp
attribute [local irreducible]
  bit_round2_theta_c_x0_z0 bit_round2_theta_c_x0_z1
  bit_round2_theta_c_x1_z0 bit_round2_theta_c_x1_z1
  bit_round2_theta_c_x2_z0 bit_round2_theta_c_x2_z1
  bit_round2_theta_c_x3_z0 bit_round2_theta_c_x3_z1
  bit_round2_theta_c_x4_z0 bit_round2_theta_c_x4_z1
  bit_round2_theta_d

@[spec high]
theorem keccakf1600_round2_theta_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_theta (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_theta
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_9, h_8, h_7, h_6, h_5, h_4, h_3, h_2, h_1, h]
  rfl

end Round2ThetaComp

section Round2PrcLiftComp
attribute [local irreducible]
  bit_round2_pi_rho_chi_y0_zeta0 bit_round2_pi_rho_chi_y0_zeta1
  bit_round2_pi_rho_chi_y1_zeta0 bit_round2_pi_rho_chi_y1_zeta1
  bit_round2_pi_rho_chi_y2_zeta0 bit_round2_pi_rho_chi_y2_zeta1
  bit_round2_pi_rho_chi_y3_zeta0 bit_round2_pi_rho_chi_y3_zeta1
  bit_round2_pi_rho_chi_y4_zeta0 bit_round2_pi_rho_chi_y4_zeta1

@[spec high]
theorem keccakf1600_round2_pi_rho_chi_1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_pi_rho_chi_1 BR (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_1
  mvcgen
  · scalar_tac
  · expose_names
    intro h_y1z1
    rw [h_y1z1, h_2, h_1.1, h.1]
    rfl

@[spec high]
theorem keccakf1600_round2_pi_rho_chi_2_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_pi_rho_chi_2 (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_2
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_4, h_3, h_2, h_1, h]
  rfl

end Round2PrcLiftComp

end libcrux_iot_sha3.BitKeccak
