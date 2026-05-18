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

end libcrux_iot_sha3.BitKeccak
