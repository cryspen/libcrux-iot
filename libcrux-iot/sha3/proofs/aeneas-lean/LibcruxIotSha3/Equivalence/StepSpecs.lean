/-
  Step preservation specs for rounds 1, 2, 3.

  For every step function used by `keccakf1600_4rounds` (rounds 1–3 of
  θ, π·ρ·χ_1, and π·ρ·χ_2), this file registers `r.st = s.st` /
  `r.i = s.i` (or `r.i = s.i + 1`) preservation as a composed
  `@[spec]`-tagged lemma.

  Each composed spec is closed by unfolding the round function plus
  all 11 (θ) / 4+6 (πρχ) sub-functions, then driving `hax_mvcgen` with
  the primitive `set_lane_value_spec`, `get_with_zeta_spec`,
  `lane_index_spec`, `rotate_left_u32_spec`, and `set_with_zeta_spec`
  specs registered in `ThetaLift.lean` and `PrcLift.lean`.

  Round-0 versions of these specs already exist in `ThetaLift.lean`
  (with stronger postconditions including `d`-cell content) and
  `PrcLift.lean`. This file extends the preservation form to rounds
  1, 2, 3 without re-doing the content strengthening.
-/
import LibcruxIotSha3.Equivalence.ThetaLiftDefs
import LibcruxIotSha3.Equivalence.PrcLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false
set_option maxHeartbeats 4000000

/-! ### Generic step proof macro

Unfolds the named step function plus any provided sub-functions, then
drives `hax_mvcgen` with `grind`/`scalar_tac` to chain the registered
primitive specs. -/

local macro "step_preserve_proof" subs:ident+ : tactic =>
  `(tactic|
    (unfold $subs:ident*
     hax_mvcgen <;> scalar_tac))

/-! ### Round 1 -- θ sub-functions -/

@[spec]
private theorem r1_theta_c_x0_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x0_z0

@[spec]
private theorem r1_theta_c_x0_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x0_z1

@[spec]
private theorem r1_theta_c_x1_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x1_z0

@[spec]
private theorem r1_theta_c_x1_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x1_z1

@[spec]
private theorem r1_theta_c_x2_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x2_z0

@[spec]
private theorem r1_theta_c_x2_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x2_z1

@[spec]
private theorem r1_theta_c_x3_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x3_z0

@[spec]
private theorem r1_theta_c_x3_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x3_z1

@[spec]
private theorem r1_theta_c_x4_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x4_z0

@[spec]
private theorem r1_theta_c_x4_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_c_x4_z1

@[spec]
private theorem r1_theta_d_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_theta_d

theorem theta_round1_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_theta
  hax_mvcgen
  all_goals (try trivial); scalar_tac

/-! ### Round 2 -- θ sub-functions -/

@[spec]
private theorem r2_theta_c_x0_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x0_z0

@[spec]
private theorem r2_theta_c_x0_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x0_z1

@[spec]
private theorem r2_theta_c_x1_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x1_z0

@[spec]
private theorem r2_theta_c_x1_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x1_z1

@[spec]
private theorem r2_theta_c_x2_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x2_z0

@[spec]
private theorem r2_theta_c_x2_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x2_z1

@[spec]
private theorem r2_theta_c_x3_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x3_z0

@[spec]
private theorem r2_theta_c_x3_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x3_z1

@[spec]
private theorem r2_theta_c_x4_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x4_z0

@[spec]
private theorem r2_theta_c_x4_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_c_x4_z1

@[spec]
private theorem r2_theta_d_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_theta_d

theorem theta_round2_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_theta
  hax_mvcgen
  all_goals (try trivial); scalar_tac

/-! ### Round 3 -- θ sub-functions -/

@[spec]
private theorem r3_theta_c_x0_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x0_z0

@[spec]
private theorem r3_theta_c_x0_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x0_z1

@[spec]
private theorem r3_theta_c_x1_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x1_z0

@[spec]
private theorem r3_theta_c_x1_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x1_z1

@[spec]
private theorem r3_theta_c_x2_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x2_z0

@[spec]
private theorem r3_theta_c_x2_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x2_z1

@[spec]
private theorem r3_theta_c_x3_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x3_z0

@[spec]
private theorem r3_theta_c_x3_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x3_z1

@[spec]
private theorem r3_theta_c_x4_z0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x4_z0

@[spec]
private theorem r3_theta_c_x4_z1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_c_x4_z1

@[spec]
private theorem r3_theta_d_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_theta_d

theorem theta_round3_preserves_st_i (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_theta
  hax_mvcgen
  all_goals (try trivial); scalar_tac

/-! ### Round 1 -- πρχ sub-functions and composed -/

@[spec]
private theorem r1_prc_y0_zeta0_preserve
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0

@[spec]
private theorem r1_prc_y0_zeta1_preserve
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1

@[spec]
private theorem r1_prc_y1_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0

@[spec]
private theorem r1_prc_y1_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1

@[spec]
private theorem r1_prc_y2_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0

@[spec]
private theorem r1_prc_y2_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1

@[spec]
private theorem r1_prc_y3_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0

@[spec]
private theorem r1_prc_y3_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1

@[spec]
private theorem r1_prc_y4_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0

@[spec]
private theorem r1_prc_y4_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1

theorem prc1_round1_spec (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_1
  hax_mvcgen
  all_goals (try trivial); scalar_tac

theorem prc2_round1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_2
  hax_mvcgen
  all_goals (try trivial); scalar_tac

/-! ### Round 2 -- πρχ sub-functions and composed -/

@[spec]
private theorem r2_prc_y0_zeta0_preserve
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0

@[spec]
private theorem r2_prc_y0_zeta1_preserve
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1

@[spec]
private theorem r2_prc_y1_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0

@[spec]
private theorem r2_prc_y1_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1

@[spec]
private theorem r2_prc_y2_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0

@[spec]
private theorem r2_prc_y2_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1

@[spec]
private theorem r2_prc_y3_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0

@[spec]
private theorem r2_prc_y3_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1

@[spec]
private theorem r2_prc_y4_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0

@[spec]
private theorem r2_prc_y4_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1

theorem prc1_round2_spec (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_1
  hax_mvcgen
  all_goals (try trivial); scalar_tac

theorem prc2_round2_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_2
  hax_mvcgen
  all_goals (try trivial); scalar_tac

/-! ### Round 3 -- πρχ sub-functions and composed -/

@[spec]
private theorem r3_prc_y0_zeta0_preserve
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0

@[spec]
private theorem r3_prc_y0_zeta1_preserve
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1

@[spec]
private theorem r3_prc_y1_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y1_zeta0

@[spec]
private theorem r3_prc_y1_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y1_zeta1

@[spec]
private theorem r3_prc_y2_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y2_zeta0

@[spec]
private theorem r3_prc_y2_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y2_zeta1

@[spec]
private theorem r3_prc_y3_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y3_zeta0

@[spec]
private theorem r3_prc_y3_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y3_zeta1

@[spec]
private theorem r3_prc_y4_zeta0_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y4_zeta0

@[spec]
private theorem r3_prc_y4_zeta1_preserve (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  step_preserve_proof keccak.keccakf1600_round3_pi_rho_chi_y4_zeta1

theorem prc1_round3_spec (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_pi_rho_chi_1
  hax_mvcgen
  all_goals (try trivial); scalar_tac

theorem prc2_round3_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_pi_rho_chi_2
  hax_mvcgen
  all_goals (try trivial); scalar_tac

end libcrux_iot_sha3.Equivalence
