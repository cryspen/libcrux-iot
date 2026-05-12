/-
  ρ ∘ π ∘ χ ∘ ι step impl-side spec (round 0).

  Each round's pi_rho_chi step is split across two impl sub-functions:
  - `keccakf1600_round0_pi_rho_chi_1`: rows y=0,1 (4 y_zeta sub-funs;
    consumes one iota constant by incrementing `s.i` once)
  - `keccakf1600_round0_pi_rho_chi_2`: rows y=2,3,4 (6 y_zeta sub-funs;
    no iota consumption)

  This file establishes the preservation invariants needed to compose
  PRC with the θ step (`d` is read but not written) and to step `s.i`
  forward by one round constant. Full r.st content characterisation is
  deferred — it requires 25-cell post-conditions on each sub-function
  and is gated on the M2 spec re-extraction.
-/
import LibcruxIotSha3.Equivalence.Lift
import LibcruxIotSha3.Equivalence.LiftLemmas
import LibcruxIotSha3.Equivalence.ThetaLift
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

/-! ### Primitive spec for `set_with_zeta`

Writes `v` into lane `(5*j + i)` at half `zeta`. Leaves `d`, `i`, `c`
untouched. For now we expose only the preservation form; the
strengthened `r.st = s.st.set (5*j+i) (...)` form requires threading
the internal Usize index through `hpost`. -/

@[spec]
private theorem set_with_zeta_spec
    (s : state.KeccakState) (i j zeta : Std.Usize) (v : Std.U32) {Q}
    (hi : i.val < 5) (hj : j.val < 5) (hzeta : zeta.val < 2)
    (hpost : ∀ r : state.KeccakState,
        r.i = s.i → r.c = s.c → r.d = s.d → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.set_with_zeta s i j zeta v
    ⦃ Q ⦄ := by
  unfold state.KeccakState.set_with_zeta
  mvcgen
  all_goals first | simpa | scalar_tac | (
    simp only [Std.WP.predn] at *
    obtain ⟨_, _⟩ := ‹_ ∧ _›
    apply hpost <;> simp [*])

/-! ### Per-sub-function preservation specs

Each of the 10 `pi_rho_chi_y{0..4}_zeta{0,1}` sub-functions writes 5
cells of `st`; they preserve `d`, `c` and (for all but `y0_zeta1`)
`i`. We register the minimal `r.d = s.d ∧ r.c = s.c ∧ r.i = s.i`
form (with `i` increment exposed for `y0_zeta1`), which is enough to
compose into the prc1 / prc2 composed specs. -/

set_option maxHeartbeats 4000000

local macro "prc_sub_preserves_proof" subfun:ident : tactic =>
  `(tactic|
    (unfold $subfun
     hax_mvcgen <;>
       first | grind | scalar_tac))

@[spec]
private theorem pi_rho_chi_y0_zeta0_spec
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0

@[spec]
private theorem pi_rho_chi_y0_zeta1_spec
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1

@[spec]
private theorem pi_rho_chi_y1_zeta0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y1_zeta0

@[spec]
private theorem pi_rho_chi_y1_zeta1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y1_zeta1

@[spec]
private theorem pi_rho_chi_y2_zeta0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y2_zeta0

@[spec]
private theorem pi_rho_chi_y2_zeta1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y2_zeta1

@[spec]
private theorem pi_rho_chi_y3_zeta0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y3_zeta0

@[spec]
private theorem pi_rho_chi_y3_zeta1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y3_zeta1

@[spec]
private theorem pi_rho_chi_y4_zeta0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y4_zeta0

@[spec]
private theorem pi_rho_chi_y4_zeta1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  prc_sub_preserves_proof keccak.keccakf1600_round0_pi_rho_chi_y4_zeta1

/-! ### Composed prc1 / prc2 specs (impl-side preservation form)

After the 4-sub-function `pi_rho_chi_1` chain, `d`/`c` are preserved
and `i` is incremented by one. After the 6-sub-function `pi_rho_chi_2`
chain, `d`/`c`/`i` are all preserved. Full `r.st` content
characterisation is deferred. -/

set_option maxHeartbeats 2000000 in
theorem pi_rho_chi_1_spec_local
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_1
  hax_mvcgen
  all_goals first | trivial | grind

set_option maxHeartbeats 2000000 in
theorem pi_rho_chi_2_spec_local (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_2
  hax_mvcgen
  all_goals first | trivial | grind

end libcrux_iot_sha3.Equivalence
