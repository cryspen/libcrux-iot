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
import LibcruxIotSha3.Equivalence.ThetaLift
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

/-! ### Primitive spec for `set_with_zeta`

Writes `v` into lane `(5*j + i)` at half `zeta`. Leaves `d`, `i`, `c`
untouched and modifies exactly one half of one lane. We express the
new `r.st` content at the underlying list level (`r.st.val = ...
List.set ...`) rather than at the `Aeneas.Std.Array` level, because
`mvcgen` produces a fresh `Usize r✝²` (with `r✝².val = 5 * j.val +
i.val`) which is *structurally* distinct from a reconstructed
`⟨5*j+i, _⟩#usize` — the two have the same `.val` but the Aeneas
Array form discriminates by the wrapping. `Array.set_val_eq` bridges
the two: `(a.set i x).val = a.val.set i.val x`. -/

@[spec]
private theorem set_with_zeta_spec
    (s : state.KeccakState) (i j zeta : Std.Usize) (v : Std.U32) {Q}
    (hi : i.val < 5) (hj : j.val < 5) (hzeta : zeta.val < 2)
    (hpost : ∀ r : state.KeccakState,
        r.i = s.i → r.c = s.c → r.d = s.d →
        r.st.val = s.st.val.set (5 * j.val + i.val)
                     ((s.st.val[5 * j.val + i.val]!).set zeta v) →
        (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.set_with_zeta s i j zeta v
    ⦃ Q ⦄ := by
  unfold state.KeccakState.set_with_zeta
  mvcgen
  all_goals first | simpa | scalar_tac | (
    simp only [Std.WP.predn] at *
    obtain ⟨_, _⟩ := ‹_ ∧ _›
    apply hpost <;> first | scalar_tac | simp_all [Std.Array.set_val_eq])

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
       scalar_tac))

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
  all_goals (try trivial); scalar_tac

set_option maxHeartbeats 2000000 in
theorem pi_rho_chi_2_spec_local (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜ r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_2
  hax_mvcgen
  all_goals (try trivial); scalar_tac

/-! ## Full-FC sub-function spec template (Step 7 — validated pattern)

The `prc_lift_spec` spec-coupling theorem requires content-level
postconditions on the 10 `pi_rho_chi_y_zeta` sub-functions: each cell
written by the sub-function must be expressed as a chi formula over
rotation-twisted XORs of `s.st`/`s.d` halves. The preservation forms
above don't carry this information, so Step 7 needs an FC layer.

This file currently lands the **first** FC sub-function spec
(`pi_rho_chi_y0_zeta0_spec_fc`) as a validated template — it proves
that `unfold; hax_mvcgen` followed by a refine-and-chain proof pattern
closes the 8-conjunct FC post (d/c/i preservation + 5 cell equations)
inside the project's 16M heartbeat budget. The remaining 9 sub-
function FC specs follow the identical structure with substituted
parameters (per-sub-function `(read_lane, half)` tuples, `bx`-index-
to-d-index permutations, rotation offsets, `(write_lane, half)`
tuples, and RC-table inclusion only for `y0_zeta0` / `y0_zeta1`).

Parameter tables for the 9 remaining sub-functions are documented in
the stage-2 plan, status update for the tenth session segment.

The `_fc` y0_zeta0 spec is **not** `@[spec]`-tagged: the preservation
form above still owns the registry slot so `pi_rho_chi_{1,2}_spec_local`
preservation proofs remain unaffected. Once all 10 FC specs land, the
preservation forms can either be replaced (cleaner) or derived from FC
forms in `RoundEquiv` if both are needed. -/

/-- Common proof pattern for FC sub-function specs: `unfold; hax_mvcgen;`
    then either `scalar_tac` for bounds, or refine the 8-conjunct post
    (d/c/i preservation + 5 cell equations) and discharge each via
    `simp_all` with `Std.UScalar.eq_equiv_bv_eq` (the U32-to-BitVec
    decomposition lemma that's tagged `@[bvify]` but NOT `@[simp]` in
    Aeneas, requiring explicit inclusion here). See
    `Scratch_UScalarNat.lean` for the root-cause investigation. -/
local macro "prc_y_zeta_fc_proof" subfun:ident : tactic => `(tactic|
  (unfold $subfun
   hax_mvcgen
   all_goals first
     | scalar_tac
     | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first
          | (apply Eq.trans ‹_›; assumption)
          | assumption
          | simp_all [Std.Array.set_val_eq, rot32,
                      Std.UScalar.eq_equiv_bv_eq,
                      Std.UScalar.bv_xor, Std.UScalar.bv_and,
                      Std.UScalar.bv_not])))

set_option maxHeartbeats 8000000

/-! ### Chained-set FC helper

`apply_5_writes` takes 5 (lane, half, value) tuples and produces the
List form `((((l.set lane0 (l[lane0]!.set half0 v0)).set lane1 ...).set
lane4 ...))`. Used to express FC sub-function posts compactly, avoiding
the multiline `.set` parsing issue inside `⌜ ⌝`. -/
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

/-- y0_zeta0 FC: 5-cell-equation form (validated template).
    Closes via `prc_y_zeta_fc_proof` macro at 8M heartbeats / ~30s.

    Composition note: this form provides 5 cell values + d/c/i
    preservation. For `prc_lift_spec`, all 50 cells are covered by the
    union of 10 sub-fn FC specs (no preservation-of-unwritten clause
    needed if all 50 cells get explicit equations from prc_1 + prc_2). -/
private theorem pi_rho_chi_y0_zeta0_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[0]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 0
      let bx1 := rot32 (s.st.val[6]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx2 := rot32 (s.st.val[12]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 22
      let bx3 := rot32 (s.st.val[18]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 11
      let bx4 := rot32 (s.st.val[24]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[0]!.val[0]! =
        bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]! ∧
      r.st.val[6]!.val[0]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[12]!.val[1]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[18]!.val[1]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[24]!.val[0]! = bx4 ^^^ ((~~~bx0) &&& bx1) ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0

/-! ### Chained-set FC form: deferred

The chained-set form (one big `r.st.val = apply_5_writes ...` equation
capturing all 25 lanes) would compose cleanly for `prc_lift_spec`, but
closing it requires peeling 5 levels of `.set` via congruence to
expose cell-level U32 equalities. `fcongr` peels only one level at a
time and `repeat' fcongr` doesn't recurse into the inner `Std.Array.set`
operations (which have a different structure than `List.set`).

The `Std.UScalar.eq_equiv_bv_eq` bridge (now in the macro) unlocks
cell-level proofs trivially, per agent investigation in
`Scratch_UScalarNat.lean`. What remains is the peeling step.

Candidates for the next session: write a custom congruence lemma
specific to `apply_5_writes`, OR explicitly state the post as 25
individual cell equations (avoiding the chained-set wrapping). -/

end libcrux_iot_sha3.Equivalence
