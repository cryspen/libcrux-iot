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
import Lean

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false

/-! ### Macro: `preserves_complement`

Given a list of 5 written lane indices, expand to the 40-conjunct
preservation block for the 20 untouched lanes (both halves each).

Usage inside a Triple post:
```
preserves_complement s r [0, 6, 12, 18, 24]
```
expands to
```
r.st.val[1]!.val[0]! = s.st.val[1]!.val[0]! ∧ r.st.val[1]!.val[1]! = s.st.val[1]!.val[1]! ∧
... (40 conjuncts total, for lanes ∈ {1,2,3,4,5,7,8,9,10,11,13,...,23})
```

The 5 other-halves of written lanes (e.g., `r.st.val[0]!.val[1]! = ...`)
remain explicit — they're sub-fn-specific (depend on which half is
written) and don't follow the lane-complement pattern. -/

open Lean in
macro "preserves_complement" s:term:max r:term:max "[" excluded:num,* "]" : term => do
  let excludedNats : List Nat := excluded.getElems.toList.map (·.getNat)
  let preserved : List Nat := (List.range 25).filter (fun l => l ∉ excludedNats)
  preserved.foldrM
    (init := (← `(True)))
    (fun lane acc => do
      let lLit := Syntax.mkNatLit lane
      `(($r).st.val[$lLit]!.val[0]! = ($s).st.val[$lLit]!.val[0]! ∧
        ($r).st.val[$lLit]!.val[1]! = ($s).st.val[$lLit]!.val[1]! ∧ $acc))

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

/-! ## Full-FC sub-function specs (Step 7)

Each of the 10 `pi_rho_chi_y{0..4}_zeta{0,1}` sub-functions writes 5
cells of `st`; we capture them in **50-cell FC form**: 5 written cells
(chi formulas), 5 other-halves of written lanes (preserved), 40 cells
of 20 untouched lanes (preserved via the `preserves_complement` macro).

The FC posts are `@[spec]`-tagged so `hax_mvcgen` threads the cell
content automatically when composing `pi_rho_chi_{1,2}` (via the
`prc_chain_FC` spec) and downstream into `prc_lift_spec`. -/

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
          | scalar_tac
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

/-! y0_zeta0 FC (50-cell form, composes for prc_lift_spec).

    Captures all 25 lanes × 2 halves: 5 written cells (chi formulas), 5
    other-halves of written lanes (preserved), 40 cells of 20 untouched
    lanes (preserved). Closes via `prc_y_zeta_fc_proof` macro at 16M
    heartbeats (the macro's 8-hole `refine` parses right-associatively
    and `simp_all` chains through all 53 conjuncts).

    Per Option B recommendation (agent investigation): chained-set form
    via `apply_5_writes` is blocked on the mvcgen chain-hypothesis
    forward-substitution problem; 50-cell form composes cleanly. -/
set_option maxHeartbeats 16000000 in
@[spec]
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
      -- 5 written cells
      r.st.val[0]!.val[0]! =
        bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]! ∧
      r.st.val[6]!.val[0]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[12]!.val[1]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[18]!.val[1]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[24]!.val[0]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      -- Other halves of written lanes (5 cells preserved)
      r.st.val[0]!.val[1]! = s.st.val[0]!.val[1]! ∧
      r.st.val[6]!.val[1]! = s.st.val[6]!.val[1]! ∧
      r.st.val[12]!.val[0]! = s.st.val[12]!.val[0]! ∧
      r.st.val[18]!.val[0]! = s.st.val[18]!.val[0]! ∧
      r.st.val[24]!.val[1]! = s.st.val[24]!.val[1]! ∧
      -- 20 untouched lanes, both halves (40 cells preserved, via macro)
      preserves_complement s r [0, 6, 12, 18, 24] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0

/-! y0_zeta1 FC: writes lanes 0/6/12/18/24 at halves 1/1/0/0/1;
    RC_INTERLEAVED_1[s.i] XORed into lane 0 half 1; INCREMENTS `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y0_zeta1_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[0]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 0
      let bx1 := rot32 (s.st.val[6]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 22
      let bx2 := rot32 (s.st.val[12]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 21
      let bx3 := rot32 (s.st.val[18]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 10
      let bx4 := rot32 (s.st.val[24]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ∧
      r.st.val[0]!.val[1]! =
        bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]! ∧
      r.st.val[6]!.val[1]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[12]!.val[0]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[18]!.val[0]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[24]!.val[1]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[0]!.val[0]! = s.st.val[0]!.val[0]! ∧
      r.st.val[6]!.val[0]! = s.st.val[6]!.val[0]! ∧
      r.st.val[12]!.val[1]! = s.st.val[12]!.val[1]! ∧
      r.st.val[18]!.val[1]! = s.st.val[18]!.val[1]! ∧
      r.st.val[24]!.val[0]! = s.st.val[24]!.val[0]! ∧
      preserves_complement s r [0, 6, 12, 18, 24] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1

/-! y1_zeta0 FC: writes lanes 2/8/14/15/21 at halves 1/1/1/0/0; preserves `s.i`.
    Shift=2: bx_i reads from write_pos[(i-2) mod 5]. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y1_zeta0_spec_fc
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[15]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 14
      let bx1 := rot32 (s.st.val[21]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 10
      let bx2 := rot32 (s.st.val[2]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 2
      let bx3 := rot32 (s.st.val[8]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 23
      let bx4 := rot32 (s.st.val[14]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 31
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[2]!.val[1]! = bx0 ^^^ ((~~~bx1) &&& bx2) ∧
      r.st.val[8]!.val[1]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[14]!.val[1]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[15]!.val[0]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[21]!.val[0]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[2]!.val[0]! = s.st.val[2]!.val[0]! ∧
      r.st.val[8]!.val[0]! = s.st.val[8]!.val[0]! ∧
      r.st.val[14]!.val[0]! = s.st.val[14]!.val[0]! ∧
      r.st.val[15]!.val[1]! = s.st.val[15]!.val[1]! ∧
      r.st.val[21]!.val[1]! = s.st.val[21]!.val[1]! ∧
      preserves_complement s r [2, 8, 14, 15, 21] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y1_zeta0

/-! y1_zeta1 FC: writes lanes 2/8/14/15/21 at halves 0/0/0/1/1; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y1_zeta1_spec_fc
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[15]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 14
      let bx1 := rot32 (s.st.val[21]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 10
      let bx2 := rot32 (s.st.val[2]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 1
      let bx3 := rot32 (s.st.val[8]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx4 := rot32 (s.st.val[14]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 30
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[2]!.val[0]! = bx0 ^^^ ((~~~bx1) &&& bx2) ∧
      r.st.val[8]!.val[0]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[14]!.val[0]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[15]!.val[1]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[21]!.val[1]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[2]!.val[1]! = s.st.val[2]!.val[1]! ∧
      r.st.val[8]!.val[1]! = s.st.val[8]!.val[1]! ∧
      r.st.val[14]!.val[1]! = s.st.val[14]!.val[1]! ∧
      r.st.val[15]!.val[0]! = s.st.val[15]!.val[0]! ∧
      r.st.val[21]!.val[0]! = s.st.val[21]!.val[0]! ∧
      preserves_complement s r [2, 8, 14, 15, 21] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y1_zeta1

/-! y2_zeta0 FC: writes lanes 4/5/11/17/23 at halves 0/1/0/1/0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y2_zeta0_spec_fc
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[5]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      let bx1 := rot32 (s.st.val[11]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 3
      let bx2 := rot32 (s.st.val[17]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 13
      let bx3 := rot32 (s.st.val[23]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 4
      let bx4 := rot32 (s.st.val[4]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[4]!.val[0]! = bx0 ^^^ ((~~~bx1) &&& bx2) ∧
      r.st.val[5]!.val[1]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[11]!.val[0]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[17]!.val[1]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[23]!.val[0]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[4]!.val[1]! = s.st.val[4]!.val[1]! ∧
      r.st.val[5]!.val[0]! = s.st.val[5]!.val[0]! ∧
      r.st.val[11]!.val[1]! = s.st.val[11]!.val[1]! ∧
      r.st.val[17]!.val[0]! = s.st.val[17]!.val[0]! ∧
      r.st.val[23]!.val[1]! = s.st.val[23]!.val[1]! ∧
      preserves_complement s r [4, 5, 11, 17, 23] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y2_zeta0

/-! y2_zeta1 FC: writes lanes 4/5/11/17/23 at halves 1/0/1/0/1; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y2_zeta1_spec_fc
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[5]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 0
      let bx1 := rot32 (s.st.val[11]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 3
      let bx2 := rot32 (s.st.val[17]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 12
      let bx3 := rot32 (s.st.val[23]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 4
      let bx4 := rot32 (s.st.val[4]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[4]!.val[1]! = bx0 ^^^ ((~~~bx1) &&& bx2) ∧
      r.st.val[5]!.val[0]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[11]!.val[1]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[17]!.val[0]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[23]!.val[1]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[4]!.val[0]! = s.st.val[4]!.val[0]! ∧
      r.st.val[5]!.val[1]! = s.st.val[5]!.val[1]! ∧
      r.st.val[11]!.val[0]! = s.st.val[11]!.val[0]! ∧
      r.st.val[17]!.val[1]! = s.st.val[17]!.val[1]! ∧
      r.st.val[23]!.val[0]! = s.st.val[23]!.val[0]! ∧
      preserves_complement s r [4, 5, 11, 17, 23] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y2_zeta1

/-! y3_zeta0 FC: writes lanes 1/7/13/19/20 at halves 0/0/1/0/1; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y3_zeta0_spec_fc
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[20]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 14
      let bx1 := rot32 (s.st.val[1]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 18
      let bx2 := rot32 (s.st.val[7]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 5
      let bx3 := rot32 (s.st.val[13]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 8
      let bx4 := rot32 (s.st.val[19]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[1]!.val[0]! = bx0 ^^^ ((~~~bx1) &&& bx2) ∧
      r.st.val[7]!.val[0]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[13]!.val[1]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[19]!.val[0]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[20]!.val[1]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[1]!.val[1]! = s.st.val[1]!.val[1]! ∧
      r.st.val[7]!.val[1]! = s.st.val[7]!.val[1]! ∧
      r.st.val[13]!.val[0]! = s.st.val[13]!.val[0]! ∧
      r.st.val[19]!.val[1]! = s.st.val[19]!.val[1]! ∧
      r.st.val[20]!.val[0]! = s.st.val[20]!.val[0]! ∧
      preserves_complement s r [1, 7, 13, 19, 20] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y3_zeta0

/-! y3_zeta1 FC: writes lanes 1/7/13/19/20 at halves 1/1/0/1/0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y3_zeta1_spec_fc
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[20]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 13
      let bx1 := rot32 (s.st.val[1]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 18
      let bx2 := rot32 (s.st.val[7]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 5
      let bx3 := rot32 (s.st.val[13]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 7
      let bx4 := rot32 (s.st.val[19]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[1]!.val[1]! = bx0 ^^^ ((~~~bx1) &&& bx2) ∧
      r.st.val[7]!.val[1]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[13]!.val[0]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[19]!.val[1]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[20]!.val[0]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[1]!.val[0]! = s.st.val[1]!.val[0]! ∧
      r.st.val[7]!.val[0]! = s.st.val[7]!.val[0]! ∧
      r.st.val[13]!.val[1]! = s.st.val[13]!.val[1]! ∧
      r.st.val[19]!.val[0]! = s.st.val[19]!.val[0]! ∧
      r.st.val[20]!.val[1]! = s.st.val[20]!.val[1]! ∧
      preserves_complement s r [1, 7, 13, 19, 20] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y3_zeta1

/-! y4_zeta0 FC: writes lanes 3/9/10/16/22 at halves 1/0/0/1/1; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y4_zeta0_spec_fc
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[10]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 31
      let bx1 := rot32 (s.st.val[16]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 28
      let bx2 := rot32 (s.st.val[22]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 20
      let bx3 := rot32 (s.st.val[3]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 21
      let bx4 := rot32 (s.st.val[9]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[3]!.val[1]! = bx0 ^^^ ((~~~bx1) &&& bx2) ∧
      r.st.val[9]!.val[0]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[10]!.val[0]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[16]!.val[1]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[22]!.val[1]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[3]!.val[0]! = s.st.val[3]!.val[0]! ∧
      r.st.val[9]!.val[1]! = s.st.val[9]!.val[1]! ∧
      r.st.val[10]!.val[1]! = s.st.val[10]!.val[1]! ∧
      r.st.val[16]!.val[0]! = s.st.val[16]!.val[0]! ∧
      r.st.val[22]!.val[0]! = s.st.val[22]!.val[0]! ∧
      preserves_complement s r [3, 9, 10, 16, 22] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y4_zeta0

/-! y4_zeta1 FC: writes lanes 3/9/10/16/22 at halves 0/1/1/0/0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y4_zeta1_spec_fc
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[10]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 31
      let bx1 := rot32 (s.st.val[16]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 27
      let bx2 := rot32 (s.st.val[22]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 19
      let bx3 := rot32 (s.st.val[3]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 20
      let bx4 := rot32 (s.st.val[9]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val[3]!.val[0]! = bx0 ^^^ ((~~~bx1) &&& bx2) ∧
      r.st.val[9]!.val[1]! = bx1 ^^^ ((~~~bx2) &&& bx3) ∧
      r.st.val[10]!.val[1]! = bx2 ^^^ ((~~~bx3) &&& bx4) ∧
      r.st.val[16]!.val[0]! = bx3 ^^^ ((~~~bx4) &&& bx0) ∧
      r.st.val[22]!.val[0]! = bx4 ^^^ ((~~~bx0) &&& bx1) ∧
      r.st.val[3]!.val[1]! = s.st.val[3]!.val[1]! ∧
      r.st.val[9]!.val[0]! = s.st.val[9]!.val[0]! ∧
      r.st.val[10]!.val[0]! = s.st.val[10]!.val[0]! ∧
      r.st.val[16]!.val[1]! = s.st.val[16]!.val[1]! ∧
      r.st.val[22]!.val[1]! = s.st.val[22]!.val[1]! ∧
      preserves_complement s r [3, 9, 10, 16, 22] ⌝ ⦄ := by
  prc_y_zeta_fc_proof keccak.keccakf1600_round0_pi_rho_chi_y4_zeta1

end libcrux_iot_sha3.Equivalence
