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

/-! ## Spec-side `@[spec]` lemmas for `keccak_f.{iota,rho_unrolled,pi_unrolled,chi_unrolled}`

These pure-semantics descriptions let `hax_mvcgen` thread the spec
computation as a black-box step rather than drilling into each
function's 25-cell do-block. Crucial for keeping `prc_lift_spec`'s
WP tractable (without these, the impl+spec WP exceeds delab budget). -/

/-- Pure semantics of `keccak_f.iota`: XORs `ROUND_CONSTANTS[round]` into lane 0. -/
def iota_applied (state : Std.Array Std.U64 25#usize) (round : Std.Usize) :
    Std.Array Std.U64 25#usize :=
  state.set 0#usize (state.val[0]! ^^^ keccak_f.ROUND_CONSTANTS.val[round.val]!)

@[spec]
theorem iota_spec (state : Std.Array Std.U64 25#usize) (round : Std.Usize)
    (h : round.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f.iota state round
    ⦃ ⇓ r => ⌜ r = iota_applied state round ⌝ ⦄ := by
  unfold keccak_f.iota
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (unfold iota_applied
       simp_all only [Std.UScalar.eq_equiv_bv_eq, Std.UScalar.bv_xor]
       congr 1
       apply Std.U64.bv_eq_imp_eq
       simp_all [Std.UScalar.bv_xor])

/-- Helper: rotate a `Std.U64` at the BitVec level. -/
private abbrev rot64 (x : Std.U64) (n : Nat) : Std.U64 := ⟨x.bv.rotateLeft n⟩

/-- Pure semantics of `keccak_f.rho_unrolled`: rotates each lane by the
    Keccak ρ-offset table entry. -/
def rho_applied (state : Std.Array Std.U64 25#usize) :
    Std.Array Std.U64 25#usize :=
  Std.Array.make 25#usize [
    rot64 (state.val[0]!) 0,
    rot64 (state.val[1]!) 36,
    rot64 (state.val[2]!) 3,
    rot64 (state.val[3]!) 41,
    rot64 (state.val[4]!) 18,
    rot64 (state.val[5]!) 1,
    rot64 (state.val[6]!) 44,
    rot64 (state.val[7]!) 10,
    rot64 (state.val[8]!) 45,
    rot64 (state.val[9]!) 2,
    rot64 (state.val[10]!) 62,
    rot64 (state.val[11]!) 6,
    rot64 (state.val[12]!) 43,
    rot64 (state.val[13]!) 15,
    rot64 (state.val[14]!) 61,
    rot64 (state.val[15]!) 28,
    rot64 (state.val[16]!) 55,
    rot64 (state.val[17]!) 25,
    rot64 (state.val[18]!) 21,
    rot64 (state.val[19]!) 56,
    rot64 (state.val[20]!) 27,
    rot64 (state.val[21]!) 20,
    rot64 (state.val[22]!) 39,
    rot64 (state.val[23]!) 8,
    rot64 (state.val[24]!) 14]

@[spec]
theorem rho_unrolled_spec (state : Std.Array Std.U64 25#usize) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f.rho_unrolled state
    ⦃ ⇓ r => ⌜ r = rho_applied state ⌝ ⦄ := by
  unfold keccak_f.rho_unrolled
  hax_mvcgen
  all_goals try scalar_tac
  -- Single residual: Array.make 25 [v0..v24] = rho_applied state
  unfold rho_applied
  apply Subtype.ext
  simp only [Std.Array.make]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  all_goals simp_all only [
    show ((0#u32 : Std.U32).val) = 0 from rfl,
    show ((1#u32 : Std.U32).val) = 1 from rfl,
    show ((2#u32 : Std.U32).val) = 2 from rfl,
    show ((3#u32 : Std.U32).val) = 3 from rfl,
    show ((6#u32 : Std.U32).val) = 6 from rfl,
    show ((8#u32 : Std.U32).val) = 8 from rfl,
    show ((10#u32 : Std.U32).val) = 10 from rfl,
    show ((14#u32 : Std.U32).val) = 14 from rfl,
    show ((15#u32 : Std.U32).val) = 15 from rfl,
    show ((18#u32 : Std.U32).val) = 18 from rfl,
    show ((20#u32 : Std.U32).val) = 20 from rfl,
    show ((21#u32 : Std.U32).val) = 21 from rfl,
    show ((25#u32 : Std.U32).val) = 25 from rfl,
    show ((27#u32 : Std.U32).val) = 27 from rfl,
    show ((28#u32 : Std.U32).val) = 28 from rfl,
    show ((36#u32 : Std.U32).val) = 36 from rfl,
    show ((39#u32 : Std.U32).val) = 39 from rfl,
    show ((41#u32 : Std.U32).val) = 41 from rfl,
    show ((43#u32 : Std.U32).val) = 43 from rfl,
    show ((44#u32 : Std.U32).val) = 44 from rfl,
    show ((45#u32 : Std.U32).val) = 45 from rfl,
    show ((55#u32 : Std.U32).val) = 55 from rfl,
    show ((56#u32 : Std.U32).val) = 56 from rfl,
    show ((61#u32 : Std.U32).val) = 61 from rfl,
    show ((62#u32 : Std.U32).val) = 62 from rfl,
    show ((0#usize : Std.Usize).val) = 0 from rfl,
    show ((1#usize : Std.Usize).val) = 1 from rfl,
    show ((2#usize : Std.Usize).val) = 2 from rfl,
    show ((3#usize : Std.Usize).val) = 3 from rfl,
    show ((4#usize : Std.Usize).val) = 4 from rfl,
    show ((5#usize : Std.Usize).val) = 5 from rfl,
    show ((6#usize : Std.Usize).val) = 6 from rfl,
    show ((7#usize : Std.Usize).val) = 7 from rfl,
    show ((8#usize : Std.Usize).val) = 8 from rfl,
    show ((9#usize : Std.Usize).val) = 9 from rfl,
    show ((10#usize : Std.Usize).val) = 10 from rfl,
    show ((11#usize : Std.Usize).val) = 11 from rfl,
    show ((12#usize : Std.Usize).val) = 12 from rfl,
    show ((13#usize : Std.Usize).val) = 13 from rfl,
    show ((14#usize : Std.Usize).val) = 14 from rfl,
    show ((15#usize : Std.Usize).val) = 15 from rfl,
    show ((16#usize : Std.Usize).val) = 16 from rfl,
    show ((17#usize : Std.Usize).val) = 17 from rfl,
    show ((18#usize : Std.Usize).val) = 18 from rfl,
    show ((19#usize : Std.Usize).val) = 19 from rfl,
    show ((20#usize : Std.Usize).val) = 20 from rfl,
    show ((21#usize : Std.Usize).val) = 21 from rfl,
    show ((22#usize : Std.Usize).val) = 22 from rfl,
    show ((23#usize : Std.Usize).val) = 23 from rfl,
    show ((24#usize : Std.Usize).val) = 24 from rfl]

end libcrux_iot_sha3.Equivalence
