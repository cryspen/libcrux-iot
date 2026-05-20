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
import LibcruxIotSha3.Equivalence.RcEquiv
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
    apply hpost <;> scalar_tac)

/-! ## Full-FC sub-function specs (Step 7)

Each of the 10 `pi_rho_chi_y{0..4}_zeta{0,1}` sub-functions writes 5
cells of `st`; we capture them in **50-cell FC form**: 5 written cells
(chi formulas), 5 other-halves of written lanes (preserved), 40 cells
of 20 untouched lanes (preserved via the `preserves_complement` macro).

The FC posts are `@[spec]`-tagged so `hax_mvcgen` threads the cell
content automatically when composing `pi_rho_chi_{1,2}` (via the
`prc_chain_FC` spec) and downstream into `prc_lift_spec`. -/

/-- Legacy macro for the original 50-cell FC posts (kept while migrating
    the remaining FCs to the R1 chained-set form). -/
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

/- Proof body for the R1 chained-set FC posts in the y1-y4 family
   (no RC step, preserves `s.i`). Uses `expose_names` to grab the stable
   hyp names produced by `hax_mvcgen` (which assigns h_25..h_55 to the
   chi value chains and h_28..h_59 to the state chain).
   Hygiene is disabled so that the `h_X` references resolve to the
   runtime-introduced names rather than fresh macro-local ones.
   Shared across rounds 0-3. -/
set_option hygiene false in
macro "prc_y_zeta_no_rc_proof" subfun:ident : tactic => `(tactic|
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
     all_goals apply Std.U32.bv_eq_imp_eq
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
         Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32]
       norm_num)))

set_option maxHeartbeats 8000000

/-! ### Chained-set FC helper

`apply_5_writes` takes 5 (lane, half, value) tuples and produces the
List form `((((l.set lane0 (l[lane0]!.set half0 v0)).set lane1 ...).set
lane4 ...))`. Used to express FC sub-function posts compactly, avoiding
the multiline `.set` parsing issue inside `⌜ ⌝`. -/
@[reducible]
def apply_5_writes
    (l : List lane.Lane2U32)
    (lane0 lane1 lane2 lane3 lane4 : Nat)
    (half0 half1 half2 half3 half4 : Std.Usize)
    (v0 v1 v2 v3 v4 : Std.U32) : List lane.Lane2U32 :=
  let l := l.set lane0 ((l[lane0]!).set half0 v0)
  let l := l.set lane1 ((l[lane1]!).set half1 v1)
  let l := l.set lane2 ((l[lane2]!).set half2 v2)
  let l := l.set lane3 ((l[lane3]!).set half3 v3)
  l.set lane4 ((l[lane4]!).set half4 v4)

/-! y0_zeta0 FC (R1 chained-set form).

    Captures the 5 writes as a single chained `apply_5_writes` equation
    on `r.st.val`. Downstream `simp` with aeneas's List.set/getElem!
    lemmas can evaluate any cell read in O(1). -/
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
      r.st.val = apply_5_writes s.st.val
        0 6 12 18 24
        0#usize 0#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- r.d = s.d
    exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · -- r.c = s.c
    exact h_59.trans (h_52.trans (h_45.trans (h_38.trans h_31)))
  · -- r.i = s.i
    exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
  · -- val-eq: ↑r.st = apply_5_writes ...
    rw [h_61, h_54, h_47, h_40, h_33]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        -- chi 0 chain (r_14)
        h_29.2, h_27.2, h_26.2, h_25,
        -- chi 1 chain (r_18)
        h_36.2, h_35.2, h_34,
        -- chi 2 chain (r_22)
        h_43.2, h_42.2, h_41,
        -- chi 3 chain (r_26)
        h_50.2, h_49.2, h_48,
        -- chi 4 chain (r_30)
        h_57.2, h_56.2, h_55,
        -- rotateLeft hyps (v_4, v_5, v_12, v_13, v_14)
        h_7, h_9, h_20, h_22, h_24,
        -- xor hyps (r_2, r_3, r_7, r_8, r_9)
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        -- RC_INTERLEAVED hyp (r_13)
        h_28,
        -- substitute v_i and r_i to s.st/s.d reads
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32]
      norm_num)

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
      r.st.val = apply_5_writes s.st.val
        0 6 12 18 24
        1#usize 1#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- r.d = s.d
    exact h_61.trans (h_54.trans (h_47.trans (h_40.trans h_33)))
  · -- r.c = s.c
    exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · -- ↑r.i = ↑s.i + 1
    rw [h_59, h_52, h_45, h_38, h_31, h_30]
    rfl
  · -- val-eq
    rw [h_62, h_55, h_48, h_41, h_34]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
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
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32]
      norm_num)

/-! y1_zeta0 FC (R1 chained-set form): writes lanes 2/8/14/15/21 at halves 1/1/1/0/0;
    preserves `s.i`. Shift=2: bx_i reads from write_pos[(i-2) mod 5]. -/
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
      r.st.val = apply_5_writes s.st.val
        2 8 14 15 21
        1#usize 1#usize 1#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round0_pi_rho_chi_y1_zeta0

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
      r.st.val = apply_5_writes s.st.val
        2 8 14 15 21
        0#usize 0#usize 0#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round0_pi_rho_chi_y1_zeta1

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
      r.st.val = apply_5_writes s.st.val
        4 5 11 17 23
        0#usize 1#usize 0#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round0_pi_rho_chi_y2_zeta0

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
      r.st.val = apply_5_writes s.st.val
        4 5 11 17 23
        1#usize 0#usize 1#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round0_pi_rho_chi_y2_zeta1

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
      r.st.val = apply_5_writes s.st.val
        1 7 13 19 20
        0#usize 0#usize 1#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round0_pi_rho_chi_y3_zeta0

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
      r.st.val = apply_5_writes s.st.val
        1 7 13 19 20
        1#usize 1#usize 0#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round0_pi_rho_chi_y3_zeta1

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
      r.st.val = apply_5_writes s.st.val
        3 9 10 16 22
        1#usize 0#usize 0#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round0_pi_rho_chi_y4_zeta0

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
      r.st.val = apply_5_writes s.st.val
        3 9 10 16 22
        0#usize 1#usize 1#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round0_pi_rho_chi_y4_zeta1

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
       simp_all only [Std.UScalar.eq_equiv_bv_eq]
       congr 1
       apply Std.U64.bv_eq_imp_eq
       simp_all [Std.UScalar.bv_xor])

/-- Helper: rotate a `Std.U64` at the BitVec level. -/
abbrev rot64 (x : Std.U64) (n : Nat) : Std.U64 := ⟨x.bv.rotateLeft n⟩

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

/-- Pure semantics of `keccak_f.pi_unrolled`: permutes lanes according
    to the Keccak π-permutation table. No rotation. -/
def pi_applied (state : Std.Array Std.U64 25#usize) :
    Std.Array Std.U64 25#usize :=
  Std.Array.make 25#usize [
    state.val[0]!, state.val[15]!, state.val[5]!, state.val[20]!, state.val[10]!,
    state.val[6]!, state.val[21]!, state.val[11]!, state.val[1]!, state.val[16]!,
    state.val[12]!, state.val[2]!, state.val[17]!, state.val[7]!, state.val[22]!,
    state.val[18]!, state.val[8]!, state.val[23]!, state.val[13]!, state.val[3]!,
    state.val[24]!, state.val[14]!, state.val[4]!, state.val[19]!, state.val[9]!]

@[spec]
theorem pi_unrolled_spec (state : Std.Array Std.U64 25#usize) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f.pi_unrolled state
    ⦃ ⇓ r => ⌜ r = pi_applied state ⌝ ⦄ := by
  unfold keccak_f.pi_unrolled
  hax_mvcgen
  all_goals try scalar_tac
  unfold pi_applied
  apply Subtype.ext
  simp only [Std.Array.make]
  simp_all only [
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

/-- Pure semantics of `keccak_f.chi_unrolled`: applies Keccak χ row-wise.
    Each output `out[i] = state[i] ⊕ (¬state[(i+5)%25] ∧ state[(i+10)%25])`. -/
def chi_applied (state : Std.Array Std.U64 25#usize) :
    Std.Array Std.U64 25#usize :=
  Std.Array.make 25#usize [
    state.val[0]! ^^^ ((~~~state.val[5]!) &&& state.val[10]!),
    state.val[1]! ^^^ ((~~~state.val[6]!) &&& state.val[11]!),
    state.val[2]! ^^^ ((~~~state.val[7]!) &&& state.val[12]!),
    state.val[3]! ^^^ ((~~~state.val[8]!) &&& state.val[13]!),
    state.val[4]! ^^^ ((~~~state.val[9]!) &&& state.val[14]!),
    state.val[5]! ^^^ ((~~~state.val[10]!) &&& state.val[15]!),
    state.val[6]! ^^^ ((~~~state.val[11]!) &&& state.val[16]!),
    state.val[7]! ^^^ ((~~~state.val[12]!) &&& state.val[17]!),
    state.val[8]! ^^^ ((~~~state.val[13]!) &&& state.val[18]!),
    state.val[9]! ^^^ ((~~~state.val[14]!) &&& state.val[19]!),
    state.val[10]! ^^^ ((~~~state.val[15]!) &&& state.val[20]!),
    state.val[11]! ^^^ ((~~~state.val[16]!) &&& state.val[21]!),
    state.val[12]! ^^^ ((~~~state.val[17]!) &&& state.val[22]!),
    state.val[13]! ^^^ ((~~~state.val[18]!) &&& state.val[23]!),
    state.val[14]! ^^^ ((~~~state.val[19]!) &&& state.val[24]!),
    state.val[15]! ^^^ ((~~~state.val[20]!) &&& state.val[0]!),
    state.val[16]! ^^^ ((~~~state.val[21]!) &&& state.val[1]!),
    state.val[17]! ^^^ ((~~~state.val[22]!) &&& state.val[2]!),
    state.val[18]! ^^^ ((~~~state.val[23]!) &&& state.val[3]!),
    state.val[19]! ^^^ ((~~~state.val[24]!) &&& state.val[4]!),
    state.val[20]! ^^^ ((~~~state.val[0]!) &&& state.val[5]!),
    state.val[21]! ^^^ ((~~~state.val[1]!) &&& state.val[6]!),
    state.val[22]! ^^^ ((~~~state.val[2]!) &&& state.val[7]!),
    state.val[23]! ^^^ ((~~~state.val[3]!) &&& state.val[8]!),
    state.val[24]! ^^^ ((~~~state.val[4]!) &&& state.val[9]!)]

set_option maxHeartbeats 16000000 in
@[spec]
theorem chi_unrolled_spec (state : Std.Array Std.U64 25#usize) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f.chi_unrolled state
    ⦃ ⇓ r => ⌜ r = chi_applied state ⌝ ⦄ := by
  unfold keccak_f.chi_unrolled
  hax_mvcgen
  all_goals try scalar_tac
  unfold chi_applied
  apply Subtype.ext
  simp only [Std.Array.make]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  all_goals simp_all only [Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not,
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

/-! ## Intermediate spec for round-0 πρχι (the fused per-cell formula)

Instead of proving the impl/spec equivalence directly against the
4-layer composition `iota_applied (chi_applied (pi_applied (rho_applied
a)))` — which blows up by ~25^4 on unfold — we introduce a monolithic
intermediate spec `prc_spec` that mirrors the impl's fused per-cell
structure (one chi formula per output, with rotation+pi-permuted reads
inlined). -/

/-- Monolithic spec mirroring the impl's fused per-cell structure. For
    each output position i ∈ 0..24, the chi formula reads rho-rotated,
    pi-permuted inputs. π[i] is inlined; ρ-offsets are inlined per
    impl-position via the `inp` helper. Lane 0 receives the iota
    round-constant injection. -/
def prc_spec (a : Std.Array Std.U64 25#usize) (r : Std.Usize) :
    Std.Array Std.U64 25#usize :=
  let inp : Nat → Std.U64 := fun k =>
    match k with
    | 0  => rot64 a.val[0]!  0
    | 1  => rot64 a.val[1]!  36
    | 2  => rot64 a.val[2]!  3
    | 3  => rot64 a.val[3]!  41
    | 4  => rot64 a.val[4]!  18
    | 5  => rot64 a.val[5]!  1
    | 6  => rot64 a.val[6]!  44
    | 7  => rot64 a.val[7]!  10
    | 8  => rot64 a.val[8]!  45
    | 9  => rot64 a.val[9]!  2
    | 10 => rot64 a.val[10]! 62
    | 11 => rot64 a.val[11]! 6
    | 12 => rot64 a.val[12]! 43
    | 13 => rot64 a.val[13]! 15
    | 14 => rot64 a.val[14]! 61
    | 15 => rot64 a.val[15]! 28
    | 16 => rot64 a.val[16]! 55
    | 17 => rot64 a.val[17]! 25
    | 18 => rot64 a.val[18]! 21
    | 19 => rot64 a.val[19]! 56
    | 20 => rot64 a.val[20]! 27
    | 21 => rot64 a.val[21]! 20
    | 22 => rot64 a.val[22]! 39
    | 23 => rot64 a.val[23]! 8
    | _  => rot64 a.val[24]! 14
  Std.Array.make 25#usize [
    -- i=0: π[0]=0, π[5]=6, π[10]=12. Chi row + iota RC.
    inp 0 ^^^ ((~~~ inp 6) &&& inp 12) ^^^ keccak_f.ROUND_CONSTANTS.val[r.val]!,
    -- i=1: π[1]=15, π[6]=21, π[11]=2
    inp 15 ^^^ ((~~~ inp 21) &&& inp 2),
    -- i=2: π[2]=5, π[7]=11, π[12]=17
    inp 5 ^^^ ((~~~ inp 11) &&& inp 17),
    -- i=3: π[3]=20, π[8]=1, π[13]=7
    inp 20 ^^^ ((~~~ inp 1) &&& inp 7),
    -- i=4: π[4]=10, π[9]=16, π[14]=22
    inp 10 ^^^ ((~~~ inp 16) &&& inp 22),
    -- i=5: π[5]=6, π[10]=12, π[15]=18
    inp 6 ^^^ ((~~~ inp 12) &&& inp 18),
    -- i=6: π[6]=21, π[11]=2, π[16]=8
    inp 21 ^^^ ((~~~ inp 2) &&& inp 8),
    -- i=7: π[7]=11, π[12]=17, π[17]=23
    inp 11 ^^^ ((~~~ inp 17) &&& inp 23),
    -- i=8: π[8]=1, π[13]=7, π[18]=13
    inp 1 ^^^ ((~~~ inp 7) &&& inp 13),
    -- i=9: π[9]=16, π[14]=22, π[19]=3
    inp 16 ^^^ ((~~~ inp 22) &&& inp 3),
    -- i=10: π[10]=12, π[15]=18, π[20]=24
    inp 12 ^^^ ((~~~ inp 18) &&& inp 24),
    -- i=11: π[11]=2, π[16]=8, π[21]=14
    inp 2 ^^^ ((~~~ inp 8) &&& inp 14),
    -- i=12: π[12]=17, π[17]=23, π[22]=4
    inp 17 ^^^ ((~~~ inp 23) &&& inp 4),
    -- i=13: π[13]=7, π[18]=13, π[23]=19
    inp 7 ^^^ ((~~~ inp 13) &&& inp 19),
    -- i=14: π[14]=22, π[19]=3, π[24]=9
    inp 22 ^^^ ((~~~ inp 3) &&& inp 9),
    -- i=15: π[15]=18, π[20]=24, π[0]=0
    inp 18 ^^^ ((~~~ inp 24) &&& inp 0),
    -- i=16: π[16]=8, π[21]=14, π[1]=15
    inp 8 ^^^ ((~~~ inp 14) &&& inp 15),
    -- i=17: π[17]=23, π[22]=4, π[2]=5
    inp 23 ^^^ ((~~~ inp 4) &&& inp 5),
    -- i=18: π[18]=13, π[23]=19, π[3]=20
    inp 13 ^^^ ((~~~ inp 19) &&& inp 20),
    -- i=19: π[19]=3, π[24]=9, π[4]=10
    inp 3 ^^^ ((~~~ inp 9) &&& inp 10),
    -- i=20: π[20]=24, π[0]=0, π[5]=6
    inp 24 ^^^ ((~~~ inp 0) &&& inp 6),
    -- i=21: π[21]=14, π[1]=15, π[6]=21
    inp 14 ^^^ ((~~~ inp 15) &&& inp 21),
    -- i=22: π[22]=4, π[2]=5, π[7]=11
    inp 4 ^^^ ((~~~ inp 5) &&& inp 11),
    -- i=23: π[23]=19, π[3]=20, π[8]=1
    inp 19 ^^^ ((~~~ inp 20) &&& inp 1),
    -- i=24: π[24]=9, π[4]=10, π[9]=16
    inp 9 ^^^ ((~~~ inp 10) &&& inp 16)
  ]

/-- Bridge 2: the intermediate `prc_spec` equals the 4-layer composite
    `iota_applied ∘ chi_applied ∘ pi_applied ∘ rho_applied`. Pure
    spec-level identity — no impl side, no chain hyps. -/
theorem prc_spec_eq_composed (a : Std.Array Std.U64 25#usize) (r : Std.Usize) :
    iota_applied (chi_applied (pi_applied (rho_applied a))) r = prc_spec a r := by
  unfold iota_applied chi_applied pi_applied rho_applied prc_spec
  rfl

/-! ## Per-cell access lemmas for `lift_theta_applied`

For the algebraic cascade in `prc_lift_spec`, we need to expose each
`(lift_theta_applied s).val[k]!.bv` as `lift_lane_bv` of theta-XORed
halves. The 25 lemmas below are each `rfl` after unfolding. They serve
the same role as `lift_getElem_bv_N` does for `lift s`. -/

theorem lift_theta_applied_bv_0 (s : state.KeccakState) :
    ((lift_theta_applied s).val[0]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[0]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_1 (s : state.KeccakState) :
    ((lift_theta_applied s).val[1]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[1]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_2 (s : state.KeccakState) :
    ((lift_theta_applied s).val[2]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[2]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_3 (s : state.KeccakState) :
    ((lift_theta_applied s).val[3]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[3]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_4 (s : state.KeccakState) :
    ((lift_theta_applied s).val[4]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[4]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_5 (s : state.KeccakState) :
    ((lift_theta_applied s).val[5]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[5]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_6 (s : state.KeccakState) :
    ((lift_theta_applied s).val[6]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[6]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_7 (s : state.KeccakState) :
    ((lift_theta_applied s).val[7]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[7]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_8 (s : state.KeccakState) :
    ((lift_theta_applied s).val[8]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[8]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_9 (s : state.KeccakState) :
    ((lift_theta_applied s).val[9]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[9]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_10 (s : state.KeccakState) :
    ((lift_theta_applied s).val[10]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[0]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[10]!).val[1]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_11 (s : state.KeccakState) :
    ((lift_theta_applied s).val[11]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[0]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[11]!).val[1]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_12 (s : state.KeccakState) :
    ((lift_theta_applied s).val[12]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[0]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[12]!).val[1]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_13 (s : state.KeccakState) :
    ((lift_theta_applied s).val[13]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[0]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[13]!).val[1]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_14 (s : state.KeccakState) :
    ((lift_theta_applied s).val[14]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[0]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[14]!).val[1]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_15 (s : state.KeccakState) :
    ((lift_theta_applied s).val[15]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[0]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[15]!).val[1]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_16 (s : state.KeccakState) :
    ((lift_theta_applied s).val[16]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[0]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[16]!).val[1]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_17 (s : state.KeccakState) :
    ((lift_theta_applied s).val[17]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[0]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[17]!).val[1]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_18 (s : state.KeccakState) :
    ((lift_theta_applied s).val[18]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[0]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[18]!).val[1]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_19 (s : state.KeccakState) :
    ((lift_theta_applied s).val[19]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[0]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[19]!).val[1]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_20 (s : state.KeccakState) :
    ((lift_theta_applied s).val[20]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[20]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_21 (s : state.KeccakState) :
    ((lift_theta_applied s).val[21]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[21]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_22 (s : state.KeccakState) :
    ((lift_theta_applied s).val[22]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[22]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_23 (s : state.KeccakState) :
    ((lift_theta_applied s).val[23]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[23]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl
theorem lift_theta_applied_bv_24 (s : state.KeccakState) :
    ((lift_theta_applied s).val[24]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[24]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  unfold lift_theta_applied; rfl

/-! ## Bridge 1: `prc_lift_spec`

Couples the impl `keccakf1600_round0_pi_rho_chi_{1,2}` chain to the spec
`iota ∘ chi_unrolled ∘ pi_unrolled ∘ rho_unrolled`. After the recursive
`hax_mvcgen` produces 50 impl cell equations plus 4 spec substitutions,
we rewrite the spec side via Bridge 2 to use `prc_spec`, then close the
25-lane equality via the standard lift cascade (lift_getElem_bv + lift
algebra). -/
set_option maxHeartbeats 32000000 in
@[spec]
theorem prc_lift_spec (s : state.KeccakState) (hi_lt : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let r1 ← keccak.keccakf1600_round0_pi_rho_chi_1 0#usize s
        keccak.keccakf1600_round0_pi_rho_chi_2 r1)
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho_unrolled (lift_theta_applied s)
          let a2 ← keccak_f.pi_unrolled a1
          let a3 ← keccak_f.chi_unrolled a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl impl_perm impl_swap)).holds ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_1
  unfold keccak.keccakf1600_round0_pi_rho_chi_2
  hax_mvcgen
  all_goals try scalar_tac
  subst_vars
  rw [prc_spec_eq_composed]
  casesm* _ ∧ _
  rename_i r9 r8 r7 r6 r5 r4 r3 r2 r1 r' hd hc hi h_chain
    l26 l25 l24 l23 l22 l21 l20 l19 l18 l17 l16 l15 l14 l13 l12 l11 l10 l9 l8
    h_FC9 l7 h_FC8 l6 h_FC7 l5 h_FC6 l4 h_FC5 l3 h_FC4 l2 h_FC3 l1 h_FC2 l_last h_FC1
  -- Substitute d/c/i preservation chains BEFORE the cell split (avoids per-cell duplication).
  simp only [l_last, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17,
    l18, l19, l20, l21, l22, l23, l24, l25, l26]
    at h_chain h_FC1 h_FC2 h_FC3 h_FC4 h_FC5 h_FC6 h_FC7 h_FC8 h_FC9
  have hr'  : (↑r'.st : List lane.Lane2U32).length = 25  := by exact r'.st.2
  have hr1  : (↑r1.st : List lane.Lane2U32).length = 25  := by exact r1.st.2
  have hr2  : (↑r2.st : List lane.Lane2U32).length = 25  := by exact r2.st.2
  have hr3  : (↑r3.st : List lane.Lane2U32).length = 25  := by exact r3.st.2
  have hr4  : (↑r4.st : List lane.Lane2U32).length = 25  := by exact r4.st.2
  have hr5  : (↑r5.st : List lane.Lane2U32).length = 25  := by exact r5.st.2
  have hr6  : (↑r6.st : List lane.Lane2U32).length = 25  := by exact r6.st.2
  have hr7  : (↑r7.st : List lane.Lane2U32).length = 25  := by exact r7.st.2
  have hr8  : (↑r8.st : List lane.Lane2U32).length = 25  := by exact r8.st.2
  have hr9  : (↑r9.st : List lane.Lane2U32).length = 25  := by exact r9.st.2
  have hss  : (↑s.st  : List lane.Lane2U32).length = 25  := by exact s.st.2
  have hlane : ∀ (L : lane.Lane2U32), L.val.length = 2 := fun L => L.2
  apply Subtype.ext
  unfold prc_spec lift_perm impl_perm impl_swap lift_lane_maybe_swap
  simp (config := { decide := true }) only [Std.Array.make, List.ofFn_succ, List.ofFn_zero,
    Fin.val_succ, Fin.val_zero, Nat.succ_eq_add_one, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceDiv, Nat.reduceMod, reduceIte]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  -- Per-cell: cascade chain through apply_5_writes + Std.Array.set, then lift_theta_applied_bv_K,
  -- then ← lift_* / ← rot_* / rc_equiv to equate spec and impl side.
  all_goals (
    apply Std.U64.bv_eq_imp_eq
    simp (config := { decide := true }) only
      [h_chain, h_FC1, h_FC2, h_FC3, h_FC4, h_FC5, h_FC6, h_FC7, h_FC8, h_FC9, apply_5_writes,
       lift_lane,
       List.getElem!_set_ne, List.getElem!_set, List.length_set,
       Std.Array.set_val_eq, hlane,
       hr', hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hss,
       show ((0#usize : Std.Usize) : Nat) = 0 from rfl,
       show ((1#usize : Std.Usize) : Nat) = 1 from rfl]
    simp only [lift_theta_applied_bv_0, lift_theta_applied_bv_1, lift_theta_applied_bv_2,
      lift_theta_applied_bv_3, lift_theta_applied_bv_4, lift_theta_applied_bv_5,
      lift_theta_applied_bv_6, lift_theta_applied_bv_7, lift_theta_applied_bv_8,
      lift_theta_applied_bv_9, lift_theta_applied_bv_10, lift_theta_applied_bv_11,
      lift_theta_applied_bv_12, lift_theta_applied_bv_13, lift_theta_applied_bv_14,
      lift_theta_applied_bv_15, lift_theta_applied_bv_16, lift_theta_applied_bv_17,
      lift_theta_applied_bv_18, lift_theta_applied_bv_19, lift_theta_applied_bv_20,
      lift_theta_applied_bv_21, lift_theta_applied_bv_22, lift_theta_applied_bv_23,
      lift_theta_applied_bv_24,
      Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32, rot64]
    simp only [Std.UScalarTy.U64_numBits_eq,
      rot_0, rot_1, rot_2, rot_3, rot_6, rot_8, rot_10,
      rot_14, rot_15, rot_18, rot_20, rot_21, rot_25, rot_27,
      rot_28, rot_36, rot_39, rot_41, rot_43, rot_44, rot_45,
      rot_55, rot_56, rot_61, rot_62,
      ← lift_xor, ← lift_and, ← lift_not, ← lift_chi,
      ← rc_equiv _ hi_lt])

end libcrux_iot_sha3.Equivalence
