/-
  Phase 0 feasibility experiment for the bit_keccak two-campaign architecture
  (plan: ~/.claude/plans/fancy-gliding-swan.md).

  Question this file answers: does a 24-round induction of the form
    canonical_view (intermediate_round^[N] s) N = hacspec_round^[N] (canonical_view s 0)
  close in Lean WITHOUT any `Balanced`-style hypothesis, when the canonical
  view carries a *cycling* permutation factor `perm^[N]` (analogous to
  `impl_perm^[k % 4]` in the real architecture)?

  If yes: the bit_keccak architecture's algebraic Campaign 2 is structurally
  sound — we can 24-round-induct without 4-round chunking.

  If no: the canonical-lift column-mixing wall reappears at the inductive
  step and the whole plan is dead.

  Toy setup. We model the real architecture with the simplest reduction
  that still tests the structural concern:

    - "State" is `Fin 4 → Int` (4 lane positions, integer-valued).
    - `perm : Fin 4 → Fin 4` is the toy analogue of `impl_perm` (a
      4-element cyclic permutation, so `perm^[4] = id`).
    - `stub_bit_round` does one storage relabel per round (reading via
      `perm_inv`), mirroring the impl's per-round addressing shift.
    - `stub_canonical_round` is identity on `Fin 4 → Int`, mirroring the
      hacspec round under a cycling lift_perm reading.
    - `canonical_view s n` reads `s` via the forward `perm^[n]`,
      cancelling the impl's cumulative relabels.

  The per-round correspondence holds via `perm_inv (perm x) = x` — a
  pointwise cancellation that does NOT require any state-level
  Balanced predicate. The 24-round closure is then a straight Nat.rec
  induction with the per-round correspondence at the step.

  Acceptance: the file builds with zero errors, and
  `#print axioms toy_24_round_correspondence` lists only Lean defaults
  (`propext`, `Classical.choice`, `Quot.sound`).
-/
import LibcruxIotSha3.Extraction.Funs

namespace libcrux_iot_sha3.Experiment

/-! ## Toy permutation (analogue of `impl_perm` on `Fin 25`) -/

private def perm (i : Fin 4) : Fin 4 := ⟨(i.val + 1) % 4, by omega⟩

private def perm_inv (i : Fin 4) : Fin 4 := ⟨(i.val + 3) % 4, by omega⟩

private theorem perm_inv_perm (i : Fin 4) : perm_inv (perm i) = i := by
  fin_cases i <;> rfl

private theorem perm_perm_inv (i : Fin 4) : perm (perm_inv i) = i := by
  fin_cases i <;> rfl

/-- `perm` has order 4: 4 iterations collapse to identity.
    Analogue of `impl_perm_pow4_eq_id` in the real tree. -/
private theorem perm_iterate_four_id : ∀ i, perm^[4] i = i := by
  intro i; fin_cases i <;> rfl

/-! ## Toy state, intermediate round, canonical round, canonical view

  The shapes match the architecture in the plan:

    impl side: `bit_keccak_spec : KState → Option KState`
               `bit_round_step k : KState → Option KState`

    spec side: `spec_round_step : Array U64 25 → Round → Result (Array U64 25)`

    bridge   : `kstate_lift_perm s (impl_perm^[k%4]) impl_swap`

  In the toy:

    impl side: `Fin 4 → Int`,   `stub_bit_round k : (Fin 4 → Int) → (Fin 4 → Int)`
    spec side: `Fin 4 → Int`,   `stub_canonical_round k : (Fin 4 → Int) → (Fin 4 → Int)`
    bridge   : `canonical_view s n` (n cycles via `perm^[n]`)
-/

/-- Toy intermediate-spec round. Mirrors the impl's per-round storage
    relabel: the new state's position `i` reads from old position
    `perm_inv i`. No round-index dependency in the body (the round
    index `k` is taken just to match the architectural shape). -/
private def stub_bit_round (_k : Nat) (s : Fin 4 → Int) : Fin 4 → Int :=
  fun i => s (perm_inv i)

/-- Toy hacspec round. In the real architecture this would be one round
    of FIPS Keccak applied via `lift_perm`. For the toy, it's identity —
    we're testing the structural induction, not bit-level chi semantics. -/
private def stub_canonical_round (_k : Nat) (a : Fin 4 → Int) : Fin 4 → Int := a

/-- Toy canonical view. Reads `s` via the forward permutation `perm^[n]`,
    cancelling the impl's cumulative per-round relabels.
    Analogue of `lift_perm s (impl_perm^[n % 4]) impl_swap` in the real
    architecture. -/
private def canonical_view (s : Fin 4 → Int) (n : Nat) : Fin 4 → Int :=
  fun L => s (perm^[n] L)

/-! ## Per-round correspondence

  The lemma the inductive step needs. Crucially: NO `Balanced`-style
  hypothesis on `s`. Closes by pointwise `perm_inv (perm x) = x`. -/

private theorem toy_round_correspondence (k : Nat) (s : Fin 4 → Int) :
    canonical_view (stub_bit_round k s) (k+1)
    = stub_canonical_round k (canonical_view s k) := by
  funext L
  simp only [canonical_view, stub_bit_round, stub_canonical_round]
  -- Goal: stub_bit_round k s (perm^[k+1] L) = s (perm^[k] L)
  -- LHS expansion: s (perm_inv (perm^[k+1] L)).
  -- perm^[k+1] L = perm (perm^[k] L) (by Function.iterate_succ').
  -- So LHS = s (perm_inv (perm (perm^[k] L))) = s (perm^[k] L) by perm_inv_perm.
  rw [Function.iterate_succ', Function.comp_apply, perm_inv_perm]

/-! ## 24-round closure — the architectural feasibility check

  Generalize over `N`, induct on it, apply `toy_round_correspondence` at
  the inductive step. NO Balanced/canonicality precondition propagated. -/

private theorem toy_general_correspondence (N : Nat) (s : Fin 4 → Int) :
    Nat.fold N (fun k _ acc => stub_canonical_round k acc) (canonical_view s 0)
    = canonical_view (Nat.fold N (fun k _ acc => stub_bit_round k acc) s) N := by
  induction N with
  | zero =>
    simp only [Nat.fold_zero]
  | succ n IH =>
    simp only [Nat.fold_succ]
    -- LHS: stub_canonical_round n (Nat.fold n ... (canonical_view s 0))
    -- RHS: canonical_view (stub_bit_round n (Nat.fold n ... s)) (n+1)
    rw [IH]
    -- LHS: stub_canonical_round n (canonical_view (Nat.fold n ... s) n)
    exact (toy_round_correspondence n
            (Nat.fold n (fun k _ acc => stub_bit_round k acc) s)).symm

/-- **Acceptance theorem.** 24-round correspondence with no Balanced
    hypothesis. If this builds, Phase 0 passes. -/
theorem toy_24_round_correspondence (s : Fin 4 → Int) :
    Nat.fold 24 (fun k _ acc => stub_canonical_round k acc) (canonical_view s 0)
    = canonical_view (Nat.fold 24 (fun k _ acc => stub_bit_round k acc) s) 24 :=
  toy_general_correspondence 24 s

end libcrux_iot_sha3.Experiment
