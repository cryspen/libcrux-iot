/-
  I32 iterator + loop helpers + spec-chain helpers.

  ## History (2026-05-20 cleanup)

  This file used to host the OLD `keccakf1600_equiv` path, which was
  structured around `Balanced` preservation across rounds 1-3 — a
  property empirically false (see memory
  `feedback_bit_keccak_balanced_preservation_false`). The OLD post
  required `lift_perm r id impl_swap` on the output, equivalent to
  the canonical `lift r` only when `Balanced r` — not generically true.

  The OLD theorems (`keccakf1600_4rounds_preserves_balanced`,
  `keccakf1600_4rounds_preserves_lift_eq`,
  `keccakf1600_loop_post_eq_spec_chain`, `four_round_chunk_equiv`,
  `keccakf1600_loop_equiv`, `keccakf1600_equiv`, plus the supporting
  `Balanced` / `lift_eq_lift_perm_iff` / `lift_lane_bv_swap_iff`
  defs and `keccakf1600_4rounds_i_inc`, `loop_inv_prop`,
  `holds_chain4_eq_ok` helpers) have been removed. They are
  superseded by `BitKeccak.keccakf1600_equiv_via_bit` in
  `BitKeccak/AlgEquiv.lean`, which proves `keccakf1600_post_canonical`
  (canonical `lift r_impl`, no `Balanced` precondition) via the
  time-varying `impl_swap_k` architecture.

  ## What remains

  Shared infrastructure still needed by:
  - `BitKeccak/StructEquiv.lean` and `BitKeccak/AlgEquiv.lean`:
    `loop_range_spec_i32`, `IteratorRange_next_spec_i32`,
    `pure_prop_holds`, `of_pure_prop_holds`.
  - `BitKeccak/AlgEquiv.lean`'s 24-round closure:
    `spec_round_step_at`, `spec_chain`, `spec_chain_zero`,
    `spec_chain_succ`.

  A future cleanup may want to rename this file (e.g. to
  `LoopHelpers.lean` or split across two files) since the original
  "keccakf1600 loop equiv" framing is no longer accurate.
-/
import LibcruxIotSha3.Equivalence.Keccakf1600

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## I32 iterator-next spec

The `core_models.I32.Insts.Core_modelsIterRangeStep` instance (defined
in `Extraction/Missing.lean:25`) uses `IScalar.tryMk .I32 (start.val +
1)` for `forward_checked`. For our use case (range `[0, 6)`), the
bounds are well within I32 and `tryMk` succeeds. -/

theorem IteratorRange_next_spec_i32 (i e : Std.I32)
    (h_e_lt_max : e.val < 2^31) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.I32), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.iter.range.IteratorRange.next core_models.I32.Insts.Core_modelsIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core_models.iter.range.IteratorRange.next
  unfold core_models.I32.Insts.Core_modelsIterRangeStep
  by_cases h : i.val < e.val
  · -- i < e: partial_cmp returns Less, forward_checked succeeds (i+1 ≤ e < 2^31).
    have hbnd : i.val + 1 < 2^31 := by omega
    have hi_min := i.hBounds.1
    have hbnd_lo : -(2^31 : Int) ≤ i.val + 1 := by
      simp only [Std.IScalar.min, Std.IScalarTy.numBits] at hi_min
      omega
    have h_lt' := h_lt h
    simp_all [compare, compareOfLessAndEq]
    have hck := Std.IScalar.tryMk_eq Std.IScalarTy.I32 (i.val + 1)
    cases hres : Std.IScalar.tryMk Std.IScalarTy.I32 (i.val + 1) with
    | ok s =>
        rw [hres] at hck
        obtain ⟨hsv, _⟩ := hck
        simp only [Option.ofResult]
        mvcgen
        exact h_lt' s hsv
    | fail _ =>
        rw [hres] at hck
        simp at hck
        omega
    | div =>
        rw [hres] at hck
        exact absurd hck (by exact False.elim)
  · -- i ≥ e: partial_cmp returns Equal or Greater (not Less); branch returns
    -- `.ok (none, range)` directly without invoking forward_checked.
    have hle : e.val ≤ i.val := Int.not_lt.mp h
    have h_ge' := h_ge hle
    -- The boolean condition `isLess` evaluates to `false` under `¬ (i < e)`.
    have hisLess_false :
        (match
          (match if i.val < e.val then Ordering.lt
                  else if i.val = e.val then Ordering.eq else Ordering.gt with
           | Ordering.lt => core_models.cmp.Ordering.Less
           | Ordering.eq => core_models.cmp.Ordering.Equal
           | Ordering.gt => core_models.cmp.Ordering.Greater) with
          | core_models.cmp.Ordering.Less => true
          | _ => false) = false := by
      simp only [if_neg h]
      by_cases hieq : i.val = e.val <;> simp [hieq]
    simp_all [compare, compareOfLessAndEq]
    mvcgen
    all_goals first
      | exact h_ge'
      | (exfalso
         rename_i hLess _ _
         have : false = true := hisLess_false.symm.trans hLess
         exact absurd this (by decide))
      | (exfalso
         rename_i hLess _
         have : false = true := hisLess_false.symm.trans hLess
         exact absurd this (by decide))

/-! ## I32 loop-over-range spec

Specialized to `loop` over `core.ops.range.Range I32`. -/

section loop_range_i32_helpers

private abbrev ResultPS := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_i32 {α : Type} {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp] using h

private theorem triple_noThrow_exists_ok_i32 {α : Type} {x : Result α}
    {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp])
  | .div, h => exact absurd h (by simp [Triple, WP.wp])

private theorem triple_of_ok_i32 {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, hp]

end loop_range_i32_helpers

set_option maxHeartbeats 2000000 in
theorem loop_range_spec_i32 {β : Type}
    (body : (core_models.ops.range.Range Std.I32 × β) →
      Result (ControlFlow (core_models.ops.range.Range Std.I32 × β) β))
    (init : β) (s e : Std.I32) (inv : Std.I32 → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : Std.I32), s.val ≤ i.val → i.val ≤ e.val →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body ({ start := i, «end» := e }, acc)
      ⦃ ⇓ r => match r with
        | .cont (iter', acc') =>
          ⌜ i.val < e.val ∧ iter'.«end» = e ∧ iter'.start.val = i.val + 1
            ∧ (inv iter'.start acc').holds ⌝
        | .done y => ⌜ (inv e y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ start := s, «end» := e }, init)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  -- Generalize over the current iteration's `start` and induct on the number
  -- of remaining steps `n = (e.val - start.val).toNat`.
  suffices gen : ∀ (n : Nat) (acc : β) (start : Std.I32),
    (e.val - start.val).toNat = n →
    s.val ≤ start.val → start.val ≤ e.val →
    (inv start acc).holds →
    ⦃ ⌜ True ⌝ ⦄ loop body ({ start := start, «end» := e }, acc)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ by
    exact gen _ init s rfl (Int.le_refl _) h_le h_init
  intro n
  induction n with
  | zero =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_i32 hs
    have hpost := triple_noThrow_elim_i32 hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp at hpost; exact absurd hpost.1 (by omega)
    | .done y =>
      simp at hpost; exact triple_of_ok_i32 rfl hpost
  | succ n ih =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_i32 hs
    have hpost := triple_noThrow_elim_i32 hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp at hpost; exact triple_of_ok_i32 rfl hpost
    | .cont (iter', acc') =>
      simp at hpost
      obtain ⟨hlt, hend, hstart, hinv'⟩ := hpost
      have hiter : iter' = { start := iter'.start, «end» := e } := by
        cases iter'; cases hend; rfl
      rw [hiter]
      exact ih acc' iter'.start
        (by rw [hstart]; omega) (by rw [hstart]; omega) (by rw [hstart]; omega) hinv'

/-! ## Spec-chain helper

`spec_round_step_at` wraps `spec_round_step` for use inside the
`Nat.fold 24` chain in `keccakf1600_loop_post` / `keccakf1600_post_canonical`.
`spec_chain` packages the `Nat.fold` form. -/

def spec_round_step_at (round_idx : Nat) (st : Std.Array Std.U64 25#usize) :
    Result (Std.Array Std.U64 25#usize) :=
  if h : round_idx < 24 then spec_round_step st (roundOfNat round_idx (by omega))
  else .fail .panic

/-- `spec_chain n s_lift` applies `n` spec rounds (indices 0..n-1) to
    the lifted initial state `s_lift`. -/
def spec_chain (s_lift : Std.Array Std.U64 25#usize) (n : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  Nat.fold n (fun i _ acc => acc >>= fun st => spec_round_step_at i st) (pure s_lift)

theorem spec_chain_zero (s_lift : Std.Array Std.U64 25#usize) :
    spec_chain s_lift 0 = .ok s_lift := by
  rfl

theorem spec_chain_succ (s_lift : Std.Array Std.U64 25#usize) (n : Nat) :
    spec_chain s_lift (n + 1) =
      spec_chain s_lift n >>= fun st => spec_round_step_at n st := by
  unfold spec_chain
  rw [Nat.fold_succ]

/-! ## `pure P` ↔ `P` for `Result Prop`

Used by `BitKeccak/StructEquiv.lean` and the loop-invariant unpacking
in `BitKeccak/AlgEquiv.lean`. -/

theorem pure_prop_holds {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]
  intro _
  exact h

theorem of_pure_prop_holds {P : Prop} (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h
  exact h trivial

end libcrux_iot_sha3.Equivalence
