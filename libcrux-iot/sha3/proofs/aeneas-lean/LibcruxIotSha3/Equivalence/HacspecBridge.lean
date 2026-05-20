/-
  Bridge between the impl-level `keccak.keccakf1600` and the hacspec
  top-level `keccak_f.keccak_f`.

  ## Architecture

  The impl's `keccak.keccakf1600` iterates `keccakf1600_4rounds` 6 times
  over an `I32` range `[0, 6)`. The hacspec's `keccak_f.keccak_f` iterates
  the body `theta ; rho ; pi ; chi ; iota round` 24 times over a `Usize`
  range `[0, 24)`. Our `BitKeccak.keccakf1600_equiv_via_bit` proves that
  the impl's output equals a 24-fold spec chain (`spec_chain (lift s) 24`)
  using the `_unrolled` variants of the spec functions.

  This file provides the loop-spec infrastructure for the `Usize` range,
  the structural-unfolding helper for `array.from_fn` / `createi` over
  small `N`, and the spec-side definitions in terms of the hacspec
  (non-unrolled) variants that mirror `keccak_f.keccak_f`'s body.

  ## History

  Added 2026-05-20 to bridge the iteration-structure gap between our
  proof infrastructure (using `Nat.fold 24` over `spec_round_step`) and
  the hacspec function (using a `Usize` range loop over single-round
  body).
-/
import LibcruxIotSha3.BitKeccak.AlgEquiv
import LibcruxIotSha3.Equivalence.I32LoopSpec

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Equivalence

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## Helper: `Usize.val` conversion for small-Nat constants

The `array.from_fn` extraction uses raw `BitVec.ofNat _ n` for iteration
indices; we need to convert these to the standard `n#usize` form. -/

private theorem bv_ofNat_val_eq (n : Nat) (hn : n < 2^32) :
    (⟨BitVec.ofNat System.Platform.numBits n⟩ : Std.Usize).val = n := by
  show (BitVec.ofNat _ n).toNat = n
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq; omega
  calc n < 2^32 := hn
    _ ≤ 2^System.Platform.numBits := Nat.pow_le_pow_right (by decide) h32

private theorem bv_ofNat_eq_usize_lit_0 :
    (⟨BitVec.ofNat _ 0⟩ : Std.Usize) = 0#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 0 (by omega)
private theorem bv_ofNat_eq_usize_lit_1 :
    (⟨BitVec.ofNat _ 1⟩ : Std.Usize) = 1#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 1 (by omega)
private theorem bv_ofNat_eq_usize_lit_2 :
    (⟨BitVec.ofNat _ 2⟩ : Std.Usize) = 2#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 2 (by omega)
private theorem bv_ofNat_eq_usize_lit_3 :
    (⟨BitVec.ofNat _ 3⟩ : Std.Usize) = 3#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 3 (by omega)
private theorem bv_ofNat_eq_usize_lit_4 :
    (⟨BitVec.ofNat _ 4⟩ : Std.Usize) = 4#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 4 (by omega)

/-! ## `array.from_fn 5` unfolding lemma

`rust_primitives.slice.array_from_fn 5#usize inst f0` unfolds to a chain
of 5 `inst.call_mut` calls building an `Array.make 5 [v0,v1,v2,v3,v4]`. -/

set_option maxHeartbeats 400000000 in
theorem array_from_fn_eq_unfold5
    {T F : Type} (inst : core_models.ops.function.FnMut F Std.Usize T) (f0 : F)
    (v0 v1 v2 v3 v4 : T) (f1 f2 f3 f4 f5 : F)
    (h0 : inst.call_mut f0 0#usize = .ok (v0, f1))
    (h1 : inst.call_mut f1 1#usize = .ok (v1, f2))
    (h2 : inst.call_mut f2 2#usize = .ok (v2, f3))
    (h3 : inst.call_mut f3 3#usize = .ok (v3, f4))
    (h4 : inst.call_mut f4 4#usize = .ok (v4, f5)) :
    rust_primitives.slice.array_from_fn 5#usize inst f0 =
      .ok (Std.Array.make 5#usize [v0, v1, v2, v3, v4]) := by
  have h_fold :
      List.foldlM
        (fun (s : List T × F) (i : Nat) => do
          let __discr ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
          match __discr with
          | (v, f') => Result.ok (s.1 ++ [v], f'))
        ([], f0) (List.range (5#usize).val)
      = .ok ([v0, v1, v2, v3, v4], f5) := by
    show List.foldlM _ ([], f0) (List.range 5) = _
    rw [show (List.range 5) = [0, 1, 2, 3, 4] from by decide]
    simp only [List.foldlM_cons, List.foldlM_nil,
               bv_ofNat_eq_usize_lit_0, bv_ofNat_eq_usize_lit_1,
               bv_ofNat_eq_usize_lit_2, bv_ofNat_eq_usize_lit_3,
               bv_ofNat_eq_usize_lit_4, h0, h1, h2, h3, h4, bind_tc_ok]
    rfl
  unfold rust_primitives.slice.array_from_fn
  split
  · rename_i e heq_match
    rw [h_fold] at heq_match
    exact absurd heq_match (by simp)
  · rename_i heq_match
    rw [h_fold] at heq_match
    exact absurd heq_match (by simp)
  · rename_i result heq_match
    rw [h_fold] at heq_match
    have hres : result = ([v0, v1, v2, v3, v4], f5) := (Result.ok.inj heq_match).symm
    subst hres
    rfl

/-! ## Spec-side single-round step using hacspec (non-`_unrolled`) variants

Mirrors `keccak_f.keccak_f_loop.body` (the `Some round` branch). -/

def spec_round_step_hacspec (state : Std.Array Std.U64 25#usize) (round : Std.Usize) :
    Result (Std.Array Std.U64 25#usize) := do
  let a ← keccak_f.theta state
  let a1 ← keccak_f.rho a
  let a2 ← keccak_f.pi a1
  let a3 ← keccak_f.chi a2
  keccak_f.iota a3 round

/-! ## `Usize` iterator-next spec (analog of `IteratorRange_next_spec_i32`)

The hacspec loop in `keccak_f.keccak_f_loop` iterates `Usize` indices over
`[0, 24)`. The `Usize.Insts.Core_modelsIterRangeStep` instance is an
abbrev for `core_models.iter.range.StepUsize` (see `FunsPrologue.lean`). -/

theorem IteratorRange_next_spec_usize (i e : Std.Usize) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.Usize), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.iter.range.IteratorRange.next
      core_models.Usize.Insts.Core_modelsIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core_models.iter.range.IteratorRange.next
  unfold core_models.Usize.Insts.Core_modelsIterRangeStep
    core_models.iter.range.StepUsize
  -- The StepUsize record's `forward_checked` is
  -- `Aeneas.Std.core.iter.range.StepUsize.forward_checked := λ start n => ok (Usize.checked_add ...)`.
  -- Unfold this so the proof can decide whether the result is Some or None.
  unfold Aeneas.Std.core.iter.range.StepUsize.forward_checked
  by_cases h : i.val < e.val
  · -- i < e: partial_cmp returns Less.
    have h_lt' := h_lt h
    have he_max : e.val ≤ Std.Usize.max := by
      have he := e.hBounds
      simp [Std.Usize.max, Std.Usize.numBits] at *
      omega
    have hi_bound : i.val + 1 ≤ Std.Usize.max := by omega
    have hck := Std.Usize.checked_add_bv_spec i 1#usize
    have h_some : ∃ s : Std.Usize, Std.Usize.checked_add i 1#usize = some s ∧ s.val = i.val + 1 := by
      cases hres : Std.Usize.checked_add i 1#usize with
      | some s =>
          rw [hres] at hck
          obtain ⟨_, hsv, _⟩ := hck
          refine ⟨s, rfl, ?_⟩
          rw [hsv]; rfl
      | none =>
          rw [hres] at hck
          have h1u : (1#usize : Std.Usize).val = 1 := by rfl
          rw [h1u] at hck
          omega
    obtain ⟨s, hres, hsv'⟩ := h_some
    simp_all only [compare, compareOfLessAndEq]
    mvcgen
    all_goals (try simp_all)
  · -- i ≥ e: partial_cmp returns Equal or Greater; branch returns none.
    have hle : e.val ≤ i.val := Nat.not_lt.mp h
    have h_ge' := h_ge hle
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
    simp_all only [compare, compareOfLessAndEq]
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

/-! ## `Usize` loop-over-range spec (analog of `loop_range_spec_i32`)

Specialized to `loop` over `core.ops.range.Range Usize`. Same shape as the
`I32` version: an invariant `inv : Usize → β → Result Prop` is preserved by
each step. Induction on `(e.val - start.val).toNat`. -/

section loop_range_usize_helpers

private abbrev ResultPSU := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_usize {α : Type} {x : Result α} {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp] using h

private theorem triple_noThrow_exists_ok_usize {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp])
  | .div, h => exact absurd h (by simp [Triple, WP.wp])

private theorem triple_of_ok_usize {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, hp]

end loop_range_usize_helpers

set_option maxHeartbeats 2000000 in
theorem loop_range_spec_usize {β : Type}
    (body : (core_models.ops.range.Range Std.Usize × β) →
      Result (ControlFlow (core_models.ops.range.Range Std.Usize × β) β))
    (init : β) (s e : Std.Usize) (inv : Std.Usize → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : Std.Usize), s.val ≤ i.val → i.val ≤ e.val →
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
  suffices gen : ∀ (n : Nat) (acc : β) (start : Std.Usize),
    e.val - start.val = n →
    s.val ≤ start.val → start.val ≤ e.val →
    (inv start acc).holds →
    ⦃ ⌜ True ⌝ ⦄ loop body ({ start := start, «end» := e }, acc)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ by
    exact gen _ init s rfl (Nat.le_refl _) h_le h_init
  intro n
  induction n with
  | zero =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_usize hs
    have hpost := triple_noThrow_elim_usize hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp at hpost; exact absurd hpost.1 (by omega)
    | .done y =>
      simp at hpost; exact triple_of_ok_usize rfl hpost
  | succ n ih =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_usize hs
    have hpost := triple_noThrow_elim_usize hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp at hpost; exact triple_of_ok_usize rfl hpost
    | .cont (iter', acc') =>
      simp at hpost
      obtain ⟨hlt, hend, hstart, hinv'⟩ := hpost
      have hiter : iter' = { start := iter'.start, «end» := e } := by
        cases iter'; cases hend; rfl
      rw [hiter]
      exact ih acc' iter'.start
        (by rw [hstart]; omega) (by rw [hstart]; omega) (by rw [hstart]; omega) hinv'

/-! ## Spec-chain via hacspec (non-`_unrolled`) variants

Mirrors `spec_chain` (from `SpecChain.lean`) but uses `spec_round_step_hacspec`. -/

def spec_round_step_hacspec_at (round_idx : Nat) (st : Std.Array Std.U64 25#usize) :
    Result (Std.Array Std.U64 25#usize) :=
  if h : round_idx < 24 then spec_round_step_hacspec st (roundOfNat round_idx (by omega))
  else .fail .panic

def spec_chain_hacspec (s : Std.Array Std.U64 25#usize) (n : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  Nat.fold n (fun i _ acc => acc >>= fun st => spec_round_step_hacspec_at i st) (pure s)

theorem spec_chain_hacspec_zero (s : Std.Array Std.U64 25#usize) :
    spec_chain_hacspec s 0 = .ok s := by rfl

theorem spec_chain_hacspec_succ (s : Std.Array Std.U64 25#usize) (n : Nat) :
    spec_chain_hacspec s (n + 1) =
      spec_chain_hacspec s n >>= fun st => spec_round_step_hacspec_at n st := by
  unfold spec_chain_hacspec
  rw [Nat.fold_succ]

/-! ## Status

This file provides the foundational infrastructure to bridge the
impl-level `keccak.keccakf1600` to the hacspec-level `keccak_f.keccak_f`:

- `IteratorRange_next_spec_usize` and `loop_range_spec_usize` — the
  `Usize` analogs of `I32LoopSpec`'s `*_i32` lemmas.
- `array_from_fn_eq_unfold5` — `rust_primitives.slice.array_from_fn 5`
  unfolds to a chain of 5 sequential `call_mut` calls (handles the
  dependent-typed `match h : foldlM ... with | ok r => ⟨r.1, _proof_1⟩`
  via a `split` + `subst` approach).
- `spec_round_step_hacspec` / `spec_chain_hacspec` — spec-side
  definitions mirroring the hacspec loop body using the non-`_unrolled`
  variants of θ/ρ/π/χ. Includes `_zero` and `_succ` recurrence lemmas.

### Remaining work for full hacspec coupling

To complete the bridge to `keccak_f.keccak_f`, two more steps are needed:

1. **Function-equality lemmas**: `keccak_f.theta s = keccak_f.theta_unrolled s`
   (and similarly for ρ/π/χ). These are NOT `rfl` — the non-`_unrolled`
   versions use `createi` over closures (which expand to
   `rust_primitives.slice.array_from_fn` over `List.foldlM`), while the
   `_unrolled` versions are straight-line code. A proof requires:
   - Extending `array_from_fn_eq_unfold5` to `_unfold25` (analogous
     pattern, 25 element steps).
   - Applying the unfolding lemmas to each of θ/ρ/π/χ's `createi` calls
     with the specific closure semantics.

   The dependent-typed `match h : ... with | ok result => .ok ⟨result.1, _⟩`
   in `rust_primitives.slice.array_from_fn` (the `_proof_1` length
   witness reads the match scrutinee) makes naive `rw` fail with
   "motive is not type correct"; the `array_from_fn_eq_unfold5` proof
   shows how to work around this via `split` + `subst`.

2. **Loop bridge** `keccak_f_loop_eq_spec_chain_hacspec` (sketched but
   not yet committed): applies `loop_range_spec_usize` with the
   invariant "after k iterations, the state equals `spec_chain_hacspec
   s k`". The body Triple proof uses `IteratorRange_next_spec_usize` to
   step the iterator, then dispatches the `θ;ρ;π;χ;ι` chain inside the
   `.cont` branch. The shape of the body post (cont vs done dispatch
   under `loop_range_spec_usize`'s invariant) is the main technical
   complexity.

3. **Top-level theorem** `keccakf1600_equiv_hacspec`: composes
   `keccakf1600_equiv_via_bit` with `spec_chain_hacspec = spec_chain`
   (which follows from the function-equality lemmas) to get the
   hacspec-level top theorem coupling `keccak.keccakf1600` to
   `keccak_f.keccak_f` directly. -/

end libcrux_iot_sha3.Equivalence
