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

/-! ## Loop bridge: `keccak_f.keccak_f` equals `spec_chain_hacspec ... 24`

Direct induction on the number of remaining loop iterations. We pair the
loop's `start` index with a `Nat`-level counter `k`, and a proof that the
spec chain to `k` succeeds with `acc`. At each step:

- Iterator at `{kU, 24}` with `kU.val = k`: if `k < 24` returns
  `Some kU, iter1` with `iter1.start.val = k + 1`; if `k = 24` returns
  `None`.
- Loop body's θ;ρ;π;χ;ι chain is precisely `spec_round_step_hacspec acc kU`.
- By `spec_chain_hacspec_succ`, `spec_chain_hacspec s (k+1) =
  spec_chain_hacspec s k >>= spec_round_step_hacspec_at k =
  spec_round_step_hacspec_at k acc =
  spec_round_step_hacspec acc (roundOfNat k _)`. Since `kU.val = k`,
  `roundOfNat k _ = kU`, so this equals `spec_round_step_hacspec acc kU`.
- Failure in `spec_round_step_hacspec acc kU` propagates identically on
  both sides (loop fails, spec_chain fails and propagates to 24). -/

/-- Direct equality form of `IteratorRange.next` over a `Usize` range
    `{kU, 24}` when `kU.val < 24`: returns `Some kU` and increments the
    start by 1. Companion to `IteratorRange_next_spec_usize` (Triple form). -/
private theorem IteratorRange_next_eq_some_usize
    (kU : Std.Usize) (hkU : kU.val < 24) :
    ∃ kU' : Std.Usize, kU'.val = kU.val + 1 ∧
      core_models.iter.range.IteratorRange.next
        core_models.Usize.Insts.Core_modelsIterRangeStep
        ({ start := kU, «end» := 24#usize } :
          core_models.ops.range.Range Std.Usize) =
        .ok (core_models.option.Option.Some kU,
             { start := kU', «end» := 24#usize }) := by
  -- Compute kU' = kU + 1.
  have hkUmax : kU.val + 1 ≤ Std.Usize.max := by
    have h24 : (24 : Nat) ≤ Std.Usize.max := by
      simp [Std.Usize.max, Std.Usize.numBits]
      have := System.Platform.numBits_eq
      rcases this with hp | hp <;> rw [hp] <;> decide
    omega
  have hck := Std.Usize.checked_add_bv_spec kU 1#usize
  have h_some :
      ∃ s' : Std.Usize, Std.Usize.checked_add kU 1#usize = some s' ∧
        s'.val = kU.val + 1 := by
    cases hres : Std.Usize.checked_add kU 1#usize with
    | some s' =>
        rw [hres] at hck
        obtain ⟨_, hsv, _⟩ := hck
        refine ⟨s', rfl, ?_⟩
        rw [hsv]; rfl
    | none =>
        rw [hres] at hck
        have h1u : (1#usize : Std.Usize).val = 1 := by rfl
        rw [h1u] at hck
        omega
  obtain ⟨kU', hres, hkU'val⟩ := h_some
  refine ⟨kU', hkU'val, ?_⟩
  unfold core_models.iter.range.IteratorRange.next
  unfold core_models.Usize.Insts.Core_modelsIterRangeStep
    core_models.iter.range.StepUsize
  unfold Aeneas.Std.core.iter.range.StepUsize.forward_checked
  have hkU_lt24 : kU.val < (24#usize : Std.Usize).val := hkU
  simp only [compare, compareOfLessAndEq, if_pos hkU_lt24, bind_tc_ok, hres,
             if_true]

/-- Direct equality form of `IteratorRange.next` when `kU.val ≥ 24`:
    returns `None`. -/
private theorem IteratorRange_next_eq_none_usize
    (kU : Std.Usize) (hkU : kU.val ≥ 24) :
    core_models.iter.range.IteratorRange.next
      core_models.Usize.Insts.Core_modelsIterRangeStep
      ({ start := kU, «end» := 24#usize } :
        core_models.ops.range.Range Std.Usize) =
      .ok (core_models.option.Option.None,
           { start := kU, «end» := 24#usize }) := by
  unfold core_models.iter.range.IteratorRange.next
  unfold core_models.Usize.Insts.Core_modelsIterRangeStep
    core_models.iter.range.StepUsize
  have hkU_ge : ¬ kU.val < (24#usize : Std.Usize).val := by
    show ¬ kU.val < 24; omega
  by_cases heq : kU.val = (24#usize : Std.Usize).val
  · simp only [compare, compareOfLessAndEq, if_neg hkU_ge, if_pos heq,
               bind_tc_ok, reduceCtorEq, if_false]
  · simp only [compare, compareOfLessAndEq, if_neg hkU_ge, if_neg heq,
               bind_tc_ok, reduceCtorEq, if_false]

/-- `roundOfNat k.val ... = kU` when `kU.val = k.val`: a `Std.Usize`
    constructed from its `.val` round-trips through `roundOfNat`. -/
private theorem roundOfNat_val_eq (kU : Std.Usize) (hk : kU.val < 24) :
    roundOfNat kU.val (by omega) = kU := by
  apply Std.UScalar.eq_of_val_eq
  unfold roundOfNat
  rw [Std.UScalar.ofNatCore_val_eq]

/-- Failure propagation: if `spec_chain_hacspec s k = .fail e`, then for
    all `n ≥ k`, `spec_chain_hacspec s n = .fail e`. -/
private theorem spec_chain_hacspec_fail_mono
    (s : Std.Array Std.U64 25#usize) (k : Nat) (e : Error)
    (h : spec_chain_hacspec s k = .fail e) :
    ∀ n, spec_chain_hacspec s (k + n) = .fail e := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [show k + (n + 1) = (k + n) + 1 from rfl, spec_chain_hacspec_succ, ih]
    rfl

/-- Divergence propagation: if `spec_chain_hacspec s k = .div`, then for
    all `n ≥ k`, `spec_chain_hacspec s n = .div`. -/
private theorem spec_chain_hacspec_div_mono
    (s : Std.Array Std.U64 25#usize) (k : Nat)
    (h : spec_chain_hacspec s k = .div) :
    ∀ n, spec_chain_hacspec s (k + n) = .div := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [show k + (n + 1) = (k + n) + 1 from rfl, spec_chain_hacspec_succ, ih]
    rfl

/-- Body of the loop after the iterator step in the Some branch: the
    `θ;ρ;π;χ;ι` chain wrapped with `ok (cont ...)`. Equals
    `spec_round_step_hacspec acc kU >>= (ok (cont (iter1, ·)))` by
    definitional unfolding of `spec_round_step_hacspec`. -/
private theorem loop_body_some_eq
    (acc : Std.Array Std.U64 25#usize) (kU : Std.Usize)
    (iter1 : core_models.ops.range.Range Std.Usize) :
    (do
      let a ← keccak_f.theta acc
      let a1 ← keccak_f.rho a
      let a2 ← keccak_f.pi a1
      let a3 ← keccak_f.chi a2
      let state1 ← keccak_f.iota a3 kU
      Aeneas.Std.Result.ok
        (cont (iter1, state1) :
          ControlFlow ((core_models.ops.range.Range Std.Usize) ×
            (Std.Array Std.U64 25#usize)) (Std.Array Std.U64 25#usize))) =
    (do
      let state1 ← spec_round_step_hacspec acc kU
      Aeneas.Std.Result.ok (cont (iter1, state1))) := by
  unfold spec_round_step_hacspec
  simp only [bind_assoc]

/-- Inductive helper: induct on `n = 24 - k`, the number of remaining
    iterations. At `n = 0` (`k = 24`), the iterator returns `None` and the
    loop yields `.ok acc`, which by hypothesis equals `spec_chain_hacspec
    s 24`. At `n + 1` (`k < 24`), the body's θ;ρ;π;χ;ι chain matches
    `spec_round_step_hacspec acc kU`; success recurses via IH on
    `(n, k+1, kU+1, acc')`, failure/div propagates to round 24 via the
    `_mono` lemmas. -/
private theorem keccak_f_loop_eq_aux (s : Std.Array Std.U64 25#usize) :
    ∀ (n k : Nat) (kU : Std.Usize) (acc : Std.Array Std.U64 25#usize),
      kU.val = k → k + n = 24 →
      spec_chain_hacspec s k = .ok acc →
      keccak_f.keccak_f_loop { start := kU, «end» := 24#usize } acc =
        spec_chain_hacspec s 24 := by
  intro n
  induction n with
  | zero =>
    intro k kU acc hkU hkn hchain
    have hk : k = 24 := by omega
    subst hk
    have hkU24 : kU.val = (24#usize : Std.Usize).val := by rw [hkU]; rfl
    have hkU24' : kU = 24#usize := Std.UScalar.eq_of_val_eq hkU24
    subst hkU24'
    have hkU_ge : (24#usize : Std.Usize).val ≥ 24 := by decide
    have hnext := IteratorRange_next_eq_none_usize 24#usize hkU_ge
    unfold keccak_f.keccak_f_loop
    rw [loop.eq_def]
    unfold keccak_f.keccak_f_loop.body
    simp only [hnext, bind_tc_ok]
    dsimp
    rw [hchain]
  | succ n ih =>
    intro k kU acc hkU hkn hchain
    have hk_lt : k < 24 := by omega
    have hkU_lt : kU.val < 24 := by rw [hkU]; exact hk_lt
    obtain ⟨kU', hkU'val, hnext⟩ := IteratorRange_next_eq_some_usize kU hkU_lt
    unfold keccak_f.keccak_f_loop
    rw [loop.eq_def]
    unfold keccak_f.keccak_f_loop.body
    simp only [hnext, bind_tc_ok]
    dsimp
    rw [loop_body_some_eq acc kU { start := kU', «end» := 24#usize }]
    have h_chain_succ : spec_chain_hacspec s (k + 1) =
        spec_round_step_hacspec acc kU := by
      rw [spec_chain_hacspec_succ, hchain]
      show spec_round_step_hacspec_at k acc = spec_round_step_hacspec acc kU
      -- Replace `k` everywhere with `kU.val` (via hkU.symm) to dispatch the
      -- dependent `roundOfNat k _` proof obligation cleanly.
      have hk_eq : k = kU.val := hkU.symm
      subst hk_eq
      unfold spec_round_step_hacspec_at
      rw [dif_pos hkU_lt]
      rw [roundOfNat_val_eq kU hkU_lt]
    cases hstep : spec_round_step_hacspec acc kU with
    | ok r =>
      simp only [bind_tc_ok]
      have hchain' : spec_chain_hacspec s (k + 1) = .ok r := by
        rw [h_chain_succ]; exact hstep
      have hkU'val' : kU'.val = k + 1 := by rw [hkU'val, hkU]
      have hkn' : (k + 1) + n = 24 := by omega
      have hih := ih (k + 1) kU' r hkU'val' hkn' hchain'
      unfold keccak_f.keccak_f_loop at hih
      exact hih
    | fail e =>
      simp only [bind_tc_fail]
      have hk1fail : spec_chain_hacspec s (k + 1) = .fail e := by
        rw [h_chain_succ]; exact hstep
      have h24eq : 24 = (k + 1) + n := by omega
      rw [h24eq, spec_chain_hacspec_fail_mono s (k + 1) e hk1fail n]
    | div =>
      simp only [bind_tc_div]
      have hk1div : spec_chain_hacspec s (k + 1) = .div := by
        rw [h_chain_succ]; exact hstep
      have h24eq : 24 = (k + 1) + n := by omega
      rw [h24eq, spec_chain_hacspec_div_mono s (k + 1) hk1div n]

/-- **Loop bridge**: the hacspec `keccak_f.keccak_f` function equals the
    `Nat.fold 24` chain `spec_chain_hacspec s 24`.

    Instantiates `keccak_f_loop_eq_aux` at `n = 24`, `k = 0`, `kU =
    0#usize`, `acc = s`. The initial spec_chain hypothesis is
    `spec_chain_hacspec s 0 = .ok s` (by `spec_chain_hacspec_zero`). -/
theorem keccak_f_loop_eq_spec_chain_hacspec
    (s : Std.Array Std.U64 25#usize) :
    keccak_f.keccak_f s = spec_chain_hacspec s 24 := by
  unfold keccak_f.keccak_f
  exact keccak_f_loop_eq_aux s 24 0 0#usize s rfl rfl (spec_chain_hacspec_zero s)

/-! ## Bridge 1: `keccak_f.{theta, rho, pi, chi}` equal their `_unrolled` variants

The hacspec definitions of `theta`/`rho`/`pi`/`chi` call `createi N inst c` —
which expands to `rust_primitives.slice.array_from_fn N inst.FnMutInst c` —
with closures whose `call_mut` returns `.ok (call state args, state)` (pure
closures). The `_unrolled` variants are straight-line do-chains terminating
in `ok (Std.Array.make N [v₀, …, v_{N-1}])`.

We prove the function equality through a generic `@[spec]` lemma
`createi_pure_spec` characterizing `createi` for pure closures, plus six
per-closure purity lemmas (one for each of θ's 3, ρ/π/χ's 1 closures). -/

/-- Per-element foldlM evaluation for pure closures. The closure state `c`
    is invariant; the result list is `acc ++ l.map f`. -/
private theorem createi_foldlM_pure_aux
    {T F : Type}
    (inst : core_models.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (l : List Nat) (acc : List T)
    (hpure : ∀ k ∈ l,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    l.foldlM
      (fun (s : List T × F) (i : Nat) => do
        let (v, f') ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
        Result.ok (s.1 ++ [v], f'))
      (acc, c) = .ok (acc ++ l.map f, c) := by
  induction l generalizing acc with
  | nil =>
      simp only [List.foldlM_nil, List.map_nil, List.append_nil]
      rfl
  | cons h t ih =>
      have hh : inst.call_mut c ⟨BitVec.ofNat _ h⟩ = .ok (f h, c) :=
        hpure h List.mem_cons_self
      have ht : ∀ k ∈ t, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (List.mem_cons_of_mem _ hk)
      have hih := ih (acc ++ [f h]) ht
      simp only [List.foldlM_cons, hh, bind_tc_ok, List.map_cons]
      rw [hih]
      simp [List.append_assoc]

/-- Lean-level equation for `createi` over pure closures. Used to power
    `createi_pure_spec` (Triple form). -/
private theorem createi_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : core_models.ops.function.Fn F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    createi N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hf : ∀ k ∈ List.range N.val,
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk; exact hpure k (List.mem_range.mp hk)
  have h_fold :=
    createi_foldlM_pure_aux inst.FnMutInst c f (List.range N.val) [] hf
  simp only [List.nil_append] at h_fold
  unfold createi core_models.array.from_fn rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = ((List.range N.val).map f, c) :=
      (Result.ok.inj heq).symm
    subst hres
    rfl

/-! ### Triple → Result-equation converter

Internal helper: when each call_mut's purity is stated as a Triple
(natural for `hax_mvcgen`-driven proofs), the Result equation needed by
`createi_pure_eq` follows directly. Not exposed externally. -/

private theorem result_eq_of_triple {α : Type} {x : Result α} {v : α}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ r = v ⌝ ⦄) : x = .ok v := by
  match hx : x, h with
  | .ok v', h =>
      have hv' : v' = v := by simpa [Triple, WP.wp] using h
      rw [hv']
  | .fail e, h => exact absurd h (by simp [Triple, WP.wp])
  | .div, h => exact absurd h (by simp [Triple, WP.wp])

/-- **Generic pure-closure `[spec]` for `createi`.**

For any closure whose `call_mut` is pure (doesn't mutate captured state),
`createi N inst c` succeeds and its `i`-th cell is `f i`. The hypothesis
`hpure` is a Triple over each call_mut so `hax_mvcgen` can recurse into
it via per-closure `@[spec]` lemmas.

Tagged `@[spec]` so `hax_mvcgen` chains through nested `createi` calls
in `keccak_f.theta` (3 calls) and `keccak_f.{rho,pi,chi}` (1 call each). -/
@[spec]
theorem createi_pure_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core_models.ops.function.Fn F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩
      ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    createi N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < N.val → a.val[i]! = f i ⌝ ⦄ := by
  have hpure_eq : ∀ k : Nat, k < N.val →
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
    fun k hk => result_eq_of_triple (hpure k hk)
  have heq := createi_pure_eq N inst c f hpure_eq
  rw [heq]
  simp only [Triple, WP.wp]
  apply SPred.pure_intro
  intro i hi
  show ((List.range N.val).map f)[i]! = f i
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi]
  rfl

/-! ### Per-closure purity (Triple form, `[spec]`-tagged for `hax_mvcgen`)

Each hacspec closure used inside `theta`/`rho`/`pi`/`chi` has the shape:
`call_mut state args := do v ← call state args; ok (v, state)` (state-preserving).
We state the per-cell purity as a `@[spec]` Triple so `hax_mvcgen` chains
through it when applied to a `createi`. -/

/-- `f`-side of theta's first closure (computes column XORs). -/
private def theta_closure_c_at (state : Std.Array Std.U64 25#usize) (k : Nat) :
    Std.U64 :=
  state.val[5*k]! ^^^ state.val[5*k+1]! ^^^ state.val[5*k+2]! ^^^
    state.val[5*k+3]! ^^^ state.val[5*k+4]!

/-- `@[spec]` for `keccak_f.get`: with bound `5*x + y < 25`, returns
    `state.val[5*x + y]!`. Chains through `5#usize * x`, `i + y`,
    `Array.index_usize` via Aeneas's `@[step]` arithmetic specs. -/
@[spec]
private theorem keccak_f_get_spec
    (state : Std.Array Std.U64 25#usize) (x y : Std.Usize)
    (hbound : 5 * x.val + y.val < 25) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f.get state x y
    ⦃ ⇓ r => ⌜ r = state.val[5*x.val + y.val]! ⌝ ⦄ := by
  unfold keccak_f.get
  hax_mvcgen
  all_goals scalar_tac

/-- Purity of theta's first closure (5 column-XORs). -/
@[spec]
private theorem theta_closure_call_mut_spec
    (state : Std.Array Std.U64 25#usize) (k : Std.Usize) (hk : k.val < 5) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.theta.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
      state k
    ⦃ ⇓ r => ⌜ r = (theta_closure_c_at state k.val, state) ⌝ ⦄ := by
  unfold keccak_f.theta.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
        keccak_f.theta.closure.Insts.Core_modelsOpsFunctionFnTupleUsizeU64.call
        theta_closure_c_at
  hax_mvcgen
  all_goals (first | scalar_tac | (simp; scalar_tac)
                   | (congr 1; apply Std.U64.bv_eq_imp_eq;
                      simp_all [Std.UScalar.bv_xor]))

/-- `f`-side of theta's second closure (5 d-values: `c[(k+4)%5] ^^^
    rotateLeft64(c[(k+1)%5], 1)`). -/
private def theta_closure_1_d_at (c : Std.Array Std.U64 5#usize) (k : Nat) :
    Std.U64 :=
  c.val[(k + 4) % 5]! ^^^ ⟨(c.val[(k + 1) % 5]!).bv.rotateLeft 1⟩

/-- Purity of theta's second closure (5 d-values). -/
@[spec]
private theorem theta_closure_1_call_mut_spec
    (c : Std.Array Std.U64 5#usize) (k : Std.Usize) (hk : k.val < 5) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.theta.closure_1.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
      c k
    ⦃ ⇓ r => ⌜ r = (theta_closure_1_d_at c k.val, c) ⌝ ⦄ := by
  unfold keccak_f.theta.closure_1.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
        keccak_f.theta.closure_1.Insts.Core_modelsOpsFunctionFnTupleUsizeU64.call
        theta_closure_1_d_at
  hax_mvcgen
  all_goals (first | scalar_tac | (simp; scalar_tac)
                   | (congr 1; apply Std.U64.bv_eq_imp_eq;
                      simp_all [Std.UScalar.bv_xor]))

/-- `f`-side of theta's third closure (25 final state values:
    `state[k] ^^^ d[k/5]`). -/
private def theta_closure_2_at
    (sd : Std.Array Std.U64 25#usize × Std.Array Std.U64 5#usize) (k : Nat) :
    Std.U64 :=
  sd.1.val[k]! ^^^ sd.2.val[k / 5]!

/-- Purity of theta's third closure (25 final values). -/
@[spec]
private theorem theta_closure_2_call_mut_spec
    (sd : Std.Array Std.U64 25#usize × Std.Array Std.U64 5#usize)
    (k : Std.Usize) (hk : k.val < 25) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.theta.closure_2.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
      sd k
    ⦃ ⇓ r => ⌜ r = (theta_closure_2_at sd k.val, sd) ⌝ ⦄ := by
  unfold keccak_f.theta.closure_2.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
        keccak_f.theta.closure_2.Insts.Core_modelsOpsFunctionFnTupleUsizeU64.call
        theta_closure_2_at
  hax_mvcgen
  all_goals (first | scalar_tac | (simp; scalar_tac)
                   | (congr 1; apply Std.U64.bv_eq_imp_eq;
                      simp_all [Std.UScalar.bv_xor]))

/-- `f`-side of `rho`'s closure (25 lane-rotations). -/
private def rho_closure_at (state : Std.Array Std.U64 25#usize) (k : Nat) :
    Std.U64 :=
  ⟨(state.val[k]!).bv.rotateLeft (keccak_f.RHO_OFFSETS.val[k]!).val⟩

/-- Purity of `rho`'s closure. -/
@[spec]
private theorem rho_closure_call_mut_spec
    (state : Std.Array Std.U64 25#usize) (k : Std.Usize) (hk : k.val < 25) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.rho.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
      state k
    ⦃ ⇓ r => ⌜ r = (rho_closure_at state k.val, state) ⌝ ⦄ := by
  unfold keccak_f.rho.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
        keccak_f.rho.closure.Insts.Core_modelsOpsFunctionFnTupleUsizeU64.call
        rho_closure_at
  hax_mvcgen
  all_goals (first | scalar_tac | (simp; scalar_tac)
                   | (congr 1; apply Std.U64.bv_eq_imp_eq;
                      simp_all [Std.UScalar.bv_xor]))

/-- `f`-side of `pi`'s closure (lane permutation). -/
private def pi_closure_at (state : Std.Array Std.U64 25#usize) (k : Nat) :
    Std.U64 :=
  state.val[5 * (((k / 5) + 3 * (k % 5)) % 5) + (k / 5)]!

/-- Purity of `pi`'s closure. -/
@[spec]
private theorem pi_closure_call_mut_spec
    (state : Std.Array Std.U64 25#usize) (k : Std.Usize) (hk : k.val < 25) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.pi.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
      state k
    ⦃ ⇓ r => ⌜ r = (pi_closure_at state k.val, state) ⌝ ⦄ := by
  unfold keccak_f.pi.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
        keccak_f.pi.closure.Insts.Core_modelsOpsFunctionFnTupleUsizeU64.call
        pi_closure_at
  hax_mvcgen
  all_goals (first | scalar_tac | (simp; scalar_tac)
                   | (congr 1; apply Std.U64.bv_eq_imp_eq;
                      simp_all [Std.UScalar.bv_xor]))

/-- `f`-side of `chi`'s closure: `state[5x+y] ^^^ ((¬state[5*((x+1)%5)+y]) &&&
    state[5*((x+2)%5)+y])`, where `x = k/5`, `y = k%5`. -/
private def chi_closure_at (state : Std.Array Std.U64 25#usize) (k : Nat) :
    Std.U64 :=
  let x := k / 5
  let y := k % 5
  state.val[5*x + y]! ^^^
    ⟨(~~~ (state.val[5*((x + 1) % 5) + y]!).bv) &&&
       (state.val[5*((x + 2) % 5) + y]!).bv⟩

/-- Purity of `chi`'s closure. -/
@[spec]
private theorem chi_closure_call_mut_spec
    (state : Std.Array Std.U64 25#usize) (k : Std.Usize) (hk : k.val < 25) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.chi.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
      state k
    ⦃ ⇓ r => ⌜ r = (chi_closure_at state k.val, state) ⌝ ⦄ := by
  unfold keccak_f.chi.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
        keccak_f.chi.closure.Insts.Core_modelsOpsFunctionFnTupleUsizeU64.call
        chi_closure_at
  hax_mvcgen
  all_goals (first
    | scalar_tac
    | (simp; scalar_tac)
    | (congr 1; apply Std.U64.bv_eq_imp_eq
       simp_all only [Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not,
         show ((1#usize : Std.Usize).val) = 1 from rfl,
         show ((2#usize : Std.Usize).val) = 2 from rfl,
         show ((5#usize : Std.Usize).val) = 5 from rfl]))

/-! ### Function-equality theorems: `keccak_f.X = keccak_f.X_unrolled`

Each non-`_unrolled` hacspec function and its `_unrolled` counterpart are
shown to produce the same `Result` value by routing both through their
shared `_applied` form. `keccak_f.X` is proven via `createi_pure_spec` (a
single `hax_mvcgen` chains through createi → per-closure `[spec]`).
`keccak_f.X_unrolled` is proven by the existing `*_unrolled_spec` Triples
in `RoundEquiv.lean` / `PrcLift.lean`. -/

/-- Normalisation bridge: `↑(BitVec.ofNat numBits k)#uscalar = k` when k is
    in bounds. The shape is what `hax_mvcgen` leaves behind when applying
    `createi_pure_spec`'s `hpure` over `inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩`. -/
private theorem usize_bv_ofNat_val (k : Nat) (h : k < 2^UScalarTy.Usize.numBits) :
    Std.UScalar.val (UScalar.mk (BitVec.ofNat UScalarTy.Usize.numBits k)) = k := by
  show (BitVec.ofNat _ k).toNat = k
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

set_option linter.unusedSimpArgs false in
theorem theta_eq_theta_unrolled (state : Std.Array Std.U64 25#usize) :
    keccak_f.theta state = keccak_f.theta_unrolled state := by
  have h1 : keccak_f.theta state = .ok (theta_unrolled_applied state) := by
    apply result_eq_of_triple
    unfold keccak_f.theta
    hax_mvcgen
    case vc1.f => exact theta_closure_c_at state ‹ℕ›
    case vc4.f => exact theta_closure_1_d_at ‹Std.Array Std.U64 5#usize› ‹ℕ›
    case vc8 => exact theta_closure_2_at (state, ‹Std.Array Std.U64 5#usize›) ‹ℕ›
    all_goals first
      | (rw [usize_bv_ofNat_val _ (by scalar_tac)] at *
         first | scalar_tac | assumption)
      | scalar_tac
      | assumption
      | (-- vc7: 25-cell array equality
         apply Subtype.ext
         unfold theta_unrolled_applied
         simp only [Std.Array.make]
         rename_i r_c hc r_d hd r_a ha
         -- hc : ∀ i < 5, r_c.val[i]! = theta_closure_c_at state i
         -- hd : ∀ i < 5, r_d.val[i]! = theta_closure_1_d_at r_c i
         -- ha : ∀ i < 25, r_a.val[i]! = theta_closure_2_at (state, r_d) i
         have hc0 := hc 0 (by decide); have hc1 := hc 1 (by decide)
         have hc2 := hc 2 (by decide); have hc3 := hc 3 (by decide)
         have hc4 := hc 4 (by decide)
         simp only [theta_closure_c_at,
           show (5 * 0 : Nat) = 0 from rfl, show (5 * 0 + 1 : Nat) = 1 from rfl,
           show (5 * 0 + 2 : Nat) = 2 from rfl, show (5 * 0 + 3 : Nat) = 3 from rfl,
           show (5 * 0 + 4 : Nat) = 4 from rfl,
           show (5 * 1 : Nat) = 5 from rfl, show (5 * 1 + 1 : Nat) = 6 from rfl,
           show (5 * 1 + 2 : Nat) = 7 from rfl, show (5 * 1 + 3 : Nat) = 8 from rfl,
           show (5 * 1 + 4 : Nat) = 9 from rfl,
           show (5 * 2 : Nat) = 10 from rfl, show (5 * 2 + 1 : Nat) = 11 from rfl,
           show (5 * 2 + 2 : Nat) = 12 from rfl, show (5 * 2 + 3 : Nat) = 13 from rfl,
           show (5 * 2 + 4 : Nat) = 14 from rfl,
           show (5 * 3 : Nat) = 15 from rfl, show (5 * 3 + 1 : Nat) = 16 from rfl,
           show (5 * 3 + 2 : Nat) = 17 from rfl, show (5 * 3 + 3 : Nat) = 18 from rfl,
           show (5 * 3 + 4 : Nat) = 19 from rfl,
           show (5 * 4 : Nat) = 20 from rfl, show (5 * 4 + 1 : Nat) = 21 from rfl,
           show (5 * 4 + 2 : Nat) = 22 from rfl, show (5 * 4 + 3 : Nat) = 23 from rfl,
           show (5 * 4 + 4 : Nat) = 24 from rfl] at hc0 hc1 hc2 hc3 hc4
         have hd0 := hd 0 (by decide); have hd1 := hd 1 (by decide)
         have hd2 := hd 2 (by decide); have hd3 := hd 3 (by decide)
         have hd4 := hd 4 (by decide)
         simp only [theta_closure_1_d_at, hc0, hc1, hc2, hc3, hc4,
           show (0 + 4) % 5 = 4 from rfl, show (0 + 1) % 5 = 1 from rfl,
           show (1 + 4) % 5 = 0 from rfl, show (1 + 1) % 5 = 2 from rfl,
           show (2 + 4) % 5 = 1 from rfl, show (2 + 1) % 5 = 3 from rfl,
           show (3 + 4) % 5 = 2 from rfl, show (3 + 1) % 5 = 4 from rfl,
           show (4 + 4) % 5 = 3 from rfl, show (4 + 1) % 5 = 0 from rfl] at hd0 hd1 hd2 hd3 hd4
         -- Build per-cell equalities for r_a.val[i]! using ha then substituting hd
         have ha0  := ha  0 (by decide); have ha1  := ha  1 (by decide)
         have ha2  := ha  2 (by decide); have ha3  := ha  3 (by decide)
         have ha4  := ha  4 (by decide); have ha5  := ha  5 (by decide)
         have ha6  := ha  6 (by decide); have ha7  := ha  7 (by decide)
         have ha8  := ha  8 (by decide); have ha9  := ha  9 (by decide)
         have ha10 := ha 10 (by decide); have ha11 := ha 11 (by decide)
         have ha12 := ha 12 (by decide); have ha13 := ha 13 (by decide)
         have ha14 := ha 14 (by decide); have ha15 := ha 15 (by decide)
         have ha16 := ha 16 (by decide); have ha17 := ha 17 (by decide)
         have ha18 := ha 18 (by decide); have ha19 := ha 19 (by decide)
         have ha20 := ha 20 (by decide); have ha21 := ha 21 (by decide)
         have ha22 := ha 22 (by decide); have ha23 := ha 23 (by decide)
         have ha24 := ha 24 (by decide)
         simp only [theta_closure_2_at,
           show (0:Nat)/5 = 0 from rfl, show (1:Nat)/5 = 0 from rfl,
           show (2:Nat)/5 = 0 from rfl, show (3:Nat)/5 = 0 from rfl,
           show (4:Nat)/5 = 0 from rfl,
           show (5:Nat)/5 = 1 from rfl, show (6:Nat)/5 = 1 from rfl,
           show (7:Nat)/5 = 1 from rfl, show (8:Nat)/5 = 1 from rfl,
           show (9:Nat)/5 = 1 from rfl,
           show (10:Nat)/5 = 2 from rfl, show (11:Nat)/5 = 2 from rfl,
           show (12:Nat)/5 = 2 from rfl, show (13:Nat)/5 = 2 from rfl,
           show (14:Nat)/5 = 2 from rfl,
           show (15:Nat)/5 = 3 from rfl, show (16:Nat)/5 = 3 from rfl,
           show (17:Nat)/5 = 3 from rfl, show (18:Nat)/5 = 3 from rfl,
           show (19:Nat)/5 = 3 from rfl,
           show (20:Nat)/5 = 4 from rfl, show (21:Nat)/5 = 4 from rfl,
           show (22:Nat)/5 = 4 from rfl, show (23:Nat)/5 = 4 from rfl,
           hd0, hd1, hd2, hd3, hd4]
           at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
              ha10 ha11 ha12 ha13 ha14 ha15 ha16 ha17 ha18 ha19
              ha20 ha21 ha22 ha23 ha24
         -- Now each ha_i states r_a.val[i]! = (state expression matching list)
         -- Destruct r_a.val using its length 25
         obtain ⟨lst, hlen⟩ := r_a
         simp only [show ((25#usize : Std.Usize).val) = 25 from rfl] at hlen
         -- Strip the list 25 elements
         match lst, hlen with
         | [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,
            v15,v16,v17,v18,v19,v20,v21,v22,v23,v24], _ =>
           simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
             at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 ha12 ha13
                ha14 ha15 ha16 ha17 ha18 ha19 ha20 ha21 ha22 ha23 ha24
           simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9,
             ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19,
             ha20, ha21, ha22, ha23, ha24])
  have h2 : keccak_f.theta_unrolled state = .ok (theta_unrolled_applied state) :=
    result_eq_of_triple (theta_unrolled_spec state)
  rw [h1, h2]

set_option linter.unusedSimpArgs false in
theorem rho_eq_rho_unrolled (state : Std.Array Std.U64 25#usize) :
    keccak_f.rho state = keccak_f.rho_unrolled state := by
  have h1 : keccak_f.rho state = .ok (rho_applied state) := by
    apply result_eq_of_triple
    unfold keccak_f.rho
    hax_mvcgen
    case vc1.f => exact rho_closure_at state ‹ℕ›
    all_goals first
      | (rw [usize_bv_ofNat_val _ (by scalar_tac)] at *
         first | scalar_tac | assumption)
      | scalar_tac
      | (-- final 25-cell array equality
         apply Subtype.ext
         unfold rho_applied
         simp only [Std.Array.make]
         rename_i r_a ha
         have ha0  := ha  0 (by decide); have ha1  := ha  1 (by decide)
         have ha2  := ha  2 (by decide); have ha3  := ha  3 (by decide)
         have ha4  := ha  4 (by decide); have ha5  := ha  5 (by decide)
         have ha6  := ha  6 (by decide); have ha7  := ha  7 (by decide)
         have ha8  := ha  8 (by decide); have ha9  := ha  9 (by decide)
         have ha10 := ha 10 (by decide); have ha11 := ha 11 (by decide)
         have ha12 := ha 12 (by decide); have ha13 := ha 13 (by decide)
         have ha14 := ha 14 (by decide); have ha15 := ha 15 (by decide)
         have ha16 := ha 16 (by decide); have ha17 := ha 17 (by decide)
         have ha18 := ha 18 (by decide); have ha19 := ha 19 (by decide)
         have ha20 := ha 20 (by decide); have ha21 := ha 21 (by decide)
         have ha22 := ha 22 (by decide); have ha23 := ha 23 (by decide)
         have ha24 := ha 24 (by decide)
         simp only [rho_closure_at, rot64,
           show (keccak_f.RHO_OFFSETS.val[0]!).val = 0 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[1]!).val = 36 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[2]!).val = 3 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[3]!).val = 41 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[4]!).val = 18 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[5]!).val = 1 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[6]!).val = 44 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[7]!).val = 10 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[8]!).val = 45 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[9]!).val = 2 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[10]!).val = 62 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[11]!).val = 6 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[12]!).val = 43 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[13]!).val = 15 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[14]!).val = 61 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[15]!).val = 28 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[16]!).val = 55 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[17]!).val = 25 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[18]!).val = 21 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[19]!).val = 56 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[20]!).val = 27 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[21]!).val = 20 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[22]!).val = 39 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[23]!).val = 8 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make],
           show (keccak_f.RHO_OFFSETS.val[24]!).val = 14 from by simp [keccak_f.RHO_OFFSETS, Std.Array.make]]
           at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
              ha10 ha11 ha12 ha13 ha14 ha15 ha16 ha17 ha18 ha19
              ha20 ha21 ha22 ha23 ha24
         obtain ⟨lst, hlen⟩ := r_a
         simp only [show ((25#usize : Std.Usize).val) = 25 from rfl] at hlen
         match lst, hlen with
         | [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,
            v15,v16,v17,v18,v19,v20,v21,v22,v23,v24], _ =>
           simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
             at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 ha12 ha13
                ha14 ha15 ha16 ha17 ha18 ha19 ha20 ha21 ha22 ha23 ha24
           simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9,
             ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19,
             ha20, ha21, ha22, ha23, ha24])
  have h2 : keccak_f.rho_unrolled state = .ok (rho_applied state) :=
    result_eq_of_triple (rho_unrolled_spec state)
  rw [h1, h2]

set_option linter.unusedSimpArgs false in
theorem pi_eq_pi_unrolled (state : Std.Array Std.U64 25#usize) :
    keccak_f.pi state = keccak_f.pi_unrolled state := by
  have h1 : keccak_f.pi state = .ok (pi_applied state) := by
    apply result_eq_of_triple
    unfold keccak_f.pi
    hax_mvcgen
    case vc1.f => exact pi_closure_at state ‹ℕ›
    all_goals first
      | (rw [usize_bv_ofNat_val _ (by scalar_tac)] at *
         first | scalar_tac | assumption)
      | scalar_tac
      | (-- final 25-cell array equality
         apply Subtype.ext
         unfold pi_applied
         simp only [Std.Array.make]
         rename_i r_a ha
         have ha0  := ha  0 (by decide); have ha1  := ha  1 (by decide)
         have ha2  := ha  2 (by decide); have ha3  := ha  3 (by decide)
         have ha4  := ha  4 (by decide); have ha5  := ha  5 (by decide)
         have ha6  := ha  6 (by decide); have ha7  := ha  7 (by decide)
         have ha8  := ha  8 (by decide); have ha9  := ha  9 (by decide)
         have ha10 := ha 10 (by decide); have ha11 := ha 11 (by decide)
         have ha12 := ha 12 (by decide); have ha13 := ha 13 (by decide)
         have ha14 := ha 14 (by decide); have ha15 := ha 15 (by decide)
         have ha16 := ha 16 (by decide); have ha17 := ha 17 (by decide)
         have ha18 := ha 18 (by decide); have ha19 := ha 19 (by decide)
         have ha20 := ha 20 (by decide); have ha21 := ha 21 (by decide)
         have ha22 := ha 22 (by decide); have ha23 := ha 23 (by decide)
         have ha24 := ha 24 (by decide)
         simp only [pi_closure_at,
           show 5 * (((0:Nat) / 5 + 3 * (0 % 5)) % 5) + (0:Nat) / 5 = 0 from rfl,
           show 5 * (((1:Nat) / 5 + 3 * (1 % 5)) % 5) + (1:Nat) / 5 = 15 from rfl,
           show 5 * (((2:Nat) / 5 + 3 * (2 % 5)) % 5) + (2:Nat) / 5 = 5 from rfl,
           show 5 * (((3:Nat) / 5 + 3 * (3 % 5)) % 5) + (3:Nat) / 5 = 20 from rfl,
           show 5 * (((4:Nat) / 5 + 3 * (4 % 5)) % 5) + (4:Nat) / 5 = 10 from rfl,
           show 5 * (((5:Nat) / 5 + 3 * (5 % 5)) % 5) + (5:Nat) / 5 = 6 from rfl,
           show 5 * (((6:Nat) / 5 + 3 * (6 % 5)) % 5) + (6:Nat) / 5 = 21 from rfl,
           show 5 * (((7:Nat) / 5 + 3 * (7 % 5)) % 5) + (7:Nat) / 5 = 11 from rfl,
           show 5 * (((8:Nat) / 5 + 3 * (8 % 5)) % 5) + (8:Nat) / 5 = 1 from rfl,
           show 5 * (((9:Nat) / 5 + 3 * (9 % 5)) % 5) + (9:Nat) / 5 = 16 from rfl,
           show 5 * (((10:Nat) / 5 + 3 * (10 % 5)) % 5) + (10:Nat) / 5 = 12 from rfl,
           show 5 * (((11:Nat) / 5 + 3 * (11 % 5)) % 5) + (11:Nat) / 5 = 2 from rfl,
           show 5 * (((12:Nat) / 5 + 3 * (12 % 5)) % 5) + (12:Nat) / 5 = 17 from rfl,
           show 5 * (((13:Nat) / 5 + 3 * (13 % 5)) % 5) + (13:Nat) / 5 = 7 from rfl,
           show 5 * (((14:Nat) / 5 + 3 * (14 % 5)) % 5) + (14:Nat) / 5 = 22 from rfl,
           show 5 * (((15:Nat) / 5 + 3 * (15 % 5)) % 5) + (15:Nat) / 5 = 18 from rfl,
           show 5 * (((16:Nat) / 5 + 3 * (16 % 5)) % 5) + (16:Nat) / 5 = 8 from rfl,
           show 5 * (((17:Nat) / 5 + 3 * (17 % 5)) % 5) + (17:Nat) / 5 = 23 from rfl,
           show 5 * (((18:Nat) / 5 + 3 * (18 % 5)) % 5) + (18:Nat) / 5 = 13 from rfl,
           show 5 * (((19:Nat) / 5 + 3 * (19 % 5)) % 5) + (19:Nat) / 5 = 3 from rfl,
           show 5 * (((20:Nat) / 5 + 3 * (20 % 5)) % 5) + (20:Nat) / 5 = 24 from rfl,
           show 5 * (((21:Nat) / 5 + 3 * (21 % 5)) % 5) + (21:Nat) / 5 = 14 from rfl,
           show 5 * (((22:Nat) / 5 + 3 * (22 % 5)) % 5) + (22:Nat) / 5 = 4 from rfl,
           show 5 * (((23:Nat) / 5 + 3 * (23 % 5)) % 5) + (23:Nat) / 5 = 19 from rfl,
           show 5 * (((24:Nat) / 5 + 3 * (24 % 5)) % 5) + (24:Nat) / 5 = 9 from rfl]
           at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
              ha10 ha11 ha12 ha13 ha14 ha15 ha16 ha17 ha18 ha19
              ha20 ha21 ha22 ha23 ha24
         obtain ⟨lst, hlen⟩ := r_a
         simp only [show ((25#usize : Std.Usize).val) = 25 from rfl] at hlen
         match lst, hlen with
         | [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,
            v15,v16,v17,v18,v19,v20,v21,v22,v23,v24], _ =>
           simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
             at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 ha12 ha13
                ha14 ha15 ha16 ha17 ha18 ha19 ha20 ha21 ha22 ha23 ha24
           simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9,
             ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19,
             ha20, ha21, ha22, ha23, ha24])
  have h2 : keccak_f.pi_unrolled state = .ok (pi_applied state) :=
    result_eq_of_triple (pi_unrolled_spec state)
  rw [h1, h2]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 16000000 in
theorem chi_eq_chi_unrolled (state : Std.Array Std.U64 25#usize) :
    keccak_f.chi state = keccak_f.chi_unrolled state := by
  have h1 : keccak_f.chi state = .ok (chi_applied state) := by
    apply result_eq_of_triple
    unfold keccak_f.chi
    hax_mvcgen
    case vc1.f => exact chi_closure_at state ‹ℕ›
    all_goals first
      | (rw [usize_bv_ofNat_val _ (by scalar_tac)] at *
         first | scalar_tac | assumption)
      | scalar_tac
      | (-- final 25-cell array equality
         apply Subtype.ext
         unfold chi_applied
         simp only [Std.Array.make]
         rename_i r_a ha
         have ha0  := ha  0 (by decide); have ha1  := ha  1 (by decide)
         have ha2  := ha  2 (by decide); have ha3  := ha  3 (by decide)
         have ha4  := ha  4 (by decide); have ha5  := ha  5 (by decide)
         have ha6  := ha  6 (by decide); have ha7  := ha  7 (by decide)
         have ha8  := ha  8 (by decide); have ha9  := ha  9 (by decide)
         have ha10 := ha 10 (by decide); have ha11 := ha 11 (by decide)
         have ha12 := ha 12 (by decide); have ha13 := ha 13 (by decide)
         have ha14 := ha 14 (by decide); have ha15 := ha 15 (by decide)
         have ha16 := ha 16 (by decide); have ha17 := ha 17 (by decide)
         have ha18 := ha 18 (by decide); have ha19 := ha 19 (by decide)
         have ha20 := ha 20 (by decide); have ha21 := ha 21 (by decide)
         have ha22 := ha 22 (by decide); have ha23 := ha 23 (by decide)
         have ha24 := ha 24 (by decide)
         simp only [chi_closure_at,
           show (0:Nat)/5 = 0 from rfl, show (0:Nat)%5 = 0 from rfl,
           show (1:Nat)/5 = 0 from rfl, show (1:Nat)%5 = 1 from rfl,
           show (2:Nat)/5 = 0 from rfl, show (2:Nat)%5 = 2 from rfl,
           show (3:Nat)/5 = 0 from rfl, show (3:Nat)%5 = 3 from rfl,
           show (4:Nat)/5 = 0 from rfl, show (4:Nat)%5 = 4 from rfl,
           show (5:Nat)/5 = 1 from rfl, show (5:Nat)%5 = 0 from rfl,
           show (6:Nat)/5 = 1 from rfl, show (6:Nat)%5 = 1 from rfl,
           show (7:Nat)/5 = 1 from rfl, show (7:Nat)%5 = 2 from rfl,
           show (8:Nat)/5 = 1 from rfl, show (8:Nat)%5 = 3 from rfl,
           show (9:Nat)/5 = 1 from rfl, show (9:Nat)%5 = 4 from rfl,
           show (10:Nat)/5 = 2 from rfl, show (10:Nat)%5 = 0 from rfl,
           show (11:Nat)/5 = 2 from rfl, show (11:Nat)%5 = 1 from rfl,
           show (12:Nat)/5 = 2 from rfl, show (12:Nat)%5 = 2 from rfl,
           show (13:Nat)/5 = 2 from rfl, show (13:Nat)%5 = 3 from rfl,
           show (14:Nat)/5 = 2 from rfl, show (14:Nat)%5 = 4 from rfl,
           show (15:Nat)/5 = 3 from rfl, show (15:Nat)%5 = 0 from rfl,
           show (16:Nat)/5 = 3 from rfl, show (16:Nat)%5 = 1 from rfl,
           show (17:Nat)/5 = 3 from rfl, show (17:Nat)%5 = 2 from rfl,
           show (18:Nat)/5 = 3 from rfl, show (18:Nat)%5 = 3 from rfl,
           show (19:Nat)/5 = 3 from rfl, show (19:Nat)%5 = 4 from rfl,
           show (20:Nat)/5 = 4 from rfl, show (20:Nat)%5 = 0 from rfl,
           show (21:Nat)/5 = 4 from rfl, show (21:Nat)%5 = 1 from rfl,
           show (22:Nat)/5 = 4 from rfl, show (22:Nat)%5 = 2 from rfl,
           show (23:Nat)/5 = 4 from rfl, show (23:Nat)%5 = 3 from rfl,
           show (24:Nat)/5 = 4 from rfl, show (24:Nat)%5 = 4 from rfl,
           show (0 + 1) % 5 = 1 from rfl, show (0 + 2) % 5 = 2 from rfl,
           show (1 + 1) % 5 = 2 from rfl, show (1 + 2) % 5 = 3 from rfl,
           show (2 + 1) % 5 = 3 from rfl, show (2 + 2) % 5 = 4 from rfl,
           show (3 + 1) % 5 = 4 from rfl, show (3 + 2) % 5 = 0 from rfl,
           show (4 + 1) % 5 = 0 from rfl, show (4 + 2) % 5 = 1 from rfl]
           at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
              ha10 ha11 ha12 ha13 ha14 ha15 ha16 ha17 ha18 ha19
              ha20 ha21 ha22 ha23 ha24
         obtain ⟨lst, hlen⟩ := r_a
         simp only [show ((25#usize : Std.Usize).val) = 25 from rfl] at hlen
         match lst, hlen with
         | [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,
            v15,v16,v17,v18,v19,v20,v21,v22,v23,v24], _ =>
           simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
             at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 ha12 ha13
                ha14 ha15 ha16 ha17 ha18 ha19 ha20 ha21 ha22 ha23 ha24
           simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9,
             ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19,
             ha20, ha21, ha22, ha23, ha24]
           apply List.cons_eq_cons.mpr
           refine ⟨?_, ?_⟩
           all_goals first
             | rfl
             | (apply Std.U64.bv_eq_imp_eq
                simp_all only [Std.UScalar.bv_xor, Std.UScalar.bv_and,
                  Std.UScalar.bv_not])
             | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  have h2 : keccak_f.chi_unrolled state = .ok (chi_applied state) :=
    result_eq_of_triple (chi_unrolled_spec state)
  rw [h1, h2]

/-! ## Bridge 1 closure: spec_round_step / spec_chain equality

These compose the four X = X_unrolled lemmas above to bridge
`spec_round_step_hacspec` ↔ `spec_round_step`, then lift via induction to
`spec_chain_hacspec` ↔ `spec_chain`. -/

theorem spec_round_step_hacspec_eq_spec_round_step
    (state : Std.Array Std.U64 25#usize) (round : Std.Usize) :
    spec_round_step_hacspec state round = spec_round_step state round := by
  unfold spec_round_step_hacspec spec_round_step
  simp only [theta_eq_theta_unrolled, rho_eq_rho_unrolled, pi_eq_pi_unrolled,
      chi_eq_chi_unrolled]

theorem spec_chain_hacspec_eq_spec_chain
    (s : Std.Array Std.U64 25#usize) (n : Nat) :
    spec_chain_hacspec s n = spec_chain s n := by
  induction n with
  | zero => rw [spec_chain_hacspec_zero, spec_chain_zero]
  | succ k ih =>
    rw [spec_chain_hacspec_succ, spec_chain_succ, ih]
    -- Both sides now end with `>>= spec_round_step_*_at k`. Show the
    -- two `_at` wrappers are equal as functions.
    congr 1
    funext st
    unfold spec_round_step_hacspec_at spec_round_step_at
    by_cases hk : k < 24
    · simp only [dif_pos hk]
      exact spec_round_step_hacspec_eq_spec_round_step st _
    · simp only [dif_neg hk]

/-! ## Top-level theorem: impl ↔ hacspec

`keccak.keccakf1600 s` succeeds and produces `r_impl` such that the
hacspec `keccak_f.keccak_f` applied to `lift s` succeeds with
`lift r_impl`. Composes `keccakf1600_equiv_via_bit` (Campaign 1+2
canonical post) with `spec_chain_hacspec ↔ spec_chain` (Bridge 1) and
`keccak_f_loop_eq_spec_chain_hacspec` (loop bridge). -/

theorem keccakf1600_equiv_hacspec (s : state.KeccakState)
    (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccak_f.keccak_f (lift s) = .ok (lift r_impl) ⌝ ⦄ := by
  -- Start from `keccakf1600_equiv_via_bit`'s canonical post.
  apply Std.Do.Triple.of_entails_right _ (BitKeccak.keccakf1600_equiv_via_bit s h_i)
  rw [PostCond.entails_noThrow]
  intro r h_post
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_post ⊢
  -- `h_post : keccakf1600_post_canonical s r`.
  -- Unfold the canonical post to get the spec_chain equation.
  unfold keccakf1600_post_canonical at h_post
  -- Convert the `Nat.fold` form to `spec_chain`.
  have h_chain :
      (do let lifted_final ← spec_chain (Equivalence.lift s) 24
          pure (lifted_final = Equivalence.lift r)).holds := by
    have h_eq :
        (do let lifted_final ← Nat.fold 24
              (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
              (pure (Equivalence.lift s))
            pure (lifted_final = Equivalence.lift r)).holds
        = (do let lifted_final ← spec_chain (Equivalence.lift s) 24
              pure (lifted_final = Equivalence.lift r)).holds := by
      unfold spec_chain spec_round_step_at
      congr 1
    rw [h_eq] at h_post
    exact h_post
  -- Extract spec_chain (lift s) 24 = .ok (lift r).
  have h_spec_chain : spec_chain (Equivalence.lift s) 24 = .ok (Equivalence.lift r) :=
    holds_chain_eq_ok h_chain
  -- Bridge via spec_chain_hacspec and keccak_f_loop_eq_spec_chain_hacspec.
  rw [keccak_f_loop_eq_spec_chain_hacspec, spec_chain_hacspec_eq_spec_chain]
  exact h_spec_chain

end libcrux_iot_sha3.Equivalence
