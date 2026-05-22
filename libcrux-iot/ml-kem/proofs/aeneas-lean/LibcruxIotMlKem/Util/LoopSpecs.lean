/-
  # `Util/LoopSpecs.lean` — Generic Aeneas `loop` + iterator-range Triples

  Factored from libcrux-iot SHA-3's generic-core loop infrastructure:

  - `result_eq_of_triple` —
    `LibcruxIotSha3/Equivalence/I32LoopSpec.lean:35` (re-exported from
    `Util.SliceSpecs` so this module's downstream consumers can `open
    libcrux_iot_ml_kem.Util` and get both).
  - `IteratorRange_next_spec_i32` + `loop_range_spec_i32` —
    `LibcruxIotSha3/Equivalence/I32LoopSpec.lean:51,146`.
  - `IteratorRange_next_spec_usize` + `loop_range_spec_usize` —
    `LibcruxIotSha3/Equivalence/HacspecBridge.lean:130,231`.
  - `array_from_fn_eq_unfold5` + the `bv_ofNat_eq_usize_lit_{0..4}`
    helpers —
    `LibcruxIotSha3/Equivalence/HacspecBridge.lean:41-110`.

  Namespace rewritten from `libcrux_iot_sha3.Equivalence` →
  `libcrux_iot_ml_kem.Util`. **No** SHA-3-specific content is carried
  over: the corresponding SHA-3 file
  `LibcruxIotSha3/Sponge/LoopSpecs.lean` (1277 LOC) is *not* generic —
  it contains the `state.load_block_2u32_loop{0,1}_spec` and
  `state.store_block_2u32_loop_spec` Triples, which are deeply tied to
  the `KeccakState` / `Lane2U32` representation. Only the genuinely
  reusable loop combinators above are lifted; SHA-3-specific loop
  invariants and bit-level deinterleave helpers stay in the SHA-3 tree.

  ## Status

  All theorems below are verbatim ports (rewriting only the namespace).
  Every proof compiles with the same `set_option`s and tactics as the
  SHA-3 originals.
-/
import LibcruxIotMlKem.Util.SliceSpecs
import Hax

open Aeneas Aeneas.Std Result ControlFlow Std.Do

namespace libcrux_iot_ml_kem.Util

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## Re-export `result_eq_of_triple`

`Util.SliceSpecs` already proves this; we re-export the name into this
module's namespace so downstream `import Util.LoopSpecs` callers
automatically see it. -/

-- (`Util.result_eq_of_triple` is in scope via `Util.SliceSpecs`.)

/-! ## `Usize.val` conversion for small-Nat constants

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

/-! ## `Usize` iterator-next spec

The `Usize.Insts.Core_modelsIterRangeStep` instance is an abbrev for
`core_models.iter.range.StepUsize` (see Aeneas-Std `FunsPrologue.lean`).

Splits on `i.val < e.val`: if so, returns `some i` plus the incremented
range; otherwise returns `none`. -/

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

/-! ## `Usize` loop-over-range spec

Specialized to `loop` over `core.ops.range.Range Usize`. An invariant
`inv : Usize → β → Result Prop` is preserved by each step. Induction on
`(e.val - start.val)`. -/

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

/-! ## `I32` iterator-next spec

The `core_models.I32.Insts.Core_modelsIterRangeStep` instance uses
`IScalar.tryMk .I32 (start.val + 1)` for `forward_checked`. For ranges
within `[-2^31, 2^31)` this always succeeds. -/

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

/-! ## `I32` loop-over-range spec

Specialized to `loop` over `core.ops.range.Range I32`. Same shape as the
`Usize` version. -/

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

end libcrux_iot_ml_kem.Util
