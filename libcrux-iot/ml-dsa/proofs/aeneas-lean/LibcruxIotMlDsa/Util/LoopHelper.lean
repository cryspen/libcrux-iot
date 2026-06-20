/-
  # `Util/LoopHelper.lean` — Layer-1 elementwise loop infrastructure (ML-DSA)

  ML-DSA analogue of ml-kem's
  `LibcruxIotMlKem/Vector/Portable/Arithmetic/LoopHelper.lean`.

  The ML-DSA elementwise binary ops (`add`, `subtract`) are
  `for i in 0..8 { a[i] = wrapping_<op>(a[i], rhs.values[i]) }` loops.
  Two structural deltas vs. ml-kem's `PortableVector`-accumulator family:

  - The loop **accumulator is the raw `Array Std.I32 8#usize`**, not the
    `simd.portable.vector_type.Coefficients` struct (ml-kem accumulated the
    whole struct). The body reads array `a`, reads `rhs.values`, and writes
    back the array.
  - Lanes: 8 (vs. 16) and `Std.I32` (vs. `Std.I16`); the loop bound `e` is
    kept generic (the top-level `add`/`subtract` derive it from
    `Slice.len (Array.to_slice lhs.values)`, which reduces to `8#usize`).

  We provide the binary family:

  - `binary_loop_body` — canonical body shape (matches
    `simd.portable.arithmetic.{add,subtract}_loop.body`).
  - `binary_loop_inv` — canonical 2-conjunct loop invariant.
  - `binary_step_post` + `elementwise_binary_step` — per-iteration step lemma.
  - `elementwise_binary_spec` — top-level wrapper that invokes
    `loop_range_spec_usize`.

  Proof strategy mirrors ml-kem: turn each component of the body
  (`IteratorRange.next`, `Array.index_usize` ×2, `per_elem`, `Array.update`)
  into a `Result` equation, compose into a single body equation, then close
  via `triple_of_ok_pv`. This is the cleanest substitute for `mvcgen` when
  the spec is generic in `per_elem`.

  This module is Mathlib-free above the `Util` barrier (it imports only
  `Util.LoopSpecs` and the extraction).
-/
import LibcruxIotMlDsa.Util.LoopSpecs
import LibcruxIotMlDsa.Extraction.Funs

open CoreModels Aeneas Aeneas.Std Result ControlFlow Std.Do

namespace libcrux_iot_ml_dsa.Util.LoopHelper
open libcrux_iot_ml_dsa.Util.LoopSpecs libcrux_iot_ml_dsa.Util.SliceSpecs
set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## `Coefficients` carrier abbreviations -/

/-- The carrier values array type (`Array Std.I32 8#usize`). -/
abbrev CoeffArray := Std.Array Std.I32 8#usize

/-! ## Length-of-values bridge -/

@[simp]
theorem Coefficients_values_length
    (v : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    v.values.length = 8 := by
  have := v.values.property
  show v.values.val.length = 8
  exact this

@[simp]
theorem CoeffArray_length (a : CoeffArray) : a.length = 8 := by
  have := a.property
  show a.val.length = 8
  exact this

/-! ## Local helpers — Triple ↔ Result.ok bridges, pure-prop holds. -/

section helpers

private theorem triple_of_ok_pv
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem triple_exists_ok_pv
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem pure_prop_holds_pv {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_pv {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Triple, WP.wp] at h; exact h trivial

end helpers

/-! ## Iterator-next reduction to a `Result` equation (generic bound `e`). -/

/-- `i.val < e.val`: `IteratorRange.next` returns `.ok (some i, iter')` with
    `iter'.end = e` and `iter'.start.val = i.val + 1`. -/
theorem iter_next_some_eq (i e : Std.Usize) (h_lt : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      CoreModels.core.iter.range.IteratorRange.next
        core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
      = .ok (some i,
          ({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      ∃ s : Std.Usize, s.val = i.val + 1
        ∧ oi = (some i,
                ({ start := s, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun _ s hs => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      exact ⟨s, hs, rfl⟩)
    (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_pv hT
  obtain ⟨s, hs_val, hpair⟩ := hP
  exact ⟨s, hs_val, by rw [hveq, hpair]⟩

/-- `i.val ≥ e.val`: `IteratorRange.next` returns `.ok (none, _)`. -/
theorem iter_next_none_eq (i e : Std.Usize) (h_ge : i.val ≥ e.val) :
    CoreModels.core.iter.range.IteratorRange.next
      core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
    = .ok ((none : Option Std.Usize),
            ({ start := i, «end» := e }
              : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      oi = ((none : Option Std.Usize),
            ({ start := i, «end» := e }
              : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun hlt => absurd hlt (Nat.not_lt.mpr h_ge))
    (fun _ => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_pv hT
  rw [hveq, hP]

/-! ## Array index/update reduction to `Result` equations. -/

theorem array_index_usize_ok_eq
    {α : Type u} {n : Std.Usize} [Inhabited α]
    (v : Std.Array α n) (i : Std.Usize) (h_bd : i.val < v.length) :
    Aeneas.Std.Array.index_usize v i = .ok (v.val[i.val]!) := by
  have hT := Aeneas.Std.Array.index_usize_spec v i h_bd
  have h_ex := Aeneas.Std.WP.spec_imp_exists hT
  obtain ⟨v', hveq, hPv'⟩ := h_ex
  rw [hveq, hPv', getElem!_pos]

theorem array_update_ok_eq
    {α : Type u} {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (x : α) (h_bd : i.val < v.length) :
    Aeneas.Std.Array.update v i x = .ok (v.set i x) := by
  have hT := Aeneas.Std.Array.update_spec v i x h_bd
  have h_ex := Aeneas.Std.WP.spec_imp_exists hT
  obtain ⟨v', hveq, hPv'⟩ := h_ex
  rw [hveq, hPv']

/-! ## Unary loop body (canonical shape from Funs.lean).

The accumulator is the raw `CoeffArray = Array Std.I32 8#usize`. The per-element
op has type `I32 → Result I32`; it reads `a[i]`, applies `per_elem`, and writes
back to `a[i]`. This is the binary body with the `rhs`/`input_rhs` operand
dropped (e.g. `negate`, `montgomery_multiply_by_constant`'s per-lane op closes
over a free constant `c`, so the loop carries a single array). -/

def unary_loop_body
    (per_elem : Std.I32 → Result Std.I32)
    (iter : CoreModels.core.ops.range.Range Std.Usize)
    (a : CoeffArray) :
    Result (ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
      CoeffArray) := do
  let (o, iter1) ←
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | core.option.Option.None => ok (done a)
  | core.option.Option.Some i =>
    let i1 ← Aeneas.Std.Array.index_usize a i
    let i2 ← per_elem i1
    let a1 ← Aeneas.Std.Array.update a i i2
    ok (cont (iter1, a1))

/-- 2-conjunct unary invariant:
    - For `j < k`, `a[j]` equals the per-elem-op output `r` for input
      `input[j]` (carrying the per-elem predicate `P`).
    - For `j ≥ k`, `a[j] = input[j]`. -/
def unary_loop_inv
    (per_elem : Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Prop)
    (input : CoeffArray) :
    Std.Usize → CoeffArray → Result Prop :=
  fun k a => pure (
    (∀ j : Nat, j < k.val →
      ∃ r, per_elem (input.val[j]!) = .ok r
            ∧ a.val[j]! = r
            ∧ P (input.val[j]!) r)
    ∧ (∀ j : Nat, k.val ≤ j → j < 8 →
        a.val[j]! = input.val[j]!))

/-- Per-iteration post for `unary_loop_body`. -/
def unary_step_post
    (per_elem : Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Prop)
    (input : CoeffArray)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
      CoeffArray) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (8#usize : Std.Usize).val ∧ iter'.«end» = 8#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (unary_loop_inv per_elem P input iter'.start acc').holds
  | .done y => (unary_loop_inv per_elem P input 8#usize y).holds

set_option maxHeartbeats 4000000 in
theorem elementwise_unary_step
    (per_elem : Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Prop)
    (per_elem_spec :
      ∀ (x : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x ⦃ ⇓ r => ⌜ P x r ⌝ ⦄)
    (input : CoeffArray)
    (acc : CoeffArray)
    (k : Std.Usize)
    (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_inv : (unary_loop_inv per_elem P input k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    unary_loop_body per_elem { start := k, «end» := 8#usize } acc
    ⦃ ⇓ r => ⌜ unary_step_post per_elem P input k r ⌝ ⦄ := by
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_pv h_inv
  have h_acc_len : acc.length = 8 := CoeffArray_length acc
  have h_8 : (8#usize : Std.Usize).val = 8 := rfl
  unfold unary_loop_body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- Some i = k branch.
    have hk_8 : k.val < 8 := by rw [h_8] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 8#usize h_lt
    have h_idx :
        Aeneas.Std.Array.index_usize acc k = .ok (acc.val[k.val]!) :=
      array_index_usize_ok_eq acc k (by rw [h_acc_len]; exact hk_8)
    obtain ⟨r, h_per_eq, h_per_P⟩ :=
      triple_exists_ok_pv (per_elem_spec (acc.val[k.val]!))
    have h_upd :
        Aeneas.Std.Array.update acc k r
        = .ok (acc.set k r) :=
      array_update_ok_eq acc k r (by rw [h_acc_len]; exact hk_8)
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
                  CoeffArray))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize acc i
            let i2 ← per_elem i1
            let a1 ← Aeneas.Std.Array.update acc i i2
            ok (cont (iter1, a1)))
        = .ok (cont
            (({ start := s, «end» := 8#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
             acc.set k r)) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [bind_tc_ok]
      rw [h_idx]
      simp only [bind_tc_ok]
      rw [h_per_eq]
      simp only [bind_tc_ok]
      rw [h_upd]
      rfl
    apply triple_of_ok_pv h_body
    show unary_step_post per_elem P input k
            (.cont (({ start := s, «end» := 8#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    acc.set k r))
    unfold unary_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (unary_loop_inv per_elem P input s (acc.set k r)).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · obtain ⟨r_j, h_per_j, h_acc_j, h_P_j⟩ := h_acc_done j hj_lt_k
        refine ⟨r_j, h_per_j, ?_, h_P_j⟩
        have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne : (acc.set k r)[j]! = acc[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc k j r h_ne
        have : (acc.set k r).val[j]! = acc.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show (acc.set k r).val[j]! = r_j
        rw [this]; exact h_acc_j
      · subst hj_eq_k
        refine ⟨r, ?_, ?_, ?_⟩
        · have h_eq : acc.val[k.val]! = input.val[k.val]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_8
          rw [← h_eq]; exact h_per_eq
        · have h_lt'' : k.val < acc.length := by rw [h_acc_len]; exact hk_8
          have h_set_eq : (acc.set k r)[k.val]! = r :=
            Aeneas.Std.Array.getElem!_Nat_set_eq acc k k.val r ⟨rfl, h_lt''⟩
          have : (acc.set k r).val[k.val]! = r := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
          show (acc.set k r).val[k.val]! = r
          exact this
        · have h_eq : acc.val[k.val]! = input.val[k.val]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_8
          rw [← h_eq]; exact h_per_P
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne : (acc.set k r)[j]! = acc[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc k j r h_ne
      have : (acc.set k r).val[j]! = acc.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.set k r).val[j]! = input.val[j]!
      rw [this]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch.
    have hk_ge : k.val ≥ (8#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 8 := by rw [h_8] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k 8#usize hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
                  CoeffArray))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize acc i
            let i2 ← per_elem i1
            let a1 ← Aeneas.Std.Array.update acc i i2
            ok (cont (iter1, a1)))
        = .ok (done acc) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_pv h_body
    show unary_step_post per_elem P input k (.done acc)
    unfold unary_step_post
    show (unary_loop_inv per_elem P input 8#usize acc).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      apply h_acc_done j
      rw [hk_eq]; rw [h_8] at hj; exact hj
    · intro j hj_ge hj_lt
      apply h_acc_undone j _ hj_lt
      rw [hk_eq]; rw [h_8] at hj_ge; exact hj_ge

/-! ## Top-level unary elementwise spec wrapper -/

set_option maxHeartbeats 2000000 in
theorem elementwise_unary_spec
    (per_elem : Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Prop)
    (per_elem_spec :
      ∀ (x : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x ⦃ ⇓ r => ⌜ P x r ⌝ ⦄)
    (input : CoeffArray) :
    ⦃ ⌜ True ⌝ ⦄
    loop (fun p => unary_loop_body per_elem p.1 p.2)
      (({ start := 0#usize, «end» := 8#usize }
        : CoreModels.core.ops.range.Range Std.Usize), input)
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 8 →
              ∃ ri, per_elem (input.val[i]!) = .ok ri
                    ∧ r.val[i]! = ri
                    ∧ P (input.val[i]!) ri ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, vec1) => unary_loop_body per_elem iter1 vec1)
      input 0#usize 8#usize
      (unary_loop_inv per_elem P input)
      (by decide : (0#usize : Std.Usize).val ≤ (8#usize : Std.Usize).val)
      (pure_prop_holds_pv ⟨
        fun j hj => by
          have h0 : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds_pv h
    intro j hj
    apply h_done j
    show j < (8#usize : Std.Usize).val
    exact hj
  · intro acc k h_ge h_le hinv
    have h_step :=
      elementwise_unary_step per_elem P per_elem_spec input acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : unary_step_post per_elem P input k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [unary_step_post] using hP
    · have hP : unary_step_post per_elem P input k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [unary_step_post] using hP

/-! ## Binary loop body (canonical shape from Funs.lean).

The accumulator is the raw `CoeffArray = Array Std.I32 8#usize`; `rhs` is the
`Coefficients` struct (read-only, captured by the body lambda). The per-element
op has type `I32 → I32 → Result I32`; it reads `a[i]` and `rhs.values[i]`,
applies `per_elem`, and writes back to `a[i]`. -/

def binary_loop_body
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (rhs : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (iter : CoreModels.core.ops.range.Range Std.Usize)
    (a : CoeffArray) :
    Result (ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
      CoeffArray) := do
  let (o, iter1) ←
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | core.option.Option.None => ok (done a)
  | core.option.Option.Some i =>
    let i1 ← Aeneas.Std.Array.index_usize a i
    let i2 ← Aeneas.Std.Array.index_usize rhs.values i
    let i3 ← per_elem i1 i2
    let a1 ← Aeneas.Std.Array.update a i i3
    ok (cont (iter1, a1))

/-- 2-conjunct binary invariant:
    - For `j < k`, `a[j]` equals the per-elem-op output `r` for inputs
      `input_lhs[j]` and `input_rhs.values[j]`.
    - For `j ≥ k`, `a[j] = input_lhs[j]` (rhs is read-only). -/
def binary_loop_inv
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Std.I32 → Prop)
    (input_lhs : CoeffArray)
    (input_rhs : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    Std.Usize → CoeffArray → Result Prop :=
  fun k a => pure (
    (∀ j : Nat, j < k.val →
      ∃ r, per_elem (input_lhs.val[j]!) (input_rhs.values.val[j]!) = .ok r
            ∧ a.val[j]! = r
            ∧ P (input_lhs.val[j]!) (input_rhs.values.val[j]!) r)
    ∧ (∀ j : Nat, k.val ≤ j → j < 8 →
        a.val[j]! = input_lhs.val[j]!))

/-- Per-iteration post for `binary_loop_body` (stated as a top-level `def`
    rather than an inline `match` to keep the `match_N` constant canonical
    across the step lemma and the `loop_range_spec_usize` call site). -/
def binary_step_post
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Std.I32 → Prop)
    (input_lhs : CoeffArray)
    (input_rhs : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
      CoeffArray) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (8#usize : Std.Usize).val ∧ iter'.«end» = 8#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (binary_loop_inv per_elem P input_lhs input_rhs iter'.start acc').holds
  | .done y => (binary_loop_inv per_elem P input_lhs input_rhs 8#usize y).holds

set_option maxHeartbeats 4000000 in
theorem elementwise_binary_step
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Std.I32 → Prop)
    (per_elem_spec :
      ∀ (x y : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x y ⦃ ⇓ r => ⌜ P x y r ⌝ ⦄)
    (input_lhs : CoeffArray)
    (input_rhs : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (acc : CoeffArray)
    (k : Std.Usize)
    (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_inv : (binary_loop_inv per_elem P input_lhs input_rhs k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    binary_loop_body per_elem input_rhs { start := k, «end» := 8#usize } acc
    ⦃ ⇓ r => ⌜ binary_step_post per_elem P input_lhs input_rhs k r ⌝ ⦄ := by
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_pv h_inv
  have h_acc_len : acc.length = 8 := CoeffArray_length acc
  have h_rhs_len : input_rhs.values.length = 8 := Coefficients_values_length input_rhs
  have h_8 : (8#usize : Std.Usize).val = 8 := rfl
  unfold binary_loop_body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- Some i = k branch.
    have hk_8 : k.val < 8 := by rw [h_8] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 8#usize h_lt
    have h_idx_lhs :
        Aeneas.Std.Array.index_usize acc k = .ok (acc.val[k.val]!) :=
      array_index_usize_ok_eq acc k (by rw [h_acc_len]; exact hk_8)
    have h_idx_rhs :
        Aeneas.Std.Array.index_usize input_rhs.values k
          = .ok (input_rhs.values.val[k.val]!) :=
      array_index_usize_ok_eq input_rhs.values k (by rw [h_rhs_len]; exact hk_8)
    obtain ⟨r, h_per_eq, h_per_P⟩ :=
      triple_exists_ok_pv (per_elem_spec (acc.val[k.val]!)
                                          (input_rhs.values.val[k.val]!))
    have h_upd :
        Aeneas.Std.Array.update acc k r
        = .ok (acc.set k r) :=
      array_update_ok_eq acc k r (by rw [h_acc_len]; exact hk_8)
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
                  CoeffArray))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize acc i
            let i2 ← Aeneas.Std.Array.index_usize input_rhs.values i
            let i3 ← per_elem i1 i2
            let a1 ← Aeneas.Std.Array.update acc i i3
            ok (cont (iter1, a1)))
        = .ok (cont
            (({ start := s, «end» := 8#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
             acc.set k r)) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [bind_tc_ok]
      rw [h_idx_lhs]
      simp only [bind_tc_ok]
      rw [h_idx_rhs]
      simp only [bind_tc_ok]
      rw [h_per_eq]
      simp only [bind_tc_ok]
      rw [h_upd]
      rfl
    apply triple_of_ok_pv h_body
    show binary_step_post per_elem P input_lhs input_rhs k
            (.cont (({ start := s, «end» := 8#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    acc.set k r))
    unfold binary_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (binary_loop_inv per_elem P input_lhs input_rhs s (acc.set k r)).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · obtain ⟨r_j, h_per_j, h_acc_j, h_P_j⟩ := h_acc_done j hj_lt_k
        refine ⟨r_j, h_per_j, ?_, h_P_j⟩
        have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne : (acc.set k r)[j]! = acc[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc k j r h_ne
        have : (acc.set k r).val[j]! = acc.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show (acc.set k r).val[j]! = r_j
        rw [this]; exact h_acc_j
      · subst hj_eq_k
        refine ⟨r, ?_, ?_, ?_⟩
        · have h_eq : acc.val[k.val]! = input_lhs.val[k.val]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_8
          rw [← h_eq]; exact h_per_eq
        · have h_lt'' : k.val < acc.length := by rw [h_acc_len]; exact hk_8
          have h_set_eq : (acc.set k r)[k.val]! = r :=
            Aeneas.Std.Array.getElem!_Nat_set_eq acc k k.val r ⟨rfl, h_lt''⟩
          have : (acc.set k r).val[k.val]! = r := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
          show (acc.set k r).val[k.val]! = r
          exact this
        · have h_eq : acc.val[k.val]! = input_lhs.val[k.val]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_8
          rw [← h_eq]; exact h_per_P
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne : (acc.set k r)[j]! = acc[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc k j r h_ne
      have : (acc.set k r).val[j]! = acc.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.set k r).val[j]! = input_lhs.val[j]!
      rw [this]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch.
    have hk_ge : k.val ≥ (8#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 8 := by rw [h_8] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k 8#usize hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
                  CoeffArray))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize acc i
            let i2 ← Aeneas.Std.Array.index_usize input_rhs.values i
            let i3 ← per_elem i1 i2
            let a1 ← Aeneas.Std.Array.update acc i i3
            ok (cont (iter1, a1)))
        = .ok (done acc) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_pv h_body
    show binary_step_post per_elem P input_lhs input_rhs k (.done acc)
    unfold binary_step_post
    show (binary_loop_inv per_elem P input_lhs input_rhs 8#usize acc).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      apply h_acc_done j
      rw [hk_eq]; rw [h_8] at hj; exact hj
    · intro j hj_ge hj_lt
      apply h_acc_undone j _ hj_lt
      rw [hk_eq]; rw [h_8] at hj_ge; exact hj_ge

/-! ## Top-level binary elementwise spec wrapper -/

set_option maxHeartbeats 2000000 in
theorem elementwise_binary_spec
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Std.I32 → Prop)
    (per_elem_spec :
      ∀ (x y : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x y ⦃ ⇓ r => ⌜ P x y r ⌝ ⦄)
    (input_lhs : CoeffArray)
    (input_rhs : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    ⦃ ⌜ True ⌝ ⦄
    loop (fun p => binary_loop_body per_elem input_rhs p.1 p.2)
      (({ start := 0#usize, «end» := 8#usize }
        : CoreModels.core.ops.range.Range Std.Usize), input_lhs)
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 8 →
              ∃ ri, per_elem (input_lhs.val[i]!) (input_rhs.values.val[i]!) = .ok ri
                    ∧ r.val[i]! = ri
                    ∧ P (input_lhs.val[i]!) (input_rhs.values.val[i]!) ri ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, vec1) => binary_loop_body per_elem input_rhs iter1 vec1)
      input_lhs 0#usize 8#usize
      (binary_loop_inv per_elem P input_lhs input_rhs)
      (by decide : (0#usize : Std.Usize).val ≤ (8#usize : Std.Usize).val)
      (pure_prop_holds_pv ⟨
        fun j hj => by
          have h0 : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds_pv h
    intro j hj
    apply h_done j
    show j < (8#usize : Std.Usize).val
    exact hj
  · intro acc k h_ge h_le hinv
    have h_step :=
      elementwise_binary_step per_elem P per_elem_spec input_lhs input_rhs acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : binary_step_post per_elem P input_lhs input_rhs k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [binary_step_post] using hP
    · have hP : binary_step_post per_elem P input_lhs input_rhs k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [binary_step_post] using hP


end libcrux_iot_ml_dsa.Util.LoopHelper
