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

/-! ## Dual-output loop body (canonical shape from Funs.lean).

The accumulator is `CoeffArray × Coefficients` — the loop carries `(iter, a1, b1)`
where `a1 : CoeffArray` is the LOW-output array and `b1 : Coefficients` is the
HIGH-output struct (its `.values` array is the scratch buffer written lane by lane).
The per-element op has type `I32 → Result (I32 × I32)`; the body reads `a[i]`, applies
`per_elem`, writes the first component to `a[i]` and the second to `b.values[i]`.
This matches `simd.portable.arithmetic.power2round_loop.body` (`power2round`/`decompose`/
`use_hint` are the dual-output rounding ops). -/

def dual_output_loop_body
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (iter : CoreModels.core.ops.range.Range Std.Usize)
    (a : CoeffArray)
    (b : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    Result (ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
        × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
      (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)) := do
  let (o, iter1) ←
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | core.option.Option.None => ok (done (a, b))
  | core.option.Option.Some i =>
    let i1 ← Aeneas.Std.Array.index_usize a i
    let (i2, i3) ← per_elem i1
    let a1 ← Aeneas.Std.Array.update a i i2
    let b2 ← Aeneas.Std.Array.update b.values i i3
    ok (cont (iter1, a1, { values := b2 }))

/-- 3-conjunct dual-output invariant:
    - For `j < k`: `a[j]` is the first per-elem output, `b.values[j]` the second,
      and the per-elem predicate `P` holds; both arrays are written.
    - For `k ≤ j < 8`: `a[j] = input[j]` (the LOW array's tail is still the input).
    The `b` tail (`j ≥ k`) is unconstrained: the top-level consumer only reads `j < 8`
    after the loop finishes (all lanes written). -/
def dual_output_loop_inv
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (P : Std.I32 → (Std.I32 × Std.I32) → Prop)
    (input : CoeffArray) :
    Std.Usize → (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) →
      Result Prop :=
  fun k ab => pure (
    (∀ j : Nat, j < k.val →
      ∃ p, per_elem (input.val[j]!) = .ok p
            ∧ ab.1.val[j]! = p.1
            ∧ ab.2.values.val[j]! = p.2
            ∧ P (input.val[j]!) p)
    ∧ (∀ j : Nat, k.val ≤ j → j < 8 →
        ab.1.val[j]! = input.val[j]!))

/-- Per-iteration post for `dual_output_loop_body`. -/
def dual_output_step_post
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (P : Std.I32 → (Std.I32 × Std.I32) → Prop)
    (input : CoeffArray)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
        × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
      (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (8#usize : Std.Usize).val ∧ iter'.«end» = 8#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (dual_output_loop_inv per_elem P input iter'.start acc').holds
  | .done y => (dual_output_loop_inv per_elem P input 8#usize y).holds

set_option maxHeartbeats 4000000 in
theorem elementwise_dual_output_step
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (P : Std.I32 → (Std.I32 × Std.I32) → Prop)
    (per_elem_spec :
      ∀ (x : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x ⦃ ⇓ r => ⌜ P x r ⌝ ⦄)
    (input : CoeffArray)
    (acc : CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (k : Std.Usize)
    (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_inv : (dual_output_loop_inv per_elem P input k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    dual_output_loop_body per_elem { start := k, «end» := 8#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ dual_output_step_post per_elem P input k r ⌝ ⦄ := by
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_pv h_inv
  obtain ⟨a, b⟩ := acc
  have h_a_len : a.length = 8 := CoeffArray_length a
  have h_b_len : b.values.length = 8 := Coefficients_values_length b
  have h_8 : (8#usize : Std.Usize).val = 8 := rfl
  unfold dual_output_loop_body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- Some i = k branch.
    have hk_8 : k.val < 8 := by rw [h_8] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 8#usize h_lt
    have h_idx :
        Aeneas.Std.Array.index_usize a k = .ok (a.val[k.val]!) :=
      array_index_usize_ok_eq a k (by rw [h_a_len]; exact hk_8)
    obtain ⟨p, h_per_eq, h_per_P⟩ :=
      triple_exists_ok_pv (per_elem_spec (a.val[k.val]!))
    have h_upd_a :
        Aeneas.Std.Array.update a k p.1 = .ok (a.set k p.1) :=
      array_update_ok_eq a k p.1 (by rw [h_a_len]; exact hk_8)
    have h_upd_b :
        Aeneas.Std.Array.update b.values k p.2 = .ok (b.values.set k p.2) :=
      array_update_ok_eq b.values k p.2 (by rw [h_b_len]; exact hk_8)
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done (a, b)) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
                    × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
                  (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize a i
            let (i2, i3) ← per_elem i1
            let a1 ← Aeneas.Std.Array.update a i i2
            let b2 ← Aeneas.Std.Array.update b.values i i3
            ok (cont (iter1, a1, { values := b2 })))
        = .ok (cont
            (({ start := s, «end» := 8#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
             a.set k p.1, { values := b.values.set k p.2 })) := by
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
      rw [h_upd_a]
      simp only [bind_tc_ok]
      rw [h_upd_b]
      rfl
    apply triple_of_ok_pv h_body
    show dual_output_step_post per_elem P input k
            (.cont (({ start := s, «end» := 8#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    a.set k p.1, { values := b.values.set k p.2 }))
    unfold dual_output_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (dual_output_loop_inv per_elem P input s
            (a.set k p.1, { values := b.values.set k p.2 })).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · obtain ⟨p_j, h_per_j, h_a_j, h_b_j, h_P_j⟩ := h_acc_done j hj_lt_k
        refine ⟨p_j, h_per_j, ?_, ?_, h_P_j⟩
        · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne : (a.set k p.1)[j]! = a[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a k j p.1 h_ne
          have : (a.set k p.1).val[j]! = a.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
          show (a.set k p.1).val[j]! = p_j.1
          rw [this]; exact h_a_j
        · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne : (b.values.set k p.2)[j]! = b.values[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne b.values k j p.2 h_ne
          have : (b.values.set k p.2).val[j]! = b.values.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
          show (b.values.set k p.2).val[j]! = p_j.2
          rw [this]; exact h_b_j
      · subst hj_eq_k
        refine ⟨p, ?_, ?_, ?_, ?_⟩
        · have h_eq : a.val[k.val]! = input.val[k.val]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_8
          rw [← h_eq]; exact h_per_eq
        · have h_lt'' : k.val < a.length := by rw [h_a_len]; exact hk_8
          have h_set_eq : (a.set k p.1)[k.val]! = p.1 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val p.1 ⟨rfl, h_lt''⟩
          have : (a.set k p.1).val[k.val]! = p.1 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
          show (a.set k p.1).val[k.val]! = p.1
          exact this
        · have h_lt'' : k.val < b.values.length := by rw [h_b_len]; exact hk_8
          have h_set_eq : (b.values.set k p.2)[k.val]! = p.2 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq b.values k k.val p.2 ⟨rfl, h_lt''⟩
          have : (b.values.set k p.2).val[k.val]! = p.2 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
          show (b.values.set k p.2).val[k.val]! = p.2
          exact this
        · have h_eq : a.val[k.val]! = input.val[k.val]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_8
          rw [← h_eq]; exact h_per_P
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne : (a.set k p.1)[j]! = a[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne a k j p.1 h_ne
      have : (a.set k p.1).val[j]! = a.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (a.set k p.1).val[j]! = input.val[j]!
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
              (Result.ok (ControlFlow.done (a, b)) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
                    × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
                  (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize a i
            let (i2, i3) ← per_elem i1
            let a1 ← Aeneas.Std.Array.update a i i2
            let b2 ← Aeneas.Std.Array.update b.values i i3
            ok (cont (iter1, a1, { values := b2 })))
        = .ok (done (a, b)) := by
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
    show dual_output_step_post per_elem P input k (.done (a, b))
    unfold dual_output_step_post
    show (dual_output_loop_inv per_elem P input 8#usize (a, b)).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      apply h_acc_done j
      rw [hk_eq]; rw [h_8] at hj; exact hj
    · intro j hj_ge hj_lt
      apply h_acc_undone j _ hj_lt
      rw [hk_eq]; rw [h_8] at hj_ge; exact hj_ge

/-! ## Top-level dual-output elementwise spec wrapper -/

set_option maxHeartbeats 2000000 in
theorem elementwise_dual_output_spec
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (P : Std.I32 → (Std.I32 × Std.I32) → Prop)
    (per_elem_spec :
      ∀ (x : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x ⦃ ⇓ r => ⌜ P x r ⌝ ⦄)
    (input : CoeffArray)
    (binput : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    ⦃ ⌜ True ⌝ ⦄
    loop (fun p => dual_output_loop_body per_elem p.1 p.2.1 p.2.2)
      (({ start := 0#usize, «end» := 8#usize }
        : CoreModels.core.ops.range.Range Std.Usize), input, binput)
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 8 →
              ∃ pi, per_elem (input.val[i]!) = .ok pi
                    ∧ r.1.val[i]! = pi.1
                    ∧ r.2.values.val[i]! = pi.2
                    ∧ P (input.val[i]!) pi ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun p => dual_output_loop_body per_elem p.1 p.2.1 p.2.2)
      (input, binput) 0#usize 8#usize
      (dual_output_loop_inv per_elem P input)
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
      elementwise_dual_output_step per_elem P per_elem_spec input acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : dual_output_step_post per_elem P input k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [dual_output_step_post] using hP
    · have hP : dual_output_step_post per_elem P input k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [dual_output_step_post] using hP


/-! ## Read-source-separate dual-output loop body (canonical shape from Funs.lean).

The accumulator is `CoeffArray × Coefficients` — the loop carries `(iter, a1, b1)` where
`a1 : CoeffArray` is the LOW-output array and `b1 : Coefficients` is the HIGH-output struct.
The structural delta vs. `dual_output_loop_body`: the **read source** `src : CoeffArray` is a
SEPARATE read-only argument (NOT the accumulator `a`). The body reads `src.val[i]`, applies
`per_elem`, writes the first component to `a[i]` and the second to `b.values[i]`. This matches
`simd.portable.arithmetic.decompose_loop.body`, which reads `simd_unit.values[i]` (the input
coefficients, untouched) while writing into the LOW array `a` and the HIGH struct `b`.

Because reads come from `src` (never `a`), the invariant needs NO `a`-tail conjunct: only the
written prefix `j < k` is constrained on `a`/`b`. -/

def src_dual_output_loop_body
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (src : CoeffArray)
    (iter : CoreModels.core.ops.range.Range Std.Usize)
    (a : CoeffArray)
    (b : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    Result (ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
        × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
      (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)) := do
  let (o, iter1) ←
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | core.option.Option.None => ok (done (a, b))
  | core.option.Option.Some i =>
    let i1 ← Aeneas.Std.Array.index_usize src i
    let (i2, i3) ← per_elem i1
    let a1 ← Aeneas.Std.Array.update a i i2
    let b2 ← Aeneas.Std.Array.update b.values i i3
    ok (cont (iter1, a1, { values := b2 }))

/-- 1-conjunct read-source invariant:
    - For `j < k`: `a[j]` is the first per-elem output of `src[j]`, `b.values[j]` the second,
      and the per-elem predicate `P (src[j])` holds.
    No tail constraint is needed: reads come from the read-only `src`, and the top-level
    consumer only reads `j < 8` after all lanes have been written. -/
def src_dual_output_loop_inv
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (P : Std.I32 → (Std.I32 × Std.I32) → Prop)
    (src : CoeffArray) :
    Std.Usize → (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) →
      Result Prop :=
  fun k ab => pure (
    ∀ j : Nat, j < k.val →
      ∃ p, per_elem (src.val[j]!) = .ok p
            ∧ ab.1.val[j]! = p.1
            ∧ ab.2.values.val[j]! = p.2
            ∧ P (src.val[j]!) p)

/-- Per-iteration post for `src_dual_output_loop_body`. -/
def src_dual_output_step_post
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (P : Std.I32 → (Std.I32 × Std.I32) → Prop)
    (src : CoeffArray)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
        × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
      (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (8#usize : Std.Usize).val ∧ iter'.«end» = 8#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (src_dual_output_loop_inv per_elem P src iter'.start acc').holds
  | .done y => (src_dual_output_loop_inv per_elem P src 8#usize y).holds

set_option maxHeartbeats 4000000 in
theorem elementwise_src_dual_output_step
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (P : Std.I32 → (Std.I32 × Std.I32) → Prop)
    (per_elem_spec :
      ∀ (x : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x ⦃ ⇓ r => ⌜ P x r ⌝ ⦄)
    (src : CoeffArray)
    (acc : CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (k : Std.Usize)
    (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_inv : (src_dual_output_loop_inv per_elem P src k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    src_dual_output_loop_body per_elem src { start := k, «end» := 8#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ src_dual_output_step_post per_elem P src k r ⌝ ⦄ := by
  have h_acc_done := of_pure_prop_holds_pv h_inv
  obtain ⟨a, b⟩ := acc
  have h_a_len : a.length = 8 := CoeffArray_length a
  have h_b_len : b.values.length = 8 := Coefficients_values_length b
  have h_src_len : src.length = 8 := CoeffArray_length src
  have h_8 : (8#usize : Std.Usize).val = 8 := rfl
  unfold src_dual_output_loop_body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- Some i = k branch.
    have hk_8 : k.val < 8 := by rw [h_8] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 8#usize h_lt
    have h_idx :
        Aeneas.Std.Array.index_usize src k = .ok (src.val[k.val]!) :=
      array_index_usize_ok_eq src k (by rw [h_src_len]; exact hk_8)
    obtain ⟨p, h_per_eq, h_per_P⟩ :=
      triple_exists_ok_pv (per_elem_spec (src.val[k.val]!))
    have h_upd_a :
        Aeneas.Std.Array.update a k p.1 = .ok (a.set k p.1) :=
      array_update_ok_eq a k p.1 (by rw [h_a_len]; exact hk_8)
    have h_upd_b :
        Aeneas.Std.Array.update b.values k p.2 = .ok (b.values.set k p.2) :=
      array_update_ok_eq b.values k p.2 (by rw [h_b_len]; exact hk_8)
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done (a, b)) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
                    × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
                  (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize src i
            let (i2, i3) ← per_elem i1
            let a1 ← Aeneas.Std.Array.update a i i2
            let b2 ← Aeneas.Std.Array.update b.values i i3
            ok (cont (iter1, a1, { values := b2 })))
        = .ok (cont
            (({ start := s, «end» := 8#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
             a.set k p.1, { values := b.values.set k p.2 })) := by
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
      rw [h_upd_a]
      simp only [bind_tc_ok]
      rw [h_upd_b]
      rfl
    apply triple_of_ok_pv h_body
    show src_dual_output_step_post per_elem P src k
            (.cont (({ start := s, «end» := 8#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    a.set k p.1, { values := b.values.set k p.2 }))
    unfold src_dual_output_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (src_dual_output_loop_inv per_elem P src s
            (a.set k p.1, { values := b.values.set k p.2 })).holds
    apply pure_prop_holds_pv
    intro j hj
    rw [hs_val] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
    · obtain ⟨p_j, h_per_j, h_a_j, h_b_j, h_P_j⟩ := h_acc_done j hj_lt_k
      refine ⟨p_j, h_per_j, ?_, ?_, h_P_j⟩
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne : (a.set k p.1)[j]! = a[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a k j p.1 h_ne
        have : (a.set k p.1).val[j]! = a.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show (a.set k p.1).val[j]! = p_j.1
        rw [this]; exact h_a_j
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne : (b.values.set k p.2)[j]! = b.values[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne b.values k j p.2 h_ne
        have : (b.values.set k p.2).val[j]! = b.values.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show (b.values.set k p.2).val[j]! = p_j.2
        rw [this]; exact h_b_j
    · subst hj_eq_k
      refine ⟨p, h_per_eq, ?_, ?_, h_per_P⟩
      · have h_lt'' : k.val < a.length := by rw [h_a_len]; exact hk_8
        have h_set_eq : (a.set k p.1)[k.val]! = p.1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val p.1 ⟨rfl, h_lt''⟩
        have : (a.set k p.1).val[k.val]! = p.1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show (a.set k p.1).val[k.val]! = p.1
        exact this
      · have h_lt'' : k.val < b.values.length := by rw [h_b_len]; exact hk_8
        have h_set_eq : (b.values.set k p.2)[k.val]! = p.2 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq b.values k k.val p.2 ⟨rfl, h_lt''⟩
        have : (b.values.set k p.2).val[k.val]! = p.2 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show (b.values.set k p.2).val[k.val]! = p.2
        exact this
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
              (Result.ok (ControlFlow.done (a, b)) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
                    × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
                  (CoeffArray × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize src i
            let (i2, i3) ← per_elem i1
            let a1 ← Aeneas.Std.Array.update a i i2
            let b2 ← Aeneas.Std.Array.update b.values i i3
            ok (cont (iter1, a1, { values := b2 })))
        = .ok (done (a, b)) := by
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
    show src_dual_output_step_post per_elem P src k (.done (a, b))
    unfold src_dual_output_step_post
    show (src_dual_output_loop_inv per_elem P src 8#usize (a, b)).holds
    apply pure_prop_holds_pv
    intro j hj
    apply h_acc_done j
    rw [hk_eq]; rw [h_8] at hj; exact hj

/-! ## Top-level read-source-separate dual-output elementwise spec wrapper -/

set_option maxHeartbeats 2000000 in
theorem elementwise_src_dual_output_spec
    (per_elem : Std.I32 → Result (Std.I32 × Std.I32))
    (P : Std.I32 → (Std.I32 × Std.I32) → Prop)
    (per_elem_spec :
      ∀ (x : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x ⦃ ⇓ r => ⌜ P x r ⌝ ⦄)
    (src : CoeffArray)
    (ainput : CoeffArray)
    (binput : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    ⦃ ⌜ True ⌝ ⦄
    loop (fun p => src_dual_output_loop_body per_elem src p.1 p.2.1 p.2.2)
      (({ start := 0#usize, «end» := 8#usize }
        : CoreModels.core.ops.range.Range Std.Usize), ainput, binput)
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 8 →
              ∃ pi, per_elem (src.val[i]!) = .ok pi
                    ∧ r.1.val[i]! = pi.1
                    ∧ r.2.values.val[i]! = pi.2
                    ∧ P (src.val[i]!) pi ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun p => src_dual_output_loop_body per_elem src p.1 p.2.1 p.2.2)
      (ainput, binput) 0#usize 8#usize
      (src_dual_output_loop_inv per_elem P src)
      (by decide : (0#usize : Std.Usize).val ≤ (8#usize : Std.Usize).val)
      (pure_prop_holds_pv (fun j hj => by
        have h0 : (0#usize : Std.Usize).val = 0 := rfl
        rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j)))
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    have h_done := of_pure_prop_holds_pv h
    intro j hj
    apply h_done j
    show j < (8#usize : Std.Usize).val
    exact hj
  · intro acc k h_ge h_le hinv
    have h_step :=
      elementwise_src_dual_output_step per_elem P per_elem_spec src acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : src_dual_output_step_post per_elem P src k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [src_dual_output_step_post] using hP
    · have hP : src_dual_output_step_post per_elem P src k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [src_dual_output_step_post] using hP


/-! ## Two-source single-output loop body (read-only `src` + read+write `acc`).

The structural shape from `simd.portable.arithmetic.use_hint_loop.body`: a SEPARATE read-only
`src : Coefficients` (the input `simd_unit`) plus an accumulator `a : CoeffArray` that is BOTH
read (`a[i]`) and written (`a[i] := per_elem (src.values[i]) (a[i])`). Single output array.

Read order in the impl body: `src.values[i]` FIRST, then `a[i]`, then `per_elem src acc`, then
write. The accumulator starts as `hint.values`, so a lane `j ≥ k` still reads its initial value
(`input.val[j]`), recovering `hint.values[j]`. Hence the 2-conjunct invariant (`< k` written,
`≥ k` untouched) mirrors `unary`/`binary`, with the per-elem op now reading `src.values[j]` and
the running accumulator (whose `≥ k` value is `input.val[j]`). -/

def two_src_single_output_loop_body
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (src : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
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
    let i1 ← Aeneas.Std.Array.index_usize src.values i
    let i3 ← Aeneas.Std.Array.index_usize a i
    let i5 ← per_elem i1 i3
    let a1 ← Aeneas.Std.Array.update a i i5
    ok (cont (iter1, a1))

/-- 2-conjunct invariant:
    - For `j < k`, `a[j]` equals the per-elem-op output `r` for inputs `src.values[j]` and the
      original accumulator value `input[j]` (carrying the per-elem predicate `P`).
    - For `j ≥ k`, `a[j] = input[j]` (the accumulator is untouched there). -/
def two_src_single_output_loop_inv
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Std.I32 → Prop)
    (src : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (input : CoeffArray) :
    Std.Usize → CoeffArray → Result Prop :=
  fun k a => pure (
    (∀ j : Nat, j < k.val →
      ∃ r, per_elem (src.values.val[j]!) (input.val[j]!) = .ok r
            ∧ a.val[j]! = r
            ∧ P (src.values.val[j]!) (input.val[j]!) r)
    ∧ (∀ j : Nat, k.val ≤ j → j < 8 →
        a.val[j]! = input.val[j]!))

/-- Per-iteration post for `two_src_single_output_loop_body`. -/
def two_src_single_output_step_post
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Std.I32 → Prop)
    (src : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (input : CoeffArray)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × CoeffArray)
      CoeffArray) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (8#usize : Std.Usize).val ∧ iter'.«end» = 8#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (two_src_single_output_loop_inv per_elem P src input iter'.start acc').holds
  | .done y => (two_src_single_output_loop_inv per_elem P src input 8#usize y).holds

set_option maxHeartbeats 4000000 in
theorem elementwise_two_src_single_output_step
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Std.I32 → Prop)
    (per_elem_spec :
      ∀ (x y : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x y ⦃ ⇓ r => ⌜ P x y r ⌝ ⦄)
    (src : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (input : CoeffArray)
    (acc : CoeffArray)
    (k : Std.Usize)
    (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_inv : (two_src_single_output_loop_inv per_elem P src input k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    two_src_single_output_loop_body per_elem src { start := k, «end» := 8#usize } acc
    ⦃ ⇓ r => ⌜ two_src_single_output_step_post per_elem P src input k r ⌝ ⦄ := by
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_pv h_inv
  have h_acc_len : acc.length = 8 := CoeffArray_length acc
  have h_src_len : src.values.length = 8 := Coefficients_values_length src
  have h_8 : (8#usize : Std.Usize).val = 8 := rfl
  unfold two_src_single_output_loop_body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- Some i = k branch.
    have hk_8 : k.val < 8 := by rw [h_8] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 8#usize h_lt
    have h_idx_src :
        Aeneas.Std.Array.index_usize src.values k
          = .ok (src.values.val[k.val]!) :=
      array_index_usize_ok_eq src.values k (by rw [h_src_len]; exact hk_8)
    have h_idx_acc :
        Aeneas.Std.Array.index_usize acc k = .ok (acc.val[k.val]!) :=
      array_index_usize_ok_eq acc k (by rw [h_acc_len]; exact hk_8)
    obtain ⟨r, h_per_eq, h_per_P⟩ :=
      triple_exists_ok_pv (per_elem_spec (src.values.val[k.val]!)
                                          (acc.val[k.val]!))
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
            let i1 ← Aeneas.Std.Array.index_usize src.values i
            let i3 ← Aeneas.Std.Array.index_usize acc i
            let i5 ← per_elem i1 i3
            let a1 ← Aeneas.Std.Array.update acc i i5
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
      rw [h_idx_src]
      simp only [bind_tc_ok]
      rw [h_idx_acc]
      simp only [bind_tc_ok]
      rw [h_per_eq]
      simp only [bind_tc_ok]
      rw [h_upd]
      rfl
    apply triple_of_ok_pv h_body
    show two_src_single_output_step_post per_elem P src input k
            (.cont (({ start := s, «end» := 8#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    acc.set k r))
    unfold two_src_single_output_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (two_src_single_output_loop_inv per_elem P src input s (acc.set k r)).holds
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
            let i1 ← Aeneas.Std.Array.index_usize src.values i
            let i3 ← Aeneas.Std.Array.index_usize acc i
            let i5 ← per_elem i1 i3
            let a1 ← Aeneas.Std.Array.update acc i i5
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
    show two_src_single_output_step_post per_elem P src input k (.done acc)
    unfold two_src_single_output_step_post
    show (two_src_single_output_loop_inv per_elem P src input 8#usize acc).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      apply h_acc_done j
      rw [hk_eq]; rw [h_8] at hj; exact hj
    · intro j hj_ge hj_lt
      apply h_acc_undone j _ hj_lt
      rw [hk_eq]; rw [h_8] at hj_ge; exact hj_ge

/-! ## Top-level two-source single-output elementwise spec wrapper -/

set_option maxHeartbeats 2000000 in
theorem elementwise_two_src_single_output_spec
    (per_elem : Std.I32 → Std.I32 → Result Std.I32)
    (P : Std.I32 → Std.I32 → Std.I32 → Prop)
    (per_elem_spec :
      ∀ (x y : Std.I32),
        ⦃ ⌜ True ⌝ ⦄ per_elem x y ⦃ ⇓ r => ⌜ P x y r ⌝ ⦄)
    (src : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (input : CoeffArray) :
    ⦃ ⌜ True ⌝ ⦄
    loop (fun p => two_src_single_output_loop_body per_elem src p.1 p.2)
      (({ start := 0#usize, «end» := 8#usize }
        : CoreModels.core.ops.range.Range Std.Usize), input)
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 8 →
              ∃ ri, per_elem (src.values.val[i]!) (input.val[i]!) = .ok ri
                    ∧ r.val[i]! = ri
                    ∧ P (src.values.val[i]!) (input.val[i]!) ri ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, vec1) => two_src_single_output_loop_body per_elem src iter1 vec1)
      input 0#usize 8#usize
      (two_src_single_output_loop_inv per_elem P src input)
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
      elementwise_two_src_single_output_step per_elem P per_elem_spec src input acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : two_src_single_output_step_post per_elem P src input k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [two_src_single_output_step_post] using hP
    · have hP : two_src_single_output_step_post per_elem P src input k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [two_src_single_output_step_post] using hP

end libcrux_iot_ml_dsa.Util.LoopHelper
