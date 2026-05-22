/-
  # `Util/PortableVector.lean` — Layer-1 elementwise loop infrastructure

  The L1 family (`barrett_reduce`, `montgomery_reduce`,
  `montgomery_multiply_by_constant`, `negate`, …) all share the same
  shape: a Rust `for i in 0..16 { ... }` loop that reads
  `vec.elements[i]`, runs a per-element field-arithmetic primitive (an
  L0.x Triple), and writes back to `acc.elements[i]`.

  This module gives a reusable infrastructure layer:

  - `unary_loop_inv` — canonical 2-conjunct loop invariant.
  - `unary_loop_body` — canonical body shape (matches every
    `vector.portable.arithmetic.<unary>_loop.body` from Funs.lean).
  - `elementwise_unary_step` — per-iteration step lemma.
  - `elementwise_unary_spec` — top-level wrapper that invokes
    `loop_range_spec_usize`. Each L1.x unary op closes via
    `apply elementwise_unary_spec` + supplying the per-element
    `@[spec]` as a `per_elem_spec` hypothesis.

  Binary ops (`add`, `sub`) get analogous `binary_loop_*` lemmas
  when L1.1/L1.2 land.

  Proof strategy: turn each component of the body
  (`IteratorRange.next`, `Array.index_usize`, `per_elem`,
  `Array.update`) into a `Result` equation, compose them into a
  single body equation, then close via `triple_of_ok_pv`. This is
  the cleanest substitute for `mvcgen` when the surrounding spec is
  generic in `per_elem` (so mvcgen has no `@[spec]` to register).
-/
import LibcruxIotMlKem.Util.LoopSpecs
import LibcruxIotMlKem.Extraction.Funs

open Aeneas Aeneas.Std Result ControlFlow Std.Do

namespace libcrux_iot_ml_kem.Util

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## `FIELD_ELEMENTS_IN_VECTOR` numerical reduction -/

theorem field_elements_in_vector_val :
    (libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR : Std.Usize).val = 16 := by
  unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl

/-! ## Length-of-elements bridge -/

@[simp]
theorem PortableVector_elements_length
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    v.elements.length = 16 := by
  have := v.elements.property
  show v.elements.val.length = 16
  exact this

/-! ## Local helpers — Triple ↔ Result.ok bridges, pure-prop holds. -/

section pv_helpers

private theorem triple_of_ok_pv
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Triple, WP.wp, hp]

private theorem triple_exists_ok_pv
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Triple, WP.wp] using h)⟩
  | .fail _ => exact absurd h (by simp [Triple, WP.wp])
  | .div => exact absurd h (by simp [Triple, WP.wp])

private theorem pure_prop_holds_pv {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_pv {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Triple, WP.wp] at h; exact h trivial

end pv_helpers

/-! ## Iterator-next reduction to a `Result` equation. -/

/-- `i.val < 16`: `IteratorRange.next` returns `.ok (some i, iter')` with
    `iter'.end = 16` and `iter'.start.val = i.val + 1`. We avoid pinning
    `iter'.start`'s exact UScalar form by stating the post existentially. -/
theorem iter_next_some_eq (i : Std.Usize) (h_lt : i.val < (16#usize : Std.Usize).val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      core_models.iter.range.IteratorRange.next
        core_models.Usize.Insts.Core_modelsIterRangeStep
        ({ start := i, «end» := 16#usize } : core_models.ops.range.Range Std.Usize)
      = .ok (some i,
          ({ start := s, «end» := 16#usize } : core_models.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i 16#usize
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      ∃ s : Std.Usize, s.val = i.val + 1
        ∧ oi = (some i,
                ({ start := s, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize)) ⌝)
    (fun _ s hs => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      exact ⟨s, hs, rfl⟩)
    (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_pv hT
  obtain ⟨s, hs_val, hpair⟩ := hP
  exact ⟨s, hs_val, by rw [hveq, hpair]⟩

/-- `i.val ≥ 16`: `IteratorRange.next` returns `.ok (none, _)`. -/
theorem iter_next_none_eq (i : Std.Usize) (h_ge : i.val ≥ (16#usize : Std.Usize).val) :
    core_models.iter.range.IteratorRange.next
      core_models.Usize.Insts.Core_modelsIterRangeStep
      ({ start := i, «end» := 16#usize } : core_models.ops.range.Range Std.Usize)
    = .ok ((none : Option Std.Usize),
            ({ start := i, «end» := 16#usize }
              : core_models.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i 16#usize
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      oi = ((none : Option Std.Usize),
            ({ start := i, «end» := 16#usize }
              : core_models.ops.range.Range Std.Usize)) ⌝)
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
  rw [hveq, hPv']

theorem array_update_ok_eq
    {α : Type u} {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (x : α) (h_bd : i.val < v.length) :
    Aeneas.Std.Array.update v i x = .ok (v.set i x) := by
  have hT := Aeneas.Std.Array.update_spec v i x h_bd
  have h_ex := Aeneas.Std.WP.spec_imp_exists hT
  obtain ⟨v', hveq, hPv'⟩ := h_ex
  rw [hveq, hPv']

/-! ## Unary loop invariant -/

/-- 2-conjunct invariant:
    - For `j < k`, `acc.elements[j]` equals the per-elem-op output `r`
      for input `input.elements[j]` (carrying the per-elem predicate
      `P` that the L0.x `@[spec]` produces).
    - For `j ≥ k`, `acc.elements[j] = input.elements[j]`. -/
def unary_loop_inv
    (per_elem : Std.I16 → Result Std.I16)
    (P : Std.I16 → Std.I16 → Prop)
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize →
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector →
    Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      ∃ r, per_elem (input.elements.val[j]!) = .ok r
            ∧ acc.elements.val[j]! = r ∧ P (input.elements.val[j]!) r)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.elements.val[j]! = input.elements.val[j]!))

/-! ## Unary loop body (canonical shape from Funs.lean) -/

def unary_loop_body
    (per_elem : Std.I16 → Result Std.I16)
    (iter : core_models.ops.range.Range Std.Usize)
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Result (ControlFlow
      ((core_models.ops.range.Range Std.Usize)
        × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) := do
  let (o, iter1) ←
    core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
      core_models.Usize.Insts.Core_modelsIterRangeStep iter
  match o with
  | core_models.option.Option.None => ok (done vec)
  | core_models.option.Option.Some i =>
    let i1 ← Aeneas.Std.Array.index_usize vec.elements i
    let vi ← per_elem i1
    let a ← Aeneas.Std.Array.update vec.elements i vi
    ok (cont (iter1, { elements := a }))

/-! ## Step lemma — reduces the body to a `Result` equation and closes via `triple_of_ok_pv`.

The step lemma's post is stated via a top-level `def` rather than an inline
`match`. Reason: an inline `match` in two different declarations (the step
lemma here and the `loop_range_spec_usize` step hypothesis at the call site)
generates *distinct* `match_N` auxiliary constants. Even though the matches
have identical bodies, the kernel sees the constants as different and rejects
the unification. A named `def` is referenced by the same canonical constant
from both sites. -/

/-- Per-iteration post for `unary_loop_body`. Identical shape to the
    `loop_range_spec_usize` step hypothesis. -/
def unary_step_post
    (per_elem : Std.I16 → Result Std.I16)
    (P : Std.I16 → Std.I16 → Prop)
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((core_models.ops.range.Range Std.Usize)
        × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (unary_loop_inv per_elem P input iter'.start acc').holds
  | .done y => (unary_loop_inv per_elem P input 16#usize y).holds

set_option maxHeartbeats 4000000 in
theorem elementwise_unary_step
    (per_elem : Std.I16 → Result Std.I16)
    (P : Std.I16 → Std.I16 → Prop)
    (per_elem_spec :
      ∀ (x : Std.I16),
        ⦃ ⌜ True ⌝ ⦄ per_elem x ⦃ ⇓ r => ⌜ P x r ⌝ ⦄)
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (acc : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (unary_loop_inv per_elem P input k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    unary_loop_body per_elem { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ unary_step_post per_elem P input k r ⌝ ⦄ := by
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_pv h_inv
  have h_acc_len : acc.elements.length = 16 := PortableVector_elements_length acc
  have h_16 : (16#usize : Std.Usize).val = 16 := rfl
  unfold unary_loop_body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some i = k branch.
    have hk_16 : k.val < 16 := by rw [h_16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    have h_idx :
        Aeneas.Std.Array.index_usize acc.elements k = .ok (acc.elements.val[k.val]!) :=
      array_index_usize_ok_eq acc.elements k (by rw [h_acc_len]; exact hk_16)
    obtain ⟨r, h_per_eq, h_per_P⟩ :=
      triple_exists_ok_pv (per_elem_spec (acc.elements.val[k.val]!))
    have h_upd :
        Aeneas.Std.Array.update acc.elements k r
        = .ok (acc.elements.set k r) :=
      array_update_ok_eq acc.elements k r (by rw [h_acc_len]; exact hk_16)
    have h_body :
        (do
          let (o, iter1) ←
            core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize)
          match o with
          | core_models.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((core_models.ops.range.Range Std.Usize)
                    × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
          | core_models.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize acc.elements i
            let vi ← per_elem i1
            let a ← Aeneas.Std.Array.update acc.elements i vi
            ok (cont (iter1, { elements := a })))
        = .ok (cont
            (({ start := s, «end» := 16#usize }
                : core_models.ops.range.Range Std.Usize),
             { elements := acc.elements.set k r })) := by
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
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
            (.cont (({ start := s, «end» := 16#usize }
                       : core_models.ops.range.Range Std.Usize),
                    { elements := acc.elements.set k r }))
    unfold unary_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (unary_loop_inv per_elem P input s
            { elements := acc.elements.set k r }).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · obtain ⟨r_j, h_per_j, h_acc_j, h_P_j⟩ := h_acc_done j hj_lt_k
        refine ⟨r_j, h_per_j, ?_, h_P_j⟩
        have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne : (acc.elements.set k r)[j]! = (acc.elements)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.elements k j r h_ne
        have : (acc.elements.set k r).val[j]! = acc.elements.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show (acc.elements.set k r).val[j]! = r_j
        rw [this]; exact h_acc_j
      · subst hj_eq_k
        refine ⟨r, ?_, ?_, ?_⟩
        · have h_eq : acc.elements.val[k.val]! = input.elements.val[k.val]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_16
          rw [← h_eq]; exact h_per_eq
        · have h_lt'' : k.val < acc.elements.length := by rw [h_acc_len]; exact hk_16
          have h_set_eq : (acc.elements.set k r)[k.val]! = r :=
            Aeneas.Std.Array.getElem!_Nat_set_eq acc.elements k k.val r ⟨rfl, h_lt''⟩
          have : (acc.elements.set k r).val[k.val]! = r := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
          show (acc.elements.set k r).val[k.val]! = r
          exact this
        · have h_eq : acc.elements.val[k.val]! = input.elements.val[k.val]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_16
          rw [← h_eq]; exact h_per_P
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne : (acc.elements.set k r)[j]! = (acc.elements)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.elements k j r h_ne
      have : (acc.elements.set k r).val[j]! = acc.elements.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.elements.set k r).val[j]! = input.elements.val[j]!
      rw [this]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h_16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize)
          match o with
          | core_models.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((core_models.ops.range.Range Std.Usize)
                    × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
          | core_models.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize acc.elements i
            let vi ← per_elem i1
            let a ← Aeneas.Std.Array.update acc.elements i vi
            ok (cont (iter1, { elements := a })))
        = .ok (done acc) := by
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_pv h_body
    show unary_step_post per_elem P input k (.done acc)
    unfold unary_step_post
    show (unary_loop_inv per_elem P input 16#usize acc).holds
    apply pure_prop_holds_pv
    refine ⟨?_, ?_⟩
    · intro j hj
      apply h_acc_done j
      rw [hk_eq]; rw [h_16] at hj; exact hj
    · intro j hj_ge hj_lt
      apply h_acc_undone j _ hj_lt
      rw [hk_eq]; rw [h_16] at hj_ge; exact hj_ge

/-! ## Top-level unary elementwise spec wrapper -/

set_option maxHeartbeats 2000000 in
theorem elementwise_unary_spec
    (per_elem : Std.I16 → Result Std.I16)
    (P : Std.I16 → Std.I16 → Prop)
    (per_elem_spec :
      ∀ (x : Std.I16),
        ⦃ ⌜ True ⌝ ⦄ per_elem x ⦃ ⇓ r => ⌜ P x r ⌝ ⦄)
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    loop (fun p => unary_loop_body per_elem p.1 p.2)
      (({ start := 0#usize, «end» := 16#usize }
        : core_models.ops.range.Range Std.Usize), input)
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              ∃ ri, per_elem (input.elements.val[i]!) = .ok ri
                    ∧ r.elements.val[i]! = ri
                    ∧ P (input.elements.val[i]!) ri ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, vec1) => unary_loop_body per_elem iter1 vec1)
      input 0#usize 16#usize
      (unary_loop_inv per_elem P input)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_pv ⟨
        fun j hj => by
          have h0 : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · -- PostCond entailment.
    rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds_pv h
    intro j hj
    apply h_done j
    show j < (16#usize : Std.Usize).val
    exact hj
  · -- Step lemma. We bridge `loop_range_spec_usize`'s inline `match`-based
    -- post with `elementwise_unary_step`'s `unary_step_post`-based post via
    -- a direct Triple weakening: both are propositionally identical on
    -- every result, so a value-level case-split on `r` discharges the
    -- entailment.
    intro acc k h_ge h_le hinv
    have h_step := elementwise_unary_step per_elem P per_elem_spec input acc k h_le hinv
    -- Convert via Triple post-equivalence (`Std.Do.Triple.of_entails_right`).
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    -- hh : ⌜ unary_step_post per_elem P input k r ⌝.down
    -- Goal: (the lambda's match) r.
    rcases r with ⟨iter', acc'⟩ | y
    · -- cont branch.
      have hP : unary_step_post per_elem P input k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [unary_step_post] using hP
    · -- done branch.
      have hP : unary_step_post per_elem P input k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [unary_step_post] using hP

end libcrux_iot_ml_kem.Util
