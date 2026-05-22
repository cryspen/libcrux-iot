/-
  # `Equivalence/L1_VectorElementOps.lean` — Layer 1 elementwise PortableVector Triples.

  Layer-1 Triples for the per-element-of-PortableVector ops. Each L1.x
  Triple proves that running the loop produces an output vector where
  every element satisfies the corresponding L0.x per-element post:

  - **L1.3 `barrett_reduce_spec`** — instantiates `elementwise_unary_spec`
    with `barrett_reduce_element_spec` from L0.2.

  L1.1-L1.10 will follow the same pattern (instantiate the per-element
  L0.x Triple via `elementwise_unary_spec`).
-/
import LibcruxIotMlKem.Util.PortableVector
import LibcruxIotMlKem.Equivalence.L0_FieldArith

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Equivalence

open Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Util

/-! ## L1.3 — `barrett_reduce_spec`

    Implements the upstream `Vector.Portable.Arithmetic.barrett_reduce`
    correctness theorem (Plan.lean § "L1.3"). The impl is a 16-iteration
    `for i in 0..16` loop that calls L0.2 `barrett_reduce_element` on each
    element. The post asserts each output element is congruent to its
    input mod 3329 and bounded in absolute value by 3328.

    F* pre: `∀ i < 16, is_i16b 28296 vec.elements[i]`
    F* post: `∀ i < 16, is_i16b 3328 r.elements[i]
                     ∧ v r.elements[i] % 3329 = v vec.elements[i] % 3329` -/

/-- Per-element predicate threading the L0.2 bound precondition into
    an implication. -/
private def barrett_per_elem_P (x y : Std.I16) : Prop :=
  x.val.natAbs ≤ 28296 →
    libcrux_iot_ml_kem.Util.modq_eq y.val x.val 3329
      ∧ y.val.natAbs ≤ 3328

/-- Per-element Triple: an unconditional Triple over
    `barrett_reduce_element` with the guarded post. The function is
    total (see `barrett_reduce_element_eq_ok`); the in-bounds case
    invokes the L0.2 `barrett_reduce_element_spec`. -/
private theorem barrett_per_elem_spec (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element x
    ⦃ ⇓ r => ⌜ barrett_per_elem_P x r ⌝ ⦄ := by
  -- The function is total: it returns `.ok (barrett_reduce_impl_value x)`
  -- unconditionally (`barrett_reduce_element_eq_ok`). Reduce the Triple
  -- to a pure goal via that .ok equation.
  have h_ok := barrett_reduce_element_eq_ok x
  rw [show libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element x
        = .ok (barrett_reduce_impl_value x) from h_ok]
  -- Triple shape: ⦃True⦄ .ok v ⦃⇓ r => ⌜barrett_per_elem_P x r⌝⦄.
  simp only [Std.Do.Triple, WP.wp]
  intro _
  -- Goal: barrett_per_elem_P x (barrett_reduce_impl_value x)
  show barrett_per_elem_P x (barrett_reduce_impl_value x)
  unfold barrett_per_elem_P
  intro hb
  -- Now use the L0.2 spec.
  have hT := barrett_reduce_element_spec x hb
  -- hT : ⦃True⦄ barrett_reduce_element x ⦃⇓ r => ⌜...⌝⦄
  -- Reduce to the .ok form via h_ok.
  rw [h_ok] at hT
  -- hT : ⦃True⦄ .ok (barrett_reduce_impl_value x) ⦃⇓ r => ⌜...⌝⦄
  -- Extract the post-condition.
  simp only [Std.Do.Triple, WP.wp] at hT
  exact hT trivial

@[spec]
theorem barrett_reduce_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bounds : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 28296) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              libcrux_iot_ml_kem.Util.modq_eq
                (r.elements.val[i]!).val (vec.elements.val[i]!).val 3329
              ∧ (r.elements.val[i]!).val.natAbs ≤ 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Replace `barrett_reduce_loop.body` with `unary_loop_body
  -- barrett_reduce_element`. Both have identical definitions modulo
  -- the per_elem variable, so funext is trivial.
  have h_body_eq :
      (fun (p : (core_models.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_loop.body p.1 p.2)
      = (fun (p : (core_models.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body
          libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_loop.body
    unfold unary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element
      barrett_per_elem_P
      barrett_per_elem_spec
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  -- hh : ∀ i < 16, ∃ ri, barrett_reduce_element (vec[i]) = .ok ri
  --        ∧ r.elements[i]! = ri ∧ barrett_per_elem_P (vec[i]) ri
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P (h_bounds j hj)

end libcrux_iot_ml_kem.Equivalence
