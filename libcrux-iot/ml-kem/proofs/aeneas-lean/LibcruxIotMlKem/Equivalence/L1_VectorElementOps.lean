/-
  # `Equivalence/L1_VectorElementOps.lean` — Layer 1 elementwise PortableVector Triples.

  Layer-1 Triples for the per-element-of-PortableVector ops. Each L1.x
  Triple proves that running the loop produces an output vector where
  every element satisfies the corresponding L0.x per-element post:

  - **L1.3 `barrett_reduce_spec`** — instantiates `elementwise_unary_spec`
    with `barrett_reduce_element_spec` from L0.2.
  - **L1.4 `montgomery_multiply_by_constant_spec`** — instantiates
    `elementwise_unary_spec` with `montgomery_multiply_fe_by_fer_spec`
    (L0.4), post-processed to expose `(r * 2^16) % 3329 = (x * c) % 3329`.
  - **L1.5 `cond_subtract_3329_spec`** — uses a conditional-body
    variant `elementwise_cond_unary_spec` (the else-branch returns
    the input vec unchanged, so the canonical `unary_loop_body`
    shape doesn't apply).
  - **L1.6 `negate_spec`** — instantiates `elementwise_unary_spec`
    with `core_models.num.I16.wrapping_neg` (per-element `.bv = -x.bv`).

  L1.1, L1.2, L1.7-L1.10 will follow the same pattern (instantiate the
  per-element L0.x Triple via `elementwise_unary_spec` / its
  conditional / binary variants).
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

/-! ## L1.4 — `montgomery_multiply_by_constant_spec`

    The Vector.Portable.Arithmetic.montgomery_multiply_by_constant impl
    is a 16-iteration loop that calls L0.4's `montgomery_multiply_fe_by_fer`
    on each element (the constant `c` is captured by the body lambda).

    Conversion from L0.4's `modq_eq r (fe*c*169) 3329` to L1.4's
    `(r*2^16) % 3329 = (fe*c) % 3329`: multiply both sides by 2^16,
    and use `169 * 65536 ≡ 1 (mod 3329)` (which is the Montgomery
    inversion identity at this q). -/

/-- Per-element predicate (unconditional form): the L0.4 bound +
    the L1.4-shaped Montgomery congruence. -/
private def montgomery_per_elem_P (c x y : Std.I16) : Prop :=
  y.val.natAbs ≤ 3328
    ∧ (y.val * (2 ^ 16 : Int)) % 3329 = (x.val * c.val) % 3329

/-- Per-element Triple: invokes the L0.4 spec under the captured `hc`,
    then weakens the post via the Montgomery-inversion identity
    `169 * 2^16 ≡ 1 (mod 3329)`. -/
private theorem montgomery_per_elem_spec
    (c : Std.I16) (hc : c.val.natAbs ≤ 1664) (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer x c
    ⦃ ⇓ r => ⌜ montgomery_per_elem_P c x r ⌝ ⦄ := by
  -- Invoke L0.4 and weaken its post to the L1.4-shaped form.
  apply Std.Do.Triple.of_entails_right _ (montgomery_multiply_fe_by_fer_spec x c hc)
  rw [PostCond.entails_noThrow]
  intro r hh
  have h_inner : r.val.natAbs ≤ 3328
                  ∧ libcrux_iot_ml_kem.Util.modq_eq r.val (x.val * c.val * 169) 3329 := by
    simpa [Std.Do.SPred.down_pure] using hh
  obtain ⟨h_bd, h_mod⟩ := h_inner
  show montgomery_per_elem_P c x r
  unfold montgomery_per_elem_P
  refine ⟨h_bd, ?_⟩
  -- From `modq_eq r (x * c * 169) 3329`, derive `(r * 2^16) % 3329 = (x * c) % 3329`.
  unfold libcrux_iot_ml_kem.Util.modq_eq at h_mod
  -- h_mod : (r.val - x.val * c.val * 169) % 3329 = 0
  -- Goal:   (r.val * 2^16) % 3329 = (x.val * c.val) % 3329
  have h_dvd : (3329 : Int) ∣ (r.val - x.val * c.val * 169) :=
    Int.dvd_of_emod_eq_zero h_mod
  -- 3329 ∣ (r*2^16 - x*c*169*2^16) (multiply prev by 2^16).
  have h_dvd2 : (3329 : Int)
                  ∣ (r.val * (2 ^ 16 : Int) - x.val * c.val * 169 * (2 ^ 16 : Int)) := by
    have h_eq : (r.val * (2 ^ 16 : Int) - x.val * c.val * 169 * (2 ^ 16 : Int))
                = (r.val - x.val * c.val * 169) * (2 ^ 16 : Int) := by ring
    rw [h_eq]; exact Dvd.dvd.mul_right h_dvd _
  -- 169 * 65536 = 11075584 = 3329 * 3327 + 1, so 169 * 2^16 - 1 = 3329 * 3327.
  have h_inv : (169 : Int) * (2 ^ 16 : Int) - 1 = 3329 * 3327 := by decide
  have h_dvd3 : (3329 : Int)
                  ∣ (x.val * c.val * 169 * (2 ^ 16 : Int) - x.val * c.val) := by
    have h_eq : (x.val * c.val * 169 * (2 ^ 16 : Int) - x.val * c.val)
                = (x.val * c.val) * ((169 : Int) * (2 ^ 16 : Int) - 1) := by ring
    rw [h_eq, h_inv]
    exact ⟨(x.val * c.val) * 3327, by ring⟩
  have h_dvd4 : (3329 : Int) ∣ (r.val * (2 ^ 16 : Int) - x.val * c.val) := by
    have h_sum : (r.val * (2 ^ 16 : Int) - x.val * c.val)
                = (r.val * (2 ^ 16 : Int) - x.val * c.val * 169 * (2 ^ 16 : Int))
                  + (x.val * c.val * 169 * (2 ^ 16 : Int) - x.val * c.val) := by ring
    rw [h_sum]; exact dvd_add h_dvd2 h_dvd3
  -- (a - b) % q = 0  ⇒  a % q = b % q.
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact Int.emod_eq_zero_of_dvd h_dvd4

@[spec]
theorem montgomery_multiply_by_constant_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16) (hc : c.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              (r.elements.val[i]!).val.natAbs ≤ 3328
              ∧ ((r.elements.val[i]!).val * (2 ^ 16 : Int)) % 3329
                 = ((vec.elements.val[i]!).val * c.val) % 3329 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Bridge the impl's body shape (captured-c) to `unary_loop_body
  -- (λ x => montgomery_multiply_fe_by_fer x c)`.
  have h_body_eq :
      (fun (p : (core_models.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant_loop.body
          c p.1 p.2)
      = (fun (p : (core_models.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body
          (fun x => libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer x c)
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant_loop.body
    unfold unary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      (fun x => libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer x c)
      (montgomery_per_elem_P c)
      (fun x => montgomery_per_elem_spec c hc x)
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P

/-! ## L1.6 — `negate_spec`

    The Vector.Portable.Arithmetic.negate impl is a 16-iter loop
    calling `core_models.num.I16.wrapping_neg` on each element. The
    per-element op is the missing-stub `wrapping_sub 0 x`. -/

/-- Per-element predicate: `.bv = -x.bv`. -/
private def negate_per_elem_P (x y : Std.I16) : Prop :=
  y.bv = -x.bv

/-- Per-element Triple: `wrapping_neg x = .ok (wrapping_sub 0 x)` and
    `(wrapping_sub 0 x).bv = 0 - x.bv = -x.bv`. -/
private theorem negate_per_elem_spec (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.I16.wrapping_neg x
    ⦃ ⇓ r => ⌜ negate_per_elem_P x r ⌝ ⦄ := by
  -- The missing-stub def: `wrapping_neg x = wrapping_sub_i16 0 x = .ok (I16.wrapping_sub 0 x)`.
  have h_ok :
      core_models.num.I16.wrapping_neg x = .ok (Aeneas.Std.I16.wrapping_sub (0#i16) x) := by
    unfold core_models.num.I16.wrapping_neg
    unfold rust_primitives.arithmetic.wrapping_sub_i16
    rfl
  rw [h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show negate_per_elem_P x (Aeneas.Std.I16.wrapping_sub (0#i16) x)
  unfold negate_per_elem_P
  -- (wrapping_sub 0 x).bv = 0.bv - x.bv = -x.bv.
  rw [Aeneas.Std.I16.wrapping_sub_bv_eq]
  -- (0#i16).bv = 0 (BitVec definitional); reduce LHS to `0 - x.bv` then
  -- apply BitVec.zero_sub. Use simp to normalize the `IScalarTy.I16.numBits`
  -- vs `16` type-level reduction (per SKILL §5.1.1).
  simp only [show (0#i16 : Std.I16).bv = (0 : BitVec 16) from rfl]
  exact BitVec.zero_sub x.bv

@[spec]
theorem negate_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.negate vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              (r.elements.val[i]!).bv = -(vec.elements.val[i]!).bv ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.negate
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.negate_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Bridge body to `unary_loop_body core_models.num.I16.wrapping_neg`.
  have h_body_eq :
      (fun (p : (core_models.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.negate_loop.body p.1 p.2)
      = (fun (p : (core_models.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body core_models.num.I16.wrapping_neg p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.negate_loop.body
    unfold unary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      core_models.num.I16.wrapping_neg
      negate_per_elem_P
      negate_per_elem_spec
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P

/-! ## L1.5 — `cond_subtract_3329_spec`

    The Vector.Portable.Arithmetic.cond_subtract_3329 impl is a
    16-iter loop where each iter conditionally subtracts 3329 from
    the element (if `x ≥ 3329`) or passes through unchanged. The
    canonical `unary_loop_body` macro doesn't fit because the
    else-branch returns the input `vec` unchanged (no `Array.update`).

    Plan-B: prove from first principles via `loop_range_spec_usize`,
    mirroring `elementwise_unary_spec`'s shape (2-conjunct invariant,
    body-reduction-to-Result-equation, step lemma) with the
    conditional branching inlined. -/

namespace L1_5

open libcrux_iot_ml_kem.Util Aeneas.Std Result ControlFlow

private theorem triple_of_ok_l1
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, Std.Do.WP.wp, hp]

private theorem of_pure_prop_holds_l1 {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] at h; exact h trivial

private theorem pure_prop_holds_l1 {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]; intro _; exact h

/-- Per-element invariant for `cond_subtract_3329`. -/
private def cond_inv
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize →
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector →
    Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
        (((input.elements.val[j]!).val ≥ 3329 ∧
            (acc.elements.val[j]!) = Std.I16.wrapping_sub (input.elements.val[j]!) 3329#i16)
          ∨ ((input.elements.val[j]!).val < 3329 ∧
              acc.elements.val[j]! = input.elements.val[j]!)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.elements.val[j]! = input.elements.val[j]!))

/-- Per-iteration post as a top-level def (avoids inline match issue
    with `loop_range_spec_usize`'s named match constants — see SKILL
    §13 / the analogous `unary_step_post` in PortableVector.lean). -/
private def cond_step_post
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
        ∧ (cond_inv input iter'.start acc').holds
  | .done y => (cond_inv input 16#usize y).holds

set_option maxHeartbeats 8000000 in
private theorem cond_step
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (acc : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (cond_inv input k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ cond_step_post input k r ⌝ ⦄ := by
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l1 h_inv
  have h_acc_len : acc.elements.length = 16 := PortableVector_elements_length acc
  have h_16 : (16#usize : Std.Usize).val = 16 := rfl
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some i = k branch.
    have hk_16 : k.val < 16 := by rw [h_16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    have h_idx :
        Aeneas.Std.Array.index_usize acc.elements k = .ok (acc.elements.val[k.val]!) :=
      array_index_usize_ok_eq acc.elements k (by rw [h_acc_len]; exact hk_16)
    -- declassify x = .ok x.
    have h_decl :
        libcrux_secrets.traits.Declassify.Blanket.declassify (acc.elements.val[k.val]!)
          = .ok (acc.elements.val[k.val]!) := rfl
    -- Two sub-cases for the ≥3329 branch.
    set xk : Std.I16 := acc.elements.val[k.val]! with hxk_def
    -- The key element at index k.
    have h_acc_xk : acc.elements.val[k.val]! = input.elements.val[k.val]! :=
      h_acc_undone k.val (Nat.le_refl _) hk_16
    by_cases h_ge : xk.val ≥ 3329
    · -- ≥ 3329: write back wrapping_sub.
      have h_ge_lit : xk ≥ 3329#i16 := by
        -- `≥` on I16 is `.val ≥ .val`.
        change (3329#i16 : Std.I16).val ≤ xk.val
        have : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [this]; exact h_ge
      have h_decide : decide (xk ≥ 3329#i16) = true := decide_eq_true h_ge_lit
      -- wrapping_sub xk 3329#i16 reduces to .ok (Std.I16.wrapping_sub xk 3329#i16).
      have h_wsub :
          core_models.num.I16.wrapping_sub xk 3329#i16
            = .ok (Std.I16.wrapping_sub xk 3329#i16) := by
        unfold core_models.num.I16.wrapping_sub
        unfold rust_primitives.arithmetic.wrapping_sub_i16
        rfl
      have h_upd :
          Aeneas.Std.Array.update acc.elements k (Std.I16.wrapping_sub xk 3329#i16)
            = .ok (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)) :=
        array_update_ok_eq acc.elements k _ (by rw [h_acc_len]; exact hk_16)
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
              let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
              if i2 >= 3329#i16
              then
                let i3 ← core_models.num.I16.wrapping_sub i1 3329#i16
                let a ← Aeneas.Std.Array.update acc.elements i i3
                ok (cont (iter1, { elements := a }))
              else ok (cont (iter1, acc)))
          = .ok (cont
              (({ start := s, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize),
               { elements := acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16) })) := by
        conv_lhs =>
          rw [show
            (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
              = (core_models.iter.range.IteratorRange.next
                  core_models.Usize.Insts.Core_modelsIterRangeStep
                  ({ start := k, «end» := 16#usize }
                    : core_models.ops.range.Range Std.Usize))
            from rfl]
        rw [h_iter_some]
        simp only [bind_tc_ok]
        rw [h_idx]
        simp only [bind_tc_ok]
        rw [show libcrux_secrets.traits.Declassify.Blanket.declassify xk = .ok xk from rfl]
        simp only [bind_tc_ok]
        rw [if_pos h_ge_lit]
        rw [h_wsub]
        simp only [bind_tc_ok]
        rw [h_upd]
        rfl
      apply triple_of_ok_l1 h_body
      show cond_step_post input k
            (.cont (({ start := s, «end» := 16#usize }
                       : core_models.ops.range.Range Std.Usize),
                    { elements := acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16) }))
      unfold cond_step_post
      refine ⟨h_lt, rfl, hs_val, ?_⟩
      apply pure_prop_holds_l1
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [hs_val] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k: invariant carries over (set at index k, j ≠ k).
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[j]!
                = (acc.elements)[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.elements k j _ h_ne
          have h_set_eq_val :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[j]!
                = acc.elements.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
          have h_old := h_acc_done j hj_lt_k
          rcases h_old with ⟨h_in_ge, h_acc_eq⟩ | ⟨h_in_lt, h_acc_eq⟩
          · left; refine ⟨h_in_ge, ?_⟩; rw [h_set_eq_val]; exact h_acc_eq
          · right; refine ⟨h_in_lt, ?_⟩; rw [h_set_eq_val]; exact h_acc_eq
        · -- j = k.val: use the just-set element.
          subst hj_eq_k
          have h_lt'' : k.val < acc.elements.length := by rw [h_acc_len]; exact hk_16
          have h_set_eq :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[k.val]!
                = Std.I16.wrapping_sub xk 3329#i16 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq acc.elements k k.val _ ⟨rfl, h_lt''⟩
          have h_set_eq_val :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[k.val]!
                = Std.I16.wrapping_sub xk 3329#i16 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
          left
          refine ⟨?_, ?_⟩
          · rw [← h_acc_xk]; exact h_ge
          · rw [h_set_eq_val, ← h_acc_xk]
      · intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        have h_set_ne :
            (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[j]!
              = (acc.elements)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.elements k j _ h_ne
        have h_set_eq_val :
            (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[j]!
              = acc.elements.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        rw [h_set_eq_val]
        exact h_acc_undone j h_ge' hj_lt
    · -- < 3329: pass through unchanged.
      have h_not_ge : ¬ (3329#i16 : Std.I16).val ≤ xk.val := by
        have h_eq : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [h_eq]; exact h_ge
      have h_not_ge' : ¬ (xk ≥ 3329#i16) := h_not_ge
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
              let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
              if i2 >= 3329#i16
              then
                let i3 ← core_models.num.I16.wrapping_sub i1 3329#i16
                let a ← Aeneas.Std.Array.update acc.elements i i3
                ok (cont (iter1, { elements := a }))
              else ok (cont (iter1, acc)))
          = .ok (cont
              (({ start := s, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize),
               acc)) := by
        conv_lhs =>
          rw [show
            (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
              = (core_models.iter.range.IteratorRange.next
                  core_models.Usize.Insts.Core_modelsIterRangeStep
                  ({ start := k, «end» := 16#usize }
                    : core_models.ops.range.Range Std.Usize))
            from rfl]
        rw [h_iter_some]
        simp only [bind_tc_ok]
        rw [h_idx]
        simp only [bind_tc_ok]
        rw [show libcrux_secrets.traits.Declassify.Blanket.declassify xk = .ok xk from rfl]
        simp only [bind_tc_ok]
        rw [if_neg h_not_ge']
      apply triple_of_ok_l1 h_body
      show cond_step_post input k
            (.cont (({ start := s, «end» := 16#usize }
                       : core_models.ops.range.Range Std.Usize),
                    acc))
      unfold cond_step_post
      refine ⟨h_lt, rfl, hs_val, ?_⟩
      apply pure_prop_holds_l1
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [hs_val] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · exact h_acc_done j hj_lt_k
        · subst hj_eq_k
          right
          refine ⟨?_, ?_⟩
          · rw [← h_acc_xk]; show xk.val < 3329
            push_neg at h_ge; exact h_ge
          · exact h_acc_xk
      · intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ge' : k.val ≤ j := by omega
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
            let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
            if i2 >= 3329#i16
            then
              let i3 ← core_models.num.I16.wrapping_sub i1 3329#i16
              let a ← Aeneas.Std.Array.update acc.elements i i3
              ok (cont (iter1, { elements := a }))
            else ok (cont (iter1, acc)))
        = .ok (done acc) := by
      conv_lhs =>
        rw [show
          (core_models.ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next
              core_models.Usize.Insts.Core_modelsIterRangeStep
              ({ start := k, «end» := 16#usize } : core_models.ops.range.Range Std.Usize))
            = (core_models.iter.range.IteratorRange.next
                core_models.Usize.Insts.Core_modelsIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : core_models.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_l1 h_body
    show cond_step_post input k (.done acc)
    unfold cond_step_post
    apply pure_prop_holds_l1
    refine ⟨?_, ?_⟩
    · intro j hj
      apply h_acc_done j
      rw [hk_eq]; rw [h_16] at hj; exact hj
    · intro j hj_ge hj_lt
      apply h_acc_undone j _ hj_lt
      rw [hk_eq]; rw [h_16] at hj_ge; exact hj_ge

end L1_5

@[spec]
theorem cond_subtract_3329_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bounds : ∀ i : Nat, i < 16 → 0 ≤ (vec.elements.val[i]!).val
                                  ∧ (vec.elements.val[i]!).val < 2 * 3329) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329 vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              0 ≤ (r.elements.val[i]!).val
              ∧ (r.elements.val[i]!).val < 3329
              ∧ (r.elements.val[i]!).val % 3329 = (vec.elements.val[i]!).val % 3329 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, vec1) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
          iter1 vec1)
      vec 0#usize 16#usize
      (L1_5.cond_inv vec)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (L1_5.pure_prop_holds_l1 ⟨
        fun j hj => by
          have h0 : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done, _h_undone⟩ := L1_5.of_pure_prop_holds_l1 h
    intro j hj
    -- Per-element: derive 0 ≤ r[j] < 3329 and r[j] % 3329 = vec[j] % 3329.
    obtain ⟨h_vec_ge, h_vec_lt⟩ := h_bounds j hj
    have h_done_j := h_done j (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hj)
    -- Pinned x := vec[j] (since the inv carries `input := vec`).
    set xj : Std.I16 := vec.elements.val[j]! with hxj_def
    rcases h_done_j with ⟨h_ge, h_eq⟩ | ⟨h_lt, h_eq⟩
    · -- ≥ 3329 branch: r[j] = wrapping_sub xj 3329.
      -- (wrapping_sub xj 3329).val = xj.val - 3329, since 3329 ≤ xj.val < 6658.
      have h_wsub_val :
          (Std.I16.wrapping_sub xj (3329#i16 : Std.I16)).val = xj.val - 3329 := by
        rw [Std.I16.wrapping_sub_val_eq]
        -- bmod xj.val - 3329 by 2^16 = xj.val - 3329 when in range
        have h_diff_lb : -(2^15 : Int) ≤ xj.val - 3329 := by
          have h_xj_lb : (0 : Int) ≤ xj.val := h_vec_ge
          have : -(2^15 : Int) ≤ -3329 := by decide
          linarith
        have h_diff_ub : xj.val - 3329 < (2^15 : Int) := by
          have h_xj_ub : xj.val < 2 * 3329 := h_vec_lt
          have h_step : (2 * 3329 - 3329 : Int) < (2^15 : Int) := by decide
          linarith
        have h_3329_val : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [h_3329_val]
        apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
        · have h_const : -((2 : Int)^(16-1)) ≤ -(2^15 : Int) := by decide
          exact le_trans h_const h_diff_lb
        · have h_const : (2^15 : Int) ≤ (2 : Int)^(16-1) := by decide
          exact lt_of_lt_of_le h_diff_ub h_const
      refine ⟨?_, ?_, ?_⟩
      · -- 0 ≤ xj.val - 3329 (since xj.val ≥ 3329).
        rw [h_eq, h_wsub_val]
        have : (0 : Int) ≤ xj.val - 3329 := by linarith
        exact this
      · -- xj.val - 3329 < 3329 (since xj.val < 2 * 3329).
        rw [h_eq, h_wsub_val]
        have : xj.val - 3329 < (3329 : Int) := by linarith
        exact this
      · rw [h_eq, h_wsub_val]
        -- (xj.val - 3329) % 3329 = xj.val % 3329 (subtracting a multiple of 3329).
        have : (xj.val - 3329) % 3329 = xj.val % 3329 := by
          have h := Int.sub_emod xj.val 3329 3329
          rw [h]
          have h_self : (3329 : Int) % 3329 = 0 := by decide
          rw [h_self]
          simp [Int.emod_emod_of_dvd]
        exact this
    · -- < 3329 branch: r[j] = xj.
      refine ⟨?_, ?_, ?_⟩
      · rw [h_eq]; exact h_vec_ge
      · rw [h_eq]; exact h_lt
      · rw [h_eq]
  · intro acc k h_ge h_le hinv
    have h_step := L1_5.cond_step vec acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : L1_5.cond_step_post vec k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L1_5.cond_step_post] using hP
    · have hP : L1_5.cond_step_post vec k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [L1_5.cond_step_post] using hP

end libcrux_iot_ml_kem.Equivalence
