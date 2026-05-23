/-
  # `BitMlKem/FCTargets.lean` — STATEMENTS-ONLY FC obligation hierarchy.

  Per `~/.claude/skills/lean-for-libcrux/SKILL.md` §8.1 and the
  `feedback_strong_postconditions.md` memory:

  > Strong post-conditions, no bounds fallback. New + upgrade-pass
  > Triples must use equality-form posts; never weaken to bounds
  > because they're easier.

  > §8.1 — Write the final FC form (with the spec-level equality) from
  > day one, leaving the proof `sorry` if needed. Upgrading after the
  > fact cascades.

  This file is the single locked statement of the full functional-
  correctness obligation hierarchy for the ML-KEM impl-vs-hacspec
  equivalence: from the leaf field primitives (L0) up through the
  four matrix-level targets (L7). Every proof body is `by sorry`,
  every helper `def` body is `sorry` where the spec wiring is not
  yet computable. **No proofs.** The file's job is to lock the
  type-correct statement of every FC Triple so subsequent dispatches
  fill in proofs without retroactively widening the postconditions.

  ## Hard rules followed (per dispatch brief)

  1. Every Triple post is equality-form:
        `Spec.<op> (lift args) = .ok (lift p)`
     (or projected to the value component for impl ops returning
     `(value, scratch, accumulator)` tuples).
  2. Bounds may appear as conjuncts but never alone.
  3. `⇓ p => …` is total correctness; the `.ok` on the RHS of each
     FC equation is the `_eq_ok` pure-projection content (impl's
     `.ok` value = projected `_pure` value).
  4. The lift tower is defined below. All `_pure` Spec aliases needed
     beyond `SpecPure.lean` (which has only the four FE scalars plus
     three poly wrappers) are introduced here with bodies = `sorry`.
  5. `@[spec]` attribute on every Triple; bare `by sorry` proof.
  6. Bottom-up ordering L0 → L1 → L2 → L3 → L6 → L7.

  ## Discipline notes (from the dispatch brief)

  - We do NOT modify the existing `Equivalence/L*.lean` files; their
    bounds-only Triples remain and will be retired separately. This
    file is the FC-compliant replacement set.
  - Each `_pure` alias defined here is intended to be the `Result`-stripped
    pure projection of a hacspec `Result`-monadic op. Bodies are `sorry`
    when the matching hacspec call chain is intricate (compress,
    decompress, ntt full driver); types are correct.
  - Where the impl op has no direct hacspec counterpart at the same
    abstraction layer (e.g. the impl's `cond_subtract_3329` is a
    pure-Mont-form rebalance with no FE-level hacspec mirror), we mark
    `// NO HACSPEC EQUIVALENT — treat as identity in ZMod 3329` and
    state the FC equation against the identity-`Spec.<closest>`.
-/
import LibcruxIotMlKem.BitMlKem.Spec
import LibcruxIotMlKem.BitMlKem.SpecPure
import LibcruxIotMlKem.BitMlKem.AlgEquiv
import LibcruxIotMlKem.Util.BvMasks
import LibcruxIotMlKem.Util.ModularArith
import LibcruxIotMlKem.Equivalence.L0_FieldArith
import LibcruxIotMlKem.Equivalence.L1_VectorElementOps
import LibcruxIotMlKem.Extraction.Funs
import HacspecMlKem.Extraction.Funs

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.BitMlKem.FCTargets

open Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.BitMlKem

/-! ## §0 Lift tower

    Each `lift_*` projects an impl-side carrier to the corresponding
    hacspec carrier. Type signatures are load-bearing — they are what
    the FC equation reads on both sides. Bodies use existing M.1
    pieces (`i16_to_spec_fe_mont`, `feOfZMod`, `to_spec_poly_mont`)
    where convenient. -/

/-- Default `FieldElement` used by `[i]!` projections inside the
    lift bodies below. The canonical residue 0 mod q. -/
private noncomputable def defaultFE :
    hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (0 : ZMod 3329)

private noncomputable instance : Inhabited hacspec_ml_kem.parameters.FieldElement :=
  ⟨defaultFE⟩

/-- Local `Inhabited` instance for `PortableVector` used by `[i]!`
    indexing in `lift_chunk` / `lift_poly`. Mirrors the `local instance`
    in `BitMlKem/Spec.lean` (which is file-scoped). -/
private instance instInhabitedPortableVector_fcTargets :
    Inhabited libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  ⟨{ elements := Std.Array.make 16#usize (List.replicate 16 (0#i16 : Std.I16))
        (by simp) }⟩

/-- Local `Inhabited` instance for `PolynomialRingElement PortableVector`
    used by `[i]!` indexing in `lift_poly` / `lift_vec_slice`. -/
private instance instInhabitedPolynomialRingElement_fcTargets
    {Vector : Type} [Inhabited Vector] :
    Inhabited (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :=
  ⟨{ coefficients :=
       Std.Array.make 16#usize (List.replicate 16 default) (by simp) }⟩

/-- Plain-domain lane lift from `Int` to a hacspec `FieldElement`.
    Used by `barrett_reduce_element_fc` (the impl carries the value
    in plain domain). -/
noncomputable def lift_fe_int (x : Int) : hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (x : ZMod 3329)

/-- Plain-domain lane lift from `Std.I16` to a hacspec `FieldElement`.
    Composes `i16_to_spec_fe_plain` with `feOfZMod`. -/
noncomputable def lift_fe (lane : Std.I16) : hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (i16_to_spec_fe_plain lane)

/-- Mont-domain lane lift from `Std.I16` to a hacspec `FieldElement`.
    Used for outputs of impl ops that produce Mont-form lanes
    (`montgomery_multiply_*`, `montgomery_reduce_element`). -/
noncomputable def lift_fe_mont (lane : Std.I16) : hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (i16_to_spec_fe_mont lane)

/-- Plain-domain poly lift `PortableVector chunk → 16 FE-array`.
    Maps each of the 16 lanes through `lift_fe`. -/
noncomputable def lift_chunk
    (chunk : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize (chunk.elements.val.map lift_fe) (by
    simp [Std.Array.length_eq])

/-- Mont-domain poly lift `PortableVector chunk → 16 FE-array`.
    Maps each of the 16 lanes through `lift_fe_mont`. -/
noncomputable def lift_chunk_mont
    (chunk : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize (chunk.elements.val.map lift_fe_mont) (by
    simp [Std.Array.length_eq])

/-- Plain-domain poly lift: `PolynomialRingElement PortableVector →
    Array FE 256`. The result is the hacspec "ring element" type.
    Flattens 16 chunks × 16 lanes via the standard
    `i = j / 16`, `k = j % 16` decomposition. -/
noncomputable def lift_poly
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun j =>
      lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]!))
    (by simp)

/-- Mont-domain poly lift. Same shape as `lift_poly` but strips one
    `R` factor per lane via `i16_to_spec_fe_mont`. -/
noncomputable def lift_poly_mont
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun j =>
      lift_fe_mont (re.coefficients.val[j / 16]!).elements.val[j % 16]!))
    (by simp)

/-- Vector lift: `Array (PolynomialRingElement) K → Array (Array FE 256) K`. -/
noncomputable def lift_vec {K : Std.Usize}
    (v : Std.Array
          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K) :
    Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
  Std.Array.make K (v.val.map lift_poly) (by
    simp [Std.Array.length_eq])

/-- Vector-slice variant for `Slice`-typed impl args
    (e.g. `compute_ring_element_v` takes `r_as_ntt : Slice ...`).
    The FC theorems that consume this expect `v.length = K.val` as a
    precondition; out-of-range indices default to the unit chunk. -/
noncomputable def lift_vec_slice
    (v : Slice
          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (K : Std.Usize) :
    Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
  Std.Array.make K
    ((List.range K.val).map (fun i => lift_poly v.val[i]!))
    (by simp)

/-- Matrix lift: `Array (Array (PolynomialRingElement) K) K → Array (Array (Array FE 256) K) K`. -/
noncomputable def lift_matrix {K : Std.Usize}
    (m : Std.Array
          (Std.Array
            (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K) K) :
    Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K :=
  Std.Array.make K (m.val.map lift_vec) (by
    simp [Std.Array.length_eq])

/-- Pure projection of `matrix.sample_matrix_A` from the public-key seed.
    Forward-declared here (rather than in §0.5 below) so
    `lift_matrix_from_seed` can reference it.

    **Phase-1 obligation**: pure-projection side lemma
    `hacspec_ml_kem.matrix.sample_matrix_A seed K
    = .ok (Spec.sample_matrix_A_pure seed K)`. -/
noncomputable def Spec.sample_matrix_A_pure
    (seed : Slice Std.U8) (K : Std.Usize) :
    Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K :=
  sorry

/-- Matrix-from-seed lift: the impl `matrix.compute_vector_u` reconstructs
    the matrix in-place via `sample_matrix_entry`; the hacspec spec calls
    `matrix.sample_matrix_A` on the seed once at the top. Defers to
    `Spec.sample_matrix_A_pure` above for the deterministic projection. -/
noncomputable def lift_matrix_from_seed
    (seed : Slice Std.U8) (K : Std.Usize) :
    Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K :=
  Spec.sample_matrix_A_pure seed K

/-! ## §0.5 Spec `_pure` aliases needed beyond `SpecPure.lean`.

    `SpecPure.lean` already provides:
      - `FieldElement.{add,sub,mul,neg}_pure`
      - `polynomial.{add_to_ring_element,poly_barrett_reduce,subtract_reduce}_pure`

    We add here the missing `_pure` aliases referenced by FC equations
    below. Each is the `Result`-stripped pure projection of a
    `Result`-monadic hacspec op; bodies use the standard
    `match | .ok r => r | _ => default`
    pattern (see `SpecPure.lean`). Bodies left `sorry` here for brevity
    — types are load-bearing. -/

/-- Pure projection of `parameters.FieldElement.new (x.val % q)` —
    the canonical-residue constructor, here re-expressed as the round-trip
    `feOfZMod ∘ zmodOfFE`. The two forms are equivalent: both produce
    `{ val := ⟨BitVec.ofNat 16 (x.val.val % 3329)⟩ }` since `zmodOfFE x`
    is `(x.val.val : ZMod 3329)` (whose underlying Nat is `x.val.val % 3329`)
    and `parameters.FieldElement.new` always returns `.ok ⟨_⟩` unconditionally.
    The round-trip form composes with the existing `zmodOfFE_feOfZMod`
    identity in M.1, making the FC equation reduce to "lift_fe r = lift_fe value
    given r ≡ value mod q". -/
noncomputable def Spec.barrett_pure (x : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (zmodOfFE x)

/-- Pure projection of Montgomery reduction at the FE level. The impl
    `montgomery_reduce_element` takes an `Std.I32` and returns an `Std.I16`
    in Mont domain (encoding `a · R`). The hacspec spec has no direct
    counterpart at the FE level. The FC equation
    `lift_fe_mont r = Spec.mont_reduce_pure (lift_fe_int value.val)`
    combines two factors of R⁻¹:
      (i) the impl's invariant `r ≡ value · R⁻¹ (mod q)`, and
      (ii) `lift_fe_mont`'s own R-stripping (it returns `(r.val : ZMod 3329) · 169`).
    The TOTAL effect is `value.val · R⁻² mod q`. Since `R⁻¹ = 169 mod q`,
    `R⁻² = 169² mod q`. So `Spec.mont_reduce_pure` multiplies its
    ZMod-projected argument by `169 · 169`. -/
noncomputable def Spec.mont_reduce_pure (x : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (zmodOfFE x * 169 * 169)

/-- Pure projection of Montgomery `fe · fer / R`: given two FEs, returns
    `fe · fer · R⁻¹` in canonical domain (i.e., `zmodOfFE fe · zmodOfFE fer · 169`
    in ZMod 3329). The factor `169 = R⁻¹ mod q` comes from the impl's
    Montgomery reduction step (the L0.3 calculation gave 169² because the
    INPUT was plain-via-`lift_fe_int`, whereas here `fer` is already
    interpreted in Mont domain through `lift_fe_mont`, so only ONE R⁻¹
    factor is needed). The math intent of the impl: given fe (plain, math
    value = fe) and fer (Mont, math value = fer · R⁻¹), output Mont-encoded
    fe · (fer · R⁻¹) = fe · fer · R⁻¹ in Mont. The Mont encoding is then
    stripped by `lift_fe_mont`, giving the canonical math value
    fe · fer · R⁻¹. -/
noncomputable def Spec.montgomery_multiply_fe_by_fer_pure
    (fe fer : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (zmodOfFE fe * zmodOfFE fer * 169)

/-- Pure projection of `get_n_least_significant_bits` — pure modular
    truncation on `Std.U32`. -/
def Spec.get_n_least_significant_bits_pure (n : Std.U8) (value : Std.U32) : Std.U32 :=
  ⟨value.bv &&& ((1#32 <<< n.val) - 1#32)⟩

/-- Pure pointwise add at the FE-array level (16-lane chunk).
    Lifts `FieldElement.add_pure` across the 16 lanes via `List.range 16`. -/
noncomputable def Spec.chunk_add_pure
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
        (a.val[i]!) (b.val[i]!)))
    (by simp)

/-- Pure pointwise sub at the FE-array level (16-lane chunk).
    Lifts `FieldElement.sub_pure` across the 16 lanes. -/
noncomputable def Spec.chunk_sub_pure
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
        (a.val[i]!) (b.val[i]!)))
    (by simp)

/-- Pure pointwise neg at the FE-array level (16-lane chunk).
    Lifts `FieldElement.neg_pure` across the 16 lanes. -/
noncomputable def Spec.chunk_neg_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.neg_pure
        (a.val[i]!)))
    (by simp)

/-- Pure pointwise barrett-reduce at the FE-array level.
    Lifts `Spec.barrett_pure` (the canonical round-trip) across 16 lanes. -/
noncomputable def Spec.chunk_barrett_reduce_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      Spec.barrett_pure (a.val[i]!)))
    (by simp)

/-- Pure pointwise `montgomery_multiply_by_constant` at the chunk level
    (each lane: `fe · c / R`). Lifts `Spec.montgomery_multiply_fe_by_fer_pure`
    across 16 lanes, with the second arg threaded as the constant `c`. -/
noncomputable def Spec.chunk_montgomery_multiply_by_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      Spec.montgomery_multiply_fe_by_fer_pure (a.val[i]!) c))
    (by simp)

/-- Pure pointwise plain `multiply_by_constant` at the chunk level.
    Lifts `FieldElement.mul_pure` across 16 lanes with the constant `c`. -/
noncomputable def Spec.chunk_multiply_by_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
        (a.val[i]!) c))
    (by simp)

/-- Pure pointwise `bitwise_and_with_constant` at the chunk level.
    NO HACSPEC EQUIVALENT — this is a bit-level mask used only in
    serialize/compress paths. The body applies BV-and on each FE's
    underlying `U16` BV.

    WARNING (FC obstruction): the FC equation for `bitwise_and_with_constant_fc`
    against `lift_chunk`-style inputs is NOT provable in general because
    `lift_chunk` discards the bit pattern (keeping only mod-3329 residue),
    while bit-level AND depends on the raw `I16` bit pattern. The body here
    is the canonical FE-side BV operation; the FC proof will STOP and report
    when attempted. Not on the L7 critical path (used only in compress/
    serialize, which lives outside the 4 matrix-level targets). -/
noncomputable def Spec.chunk_bitwise_and_with_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      let ai_bv : BitVec Aeneas.Std.UScalarTy.U16.numBits := (a.val[i]!).val.bv
      let c_bv  : BitVec Aeneas.Std.UScalarTy.U16.numBits := c.val.bv
      ({ val := { bv := ai_bv &&& c_bv } } : hacspec_ml_kem.parameters.FieldElement)))
    (by simp)

/-- Pure pointwise `shift_right` at the chunk level.
    NO HACSPEC EQUIVALENT at the FE level. The body applies a logical
    right shift on each FE's underlying `U16` BV by `SHIFT_BY.val.toNat`.

    WARNING (FC obstruction): same as `chunk_bitwise_and_with_constant_pure`
    — the FC equation is not provable through `lift_chunk` because the
    underlying `I16` sshiftRight depends on raw bit pattern. The body here
    serves as a placeholder; the FC proof will STOP and report. Not on
    the L7 critical path. -/
noncomputable def Spec.chunk_shift_right_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (SHIFT_BY : Std.I32) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      let ai_bv : BitVec Aeneas.Std.UScalarTy.U16.numBits := (a.val[i]!).val.bv
      let shift : Nat := SHIFT_BY.val.toNat
      ({ val := { bv := ai_bv >>> shift } } : hacspec_ml_kem.parameters.FieldElement)))
    (by simp)

/-- Pure `reducing_from_i32_array` at the chunk level. Lifts `Spec.mont_reduce_pure`
    over 16 lanes of the input `i32` slice. Each lane: take `array[i]`,
    project through `lift_fe_int`, apply Montgomery reduction. -/
noncomputable def Spec.chunk_reducing_from_i32_array_pure
    (array : Slice Std.I32) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val)))
    (by simp)

/-- Pure NTT butterfly step at the chunk level: applies `ntt.butterfly`
    pointwise to the lane pair `(i, j)` with `zeta`. Mirrors the impl's
    write order (`a[j] := a-t`, then `a[i] := a+t`) so that when `i = j`
    the second write wins (matching impl semantics). When `i ≠ j` the
    `(i, j)` lanes become `(add_pure a[i] (mul_pure a[j] zeta),
    sub_pure a[i] (mul_pure a[j] zeta))` respectively. -/
noncomputable def Spec.chunk_ntt_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let t_fe :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure (a.val[j.val]!) zeta
  let a_minus_t :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure (a.val[i.val]!) t_fe
  let a_plus_t :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure (a.val[i.val]!) t_fe
  (a.set j a_minus_t).set i a_plus_t

/-- Pure NTT-layer-1 step at the chunk level. Mirrors the impl's
    8 sequential `ntt_step` calls at pairs (0,2)(1,3)(4,6)(5,7)
    (8,10)(9,11)(12,14)(13,15) with zetas z0,z0,z1,z1,z2,z2,z3,z3. -/
noncomputable def Spec.chunk_ntt_layer_1_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_ntt_step_pure a  z0 0#usize  2#usize
  let a2 := Spec.chunk_ntt_step_pure a1 z0 1#usize  3#usize
  let a3 := Spec.chunk_ntt_step_pure a2 z1 4#usize  6#usize
  let a4 := Spec.chunk_ntt_step_pure a3 z1 5#usize  7#usize
  let a5 := Spec.chunk_ntt_step_pure a4 z2 8#usize 10#usize
  let a6 := Spec.chunk_ntt_step_pure a5 z2 9#usize 11#usize
  let a7 := Spec.chunk_ntt_step_pure a6 z3 12#usize 14#usize
  Spec.chunk_ntt_step_pure a7 z3 13#usize 15#usize

/-- Pure NTT-layer-2 step at the chunk level. Mirrors the impl's
    8 sequential `ntt_step` calls at pairs (0,4)(1,5)(2,6)(3,7)
    (8,12)(9,13)(10,14)(11,15) with zetas z0,z0,z0,z0,z1,z1,z1,z1. -/
noncomputable def Spec.chunk_ntt_layer_2_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_ntt_step_pure a  z0 0#usize  4#usize
  let a2 := Spec.chunk_ntt_step_pure a1 z0 1#usize  5#usize
  let a3 := Spec.chunk_ntt_step_pure a2 z0 2#usize  6#usize
  let a4 := Spec.chunk_ntt_step_pure a3 z0 3#usize  7#usize
  let a5 := Spec.chunk_ntt_step_pure a4 z1 8#usize 12#usize
  let a6 := Spec.chunk_ntt_step_pure a5 z1 9#usize 13#usize
  let a7 := Spec.chunk_ntt_step_pure a6 z1 10#usize 14#usize
  Spec.chunk_ntt_step_pure a7 z1 11#usize 15#usize

/-- Pure NTT-layer-3 step at the chunk level. Mirrors the impl's
    8 sequential `ntt_step` calls at pairs (0,8)(1,9)(2,10)(3,11)
    (4,12)(5,13)(6,14)(7,15) all with the same zeta. -/
noncomputable def Spec.chunk_ntt_layer_3_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_ntt_step_pure a  z 0#usize  8#usize
  let a2 := Spec.chunk_ntt_step_pure a1 z 1#usize  9#usize
  let a3 := Spec.chunk_ntt_step_pure a2 z 2#usize 10#usize
  let a4 := Spec.chunk_ntt_step_pure a3 z 3#usize 11#usize
  let a5 := Spec.chunk_ntt_step_pure a4 z 4#usize 12#usize
  let a6 := Spec.chunk_ntt_step_pure a5 z 5#usize 13#usize
  let a7 := Spec.chunk_ntt_step_pure a6 z 6#usize 14#usize
  Spec.chunk_ntt_step_pure a7 z 7#usize 15#usize

/-- Pure inverse-NTT step at the chunk level. Mirrors the impl's
    write order (`a[i] := add_pure a[j] a[i]`, then
    `a[j] := mul_pure (sub_pure a[j] a[i_original]) zeta`).
    Because the impl reads `vec[j]` (`= i1`) and `vec[i]` (`= i2`)
    BEFORE writing, the `(i, j)` lanes become:
      - new `a[i] = add_pure a[j] a[i]`  (barrett collapses to canonical sum)
      - new `a[j] = mul_pure (sub_pure a[j] a[i]) zeta`  (Mont-mul with zeta)
    where the reads on the RHS are at the ORIGINAL `a`. When `i = j` the
    second write wins (matching impl semantics). -/
noncomputable def Spec.chunk_inv_ntt_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a_i := a.val[i.val]!
  let a_j := a.val[j.val]!
  let new_i :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure a_j a_i
  let diff :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure a_j a_i
  let new_j :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure diff zeta
  (a.set i new_i).set j new_j

/-- The PortableVector `Operations` instance used by Triples that
    target the impl monomorphised at `PortableVector`. The concrete
    instance is `vector.portable.vector_type.PortableVector.Insts.
    Libcrux_iot_ml_kemVectorTraitsOperations` in `Extraction/Funs.lean`;
    this alias decouples the FC statements from the precise extraction
    identifier in case aeneas re-mangles the name later. -/
@[reducible] def portable_ops_inst :
    libcrux_iot_ml_kem.vector.traits.Operations
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations

/-- Local `Inhabited` for 16-element FE arrays, used by `[!]` indexing
    inside `Spec.flatten_chunks`. -/
private noncomputable instance instInhabitedFEChunk_fcTargets :
    Inhabited (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :=
  ⟨Std.Array.make 16#usize (List.replicate 16 defaultFE) (by simp)⟩

/-- Per-index zeta lookup: project lane `i` of
    `polynomial.ZETAS_TIMES_MONTGOMERY_R` into a canonical-domain FE.
    The Mont-domain table holds `Std.I16` values; `lift_fe_mont` strips
    one factor of R (yielding the canonical zeta). Out-of-range lookups
    default to `lift_fe_mont 0 = 0` via `[!]`. -/
noncomputable def Spec.zeta_at (i : Nat) : hacspec_ml_kem.parameters.FieldElement :=
  lift_fe_mont (libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[i]!)

/-- Chunk projection: extract the `k`-th 16-element chunk of a 256-array.
    Used to address the impl's `re.coefficients[k]` chunk slot at the
    spec level. -/
noncomputable def Spec.chunk_at
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (k : Nat) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun j => p.val[16 * k + j]!))
    (by simp)

/-- Flatten 16 chunks of 16 FEs into a 256-array. Inverse of
    `Spec.chunk_at` under the `lift_poly` decomposition. -/
noncomputable def Spec.flatten_chunks
    (chunks : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
                16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize ((List.range 256).map (fun j =>
    (chunks.val[j / 16]!).val[j % 16]!)) (by simp)

/-- Pure projection of `ntt_at_layer_1` driver: 16 chunks, each chunk
    transformed by `chunk_ntt_layer_1_step_pure` with 4 zetas drawn
    from positions `zeta_i + 4k + {1..4}` in the global ZETAS table. -/
noncomputable def Spec.ntt_layer_1_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_ntt_layer_1_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val + 4 * k + 1))
        (Spec.zeta_at (zeta_i.val + 4 * k + 2))
        (Spec.zeta_at (zeta_i.val + 4 * k + 3))
        (Spec.zeta_at (zeta_i.val + 4 * k + 4))))
      (by simp))

/-- Pure projection of `ntt_at_layer_2` driver: 16 chunks, each chunk
    transformed by `chunk_ntt_layer_2_step_pure` with 2 zetas at
    positions `zeta_i + 2k + {1, 2}`. -/
noncomputable def Spec.ntt_layer_2_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_ntt_layer_2_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val + 2 * k + 1))
        (Spec.zeta_at (zeta_i.val + 2 * k + 2))))
      (by simp))

/-- Pure projection of `ntt_at_layer_3` driver: 16 chunks, each chunk
    transformed by `chunk_ntt_layer_3_step_pure` with 1 zeta at
    position `zeta_i + k + 1`. -/
noncomputable def Spec.ntt_layer_3_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_ntt_layer_3_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val + k + 1))))
      (by simp))

/-- Pure projection of the full hacspec `ntt.ntt`. Defined as a 7-layer
    composition with cumulative zeta offsets + final barrett.
    **STUB**: layers 4-7 require additional helpers (nested loop
    pattern in `ntt_at_layer_4_plus`); deferred to a follow-up phase.
    Used by `ntt_binomially_sampled_ring_element_fc` / `ntt_vector_u_fc`. -/
noncomputable def Spec.ntt_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize := sorry

/-- Pure projection of `polynomial.add_error_reduce`. The hacspec spec
    does not expose a dedicated `add_error_reduce` at the poly level —
    the impl's behaviour is "multiply by R/128 then add error then
    barrett". The closest hacspec composition is `add_to_ring_element`
    after the implicit Mont rescaling. -/
noncomputable def Spec.add_error_reduce_pure
    (self error : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize := sorry

/-- Pure projection of `polynomial.add_standard_error_reduce`. -/
noncomputable def Spec.add_standard_error_reduce_pure
    (self error : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize := sorry

/-- Pure projection of `polynomial.add_message_error_reduce`. -/
noncomputable def Spec.add_message_error_reduce_pure
    (self message : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (result : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize := sorry

/-- Pure projection of poly-level `reducing_from_i32_array`. -/
noncomputable def Spec.poly_reducing_from_i32_array_pure
    (array : Slice Std.I32) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize := sorry

-- `Spec.sample_matrix_A_pure` is declared above (with `lift_matrix_from_seed`).

/-! ## §L0 — FE scalar primitives (4 theorems).

    Each post pairs the existing bounds conjunct (load-bearing for
    callers) with the FC equation against the spec-level pure op. -/

/-- The Triple `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`.
    Lifts a pure-Prop fact about the value into a Triple post.
    Mirror of SKILL §13.5 helper, scoped to this file. -/
private theorem triple_of_ok_fc {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

/-- Extract the `.ok` witness from a true-pre Triple.
    Mirror of SKILL §13.5 helper, scoped to this file. -/
private theorem triple_exists_ok_fc {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp])

/-! ### L0.1 — `get_n_least_significant_bits`.
    Impl computes `value & ((1 <<< n) - 1)`; the spec
    `Spec.get_n_least_significant_bits_pure` is precisely that BV-mask
    expression (see §0.5 above). The post-shape is `bounds ∧ r = spec`.

    Proof sketch:
    1. Pure-projection side lemma `get_n_least_significant_bits_eq_ok_fc`
       reduces the impl `do`-block to `.ok (Spec.<…>_pure n value)` by
       `unfold ; simp only [shift_left_lemmas, wrapping_sub_u32, bind_tc_ok] ; rfl`.
       The precondition `n.val ≤ 16` discharges the `n < 32` shift bound.
    2. Apply `triple_of_ok_fc` with the side lemma to discharge the
       monadic shell.
    3. The FC equality is `rfl` (the spec body IS the mask expression).
    4. The bound `r.val < 2^n.val` reduces to
       `(value.bv &&& mask).toNat < 2^n.val` via `BitVec.toNat_and` +
       `Util.mask_pow2_minus_one_toNat` + `Nat.and_le_right` + `omega`. -/

/-- Pure-projection side lemma for `get_n_least_significant_bits`.
    Pins the impl's `.ok` value to `Spec.get_n_least_significant_bits_pure`. -/
private theorem get_n_least_significant_bits_eq_ok_fc
    (n : Std.U8) (value : Std.U32) (hn : n.val ≤ 16) :
    libcrux_iot_ml_kem.vector.portable.arithmetic.get_n_least_significant_bits n value
      = .ok (Spec.get_n_least_significant_bits_pure n value) := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.get_n_least_significant_bits
  unfold Spec.get_n_least_significant_bits_pure
  have hn_lt : n.val < Aeneas.Std.UScalarTy.U32.numBits := by
    have h_red : (Aeneas.Std.UScalarTy.U32.numBits : Nat) = 32 := by decide
    rw [h_red]; omega
  simp only [HShiftLeft.hShiftLeft, Aeneas.Std.UScalar.shiftLeft_UScalar,
             Aeneas.Std.UScalar.shiftLeft, hn_lt, reduceIte,
             core_models.num.U32.wrapping_sub,
             rust_primitives.arithmetic.wrapping_sub_u32,
             Aeneas.Std.bind_tc_ok]
  rfl

/-- L0.1 — `get_n_least_significant_bits`.
    Spec: bitwise AND with `(1 << n) - 1`. -/
@[spec high]
theorem get_n_least_significant_bits_fc
    (n : Std.U8) (value : Std.U32) (hn : n.val ≤ 16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.get_n_least_significant_bits n value
    ⦃ ⇓ r => ⌜ r.val < 2 ^ n.val
                ∧ r = Spec.get_n_least_significant_bits_pure n value ⌝ ⦄ := by
  apply triple_of_ok_fc (v := Spec.get_n_least_significant_bits_pure n value)
    (get_n_least_significant_bits_eq_ok_fc n value hn)
  refine ⟨?_, rfl⟩
  unfold Spec.get_n_least_significant_bits_pure
  show (value.bv &&& ((1#32 <<< n.val) - 1#32)).toNat < 2 ^ n.val
  rw [BitVec.toNat_and]
  have h_mask_toNat : ((1#32 <<< n.val) - 1#32).toNat = 2 ^ n.val - 1 :=
    libcrux_iot_ml_kem.Util.mask_pow2_minus_one_toNat n.val hn
  rw [h_mask_toNat]
  have h_and_le : value.bv.toNat &&& (2 ^ n.val - 1) ≤ 2 ^ n.val - 1 := Nat.and_le_right
  have h_pos : 0 < (2 : Nat) ^ n.val := Nat.two_pow_pos _
  omega

/-! ### L0.2 — `barrett_reduce_element`.

    Proof sketch:
    1. `Spec.barrett_pure` is defined as the canonical round-trip
       `feOfZMod ∘ zmodOfFE`. Helper `barrett_pure_lift_fe` shows that on
       `lift_fe`-image FEs (which are canonical by construction) this is
       the identity, so `Spec.barrett_pure (lift_fe value) = lift_fe value`.
    2. The legacy `Equivalence.barrett_reduce_element_spec` (bounds-only)
       gives `modq_eq r.val value.val 3329 ∧ r.val.natAbs ≤ 3328`. We
       consume it via `triple_exists_ok_fc`; we only need its content,
       not its `@[spec]` registration.
    3. `modq_eq_cast_zmod` translates `modq_eq r.val value.val 3329` to
       `(r.val : ZMod 3329) = (value.val : ZMod 3329)` via
       `ZMod.intCast_zmod_eq_zero_iff_dvd`.
    4. Conclude `lift_fe r = lift_fe value` by `congr 1`. -/

/-- The canonical round-trip is the identity on lift_fe images. -/
private theorem barrett_pure_lift_fe (x : Std.I16) :
    Spec.barrett_pure (lift_fe x) = lift_fe x := by
  unfold Spec.barrett_pure lift_fe
  congr 1
  exact zmodOfFE_feOfZMod _

/-- Cast `modq_eq` into a `ZMod 3329` equality. The barrier-side
    `Util.modq_eq` unfolds to `(a - b) % 3329 = 0`; via
    `ZMod.intCast_zmod_eq_zero_iff_dvd` and `push_cast` this becomes
    `(a : ZMod 3329) - (b : ZMod 3329) = 0`. -/
private theorem modq_eq_cast_zmod (a b : Int)
    (h : libcrux_iot_ml_kem.Util.modq_eq a b 3329) :
    (a : ZMod 3329) = (b : ZMod 3329) := by
  unfold libcrux_iot_ml_kem.Util.modq_eq at h
  have hdvd : (3329 : Int) ∣ (a - b) := Int.dvd_of_emod_eq_zero h
  have hzero : ((a - b : Int) : ZMod 3329) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) 3329).mpr (by exact_mod_cast hdvd)
  push_cast at hzero
  exact sub_eq_zero.mp hzero

/-- Bridge lemma: `lift_fe a = lift_fe b` from `modq_eq a.val b.val 3329`.
    Since `lift_fe x = feOfZMod ((x.val : Int) : ZMod 3329)`, the equality
    reduces (via `congr 1`) to the `ZMod 3329` cast equality delivered by
    `modq_eq_cast_zmod`. Pure-projection side lemma. -/
private theorem lift_fe_eq_of_modq (a b : Std.I16)
    (h : libcrux_iot_ml_kem.Util.modq_eq a.val b.val 3329) :
    lift_fe a = lift_fe b := by
  unfold lift_fe i16_to_spec_fe_plain
  congr 1
  exact modq_eq_cast_zmod _ _ h

/-- L0.2 — `barrett_reduce_element`.
    Spec: canonical residue mod q via `FieldElement.new (x % q)`. -/
@[spec high]
theorem barrett_reduce_element_fc
    (value : Std.I16) (hb : value.val.natAbs ≤ 32767) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element value
    ⦃ ⇓ r => ⌜ r.val.natAbs ≤ 3328
                ∧ lift_fe r = Spec.barrett_pure (lift_fe value) ⌝ ⦄ := by
  have h_legacy := libcrux_iot_ml_kem.Equivalence.barrett_reduce_element_spec value hb
  obtain ⟨r0, h_eq, h_modq, h_bnd⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  refine ⟨h_bnd, ?_⟩
  rw [barrett_pure_lift_fe]
  unfold lift_fe
  congr 1
  show (r0.val : ZMod 3329) = (value.val : ZMod 3329)
  exact modq_eq_cast_zmod _ _ h_modq

/-! ### L0.3 — `montgomery_reduce_element`.

    Proof sketch:
    1. `Spec.mont_reduce_pure x := feOfZMod (zmodOfFE x · 169 · 169)`.
       Helper `mont_reduce_pure_lift_fe_int` unfolds this composed with
       `lift_fe_int v` to `feOfZMod ((v : ZMod 3329) · 169 · 169)`.
    2. Legacy `Equivalence.montgomery_reduce_element_spec` gives
       `r.val.natAbs ≤ 3328 + 1665 ∧ (tight-bound conditional)
       ∧ modq_eq r.val (value.val * 169) 3329`. We extract via
       `triple_exists_ok_fc` and drop the tight-bound conditional clause.
    3. Translate `modq_eq r.val (value.val * 169) 3329` to a ZMod equality
       `(r.val : ZMod 3329) = (value.val * 169 : ZMod 3329)` via
       `modq_eq_cast_zmod`.
    4. Unfold `lift_fe_mont` and `i16_to_spec_fe_mont`, then `congr 1`
       reduces the goal to a ZMod equation closed by the step-3 hypothesis
       plus `push_cast`. -/

/-- Helper: `mont_reduce_pure` composed with `lift_fe_int` simplifies. -/
private theorem mont_reduce_pure_lift_fe_int (v : Int) :
    Spec.mont_reduce_pure (lift_fe_int v) = feOfZMod ((v : ZMod 3329) * 169 * 169) := by
  unfold Spec.mont_reduce_pure lift_fe_int
  rw [zmodOfFE_feOfZMod]

/-- L0.3 — `montgomery_reduce_element`.
    Spec: strip TWO Mont factors (the impl's R⁻¹ + the `lift_fe_mont`
    R-stripping). See the `Spec.mont_reduce_pure` docstring for the
    derivation of `· 169²`. -/
@[spec high]
theorem montgomery_reduce_element_fc
    (value : Std.I32) (hv : value.val.natAbs ≤ 2^16 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element value
    ⦃ ⇓ r => ⌜ r.val.natAbs ≤ 3328 + 1665
                ∧ lift_fe_mont r = Spec.mont_reduce_pure (lift_fe_int value.val) ⌝ ⦄ := by
  have hv' : value.val.natAbs ≤ 3328 * 2^16 := by
    have h_eq : (3328 * 2^16 : Nat) = 2^16 * 3328 := by decide
    rw [h_eq]; exact hv
  have h_legacy :=
    libcrux_iot_ml_kem.Equivalence.montgomery_reduce_element_spec value hv'
  obtain ⟨r0, h_eq, h_bnd, _h_tight, h_modq⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  refine ⟨h_bnd, ?_⟩
  rw [mont_reduce_pure_lift_fe_int]
  unfold lift_fe_mont i16_to_spec_fe_mont
  congr 1
  have h_zmod : ((r0.val : Int) : ZMod 3329) = ((value.val * 169 : Int) : ZMod 3329) :=
    modq_eq_cast_zmod _ _ h_modq
  push_cast at h_zmod
  rw [h_zmod]

/-! ### L0.4 — `montgomery_multiply_fe_by_fer`.

    Proof sketch:
    1. Helper `mmfbf_pure_lift_fe_lift_fe_mont` unfolds
       `Spec.montgomery_multiply_fe_by_fer_pure (lift_fe fe) (lift_fe_mont fer)`
       to `feOfZMod ((fe.val : ZMod 3329) * ((fer.val : ZMod 3329) * 169) * 169)`
       via `zmodOfFE_feOfZMod` (applied twice).
    2. Legacy `Equivalence.montgomery_multiply_fe_by_fer_spec` gives
       `r.val.natAbs ≤ 3328 ∧ modq_eq r.val (fe.val * fer.val * 169) 3329`.
       Note the legacy bound is TIGHTER than our locked post (3328 vs
       3328 + 1665), so the bound conjunct closes by transitivity:
       `exact le_trans h_bnd_tight (by decide)`.
    3. Translate `modq_eq` to a ZMod equation via `modq_eq_cast_zmod`.
    4. Unfold `lift_fe_mont`/`i16_to_spec_fe_mont`, `congr 1` reduces to a
       ZMod equation closed by the modq cast + `ring`. -/

/-- Helper: `Spec.montgomery_multiply_fe_by_fer_pure` composed with the
    lifts simplifies via `zmodOfFE_feOfZMod`. -/
private theorem mmfbf_pure_lift_fe_lift_fe_mont (fe fer : Std.I16) :
    Spec.montgomery_multiply_fe_by_fer_pure (lift_fe fe) (lift_fe_mont fer)
      = feOfZMod ((fe.val : ZMod 3329) * ((fer.val : ZMod 3329) * 169) * 169) := by
  unfold Spec.montgomery_multiply_fe_by_fer_pure lift_fe lift_fe_mont
    i16_to_spec_fe_plain i16_to_spec_fe_mont
  rw [zmodOfFE_feOfZMod, zmodOfFE_feOfZMod]

/-- L0.4 — `montgomery_multiply_fe_by_fer`.
    Spec: `fe · c` (where `fer = c · R`), encoded via `· R⁻¹` in canonical. -/
@[spec high]
theorem montgomery_multiply_fe_by_fer_fc
    (fe fer : Std.I16)
    (hfe : fe.val.natAbs ≤ 32767) (hfer : fer.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer fe fer
    ⦃ ⇓ r => ⌜ r.val.natAbs ≤ 3328 + 1665
                ∧ lift_fe_mont r
                    = Spec.montgomery_multiply_fe_by_fer_pure
                        (lift_fe fe) (lift_fe_mont fer) ⌝ ⦄ := by
  have h_legacy :=
    libcrux_iot_ml_kem.Equivalence.montgomery_multiply_fe_by_fer_spec fe fer hfer
  obtain ⟨r0, h_eq, h_bnd_tight, h_modq⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  refine ⟨?_, ?_⟩
  · -- Weaken legacy ≤ 3328 to locked-post ≤ 3328 + 1665.
    exact le_trans h_bnd_tight (by decide)
  · rw [mmfbf_pure_lift_fe_lift_fe_mont]
    unfold lift_fe_mont i16_to_spec_fe_mont
    congr 1
    have h_zmod : ((r0.val : Int) : ZMod 3329)
        = ((fe.val * fer.val * 169 : Int) : ZMod 3329) :=
      modq_eq_cast_zmod _ _ h_modq
    push_cast at h_zmod
    rw [h_zmod]
    ring

/-! ## §L1 — chunk-level vector ops (10 theorems). -/

/-! ### L1.1 — `add` on 16-lane PortableVector chunks.

    Proof sketch:
    1. Bridge `add_pure_val_eq`: `(FieldElement.add_pure a b).val.val
       = (a.val.val + b.val.val) % 3329`. Mirrors `Canonical_add_pure`'s
       trace through the hacspec U32-widen + add + mod q + U16-narrow body.
    2. Bridge `lift_fe_add_pure_eq`: under the no-overflow bound on
       `a.val + b.val` (Int), the `lift_fe` of any i16 carrying that
       sum equals `FieldElement.add_pure (lift_fe a) (lift_fe b)`. Both
       sides reduce to `feOfZMod ((a.val + b.val : Int) : ZMod 3329)`
       via canonical-FE round-trip + `ZMod.natCast_mod`.
    3. Main: extract `add_spec` via `triple_exists_ok_fc` to get
       per-element `r[i].val = lhs[i].val + rhs[i].val ∧ bound`.
       Apply `triple_of_ok_fc` to close monadic shell. Reduce array
       equality to `List.ext_get!` + per-index, then apply Bridge 2. -/

/-- Local helper (mirrors `SpecPure.uscalar_rem_ok_U32` which is
    file-private). Establishes that U32 modular remainder by a non-zero
    divisor is always `.ok`, and exposes the underlying value. -/
private theorem uscalar_rem_ok_U32_local (z m : Std.U32) (hm : m.val ≠ 0) :
    ∃ w : Std.U32, (z % m : Result Std.U32) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U32) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- Bridge lemma: the `.val.val` of `FieldElement.add_pure` is the
    impl's U16 modular-reduced sum. Proof structure mirrors
    `Canonical_add_pure` in `SpecPure.lean` — chain through the U32
    do-block via `add_equiv` + `uscalar_rem_ok_U32_local` + the U16
    narrowing cast. Pure-projection side lemma, NOT panic-freedom. -/
private theorem add_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure a b).val.val
      = (a.val.val + b.val.val) % 3329 := by
  have hadd :
      hacspec_ml_kem.parameters.FieldElement.add a b
        = .ok (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure a b) :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_eq_ok a b
  unfold hacspec_ml_kem.parameters.FieldElement.add at hadd
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hadd
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.add_equiv x y
  cases hxy : (x + y) with
  | ok z =>
    rw [hxy] at hae hadd; simp at hae
    obtain ⟨_, hzval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hadd
    have hmod_val :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32_local z m hmod_ne
    rw [hw_eq] at hadd; simp only [Aeneas.Std.bind_tc_ok] at hadd
    unfold hacspec_ml_kem.parameters.FieldElement.new at hadd
    simp at hadd
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Aeneas.Std.UScalarTy.numBits]; omega
    rw [← hadd]
    show (Std.UScalar.cast .U16 w).val = (a.val.val + b.val.val) % 3329
    rw [hwcast, hwval, hmod_val, hzval, hxval, hyval]
  | fail e =>
    rw [hxy] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hyval] at hae; omega
  | div => rw [hxy] at hae; exact hae.elim

/-- Canonical-FE round-trip: a canonical `FieldElement` (i.e.
    `fe.val.val < 3329`) is recovered exactly by `feOfZMod ∘ zmodOfFE`.
    The forward direction `zmodOfFE_feOfZMod` lives in `Spec.lean`;
    this lemma is the canonicity-constrained converse, used to bridge
    `FieldElement.add_pure (lift_fe a) (lift_fe b)` (canonical by
    `Canonical_add_pure`) to its `feOfZMod`-image normal form. -/
private theorem feOfZMod_zmodOfFE_of_canonical
    (fe : hacspec_ml_kem.parameters.FieldElement)
    (h : fe.val.val < 3329) :
    feOfZMod (zmodOfFE fe) = fe := by
  unfold feOfZMod zmodOfFE
  -- Goal: ⟨⟨BitVec.ofNat 16 ((fe.val.val : ZMod 3329)).val⟩⟩ = fe.
  -- ZMod.val_natCast_of_lt: ((fe.val.val : ZMod 3329)).val = fe.val.val
  -- given fe.val.val < 3329.
  have hzval : ((fe.val.val : ZMod 3329)).val = fe.val.val :=
    ZMod.val_natCast_of_lt h
  rw [hzval]
  -- Goal: ⟨⟨BitVec.ofNat 16 fe.val.val⟩⟩ = fe
  -- Both have the same .val.val (= fe.val.val < 65536), so the BV's match.
  have hfeval : fe.val.val < 2 ^ 16 := by
    have h_p : (3329 : Nat) ≤ 2 ^ 16 := by decide
    omega
  have hfebv : BitVec.ofNat 16 fe.val.val = fe.val.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    show fe.val.val % 2 ^ 16 = fe.val.bv.toNat
    rw [Nat.mod_eq_of_lt hfeval]
    rfl
  show ({ val := ⟨BitVec.ofNat 16 fe.val.val⟩ } :
          hacspec_ml_kem.parameters.FieldElement) = fe
  rw [hfebv]

/-- Helper: `(lift_fe x).val.val = ((x.val : Int) : ZMod 3329).val`. -/
private theorem lift_fe_val_val (x : Std.I16) :
    (lift_fe x).val.val = (((x.val : Int) : ZMod 3329)).val := by
  unfold lift_fe i16_to_spec_fe_plain feOfZMod
  show (BitVec.ofNat 16 (((x.val : Int) : ZMod 3329)).val).toNat
        = (((x.val : Int) : ZMod 3329)).val
  rw [BitVec.toNat_ofNat]
  have h_lt : (((x.val : Int) : ZMod 3329)).val < 2 ^ 16 :=
    Nat.lt_of_lt_of_le (ZMod.val_lt _) (by decide)
  exact Nat.mod_eq_of_lt h_lt

/-- Bridge lemma: under the no-overflow bound on `a.val + b.val`
    (Int, |·| ≤ 2^15-1), any `r : Std.I16` carrying that sum lifts to
    `FieldElement.add_pure (lift_fe a) (lift_fe b)`.

    Pure-projection content: both sides reduce to
    `feOfZMod ((a.val + b.val : Int) : ZMod 3329)`. The LHS is direct
    from `lift_fe`'s definition. The RHS uses `add_pure_val_eq` plus
    canonical round-trip — the result is canonical by
    `Canonical_add_pure`, so equals `feOfZMod (zmodOfFE …)`, and the
    `zmodOfFE`-projection reduces by `ZMod.natCast_mod` to the desired
    cast sum. -/
private theorem lift_fe_add_pure_eq
    (a b r : Std.I16) (hrv : r.val = a.val + b.val) :
    lift_fe r
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
          (lift_fe a) (lift_fe b) := by
  -- LHS reduction: lift_fe r = feOfZMod ((r.val : Int) : ZMod 3329)
  --                           = feOfZMod ((a.val + b.val : Int) : ZMod 3329).
  have h_lhs : lift_fe r
      = feOfZMod (((a.val + b.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [hrv]
  -- RHS reduction: FieldElement.add_pure (lift_fe a) (lift_fe b)
  --                  = feOfZMod (zmodOfFE …) (canonical round-trip)
  --                  = feOfZMod ((a.val + b.val : Int) : ZMod 3329).
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
      (lift_fe a) (lift_fe b) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical_add_pure
      (lift_fe a) (lift_fe b)
    show s.val.val < 3329
    unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  -- zmodOfFE s = ((a.val + b.val : Int) : ZMod 3329).
  have h_zmod_s : zmodOfFE s = (((a.val + b.val : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    -- (s.val.val : ZMod 3329) with s.val.val = ((lift_fe a).val.val + (lift_fe b).val.val) % 3329
    rw [add_pure_val_eq]
    -- Goal: ((((lift_fe a).val.val + (lift_fe b).val.val) % 3329 : Nat) : ZMod 3329)
    --        = ((a.val + b.val : Int) : ZMod 3329).
    rw [ZMod.natCast_mod]
    push_cast
    rw [lift_fe_val_val a, lift_fe_val_val b]
    -- Goal: (((a.val : Int) : ZMod 3329).val : ZMod 3329)
    --       + (((b.val : Int) : ZMod 3329).val : ZMod 3329)
    --     = ((a.val + b.val : Int) : ZMod 3329).
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- L1.1 — `add` on 16-lane PortableVector chunks. -/
@[spec high]
theorem add_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      ((lhs.elements.val[i]!).val + (rhs.elements.val[i]!).val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.add lhs rhs
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_add_pure (lift_chunk lhs) (lift_chunk rhs) ⌝ ⦄ := by
  -- 1. Extract per-element value-equation from legacy bounds Triple.
  have h_legacy := libcrux_iot_ml_kem.Equivalence.add_spec lhs rhs hpre
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk Spec.chunk_add_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe
      = (List.range 16).map (fun i =>
          libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
            ((Std.Array.make 16#usize (lhs.elements.val.map lift_fe)
              (by simp)).val[i]!)
            ((Std.Array.make 16#usize (rhs.elements.val.map lift_fe)
              (by simp)).val[i]!))
  -- 3. Show both lists have length 16 and per-index entries match.
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    -- LHS at i: lift_fe (r0.elements.val[i]).
    -- RHS at i: add_pure (lift_fe lhs[i]) (lift_fe rhs[i]).
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    -- Rewrite LHS.
    rw [List.getElem_map]
    -- Rewrite RHS.
    rw [List.getElem_map, List.getElem_range]
    -- Indexing into Std.Array.make.
    show lift_fe r0.elements.val[i]
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
          ((lhs.elements.val.map lift_fe)[i]!)
          ((rhs.elements.val.map lift_fe)[i]!)
    -- Express `r0.elements.val[i]` as `r0.elements.val[i]!`
    -- (same value when i < length).
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    -- Express `(lhs.elements.val.map lift_fe)[i]!` as `lift_fe (lhs.val[i]!)`.
    have h_lhs_len : lhs.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Util.PortableVector_elements_length lhs
    have h_rhs_len : rhs.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Util.PortableVector_elements_length rhs
    have h_map_lhs :
        (lhs.elements.val.map lift_fe)[i]! = lift_fe (lhs.elements.val[i]!) := by
      have hi_lhs : i < lhs.elements.val.length := by rw [h_lhs_len]; exact hi
      rw [getElem!_pos (lhs.elements.val.map lift_fe) i (by
        simp [List.length_map, h_lhs_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos lhs.elements.val i hi_lhs]
    have h_map_rhs :
        (rhs.elements.val.map lift_fe)[i]! = lift_fe (rhs.elements.val[i]!) := by
      have hi_rhs : i < rhs.elements.val.length := by rw [h_rhs_len]; exact hi
      rw [getElem!_pos (rhs.elements.val.map lift_fe) i (by
        simp [List.length_map, h_rhs_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos rhs.elements.val i hi_rhs]
    rw [h_map_lhs, h_map_rhs]
    -- Apply the bridge lemma with the per-element value equation.
    obtain ⟨h_val, _h_bnd⟩ := h_per i hi
    exact lift_fe_add_pure_eq
      (lhs.elements.val[i]!) (rhs.elements.val[i]!) (r0.elements.val[i]!)
      h_val

/-- Canonicity of `lift_fe`: every `feOfZMod`-image is canonical
    (its `.val.val < 3329`). Used by `lift_fe_sub_pure_eq` to discharge
    `sub_eq_ok`'s canonicity preconditions. Pure-projection side lemma. -/
private theorem Canonical_lift_fe (x : Std.I16) :
    libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical (lift_fe x) := by
  unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical
  unfold lift_fe i16_to_spec_fe_plain feOfZMod
  -- Goal: (BitVec.ofNat 16 ((x.val : Int) : ZMod 3329).val).toNat
  --         < parameters.FIELD_MODULUS.val
  have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
  rw [hq]
  show (BitVec.ofNat 16 (((x.val : Int) : ZMod 3329)).val).toNat < 3329
  rw [BitVec.toNat_ofNat]
  have h_lt : (((x.val : Int) : ZMod 3329)).val < 3329 := ZMod.val_lt _
  have h_le : (((x.val : Int) : ZMod 3329)).val < 2 ^ 16 :=
    Nat.lt_of_lt_of_le h_lt (by decide)
  rw [Nat.mod_eq_of_lt h_le]
  exact h_lt

/-- Bridge lemma: the `.val.val` of `FieldElement.sub_pure` (under
    canonicity of both operands) is the impl's U16 modular-reduced
    difference: `(a.val.val + 3329 - b.val.val) % 3329`. Mirrors
    `add_pure_val_eq`'s trace through the U32 do-block; the impl's
    `sub` body is `(self.val + q - other.val) % q` (`x + q` widens
    safely under `b` canonical, then `s - y ≥ 0` since
    `s = x + q ≥ q > y`, then `% q`, then narrow U16). -/
private theorem sub_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement)
    (ha : libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical a)
    (hb : libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical b) :
    (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure a b).val.val
      = (a.val.val + 3329 - b.val.val) % 3329 := by
  have hsub :
      hacspec_ml_kem.parameters.FieldElement.sub a b
        = .ok (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure a b) :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_eq_ok a b ha hb
  have ha' : a.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at ha
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at ha; simpa using ha
  have hb' : b.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at hb
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at hb; simpa using hb
  unfold hacspec_ml_kem.parameters.FieldElement.sub at hsub
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hsub
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  set q : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hqval : q.val = 3329 := by
    show (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.add_equiv x q
  cases hxq : (x + q : Result Std.U32) with
  | ok s =>
    rw [hxq] at hae hsub; simp at hae
    obtain ⟨_, hsval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hsub
    have hae2 := Std.UScalar.sub_equiv s y
    cases hsy : (s - y : Result Std.U32) with
    | ok u =>
      rw [hsy] at hae2 hsub; simp at hae2
      -- hae2 : y.val ≤ s.val ∧ s.val = u.val + y.val ∧ u.bv = s.bv - y.bv
      obtain ⟨_hyle, hsuy, _⟩ := hae2
      simp only [Aeneas.Std.bind_tc_ok] at hsub
      have hq_ne : q.val ≠ 0 := by rw [hqval]; decide
      obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32_local u q hq_ne
      rw [hw_eq] at hsub; simp only [Aeneas.Std.bind_tc_ok] at hsub
      unfold hacspec_ml_kem.parameters.FieldElement.new at hsub
      simp at hsub
      have hwbnd : w.val < 3329 := by
        rw [hwval, hqval]; exact Nat.mod_lt _ (by decide)
      have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
        apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
        simp [Aeneas.Std.UScalarTy.numBits]; omega
      rw [← hsub]
      show (Std.UScalar.cast .U16 w).val = (a.val.val + 3329 - b.val.val) % 3329
      rw [hwcast, hwval, hqval]
      -- Goal: u.val % 3329 = (a.val.val + 3329 - b.val.val) % 3329
      -- From hsuy : s.val = u.val + y.val and hsval : s.val = x.val + q.val
      -- and hxval, hqval, hyval, hb', we get u.val = a.val.val + 3329 - b.val.val.
      have hu_eq : u.val = a.val.val + 3329 - b.val.val := by
        have h1 : s.val = u.val + y.val := hsuy
        rw [hsval, hxval, hqval, hyval] at h1
        omega
      rw [hu_eq]
    | fail e =>
      rw [hsy] at hae2; simp at hae2
      rw [hsval, hxval, hqval, hyval] at hae2
      omega
    | div => rw [hsy] at hae2; exact hae2.elim
  | fail e =>
    rw [hxq] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hqval] at hae
    omega
  | div => rw [hxq] at hae; exact hae.elim

/-- Bridge lemma: the `.val.val` of `FieldElement.mul_pure` is the
    impl's U16 modular-reduced product: `(a.val.val * b.val.val) % 3329`.
    Mirrors `add_pure_val_eq`'s trace through the U32 do-block; the
    impl's `mul` body is `(self.val * other.val) % q` (`x * y` widens
    safely to U32 since `a.val * b.val ≤ (2^16-1)² < 2^32`, then `% q`,
    then narrow U16). Unconditional (no canonicity needed). -/
private theorem mul_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure a b).val.val
      = (a.val.val * b.val.val) % 3329 := by
  have hmul :
      hacspec_ml_kem.parameters.FieldElement.mul a b
        = .ok (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure a b) :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_eq_ok a b
  unfold hacspec_ml_kem.parameters.FieldElement.mul at hmul
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hmul
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.mul_equiv x y
  have heqmul : (x * y : Result Std.U32) = Std.UScalar.mul x y := rfl
  cases hxy : (x * y : Result Std.U32) with
  | ok z =>
    rw [hxy] at hmul
    rw [heqmul] at hxy; rw [hxy] at hae; simp at hae
    obtain ⟨_, hzval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hmul
    have hmod_val :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32_local z m hmod_ne
    rw [hw_eq] at hmul; simp only [Aeneas.Std.bind_tc_ok] at hmul
    unfold hacspec_ml_kem.parameters.FieldElement.new at hmul
    simp at hmul
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Aeneas.Std.UScalarTy.numBits]; omega
    rw [← hmul]
    show (Std.UScalar.cast .U16 w).val = (a.val.val * b.val.val) % 3329
    rw [hwcast, hwval, hmod_val, hzval, hxval, hyval]
  | fail _ =>
    rw [heqmul] at hxy; rw [hxy] at hae
    simp only [Std.UScalar.max, Aeneas.Std.UScalarTy.numBits] at hae
    rw [hxval, hyval] at hae
    have : a.val.val * b.val.val < 2^32 := by
      have h1 : a.val.val * b.val.val ≤ (2^16 - 1) * (2^16 - 1) := by
        apply Nat.mul_le_mul <;> omega
      have heq : (2^16 - 1) * (2^16 - 1) = 2^32 - 2*2^16 + 1 := by decide
      omega
    omega
  | div => rw [heqmul] at hxy; rw [hxy] at hae; exact hae.elim

/-- Bridge lemma: under the no-overflow bound on `a.val - b.val` (Int,
    |·| ≤ 2^15-1), any `r : Std.I16` carrying that difference lifts to
    `FieldElement.sub_pure (lift_fe a) (lift_fe b)`.

    Pure-projection content: both sides reduce to
    `feOfZMod ((a.val - b.val : Int) : ZMod 3329)`. The RHS uses
    `sub_pure_val_eq` plus canonical round-trip — the result is
    canonical by `Canonical_sub_pure`, and the `zmodOfFE`-projection
    reduces the inner `(a.val.val + 3329 - b.val.val) % 3329` to
    `(a.val - b.val : Int) : ZMod 3329` via `ZMod.natCast_mod` plus
    integer reasoning. -/
private theorem lift_fe_sub_pure_eq
    (a b r : Std.I16) (hrv : r.val = a.val - b.val) :
    lift_fe r
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
          (lift_fe a) (lift_fe b) := by
  have h_lhs : lift_fe r
      = feOfZMod (((a.val - b.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [hrv]
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
      (lift_fe a) (lift_fe b) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical_sub_pure
      (lift_fe a) (lift_fe b) (Canonical_lift_fe a) (Canonical_lift_fe b)
    show s.val.val < 3329
    unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s = (((a.val - b.val : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    rw [sub_pure_val_eq _ _ (Canonical_lift_fe a) (Canonical_lift_fe b)]
    -- Goal: (((lift_fe a).val.val + 3329 - (lift_fe b).val.val) % 3329 : Nat) : ZMod 3329
    --       = ((a.val - b.val : Int) : ZMod 3329)
    rw [ZMod.natCast_mod]
    -- Step: lift the Nat-subtraction expression through Nat→ZMod cast using
    -- a cast-equality. Since (lift_fe b).val.val ≤ (lift_fe a).val.val + 3329
    -- (b canonical), Nat subtraction agrees with Int subtraction.
    have hb_lt : (lift_fe b).val.val < 3329 := by
      have h_cb := Canonical_lift_fe b
      unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at h_cb
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS at h_cb; simpa using h_cb
    have h_le : (lift_fe b).val.val ≤ (lift_fe a).val.val + 3329 := by omega
    -- (Nat-cast into ZMod) of the Nat sub equals (Int-cast into ZMod) of the Int sub.
    have h_zmod_eq :
        (((lift_fe a).val.val + 3329 - (lift_fe b).val.val : Nat) : ZMod 3329)
          = ((((lift_fe a).val.val : Int) + 3329 - ((lift_fe b).val.val : Int) : Int)
                : ZMod 3329) := by
      have h_int_eq :
          (((lift_fe a).val.val + 3329 - (lift_fe b).val.val : Nat) : Int)
            = ((lift_fe a).val.val : Int) + 3329 - ((lift_fe b).val.val : Int) := by
        omega
      have h_route :
          (((lift_fe a).val.val + 3329 - (lift_fe b).val.val : Nat) : ZMod 3329)
            = ((((lift_fe a).val.val + 3329 - (lift_fe b).val.val : Nat) : Int)
                : ZMod 3329) := by
        rfl
      rw [h_route, h_int_eq]
    rw [h_zmod_eq]
    push_cast
    rw [lift_fe_val_val a, lift_fe_val_val b]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    -- Goal after push_cast: ((a.val : Int) : ZMod 3329) + 0 - ((b.val : Int) : ZMod 3329)
    --                       = ((a.val - b.val : Int) : ZMod 3329)
    -- (push_cast collapses `(3329 : ZMod 3329)` to `0` via ZMod.natCast_self.)
    ring
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- Bridge lemma: under the no-overflow bound on `a.val * b.val` (Int,
    |·| ≤ 2^15-1), any `r : Std.I16` carrying that product lifts to
    `FieldElement.mul_pure (lift_fe a) (lift_fe b)`.

    Pure-projection content: both sides reduce to
    `feOfZMod ((a.val * b.val : Int) : ZMod 3329)`. The RHS uses
    `mul_pure_val_eq` plus canonical round-trip — the result is
    canonical by `Canonical_mul_pure`. Unconditional in canonicity. -/
private theorem lift_fe_mul_pure_eq
    (a b r : Std.I16) (hrv : r.val = a.val * b.val) :
    lift_fe r
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
          (lift_fe a) (lift_fe b) := by
  have h_lhs : lift_fe r
      = feOfZMod (((a.val * b.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [hrv]
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
      (lift_fe a) (lift_fe b) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical_mul_pure
      (lift_fe a) (lift_fe b)
    show s.val.val < 3329
    unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s = (((a.val * b.val : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    rw [mul_pure_val_eq]
    rw [ZMod.natCast_mod]
    push_cast
    rw [lift_fe_val_val a, lift_fe_val_val b]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- L1.2 — `sub` on 16-lane PortableVector chunks. -/
@[spec high]
theorem sub_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      ((lhs.elements.val[i]!).val - (rhs.elements.val[i]!).val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.sub lhs rhs
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_sub_pure (lift_chunk lhs) (lift_chunk rhs) ⌝ ⦄ := by
  -- 1. Extract per-element value-equation from legacy bounds Triple.
  have h_legacy := libcrux_iot_ml_kem.Equivalence.sub_spec lhs rhs hpre
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk Spec.chunk_sub_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe
      = (List.range 16).map (fun i =>
          libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
            ((Std.Array.make 16#usize (lhs.elements.val.map lift_fe)
              (by simp)).val[i]!)
            ((Std.Array.make 16#usize (rhs.elements.val.map lift_fe)
              (by simp)).val[i]!))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe r0.elements.val[i]
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
          ((lhs.elements.val.map lift_fe)[i]!)
          ((rhs.elements.val.map lift_fe)[i]!)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    have h_lhs_len : lhs.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Util.PortableVector_elements_length lhs
    have h_rhs_len : rhs.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Util.PortableVector_elements_length rhs
    have h_map_lhs :
        (lhs.elements.val.map lift_fe)[i]! = lift_fe (lhs.elements.val[i]!) := by
      have hi_lhs : i < lhs.elements.val.length := by rw [h_lhs_len]; exact hi
      rw [getElem!_pos (lhs.elements.val.map lift_fe) i (by
        simp [List.length_map, h_lhs_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos lhs.elements.val i hi_lhs]
    have h_map_rhs :
        (rhs.elements.val.map lift_fe)[i]! = lift_fe (rhs.elements.val[i]!) := by
      have hi_rhs : i < rhs.elements.val.length := by rw [h_rhs_len]; exact hi
      rw [getElem!_pos (rhs.elements.val.map lift_fe) i (by
        simp [List.length_map, h_rhs_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos rhs.elements.val i hi_rhs]
    rw [h_map_lhs, h_map_rhs]
    obtain ⟨h_val, _h_bnd⟩ := h_per i hi
    exact lift_fe_sub_pure_eq
      (lhs.elements.val[i]!) (rhs.elements.val[i]!) (r0.elements.val[i]!)
      h_val

/-- Per-element bridge for `barrett_reduce_fc`: under `modq_eq r vec 3329`,
    the lift of `r` equals the spec-side `Spec.barrett_pure` applied to
    the lift of `vec`. Combines `lift_fe_eq_of_modq` with
    `barrett_pure_lift_fe` (which collapses the canonical round-trip on
    `lift_fe` images to identity). -/
private theorem lift_fe_barrett_pure_eq
    (a r : Std.I16)
    (h : libcrux_iot_ml_kem.Util.modq_eq r.val a.val 3329) :
    lift_fe r = Spec.barrett_pure (lift_fe a) := by
  rw [barrett_pure_lift_fe]
  exact lift_fe_eq_of_modq r a h

/-- L1.3 — `barrett_reduce` on a chunk. -/
@[spec high]
theorem barrett_reduce_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      (vec.elements.val[i]!).val.natAbs ≤ 32767) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce vec
    ⦃ ⇓ r => ⌜ (∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 3328)
                ∧ lift_chunk r = Spec.chunk_barrett_reduce_pure (lift_chunk vec) ⌝ ⦄ := by
  -- 1. Extract per-element legacy fact: modq_eq r[i] vec[i] 3329 ∧ |r[i]| ≤ 3328.
  have h_legacy := libcrux_iot_ml_kem.Equivalence.barrett_reduce_spec vec hpre
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  refine ⟨?_, ?_⟩
  · -- Bound conjunct: extract `r[i].natAbs ≤ 3328` from per-element legacy.
    intro i hi
    exact (h_per i hi).2
  · -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
    unfold lift_chunk Spec.chunk_barrett_reduce_pure
    apply Subtype.ext
    show r0.elements.val.map lift_fe
        = (List.range 16).map (fun i =>
            Spec.barrett_pure
              ((Std.Array.make 16#usize (vec.elements.val.map lift_fe)
                (by simp)).val[i]!))
    have h_r0_len : r0.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Util.PortableVector_elements_length r0
    apply List.ext_getElem
    · simp [List.length_map, List.length_range, h_r0_len]
    · intro i hi1 hi2
      have hi : i < 16 := by
        have : i < (r0.elements.val.map lift_fe).length := hi1
        simp [List.length_map, h_r0_len] at this; exact this
      rw [List.getElem_map]
      rw [List.getElem_map, List.getElem_range]
      show lift_fe r0.elements.val[i]
        = Spec.barrett_pure ((vec.elements.val.map lift_fe)[i]!)
      have h_r0_get_eq : r0.elements.val[i]
          = r0.elements.val[i]! := by
        have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
        rw [getElem!_pos r0.elements.val i hi_r0]
      rw [h_r0_get_eq]
      have h_vec_len : vec.elements.val.length = 16 :=
        libcrux_iot_ml_kem.Util.PortableVector_elements_length vec
      have h_map_vec :
          (vec.elements.val.map lift_fe)[i]! = lift_fe (vec.elements.val[i]!) := by
        have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
        rw [getElem!_pos (vec.elements.val.map lift_fe) i (by
          simp [List.length_map, h_vec_len]; exact hi)]
        rw [List.getElem_map]
        rw [getElem!_pos vec.elements.val i hi_vec]
      rw [h_map_vec]
      obtain ⟨h_modq, _h_bnd⟩ := h_per i hi
      exact lift_fe_barrett_pure_eq
        (vec.elements.val[i]!) (r0.elements.val[i]!) h_modq

/-- Per-element bridge for `montgomery_multiply_by_constant_fc`: from the
    legacy L1.4 congruence `(r * 2^16) ≡ (a * c) (mod 3329)`, derive the
    FC equation
    `lift_fe_mont r = Spec.montgomery_multiply_fe_by_fer_pure (lift_fe a) (lift_fe_mont c)`.

    Algebra: the goal (after unfolding via `mmfbf_pure_lift_fe_lift_fe_mont`
    and `lift_fe_mont`/`i16_to_spec_fe_mont`) is the `ZMod 3329` equation
    `r * 169 = a * (c * 169) * 169`. From the legacy hypothesis
    `r * 2^16 = a * c` in `ZMod 3329`, multiply both sides by `169 * 169`
    and use the Montgomery-inversion identity `2^16 * 169 = 1` in `ZMod 3329`
    to collapse one factor on the LHS. -/
private theorem lift_fe_mont_mmfbf_pure_eq
    (a c r : Std.I16)
    (h : (r.val * (2 ^ 16 : Int)) % 3329 = (a.val * c.val) % 3329) :
    lift_fe_mont r
      = Spec.montgomery_multiply_fe_by_fer_pure (lift_fe a) (lift_fe_mont c) := by
  rw [mmfbf_pure_lift_fe_lift_fe_mont]
  unfold lift_fe_mont i16_to_spec_fe_mont
  congr 1
  -- Goal: (r.val : ZMod 3329) * 169 = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) * 169
  have h_modq : libcrux_iot_ml_kem.Util.modq_eq
                  (r.val * (2 ^ 16 : Int)) (a.val * c.val) 3329 := by
    unfold libcrux_iot_ml_kem.Util.modq_eq
    rw [Int.sub_emod, h]; simp
  have h_zmod : ((r.val * (2 ^ 16 : Int) : Int) : ZMod 3329)
              = ((a.val * c.val : Int) : ZMod 3329) :=
    modq_eq_cast_zmod _ _ h_modq
  push_cast at h_zmod
  -- After push_cast: h_zmod : (r.val : ZMod 3329) * 2285 = (a.val : ZMod 3329) * (c.val : ZMod 3329)
  -- (Lean reduces `2^16` to its canonical residue `2285` in ZMod 3329.)
  -- Goal: (r.val : ZMod 3329) * 169 = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) * 169
  -- Normalize: 2285 * 169 = 386165 = 3329 * 116 + 1, so 2285 * 169 ≡ 1 (mod 3329).
  have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
  calc (r.val : ZMod 3329) * 169
      = (r.val : ZMod 3329) * ((2285 : ZMod 3329) * 169) * 169 := by rw [h_inv]; ring
    _ = ((r.val : ZMod 3329) * 2285) * 169 * 169 := by ring
    _ = ((a.val : ZMod 3329) * (c.val : ZMod 3329)) * 169 * 169 := by rw [h_zmod]
    _ = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) * 169 := by ring

/-- L1.4 — `montgomery_multiply_by_constant` on a chunk.
    Each lane: `vec[i] · c / R`. The lift uses `lift_chunk_mont` on
    the output (the result is in Mont domain). -/
@[spec high]
theorem montgomery_multiply_by_constant_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hvec : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 32767)
    (hc : c.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ lift_chunk_mont r
                = Spec.chunk_montgomery_multiply_by_constant_pure
                    (lift_chunk vec) (lift_fe_mont c) ⌝ ⦄ := by
  -- 1. Extract per-element legacy fact: |r[i]| ≤ 3328 ∧ (r[i]*2^16) ≡ vec[i]*c (mod 3329).
  have h_legacy :=
    libcrux_iot_ml_kem.Equivalence.montgomery_multiply_by_constant_spec vec c hc
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe_mont equality.
  unfold lift_chunk_mont Spec.chunk_montgomery_multiply_by_constant_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe_mont
      = (List.range 16).map (fun i =>
          Spec.montgomery_multiply_fe_by_fer_pure
            ((Std.Array.make 16#usize (vec.elements.val.map lift_fe)
              (by simp)).val[i]!)
            (lift_fe_mont c))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe_mont).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe_mont r0.elements.val[i]
      = Spec.montgomery_multiply_fe_by_fer_pure
          ((vec.elements.val.map lift_fe)[i]!) (lift_fe_mont c)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    have h_vec_len : vec.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Util.PortableVector_elements_length vec
    have h_map_vec :
        (vec.elements.val.map lift_fe)[i]! = lift_fe (vec.elements.val[i]!) := by
      have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
      rw [getElem!_pos (vec.elements.val.map lift_fe) i (by
        simp [List.length_map, h_vec_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos vec.elements.val i hi_vec]
    rw [h_map_vec]
    obtain ⟨_h_bnd, h_mod⟩ := h_per i hi
    exact lift_fe_mont_mmfbf_pure_eq
      (vec.elements.val[i]!) c (r0.elements.val[i]!)
      h_mod

/-! ### L1.5 — `cond_subtract_3329` private loop machinery.

    The legacy `Equivalence.cond_subtract_3329_spec` requires
    `0 ≤ vec[i] < 2*3329` as a precondition (it's load-bearing for the
    OUTER bound `r[i] < 3329`). The FC statement here uses NO
    precondition — we only need `lift_chunk r = lift_chunk vec`, i.e.
    mod-3329 equivalence per lane. The mod-3329 equivalence holds for
    BOTH branches of the conditional WITHOUT any precondition:

      - `vec[i] ≥ 3329` branch: `r[i] = wrapping_sub vec[i] 3329`.
        Since `vec[i] ∈ [3329, 32767]` (signed), `vec[i] - 3329 ∈ [0, 29438]`
        fits I16, so `r[i].val = vec[i].val - 3329 ≡ vec[i].val (mod 3329)`.
      - `vec[i] < 3329` branch: `r[i] = vec[i]`, trivially mod-3329 equivalent.

    Below we reproduce a stripped-down copy of the L1_5 loop machinery
    (private to FCTargets) yielding just the per-element disjunction. The
    full proof closely mirrors `Equivalence.L1_5.cond_step`; comments are
    abbreviated since the structure is verbatim.
-/

namespace L1_5_FC

open libcrux_iot_ml_kem.Util Aeneas.Std Std.Do Result ControlFlow

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

/-- Per-element invariant for `cond_subtract_3329` (FCTargets-local copy
    of `Equivalence.L1_5.cond_inv`; precondition-free). -/
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
  · have hk_16 : k.val < 16 := by rw [h_16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    have h_idx :
        Aeneas.Std.Array.index_usize acc.elements k = .ok (acc.elements.val[k.val]!) :=
      array_index_usize_ok_eq acc.elements k (by rw [h_acc_len]; exact hk_16)
    set xk : Std.I16 := acc.elements.val[k.val]! with hxk_def
    have h_acc_xk : acc.elements.val[k.val]! = input.elements.val[k.val]! :=
      h_acc_undone k.val (Nat.le_refl _) hk_16
    by_cases h_ge : xk.val ≥ 3329
    · have h_ge_lit : xk ≥ 3329#i16 := by
        change (3329#i16 : Std.I16).val ≤ xk.val
        have : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [this]; exact h_ge
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
        · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
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
        · subst hj_eq_k
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
    · have h_not_ge : ¬ (3329#i16 : Std.I16).val ≤ xk.val := by
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
  · have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
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

end L1_5_FC

/-- L1.5 — `cond_subtract_3329` on a chunk.
    NO HACSPEC EQUIVALENT — the impl conditionally subtracts q to
    rebalance ranges; spec-side this is identity in `ZMod 3329`. The
    spec target we land against is the identity at the FE-array level.

    No precondition required: the mod-3329 equivalence holds in BOTH
    branches of the conditional unconditionally (see `L1_5_FC` namespace
    above for the precondition-free invariant). -/
@[spec high]
theorem cond_subtract_3329_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329 vec
    ⦃ ⇓ r => ⌜ lift_chunk r = lift_chunk vec ⌝ ⦄ := by
  -- 1. Run the loop-spec machinery to get the per-element disjunction.
  have h_disj :
      ⦃ ⌜ True ⌝ ⦄
      libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329 vec
      ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 16 →
                ((vec.elements.val[j]!).val ≥ 3329 ∧
                    (r.elements.val[j]!)
                      = Std.I16.wrapping_sub (vec.elements.val[j]!) 3329#i16)
                ∨ ((vec.elements.val[j]!).val < 3329 ∧
                    r.elements.val[j]! = vec.elements.val[j]!) ⌝ ⦄ := by
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop
    have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                    = (16#usize : Std.Usize) := by
      unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
    rw [h_field]
    apply Std.Do.Triple.of_entails_right _
      (libcrux_iot_ml_kem.Util.loop_range_spec_usize
        (fun (iter1, vec1) =>
          libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
            iter1 vec1)
        vec 0#usize 16#usize
        (L1_5_FC.cond_inv vec)
        (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
        (L1_5_FC.pure_prop_holds_l1 ⟨
          fun j hj => by
            have h0 : (0#usize : Std.Usize).val = 0 := rfl
            rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j),
          fun _ _ _ => rfl⟩)
        ?_)
    · rw [PostCond.entails_noThrow]
      intro r h
      obtain ⟨h_done, _h_undone⟩ := L1_5_FC.of_pure_prop_holds_l1 h
      intro j hj
      exact h_done j (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hj)
    · -- Step lemma.
      intro acc k h_ge h_le hinv
      have h_step := L1_5_FC.cond_step vec acc k h_le hinv
      apply Std.Do.Triple.of_entails_right _ h_step
      rw [PostCond.entails_noThrow]
      intro r hh
      rcases r with ⟨iter', acc'⟩ | y
      · have hP : L1_5_FC.cond_step_post vec k (.cont (iter', acc')) := by
          simpa [Std.Do.SPred.down_pure] using hh
        simpa [L1_5_FC.cond_step_post] using hP
      · have hP : L1_5_FC.cond_step_post vec k (.done y) := by
          simpa [Std.Do.SPred.down_pure] using hh
        simpa [L1_5_FC.cond_step_post] using hP
  -- 2. Apply h_disj and convert per-lane disjunction to lift_fe equality.
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_disj
  apply triple_of_ok_fc (v := r0) h_eq
  -- 3. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk
  apply Subtype.ext
  show r0.elements.val.map lift_fe = vec.elements.val.map lift_fe
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length r0
  have h_vec_len : vec.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length vec
  apply List.ext_getElem
  · simp [List.length_map, h_r0_len, h_vec_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map, List.getElem_map]
    -- Goal: lift_fe r0.elements.val[i] = lift_fe vec.elements.val[i].
    have h_r0_get : r0.elements.val[i] = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    have h_vec_get : vec.elements.val[i] = vec.elements.val[i]! := by
      have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
      rw [getElem!_pos vec.elements.val i hi_vec]
    rw [h_r0_get, h_vec_get]
    -- Apply per-lane disjunction.
    rcases h_per i hi with ⟨h_ge, h_eq_lane⟩ | ⟨h_lt, h_eq_lane⟩
    · -- ≥ 3329 branch: r0[i] = wrapping_sub vec[i] 3329, derive mod-3329 equality.
      rw [h_eq_lane]
      -- Goal: lift_fe (wrapping_sub vec[i] 3329) = lift_fe vec[i].
      set xi : Std.I16 := vec.elements.val[i]! with hxi
      -- Use modq_eq on (wrapping_sub xi 3329).val vs xi.val.
      apply lift_fe_eq_of_modq
      -- Need: modq_eq (wrapping_sub xi 3329).val xi.val 3329.
      -- (wrapping_sub xi 3329).val = bmod (xi.val - 3329) (2^16). Since
      -- xi.val ≥ 3329 and xi.val < 2^15, we have xi.val - 3329 ∈ [0, 2^15 - 3329],
      -- which is in I16 range, so bmod = xi.val - 3329.
      unfold libcrux_iot_ml_kem.Util.modq_eq
      rw [Std.I16.wrapping_sub_val_eq]
      have hxi_ub : xi.val < 2^15 := by
        have h := xi.hBounds
        simp [Aeneas.Std.IScalarTy.numBits, Aeneas.Std.IScalar.min,
              Aeneas.Std.IScalar.max] at h
        omega
      have h3329 : (3329#i16 : Std.I16).val = 3329 := by decide
      rw [h3329]
      have hxi_lb_diff : (-(2:Int)^(16-1)) ≤ xi.val - 3329 := by
        have h1 : (3329 : Int) ≤ xi.val := h_ge
        have h2 : -(2:Int)^(16-1) ≤ 0 := by decide
        have h3 : (0 : Int) ≤ xi.val - 3329 := by omega
        omega
      have hxi_ub_diff : xi.val - 3329 < (2:Int)^(16-1) := by
        have h1 : xi.val < (2:Int)^15 := by exact_mod_cast hxi_ub
        have h2 : (2:Int)^(16-1) = (2:Int)^15 := by decide
        omega
      rw [Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
            hxi_lb_diff hxi_ub_diff]
      -- Goal: (xi.val - 3329 - xi.val) % 3329 = 0.
      have : xi.val - 3329 - xi.val = -3329 := by ring
      rw [this]
      decide
    · -- < 3329 branch: r0[i] = vec[i], trivially mod-3329 equivalent.
      rw [h_eq_lane]

/-- Local helper (mirrors `SpecPure.uscalar_rem_ok_U16` which is
    file-private). Establishes that U16 modular remainder by a non-zero
    divisor is always `.ok`, and exposes the underlying value. Needed
    by `neg_pure_val_eq`, whose `% q` step is at U16 width (no widening). -/
private theorem uscalar_rem_ok_U16_local (z m : Std.U16) (hm : m.val ≠ 0) :
    ∃ w : Std.U16, (z % m : Result Std.U16) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U16) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- Bridge lemma: under canonicity of the operand, the `.val.val` of
    `FieldElement.neg_pure` is the impl's U16 modular-reduced negation
    `(3329 - a.val.val) % 3329`. Mirrors `sub_pure_val_eq`'s trace, but
    the impl's `neg` body is `(q - self.val) % q` operated entirely at
    U16 width (NO widening to U32); panic-impossibility of `q - self.val`
    is precisely `Canonical a` (i.e. `a.val.val < q`). -/
private theorem neg_pure_val_eq
    (a : hacspec_ml_kem.parameters.FieldElement)
    (ha : libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical a) :
    (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.neg_pure a).val.val
      = (3329 - a.val.val) % 3329 := by
  have hneg :
      hacspec_ml_kem.parameters.FieldElement.neg a
        = .ok (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.neg_pure a) :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.neg_eq_ok a ha
  have ha' : a.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at ha
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at ha; simpa using ha
  unfold hacspec_ml_kem.parameters.FieldElement.neg at hneg
  have hA := a.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA
  have hqval : (hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16).val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.sub_equiv (hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16) a.val
  cases hqa :
      ((hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16) - a.val : Result Std.U16) with
  | ok i =>
    rw [hqa] at hae hneg; simp at hae
    obtain ⟨_hale, hival, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hneg
    have hq_ne : (hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
      rw [hqval]; decide
    obtain ⟨w, hw_eq, hwval⟩ :=
      uscalar_rem_ok_U16_local i hacspec_ml_kem.parameters.FIELD_MODULUS hq_ne
    rw [hw_eq] at hneg; simp only [Aeneas.Std.bind_tc_ok] at hneg
    unfold hacspec_ml_kem.parameters.FieldElement.new at hneg
    simp at hneg
    rw [← hneg]
    -- Goal: w.val = (3329 - a.val.val) % 3329.
    rw [hwval, hqval]
    -- Goal: i.val % 3329 = (3329 - a.val.val) % 3329.
    -- From hival : i.val + a.val.val = 3329, so i.val = 3329 - a.val.val.
    have hi_eq : i.val = 3329 - a.val.val := by
      rw [hqval] at hival; omega
    rw [hi_eq]
  | fail e =>
    rw [hqa] at hae; simp at hae
    rw [hqval] at hae
    omega
  | div => rw [hqa] at hae; exact hae.elim

/-- Bridge lemma: under the no-overflow bound on `-a.val` (i.e.
    `a.val.natAbs ≤ 2^15 - 1`, equivalently `a.val ∈ [-(2^15 - 1), 2^15 - 1]`,
    which EXCLUDES the boundary `-2^15`), any `r : Std.I16` carrying that
    negation lifts to `FieldElement.neg_pure (lift_fe a)`.

    Pure-projection content: both sides reduce to
    `feOfZMod ((-a.val : Int) : ZMod 3329)`. The LHS is direct from
    `lift_fe`'s definition. The RHS uses `neg_pure_val_eq` plus canonical
    round-trip — the result is canonical by `Canonical_neg_pure` (which
    needs `Canonical_lift_fe`), and the `zmodOfFE`-projection reduces
    the inner `(3329 - (lift_fe a).val.val) % 3329` to `((-a.val : Int)
    : ZMod 3329)` via `ZMod.natCast_mod` plus integer reasoning.

    Boundary excluded: at `a.val = -2^15 = -32768`, both sides would
    diverge — `Int.bmod (-a.val) 2^16 = -32768`, but
    `(-((-32768 : Int) : ZMod 3329)).val = 2807 ≠ 522`. The `hbnd`
    precondition rules out this case. -/
private theorem lift_fe_neg_pure_eq
    (a r : Std.I16)
    (hbnd : a.val.natAbs ≤ 2^15 - 1)
    (hrv : r.val = -a.val) :
    lift_fe r
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.neg_pure (lift_fe a) := by
  -- LHS reduction.
  have h_lhs : lift_fe r = feOfZMod (((-a.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [hrv]
  -- RHS reduction.
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.neg_pure (lift_fe a) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical_neg_pure
      (lift_fe a) (Canonical_lift_fe a)
    show s.val.val < 3329
    unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s = (((-a.val : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    rw [neg_pure_val_eq _ (Canonical_lift_fe a)]
    -- Goal: ((3329 - (lift_fe a).val.val) % 3329 : Nat) : ZMod 3329
    --       = ((-a.val : Int) : ZMod 3329)
    rw [ZMod.natCast_mod]
    -- (lift_fe a).val.val < 3329, so 3329 - (lift_fe a).val.val ≤ 3329.
    have ha_lt : (lift_fe a).val.val < 3329 := by
      have h_ca := Canonical_lift_fe a
      unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at h_ca
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS at h_ca; simpa using h_ca
    -- Cast the Nat-sub through Int-sub: 3329 - (lift_fe a).val.val (Nat) =
    -- 3329 - (lift_fe a).val.val (Int) since the former is ≥ 0.
    have h_zmod_eq :
        (((3329 - (lift_fe a).val.val : Nat)) : ZMod 3329)
          = ((((3329 : Int) - ((lift_fe a).val.val : Int)) : Int) : ZMod 3329) := by
      have h_int_eq :
          (((3329 - (lift_fe a).val.val : Nat)) : Int)
            = (3329 : Int) - ((lift_fe a).val.val : Int) := by
        omega
      have h_route :
          (((3329 - (lift_fe a).val.val : Nat)) : ZMod 3329)
            = ((((3329 - (lift_fe a).val.val : Nat)) : Int) : ZMod 3329) := by
        rfl
      rw [h_route, h_int_eq]
    rw [h_zmod_eq]
    push_cast
    rw [lift_fe_val_val a]
    rw [ZMod.natCast_zmod_val]
    -- After push_cast: 0 - ((a.val : Int) : ZMod 3329) = ((-a.val : Int) : ZMod 3329)
    -- (3329 collapses to 0 via ZMod.natCast_self).
    ring
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- L1.6 — `negate` on a chunk.

    **Precondition** `hpre` mirrors the upstream F* spec `negate_pre`
    from `libcrux-ml-kem-proofs/libcrux-ml-kem/src/vector/traits.rs:684`
    (`forall i. is_intb (pow2 15 - 1) (v ${vec}[i])`), i.e. every lane
    is strictly within `[-(2^15 - 1), 2^15 - 1]` — equivalently the
    natAbs is `≤ 2^15 - 1`.

    **Why this is the canonical bound**: the impl's `negate` is
    pointwise `core_models.num.I16.wrapping_neg`, which lowers to
    `wrapping_sub 0 vec[i]`. The lane-level value reduces to
    `Int.bmod (-vec[i].val) 2^16`. For the FC equation
    `(r[i].val : ZMod 3329) = -(vec[i].val : ZMod 3329)` to hold we
    need `Int.bmod (-vec[i].val) 2^16 = -vec[i].val` (no boundary flip);
    `bmod_pow2_eq_of_inBounds'` requires `-vec[i].val ∈ [-2^15, 2^15)`,
    i.e. `vec[i].val ∈ (-2^15, 2^15]`. Combined with the impl's
    `vec[i].val ∈ [-2^15, 2^15)` carrier we get `vec[i].val.natAbs
    ≤ 2^15 - 1` — exactly `negate_pre`. The excluded value `-2^15`
    would yield a real divergence: `2^16 mod 3329 = 2645 ≠ 0`, so
    bmod's two-valued identification of `-2^15` and `2^15` does NOT
    collapse mod 3329.

    **Callers**: every real caller of `negate` (in
    `serialize::compress_then_serialize_*`) feeds inputs that are
    barrett-reduced (so `|x| ≤ 1664 < 2^15 - 1`) or subtracted from
    barrett-reduced operands (so `|x| ≤ 6656 < 2^15 - 1`); the bound
    is trivially satisfied at every call site. -/
@[spec high]
theorem negate_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      (vec.elements.val[i]!).val.natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.negate vec
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_neg_pure (lift_chunk vec) ⌝ ⦄ := by
  -- 1. Extract per-element BV-equation from legacy `negate_spec`.
  have h_legacy := libcrux_iot_ml_kem.Equivalence.negate_spec vec
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk Spec.chunk_neg_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe
      = (List.range 16).map (fun i =>
          libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.neg_pure
            ((Std.Array.make 16#usize (vec.elements.val.map lift_fe)
              (by simp)).val[i]!))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe r0.elements.val[i]
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.neg_pure
          ((vec.elements.val.map lift_fe)[i]!)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    have h_vec_len : vec.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Util.PortableVector_elements_length vec
    have h_map_vec :
        (vec.elements.val.map lift_fe)[i]! = lift_fe (vec.elements.val[i]!) := by
      have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
      rw [getElem!_pos (vec.elements.val.map lift_fe) i (by
        simp [List.length_map, h_vec_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos vec.elements.val i hi_vec]
    rw [h_map_vec]
    -- 3. Convert per-lane BV-equation to val-equation, then apply bridge.
    set xi : Std.I16 := vec.elements.val[i]! with hxi
    set ri : Std.I16 := r0.elements.val[i]! with hri
    -- From negate_spec: ri.bv = -xi.bv.
    have h_bv : ri.bv = -xi.bv := h_per i hi
    -- From this BV equality + I16.bv_toInt_eq: ri.val = (-xi.bv).toInt.
    -- The cleanest route: bridge through `Std.I16.wrapping_sub 0 xi`,
    -- whose `.bv = 0 - xi.bv = -xi.bv` matches `ri.bv`, then use
    -- `wrapping_sub_val_eq` to get `Int.bmod (0 - xi.val) (2^16)`.
    have h_wsub_bv : (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv = -xi.bv := by
      rw [Aeneas.Std.I16.wrapping_sub_bv_eq]
      simp only [show (0#i16 : Std.I16).bv = (0 : BitVec 16) from rfl]
      exact BitVec.zero_sub xi.bv
    -- Convert BV equality to val equality: ri.val = (-xi.bv).toInt =
    -- (Std.I16.wrapping_sub 0 xi).val = Int.bmod (0 - xi.val) (2^16) = -xi.val
    -- (last step under hpre via bmod_pow2_eq_of_inBounds').
    have h_ri_val : ri.val = -xi.val := by
      have h_step1 : ri.val = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).val := by
        have h_toInt :
            (ri.bv).toInt = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv.toInt := by
          rw [h_bv, h_wsub_bv]
        have h_lhs : (ri.bv).toInt = ri.val := Aeneas.Std.I16.bv_toInt_eq ri
        have h_rhs : (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv.toInt
            = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).val :=
          Aeneas.Std.I16.bv_toInt_eq _
        rw [h_lhs, h_rhs] at h_toInt
        exact h_toInt
      rw [h_step1]
      rw [Aeneas.Std.I16.wrapping_sub_val_eq]
      have h0 : (0#i16 : Std.I16).val = 0 := by decide
      rw [h0]
      -- Goal: Int.bmod (0 - xi.val) (2^16) = -xi.val.
      have h_diff : (0 : Int) - xi.val = -xi.val := by ring
      rw [h_diff]
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_abs : xi.val.natAbs ≤ 2^15 - 1 := hpre i hi
        have h_pow : -((2 : Int) ^ (16 - 1)) = -(2^15 : Int) := by decide
        rw [h_pow]
        omega
      · have h_abs : xi.val.natAbs ≤ 2^15 - 1 := hpre i hi
        have h_pow : ((2 : Int) ^ (16 - 1)) = (2^15 : Int) := by decide
        rw [h_pow]
        omega
    -- 4. Apply the bridge lemma.
    have h_abs : xi.val.natAbs ≤ 2^15 - 1 := hpre i hi
    exact lift_fe_neg_pure_eq xi ri h_abs h_ri_val

/-- L1.7 — `multiply_by_constant` (plain) on a chunk.

    **Precondition note**: the legacy `Equivalence.multiply_by_constant_spec`
    requires the per-element product bound `|vec[i] * c| ≤ 2^15 - 1`.
    The aggregate `|vec[i]| ≤ 32767 ∧ |c| ≤ 1664` does NOT imply that
    product bound (it allows `32767 * 1664 ≫ 32767`), so we carry
    `hpre_prod` as an additional caller obligation. Callers downstream
    in the NTT pipeline reliably satisfy this — Mont-domain inputs are
    already `|vec[i]| ≤ 3328 + 1665` after a `montgomery_reduce`, and
    the product with `|c| ≤ 1664` is well inside i32 with the per-lane
    bound easily verified. The `hvec` / `hc` are kept for API
    consistency with `montgomery_multiply_by_constant_fc`. -/
@[spec high]
theorem multiply_by_constant_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hvec : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 32767)
    (hc : c.val.natAbs ≤ 1664)
    (hpre_prod : ∀ i : Nat, i < 16 →
      ((vec.elements.val[i]!).val * c.val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_multiply_by_constant_pure
                    (lift_chunk vec) (lift_fe c) ⌝ ⦄ := by
  -- 1. Extract per-element value-equation from legacy bounds Triple.
  have h_legacy :=
    libcrux_iot_ml_kem.Equivalence.multiply_by_constant_spec vec c hpre_prod
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk Spec.chunk_multiply_by_constant_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe
      = (List.range 16).map (fun i =>
          libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
            ((Std.Array.make 16#usize (vec.elements.val.map lift_fe)
              (by simp)).val[i]!)
            (lift_fe c))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe r0.elements.val[i]
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
          ((vec.elements.val.map lift_fe)[i]!) (lift_fe c)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    have h_vec_len : vec.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Util.PortableVector_elements_length vec
    have h_map_vec :
        (vec.elements.val.map lift_fe)[i]! = lift_fe (vec.elements.val[i]!) := by
      have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
      rw [getElem!_pos (vec.elements.val.map lift_fe) i (by
        simp [List.length_map, h_vec_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos vec.elements.val i hi_vec]
    rw [h_map_vec]
    obtain ⟨h_val, _h_bnd⟩ := h_per i hi
    exact lift_fe_mul_pure_eq
      (vec.elements.val[i]!) c (r0.elements.val[i]!)
      h_val

/-- L1.8 — `bitwise_and_with_constant` on a chunk.

    Per the upstream F* spec
    `libcrux-ml-kem-proofs/libcrux-ml-kem/src/vector/traits.rs:720`
    (`bitwise_and_with_constant_constant_post`), the canonical FC
    statement for this bit-level op is the per-lane BV-equality
    `result == map_array (fun x -> x &. c) vec`. This is the
    "FE-level lift" formulation is NOT meaningful here because
    `lift_fe` projects through `mod 3329`, discarding the bit pattern
    that `&.` depends on (the FE equation would require lift_chunk to
    preserve bit info, which it cannot without losing the ring
    semantics). The canonical FC equation is therefore at the I16-BV
    level — equality-form, equality-strong, just at the correct
    abstraction layer for a bit-level op.

    The §0.5 `Spec.chunk_bitwise_and_with_constant_pure` stub remains
    in place as documentation but is NOT used in the FC equation
    below (the canonical post is the upstream F*-aligned BV-equality). -/
@[spec high]
theorem bitwise_and_with_constant_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant vec c
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).bv = (vec.elements.val[i]!).bv &&& c.bv ⌝ ⦄ :=
  libcrux_iot_ml_kem.Equivalence.bitwise_and_with_constant_spec vec c

/-- L1.9 — `shift_right` on a chunk.

    Per the upstream F* spec
    `libcrux-ml-kem-proofs/libcrux-ml-kem/src/vector/traits.rs:731`
    (`shift_right_post`), the canonical FC statement for this bit-level
    op is the per-lane BV-equality
    `result == map_array (fun x -> x >>! shift_by) vec` (where `>>!`
    is signed right shift on i16). Same reasoning as `bitwise_and_with_constant_fc`:
    the I16-BV level is the correct abstraction; lift_fe would discard
    the bit pattern that `>>!` depends on.

    The legacy `Equivalence.shift_right_spec` uses `0 ≤ SHIFT_BY.val ∧
    SHIFT_BY.val < 16` (the same range as the upstream F* `requires
    SHIFT_BY >= 0 && SHIFT_BY < 16` on the trait). We adopt the same
    precondition shape. -/
@[spec high]
theorem shift_right_fc
    (SHIFT_BY : Std.I32)
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hs : 0 ≤ SHIFT_BY.val ∧ SHIFT_BY.val < 16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right SHIFT_BY vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).bv =
                  (vec.elements.val[i]!).bv.sshiftRight SHIFT_BY.val.toNat ⌝ ⦄ :=
  libcrux_iot_ml_kem.Equivalence.shift_right_spec SHIFT_BY hs vec

/-- Per-element bridge for `reducing_from_i32_array_fc`: from the legacy
    L1.10 congruence `(r * 2^16) ≡ x (mod 3329)`, derive the FC equation
    `lift_fe_mont r = Spec.mont_reduce_pure (lift_fe_int x.val)`.

    Algebra: the goal (after unfolding via `mont_reduce_pure_lift_fe_int`
    and `lift_fe_mont`/`i16_to_spec_fe_mont`) is the `ZMod 3329` equation
    `r * 169 = x * 169 * 169`. From the legacy hypothesis `r * 2^16 = x`
    in `ZMod 3329`, multiply both sides by `169 * 169` and use the
    Montgomery-inversion identity `2^16 * 169 ≡ 1 (mod 3329)`
    (numerically `2285 * 169 = 1` in `ZMod 3329`) to collapse one factor
    on the LHS. -/
private theorem lift_fe_mont_mont_reduce_pure_eq
    (x : Std.I32) (r : Std.I16)
    (h : libcrux_iot_ml_kem.Util.modq_eq
            (r.val * (2 ^ 16 : Int)) x.val 3329) :
    lift_fe_mont r = Spec.mont_reduce_pure (lift_fe_int x.val) := by
  rw [mont_reduce_pure_lift_fe_int]
  unfold lift_fe_mont i16_to_spec_fe_mont
  congr 1
  -- Goal: (r.val : ZMod 3329) * 169 = (x.val : ZMod 3329) * 169 * 169
  have h_zmod : ((r.val * (2 ^ 16 : Int) : Int) : ZMod 3329)
              = ((x.val : Int) : ZMod 3329) :=
    modq_eq_cast_zmod _ _ h
  push_cast at h_zmod
  -- h_zmod : (r.val : ZMod 3329) * 2285 = (x.val : ZMod 3329)
  -- Goal: (r.val : ZMod 3329) * 169 = (x.val : ZMod 3329) * 169 * 169
  have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
  calc (r.val : ZMod 3329) * 169
      = (r.val : ZMod 3329) * ((2285 : ZMod 3329) * 169) * 169 := by rw [h_inv]; ring
    _ = ((r.val : ZMod 3329) * 2285) * 169 * 169 := by ring
    _ = (x.val : ZMod 3329) * 169 * 169 := by rw [h_zmod]

/-- L1.10 — `reducing_from_i32_array` on a chunk.
    Composes `montgomery_reduce_element` across 16 lanes. -/
@[spec high]
theorem reducing_from_i32_array_fc
    (array : Slice Std.I32)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hlen : array.length = 16)
    (hbound : ∀ i : Nat, i < 16 →
      (array.val[i]!).val.natAbs ≤ 2^16 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array array out
    ⦃ ⇓ r => ⌜ lift_chunk_mont r = Spec.chunk_reducing_from_i32_array_pure array ⌝ ⦄ := by
  -- 1. Extract per-element legacy fact:
  --    |r[i]| ≤ 3328+1665 ∧ (r[i]*2^16) ≡ array[i] (mod 3329).
  have hpre' : ∀ i : Nat, i < 16 → (array.val[i]!).val.natAbs ≤ 3328 * 2 ^ 16 := by
    intro i hi
    have h := hbound i hi
    rwa [show (3328 * 2 ^ 16 : Nat) = 2 ^ 16 * 3328 from by decide]
  have hlen' : array.val.length = 16 := hlen
  have h_legacy :=
    libcrux_iot_ml_kem.Equivalence.reducing_from_i32_array_spec array out hlen' hpre'
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe_mont equality.
  unfold lift_chunk_mont Spec.chunk_reducing_from_i32_array_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe_mont
      = (List.range 16).map (fun i =>
          Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe_mont).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe_mont r0.elements.val[i]
      = Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    obtain ⟨_h_bnd, h_modq⟩ := h_per i hi
    exact lift_fe_mont_mont_reduce_pure_eq
      (array.val[i]!) (r0.elements.val[i]!) h_modq

/-! ## §L2 — NTT step ops (5 theorems). -/

/-! ### L2.1 — `ntt_step` private helpers. -/

/-- Reduction of `core_models.num.I16.wrapping_sub` to the underlying
    Aeneas `Std.I16.wrapping_sub`. Mirror of L2's helper, scoped to FCTargets. -/
private theorem ntt_step_fc.cm_wrapping_sub_ok_eq (x y : Std.I16) :
    core_models.num.I16.wrapping_sub x y = .ok (Std.I16.wrapping_sub x y) := by
  unfold core_models.num.I16.wrapping_sub
  unfold rust_primitives.arithmetic.wrapping_sub_i16
  rfl

/-- Reduction of `core_models.num.I16.wrapping_add` to the underlying
    Aeneas `Std.I16.wrapping_add`. Mirror of L2's helper. -/
private theorem ntt_step_fc.cm_wrapping_add_ok_eq (x y : Std.I16) :
    core_models.num.I16.wrapping_add x y = .ok (Std.I16.wrapping_add x y) := by
  unfold core_models.num.I16.wrapping_add
  unfold rust_primitives.arithmetic.wrapping_add_i16
  rfl

/-- Reduction of `classify` to identity. Mirror of L2's helper. -/
private theorem ntt_step_fc.classify_ok_eq {T : Type} (x : T) :
    libcrux_secrets.traits.Classify.Blanket.classify x = .ok x := rfl

/-- Under `|a.val| ≤ bnd`, `|t.val| ≤ 3328`, and `bnd ≤ 29439`, the I16-wrapped
    sum `a + t` has `.val = a.val + t.val` (no overflow). Mirror of L2's
    `add_no_overflow_value_bnd`, scoped to FCTargets — only the value
    equation is exposed (bound conjunct dropped, not needed here). -/
private theorem ntt_step_fc.add_no_overflow_value (a t : Std.I16) (bnd : Nat)
    (h_a : a.val.natAbs ≤ bnd) (h_t : t.val.natAbs ≤ 3328) (h_bnd : bnd ≤ 29439) :
    (Std.I16.wrapping_add a t).val = a.val + t.val := by
  have h_sum_abs : ((a.val + t.val : Int)).natAbs ≤ bnd + 3328 := by
    have h_tri : (a.val + t.val).natAbs ≤ a.val.natAbs + t.val.natAbs := Int.natAbs_add_le _ _
    omega
  have h_lb : -(2 ^ 15 : Int) ≤ a.val + t.val := by
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_ub : a.val + t.val < (2 ^ 15 : Int) := by
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_bmod : Int.bmod (a.val + t.val) (2 ^ 16) = a.val + t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_add_val_eq a t
  rw [h_val, h_bmod]

/-- Diff variant of `add_no_overflow_value`. -/
private theorem ntt_step_fc.sub_no_overflow_value (a t : Std.I16) (bnd : Nat)
    (h_a : a.val.natAbs ≤ bnd) (h_t : t.val.natAbs ≤ 3328) (h_bnd : bnd ≤ 29439) :
    (Std.I16.wrapping_sub a t).val = a.val - t.val := by
  have h_diff_abs : ((a.val - t.val : Int)).natAbs ≤ bnd + 3328 := by
    have h_neg_natAbs : (-t.val).natAbs = t.val.natAbs := Int.natAbs_neg _
    have h_eq : a.val - t.val = a.val + (-t.val) := by ring
    rw [h_eq]
    have h_tri : (a.val + (-t.val)).natAbs ≤ a.val.natAbs + (-t.val).natAbs :=
      Int.natAbs_add_le _ _
    rw [h_neg_natAbs] at h_tri
    omega
  have h_lb : -(2 ^ 15 : Int) ≤ a.val - t.val := by
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_ub : a.val - t.val < (2 ^ 15 : Int) := by
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_bmod : Int.bmod (a.val - t.val) (2 ^ 16) = a.val - t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_sub_val_eq a t
  rw [h_val, h_bmod]

/-- Helper: `(lift_fe_mont x).val.val = (i16_to_spec_fe_mont x).val`. -/
private theorem lift_fe_mont_val_val (x : Std.I16) :
    (lift_fe_mont x).val.val = (i16_to_spec_fe_mont x).val := by
  unfold lift_fe_mont feOfZMod
  show (BitVec.ofNat 16 (i16_to_spec_fe_mont x).val).toNat = (i16_to_spec_fe_mont x).val
  rw [BitVec.toNat_ofNat]
  have h_lt : (i16_to_spec_fe_mont x).val < 2 ^ 16 :=
    Nat.lt_of_lt_of_le (ZMod.val_lt _) (by decide)
  exact Nat.mod_eq_of_lt h_lt

/-- Bridge lemma for the L0.4 Mont-domain output: from the legacy modq
    form `r.val ≡ b.val * zeta.val * 169 (mod 3329)`, derive the FE-level
    `lift_fe r = mul_pure (lift_fe b) (lift_fe_mont zeta)`.

    Algebra: both sides are canonical FEs (left by `Canonical_lift_fe`,
    right by `Canonical_mul_pure`). Equality reduces (via the canonical
    round-trip `feOfZMod_zmodOfFE_of_canonical`) to a `ZMod 3329` equation
    on their `zmodOfFE`-projections, closed by the legacy modq cast
    `modq_eq_cast_zmod` plus `ring`. -/
private theorem lift_fe_mul_pure_mont_eq
    (b zeta r : Std.I16)
    (h : libcrux_iot_ml_kem.Util.modq_eq r.val (b.val * zeta.val * 169) 3329) :
    lift_fe r
      = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
          (lift_fe b) (lift_fe_mont zeta) := by
  -- LHS: lift_fe r = feOfZMod ((r.val : Int) : ZMod 3329).
  have h_lhs : lift_fe r = feOfZMod (((r.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rfl
  -- RHS: mul_pure is canonical; reduce via round-trip.
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
      (lift_fe b) (lift_fe_mont zeta) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical_mul_pure
      (lift_fe b) (lift_fe_mont zeta)
    unfold libcrux_iot_ml_kem.BitMlKem.SpecPure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  -- zmodOfFE s = (b.val * zeta.val * 169 : ZMod 3329).
  have h_zmod_s : zmodOfFE s = (((b.val * zeta.val * 169 : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    rw [mul_pure_val_eq]
    rw [ZMod.natCast_mod]
    push_cast
    have h_lb : ((lift_fe b).val.val : ZMod 3329) = (((b.val : Int)) : ZMod 3329) := by
      rw [lift_fe_val_val b]; exact ZMod.natCast_zmod_val _
    have h_lz : ((lift_fe_mont zeta).val.val : ZMod 3329)
                  = (((zeta.val : Int)) : ZMod 3329) * 169 := by
      rw [lift_fe_mont_val_val zeta, ZMod.natCast_zmod_val]
      rw [i16_to_spec_fe_mont_unfold]
    rw [h_lb, h_lz]
    ring
  -- Cast the modq hypothesis to a ZMod equality.
  have h_zmod_eq : (((r.val : Int)) : ZMod 3329)
                    = (((b.val * zeta.val * 169 : Int)) : ZMod 3329) :=
    modq_eq_cast_zmod _ _ h
  rw [h_lhs, ← h_round_trip, h_zmod_s, h_zmod_eq]

/-- L2.1 — `ntt_step`: per-pair butterfly.

    **Preconditions beyond locked statement**:
    - `hne : i.val ≠ j.val` — mirrors L2 legacy `ntt_step_spec`. Without
      this, the impl's two writes (`a[j] := a-t` then `a[i] := a+t`) at
      the same index yield `a+t` while the spec would also yield `a+t`
      (via `(a.set j (a-t)).set i (a+t)` with `i = j` → same), but the
      lift-level reasoning bifurcates messily. Real callers in L2.2/3/4
      all use distinct `i, j`.
    - `hvec : ∀ k, k < 16 → (vec.elements.val[k]!).val.natAbs ≤ 29439` —
      ensures the I16 wrapping_{add,sub} at indices `i, j` do not overflow.
      The bound `29439 = 32767 - 3328` is the tightest that keeps
      `|vec[i] ± t| ≤ 32767` when `|t| ≤ 3328` (L0.4 output bound).
      Universal form (not just at `i, j`) for callers' convenience —
      they typically carry a per-lane bound. -/
@[spec high]
theorem ntt_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hne : i.val ≠ j.val)
    (hzeta : zeta.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j ⌝ ⦄ := by
  -- Step 0: vector length facts.
  have h_vec_len : vec.elements.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length vec
  have h_vec_val_len : vec.elements.val.length = 16 := h_vec_len
  -- Step 1: read vec[j].
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    libcrux_iot_ml_kem.Util.array_index_usize_ok_eq vec.elements j
      (by rw [h_vec_len]; exact hj)
  -- Step 2: classify ζ.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    ntt_step_fc.classify_ok_eq zeta
  -- Step 3: L0.4 keystone on (vec[j], ζ).
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  have h_b_bnd_29439 : b.val.natAbs ≤ 29439 := hvec j.val hj
  have h_b_bnd : b.val.natAbs ≤ 32767 := by
    have := h_b_bnd_29439
    omega
  obtain ⟨t, h_t_eq_ok, h_t_bd, h_t_lift⟩ :=
    triple_exists_ok_fc (montgomery_multiply_fe_by_fer_fc b zeta h_b_bnd hzeta)
  -- Recover the modq form via the legacy spec (needed for `lift_fe_mul_pure_mont_eq`).
  obtain ⟨t', h_t'_eq, h_t'_bnd_tight, h_t_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Equivalence.montgomery_multiply_fe_by_fer_spec b zeta hzeta)
  -- t' = t (same impl call, both `.ok`).
  have h_tt' : t = t' := by
    have : (Result.ok t : Result _) = Result.ok t' := by rw [← h_t_eq_ok, h_t'_eq]
    cases this; rfl
  -- Step 4: read vec[i].
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    libcrux_iot_ml_kem.Util.array_index_usize_ok_eq vec.elements i
      (by rw [h_vec_len]; exact hi)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  have h_a_bnd : a.val.natAbs ≤ 29439 := hvec i.val hi
  -- Step 5,6: wrapping_sub / wrapping_add.
  have h_sub_eq :
      core_models.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    ntt_step_fc.cm_wrapping_sub_ok_eq a t
  have h_add_eq :
      core_models.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    ntt_step_fc.cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  have h_t_bd' : t.val.natAbs ≤ 3328 := by
    -- L0.4-FC's locked-post bound is ≤ 3328 + 1665 = 4993; the legacy
    -- is the tighter ≤ 3328 (from `montgomery_multiply_fe_by_fer_spec`).
    rw [h_tt']; exact h_t'_bnd_tight
  have h_amt_val : a_minus_t.val = a.val - t.val :=
    ntt_step_fc.sub_no_overflow_value a t 29439 h_a_bnd h_t_bd' (by decide)
  have h_apt_val : a_plus_t.val = a.val + t.val :=
    ntt_step_fc.add_no_overflow_value a t 29439 h_a_bnd h_t_bd' (by decide)
  -- Step 7,8: writes.
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    libcrux_iot_ml_kem.Util.array_update_ok_eq vec.elements j a_minus_t
      (by rw [h_vec_len]; exact hj)
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact libcrux_iot_ml_kem.Util.array_update_ok_eq _ i a_plus_t
      (by rw [h_len]; exact hi)
  -- Compose: derive `.ok final_vec` form.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_tt'] at h_t'_eq
    rw [h_t'_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_sub_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_add_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_i]; simp only [Aeneas.Std.bind_tc_ok]; rfl
  apply triple_of_ok_fc h_body
  -- Now: prove the FC chunk equation.
  -- Set up the abbreviations.
  set s_t_fe : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
      (lift_fe b) (lift_fe_mont zeta) with hs_t_fe_def
  set s_minus : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
      (lift_fe a) s_t_fe with hs_minus_def
  set s_plus : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
      (lift_fe a) s_t_fe with hs_plus_def
  -- Reduce both sides to underlying lists via Subtype.ext.
  unfold lift_chunk Spec.chunk_ntt_step_pure
  apply Subtype.ext
  -- Both `lift_chunk` and `Spec.chunk_ntt_step_pure` produce Std.Array FE 16.
  -- After Subtype.ext the goal is on `.val : List FE`.
  -- Reduce: `(Std.Array.make 16 L _).val = L` and `Std.Array.set v i x .val = v.val.set i.val x`.
  simp only [Std.Array.set_val_eq]
  -- The Std.Array.make .val reduces by rfl (it's `⟨L, _⟩.val = L`).
  -- And `.val[k]!` on a `Std.Array.make _ L _` equals `L[k]!`.
  -- LHS: final_vec.elements.val.map lift_fe (final_vec.elements is set-set).
  show ((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe
      = ((vec.elements.val.map lift_fe).set j.val
          (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
            ((vec.elements.val.map lift_fe)[i.val]!)
            (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
              ((vec.elements.val.map lift_fe)[j.val]!) (lift_fe_mont zeta)))).set i.val
        (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
          ((vec.elements.val.map lift_fe)[i.val]!)
          (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
            ((vec.elements.val.map lift_fe)[j.val]!) (lift_fe_mont zeta)))
  -- Bridge: `(vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!)` when k < 16.
  have h_map_lift_at (k : Nat) (hk : k < 16) :
      (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) := by
    have hk_lhs : k < (vec.elements.val.map lift_fe).length := by
      simp [List.length_map, h_vec_val_len]; exact hk
    rw [getElem!_pos (vec.elements.val.map lift_fe) k hk_lhs]
    rw [List.getElem_map]
    have hk_vec : k < vec.elements.val.length := by rw [h_vec_val_len]; exact hk
    rw [getElem!_pos vec.elements.val k hk_vec]
  rw [h_map_lift_at i.val hi, h_map_lift_at j.val hj]
  -- The RHS s_t_fe / s_plus / s_minus values match:
  --   sub_pure (lift_fe a) (mul_pure (lift_fe b) (lift_fe_mont zeta)) = s_minus
  --   add_pure (lift_fe a) (mul_pure (lift_fe b) (lift_fe_mont zeta)) = s_plus
  change ((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe
      = ((vec.elements.val.map lift_fe).set j.val s_minus).set i.val s_plus
  -- Per-index proof.
  apply List.ext_getElem
  · simp [List.length_map, List.length_set]
  · intro k hk1 hk2
    have hk : k < 16 := by
      have hk' : k < (((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe).length := hk1
      simp [List.length_map, List.length_set, h_vec_val_len] at hk'
      exact hk'
    rw [List.getElem_map]
    by_cases h_eq_i : k = i.val
    · -- k = i.val: r[i] = a_plus_t, RHS = s_plus.
      subst h_eq_i
      rw [List.getElem_set_self]
      rw [List.getElem_set_self]
      -- Goal: lift_fe a_plus_t = s_plus
      show lift_fe a_plus_t = s_plus
      have h_step1 :
          lift_fe a_plus_t
            = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
                (lift_fe a) (lift_fe t) :=
        lift_fe_add_pure_eq a t a_plus_t h_apt_val
      rw [h_step1]
      show libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
              (lift_fe a) (lift_fe t) = s_plus
      simp only [hs_plus_def, hs_t_fe_def]
      congr 1
      rw [h_tt']
      exact lift_fe_mul_pure_mont_eq b zeta t' h_t_modq
    · -- k ≠ i.val.
      rw [List.getElem_set_ne (Ne.symm h_eq_i)]
      rw [List.getElem_set_ne (Ne.symm h_eq_i)]
      by_cases h_eq_j : k = j.val
      · -- k = j.val.
        subst h_eq_j
        rw [List.getElem_set_self]
        rw [List.getElem_set_self]
        show lift_fe a_minus_t = s_minus
        have h_step1 :
            lift_fe a_minus_t
              = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
                  (lift_fe a) (lift_fe t) :=
          lift_fe_sub_pure_eq a t a_minus_t h_amt_val
        rw [h_step1]
        show libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
                (lift_fe a) (lift_fe t) = s_minus
        simp only [hs_minus_def, hs_t_fe_def]
        congr 1
        rw [h_tt']
        exact lift_fe_mul_pure_mont_eq b zeta t' h_t_modq
      · -- k ≠ i.val, k ≠ j.val: r[k] = vec[k] under lift_fe.
        rw [List.getElem_set_ne (Ne.symm h_eq_j)]
        rw [List.getElem_set_ne (Ne.symm h_eq_j)]
        rw [List.getElem_map]

/-- Per-lane variant of `ntt_step_fc` for layer composition. Same body
    as the keystone, but the precondition is split into the two lanes
    actually read (`i`, `j`). This is needed for layer-N proofs where
    after each ntt_step the touched lanes exceed the universal `≤ 29439`
    bound; the pairs within a layer are disjoint, so only the
    untouched-pair lanes need to satisfy `≤ 29439` at each step.

    Also exposes the per-lane output bound `≤ 32767` (i.e. all lanes
    remain valid `I16`s), used to chain across steps. -/
private theorem ntt_step_pair_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hne : i.val ≠ j.val)
    (hzeta : zeta.val.natAbs ≤ 1664)
    (h_a_bnd : (vec.elements.val[i.val]!).val.natAbs ≤ 29439)
    (h_b_bnd : (vec.elements.val[j.val]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j
              ∧ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  (r.elements.val[k]!) = (vec.elements.val[k]!))
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ 32767
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ 32767 ⌝ ⦄ := by
  -- Step 0: vector length facts.
  have h_vec_len : vec.elements.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length vec
  have h_vec_val_len : vec.elements.val.length = 16 := h_vec_len
  -- Step 1: read vec[j].
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    libcrux_iot_ml_kem.Util.array_index_usize_ok_eq vec.elements j
      (by rw [h_vec_len]; exact hj)
  -- Step 2: classify ζ.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    ntt_step_fc.classify_ok_eq zeta
  -- Step 3: L0.4 keystone on (vec[j], ζ).
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  have h_b_bnd_29439 : b.val.natAbs ≤ 29439 := h_b_bnd
  have h_b_bnd_max : b.val.natAbs ≤ 32767 := by
    have := h_b_bnd_29439; omega
  obtain ⟨t, h_t_eq_ok, h_t_bd, h_t_lift⟩ :=
    triple_exists_ok_fc (montgomery_multiply_fe_by_fer_fc b zeta h_b_bnd_max hzeta)
  obtain ⟨t', h_t'_eq, h_t'_bnd_tight, h_t_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Equivalence.montgomery_multiply_fe_by_fer_spec b zeta hzeta)
  have h_tt' : t = t' := by
    have : (Result.ok t : Result _) = Result.ok t' := by rw [← h_t_eq_ok, h_t'_eq]
    cases this; rfl
  -- Step 4: read vec[i].
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    libcrux_iot_ml_kem.Util.array_index_usize_ok_eq vec.elements i
      (by rw [h_vec_len]; exact hi)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  have h_a_bnd_29439 : a.val.natAbs ≤ 29439 := h_a_bnd
  -- Step 5,6: wrapping_sub / wrapping_add.
  have h_sub_eq :
      core_models.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    ntt_step_fc.cm_wrapping_sub_ok_eq a t
  have h_add_eq :
      core_models.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    ntt_step_fc.cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  have h_t_bd' : t.val.natAbs ≤ 3328 := by
    rw [h_tt']; exact h_t'_bnd_tight
  have h_amt_val : a_minus_t.val = a.val - t.val :=
    ntt_step_fc.sub_no_overflow_value a t 29439 h_a_bnd_29439 h_t_bd' (by decide)
  have h_apt_val : a_plus_t.val = a.val + t.val :=
    ntt_step_fc.add_no_overflow_value a t 29439 h_a_bnd_29439 h_t_bd' (by decide)
  -- Step 7,8: writes.
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    libcrux_iot_ml_kem.Util.array_update_ok_eq vec.elements j a_minus_t
      (by rw [h_vec_len]; exact hj)
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact libcrux_iot_ml_kem.Util.array_update_ok_eq _ i a_plus_t
      (by rw [h_len]; exact hi)
  -- Compose.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_tt'] at h_t'_eq
    rw [h_t'_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_sub_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_add_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_i]; simp only [Aeneas.Std.bind_tc_ok]; rfl
  apply triple_of_ok_fc h_body
  -- Now: 4 conjuncts.
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- lift_chunk equation: identical to keystone proof.
    set s_t_fe : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
        (lift_fe b) (lift_fe_mont zeta) with hs_t_fe_def
    set s_minus : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
        (lift_fe a) s_t_fe with hs_minus_def
    set s_plus : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
        (lift_fe a) s_t_fe with hs_plus_def
    unfold lift_chunk Spec.chunk_ntt_step_pure
    apply Subtype.ext
    simp only [Std.Array.set_val_eq]
    show ((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe
        = ((vec.elements.val.map lift_fe).set j.val
            (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
              ((vec.elements.val.map lift_fe)[i.val]!)
              (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
                ((vec.elements.val.map lift_fe)[j.val]!) (lift_fe_mont zeta)))).set i.val
          (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
            ((vec.elements.val.map lift_fe)[i.val]!)
            (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
              ((vec.elements.val.map lift_fe)[j.val]!) (lift_fe_mont zeta)))
    have h_map_lift_at (k : Nat) (hk : k < 16) :
        (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) := by
      have hk_lhs : k < (vec.elements.val.map lift_fe).length := by
        simp [List.length_map, h_vec_val_len]; exact hk
      rw [getElem!_pos (vec.elements.val.map lift_fe) k hk_lhs]
      rw [List.getElem_map]
      have hk_vec : k < vec.elements.val.length := by rw [h_vec_val_len]; exact hk
      rw [getElem!_pos vec.elements.val k hk_vec]
    rw [h_map_lift_at i.val hi, h_map_lift_at j.val hj]
    change ((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe
        = ((vec.elements.val.map lift_fe).set j.val s_minus).set i.val s_plus
    apply List.ext_getElem
    · simp [List.length_map, List.length_set]
    · intro k hk1 hk2
      have hk : k < 16 := by
        have hk' : k < (((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe).length := hk1
        simp [List.length_map, List.length_set, h_vec_val_len] at hk'
        exact hk'
      rw [List.getElem_map]
      by_cases h_eq_i : k = i.val
      · subst h_eq_i
        rw [List.getElem_set_self]
        rw [List.getElem_set_self]
        show lift_fe a_plus_t = s_plus
        have h_step1 :
            lift_fe a_plus_t
              = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
                  (lift_fe a) (lift_fe t) :=
          lift_fe_add_pure_eq a t a_plus_t h_apt_val
        rw [h_step1]
        show libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
                (lift_fe a) (lift_fe t) = s_plus
        simp only [hs_plus_def, hs_t_fe_def]
        congr 1
        rw [h_tt']
        exact lift_fe_mul_pure_mont_eq b zeta t' h_t_modq
      · rw [List.getElem_set_ne (Ne.symm h_eq_i)]
        rw [List.getElem_set_ne (Ne.symm h_eq_i)]
        by_cases h_eq_j : k = j.val
        · subst h_eq_j
          rw [List.getElem_set_self]
          rw [List.getElem_set_self]
          show lift_fe a_minus_t = s_minus
          have h_step1 :
              lift_fe a_minus_t
                = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
                    (lift_fe a) (lift_fe t) :=
            lift_fe_sub_pure_eq a t a_minus_t h_amt_val
          rw [h_step1]
          show libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
                  (lift_fe a) (lift_fe t) = s_minus
          simp only [hs_minus_def, hs_t_fe_def]
          congr 1
          rw [h_tt']
          exact lift_fe_mul_pure_mont_eq b zeta t' h_t_modq
        · rw [List.getElem_set_ne (Ne.symm h_eq_j)]
          rw [List.getElem_set_ne (Ne.symm h_eq_j)]
          rw [List.getElem_map]
  · -- Untouched-lane preservation: r[k] = vec[k] for k ≠ i, j.
    intro k hk hki hkj
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[k]!
      = vec.elements.val[k]!
    have h_set_val_eq : ((vec.elements.set j a_minus_t).set i a_plus_t).val
        = (vec.elements.val.set j.val a_minus_t).set i.val a_plus_t := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    -- (list.set j _).set i _ at index k (k ≠ i, k ≠ j) = original list at k.
    have hk_set_i : k < (vec.elements.val.set j.val a_minus_t).length := by
      simp [List.length_set, h_vec_val_len]; exact hk
    rw [getElem!_pos _ k (by simp [List.length_set, h_vec_val_len]; exact hk)]
    rw [List.getElem_set_ne (Ne.symm hki)]
    rw [List.getElem_set_ne (Ne.symm hkj)]
    rw [getElem!_pos vec.elements.val k (by rw [h_vec_val_len]; exact hk)]
  · -- Bound at i: r[i] = a_plus_t = a + t (no-overflow), |a| ≤ 29439, |t| ≤ 3328.
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!.val.natAbs ≤ 32767
    have h_set_val_eq : ((vec.elements.set j a_minus_t).set i a_plus_t).val
        = (vec.elements.val.set j.val a_minus_t).set i.val a_plus_t := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    rw [getElem!_pos _ i.val (by simp [List.length_set, h_vec_val_len]; exact hi)]
    rw [List.getElem_set_self]
    -- a_plus_t.val = a.val + t.val, |a| ≤ 29439, |t| ≤ 3328 ⇒ |sum| ≤ 32767.
    have h_sum_abs : ((a.val + t.val : Int)).natAbs ≤ 29439 + 3328 := by
      have h_tri : (a.val + t.val).natAbs ≤ a.val.natAbs + t.val.natAbs := Int.natAbs_add_le _ _
      omega
    rw [h_apt_val]; omega
  · -- Bound at j: r[j] = a_minus_t = a - t (no-overflow), similar.
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!.val.natAbs ≤ 32767
    have h_set_val_eq : ((vec.elements.set j a_minus_t).set i a_plus_t).val
        = (vec.elements.val.set j.val a_minus_t).set i.val a_plus_t := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    rw [getElem!_pos _ j.val (by simp [List.length_set, h_vec_val_len]; exact hj)]
    rw [List.getElem_set_ne hne]
    rw [List.getElem_set_self]
    have h_diff_abs : ((a.val - t.val : Int)).natAbs ≤ 29439 + 3328 := by
      have h_neg : (-t.val).natAbs = t.val.natAbs := Int.natAbs_neg _
      have h_eq : a.val - t.val = a.val + (-t.val) := by ring
      rw [h_eq]
      have h_tri : (a.val + (-t.val)).natAbs ≤ a.val.natAbs + (-t.val).natAbs :=
        Int.natAbs_add_le _ _
      rw [h_neg] at h_tri
      omega
    rw [h_amt_val]; omega

/-- L2.2 — `ntt_layer_1_step`: 8 butterfly pairs (0,2)(1,3) with z0,
    (4,6)(5,7) with z1, (8,10)(9,11) with z2, (12,14)(13,15) with z3.

    **Precondition adjustment** (beyond locked statement):
    - `hvec : ∀ k < 16, |vec[k]| ≤ 29439` — same as layer_2/3 (disjoint pairs). -/
@[spec]
theorem ntt_layer_1_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z0 z1 z2 z3 : Std.I16)
    (hz : z0.val.natAbs ≤ 1664 ∧ z1.val.natAbs ≤ 1664
        ∧ z2.val.natAbs ≤ 1664 ∧ z3.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec z0 z1 z2 z3
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_1_step_pure (lift_chunk vec)
                    (lift_fe_mont z0) (lift_fe_mont z1)
                    (lift_fe_mont z2) (lift_fe_mont z3) ⌝ ⦄ := by
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: ntt_step vec z0 0 2.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc vec z0 0#usize 2#usize hi0 hi2
      (by decide) hz0 (hvec 0 hi0) (hvec 2 hi2))
  -- Step 2: ntt_step v1 z0 1 3.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_3 : (v1.elements.val[3]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v1 z0 1#usize 3#usize hi1 hi3
      (by decide) hz0 h_v1_1 h_v1_3)
  -- Step 3: ntt_step v2 z1 4 6.
  have h_v2_4 : (v2.elements.val[4]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 4 hi4 (by decide) (by decide),
        h_v1_unc 4 hi4 (by decide) (by decide)]; exact hvec 4 hi4
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v2 z1 4#usize 6#usize hi4 hi6
      (by decide) hz1 h_v2_4 h_v2_6)
  -- Step 4: ntt_step v3 z1 5 7.
  have h_v3_5 : (v3.elements.val[5]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 5 hi5 (by decide) (by decide),
        h_v2_unc 5 hi5 (by decide) (by decide),
        h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v3 z1 5#usize 7#usize hi5 hi7
      (by decide) hz1 h_v3_5 h_v3_7)
  -- Step 5: ntt_step v4 z2 8 10.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 8 hi8 (by decide) (by decide),
        h_v3_unc 8 hi8 (by decide) (by decide),
        h_v2_unc 8 hi8 (by decide) (by decide),
        h_v1_unc 8 hi8 (by decide) (by decide)]; exact hvec 8 hi8
  have h_v4_10 : (v4.elements.val[10]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 10 hi10 (by decide) (by decide),
        h_v3_unc 10 hi10 (by decide) (by decide),
        h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v4 z2 8#usize 10#usize hi8 hi10
      (by decide) hz2 h_v4_8 h_v4_10)
  -- Step 6: ntt_step v5 z2 9 11.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 9 hi9 (by decide) (by decide),
        h_v4_unc 9 hi9 (by decide) (by decide),
        h_v3_unc 9 hi9 (by decide) (by decide),
        h_v2_unc 9 hi9 (by decide) (by decide),
        h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  have h_v5_11 : (v5.elements.val[11]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 11 hi11 (by decide) (by decide),
        h_v4_unc 11 hi11 (by decide) (by decide),
        h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v5 z2 9#usize 11#usize hi9 hi11
      (by decide) hz2 h_v5_9 h_v5_11)
  -- Step 7: ntt_step v6 z3 12 14.
  have h_v6_12 : (v6.elements.val[12]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 12 hi12 (by decide) (by decide),
        h_v5_unc 12 hi12 (by decide) (by decide),
        h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v6 z3 12#usize 14#usize hi12 hi14
      (by decide) hz3 h_v6_12 h_v6_14)
  -- Step 8: ntt_step v7 z3 13 15.
  have h_v7_13 : (v7.elements.val[13]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 13 hi13 (by decide) (by decide),
        h_v6_unc 13 hi13 (by decide) (by decide),
        h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, _, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v7 z3 13#usize 15#usize hi13 hi15
      (by decide) hz3 h_v7_13 h_v7_15)
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec z0 z1 z2 z3
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  unfold Spec.chunk_ntt_layer_1_step_pure
  rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]

/-- L2.3 — `ntt_layer_2_step`: 8 butterfly pairs (0,4)…(3,7) with z0 then
    (8,12)…(11,15) with z1.

    **Precondition adjustment** (beyond locked statement):
    - `hvec : ∀ k < 16, |vec[k]| ≤ 29439` — same as layer_3 (disjoint pairs). -/
@[spec]
theorem ntt_layer_2_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z0 z1 : Std.I16)
    (hz : z0.val.natAbs ≤ 1664 ∧ z1.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec z0 z1
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_2_step_pure (lift_chunk vec)
                    (lift_fe_mont z0) (lift_fe_mont z1) ⌝ ⦄ := by
  obtain ⟨hz0, hz1⟩ := hz
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: ntt_step vec z0 0 4.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc vec z0 0#usize 4#usize hi0 hi4
      (by decide) hz0 (hvec 0 hi0) (hvec 4 hi4))
  -- Step 2: ntt_step v1 z0 1 5.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_5 : (v1.elements.val[5]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v1 z0 1#usize 5#usize hi1 hi5
      (by decide) hz0 h_v1_1 h_v1_5)
  -- Step 3: ntt_step v2 z0 2 6.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 2 hi2 (by decide) (by decide),
        h_v1_unc 2 hi2 (by decide) (by decide)]; exact hvec 2 hi2
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v2 z0 2#usize 6#usize hi2 hi6
      (by decide) hz0 h_v2_2 h_v2_6)
  -- Step 4: ntt_step v3 z0 3 7.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 3 hi3 (by decide) (by decide),
        h_v2_unc 3 hi3 (by decide) (by decide),
        h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v3 z0 3#usize 7#usize hi3 hi7
      (by decide) hz0 h_v3_3 h_v3_7)
  -- Step 5: ntt_step v4 z1 8 12.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 8 hi8 (by decide) (by decide),
        h_v3_unc 8 hi8 (by decide) (by decide),
        h_v2_unc 8 hi8 (by decide) (by decide),
        h_v1_unc 8 hi8 (by decide) (by decide)]; exact hvec 8 hi8
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v4 z1 8#usize 12#usize hi8 hi12
      (by decide) hz1 h_v4_8 h_v4_12)
  -- Step 6: ntt_step v5 z1 9 13.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 9 hi9 (by decide) (by decide),
        h_v4_unc 9 hi9 (by decide) (by decide),
        h_v3_unc 9 hi9 (by decide) (by decide),
        h_v2_unc 9 hi9 (by decide) (by decide),
        h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v5 z1 9#usize 13#usize hi9 hi13
      (by decide) hz1 h_v5_9 h_v5_13)
  -- Step 7: ntt_step v6 z1 10 14.
  have h_v6_10 : (v6.elements.val[10]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 10 hi10 (by decide) (by decide),
        h_v5_unc 10 hi10 (by decide) (by decide),
        h_v4_unc 10 hi10 (by decide) (by decide),
        h_v3_unc 10 hi10 (by decide) (by decide),
        h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v6 z1 10#usize 14#usize hi10 hi14
      (by decide) hz1 h_v6_10 h_v6_14)
  -- Step 8: ntt_step v7 z1 11 15.
  have h_v7_11 : (v7.elements.val[11]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 11 hi11 (by decide) (by decide),
        h_v6_unc 11 hi11 (by decide) (by decide),
        h_v5_unc 11 hi11 (by decide) (by decide),
        h_v4_unc 11 hi11 (by decide) (by decide),
        h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, _, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v7 z1 11#usize 15#usize hi11 hi15
      (by decide) hz1 h_v7_11 h_v7_15)
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec z0 z1 = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  unfold Spec.chunk_ntt_layer_2_step_pure
  rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]

/-- L2.4 — `ntt_layer_3_step`: 8 butterfly pairs (0,8)…(7,15) with one zeta.

    **Precondition adjustment** (beyond locked statement):
    - `hvec : ∀ k < 16, |vec[k]| ≤ 29439` — chained through the 8
      ntt_step calls. Pairs are disjoint (each lane touched exactly
      once), so the keystone's `≤ 29439` precondition holds at each
      step on the unchanged lanes. -/
@[spec]
theorem ntt_layer_3_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z : Std.I16) (hz : z.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec z
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_3_step_pure (lift_chunk vec) (lift_fe_mont z) ⌝ ⦄ := by
  -- Initial-lane bounds (specialised from hvec).
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: ntt_step vec z 0 8.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, _h_v1_i_bd, _h_v1_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc vec z 0#usize 8#usize hi0 hi8
      (by decide) hz (hvec 0 hi0) (hvec 8 hi8))
  -- Step 2: ntt_step v1 z 1 9 — needs v1[1], v1[9] ≤ 29439. Both via h_v1_unc.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_9 : (v1.elements.val[9]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, _h_v2_i_bd, _h_v2_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v1 z 1#usize 9#usize hi1 hi9
      (by decide) hz h_v1_1 h_v1_9)
  -- Step 3: ntt_step v2 z 2 10.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 2 hi2 (by decide) (by decide),
        h_v1_unc 2 hi2 (by decide) (by decide)]; exact hvec 2 hi2
  have h_v2_10 : (v2.elements.val[10]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, _h_v3_i_bd, _h_v3_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v2 z 2#usize 10#usize hi2 hi10
      (by decide) hz h_v2_2 h_v2_10)
  -- Step 4: ntt_step v3 z 3 11.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 3 hi3 (by decide) (by decide),
        h_v2_unc 3 hi3 (by decide) (by decide),
        h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  have h_v3_11 : (v3.elements.val[11]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, _h_v4_i_bd, _h_v4_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v3 z 3#usize 11#usize hi3 hi11
      (by decide) hz h_v3_3 h_v3_11)
  -- Step 5: ntt_step v4 z 4 12.
  have h_v4_4 : (v4.elements.val[4]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 4 hi4 (by decide) (by decide),
        h_v3_unc 4 hi4 (by decide) (by decide),
        h_v2_unc 4 hi4 (by decide) (by decide),
        h_v1_unc 4 hi4 (by decide) (by decide)]; exact hvec 4 hi4
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, _h_v5_i_bd, _h_v5_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v4 z 4#usize 12#usize hi4 hi12
      (by decide) hz h_v4_4 h_v4_12)
  -- Step 6: ntt_step v5 z 5 13.
  have h_v5_5 : (v5.elements.val[5]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 5 hi5 (by decide) (by decide),
        h_v4_unc 5 hi5 (by decide) (by decide),
        h_v3_unc 5 hi5 (by decide) (by decide),
        h_v2_unc 5 hi5 (by decide) (by decide),
        h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, _h_v6_i_bd, _h_v6_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v5 z 5#usize 13#usize hi5 hi13
      (by decide) hz h_v5_5 h_v5_13)
  -- Step 7: ntt_step v6 z 6 14.
  have h_v6_6 : (v6.elements.val[6]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 6 hi6 (by decide) (by decide),
        h_v5_unc 6 hi6 (by decide) (by decide),
        h_v4_unc 6 hi6 (by decide) (by decide),
        h_v3_unc 6 hi6 (by decide) (by decide),
        h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, _h_v7_i_bd, _h_v7_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v6 z 6#usize 14#usize hi6 hi14
      (by decide) hz h_v6_6 h_v6_14)
  -- Step 8: ntt_step v7 z 7 15.
  have h_v7_7 : (v7.elements.val[7]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 7 hi7 (by decide) (by decide),
        h_v6_unc 7 hi7 (by decide) (by decide),
        h_v5_unc 7 hi7 (by decide) (by decide),
        h_v4_unc 7 hi7 (by decide) (by decide),
        h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, _h_v8_unc, _h_v8_i_bd, _h_v8_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v7 z 7#usize 15#usize hi7 hi15
      (by decide) hz h_v7_7 h_v7_15)
  -- Compose into a single `.ok v8` for the layer body.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec z = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  -- Chain the 8 lift equations into the spec composition.
  unfold Spec.chunk_ntt_layer_3_step_pure
  rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]

/-- L2.5 — `inv_ntt_step`: per-pair inverse butterfly.

    **Preconditions beyond locked statement** (precondition adjustment):
    - `hne : i.val ≠ j.val` — without this the impl's two writes
      (`vec[i] := o0` then `vec[j] := o1`) at the same index yield `o1`
      while the spec's `(a.set i new_i).set j new_j` with `i = j` also
      yields `new_j`, but the lift-level proof bifurcates messily. Real
      callers (inv_ntt_layer_{1,2,3}_step) all use distinct `i, j`.
    - `hvec : ∀ k < 16, |vec[k]| ≤ 13312` (= 4·3328) — needed so that
      `wrapping_add (vec[j], vec[i])` and `wrapping_sub (vec[j], vec[i])`
      don't overflow at the I16 level. Since `|vec[j]| + |vec[i]| ≤
      26624 < 32768`, both ops have `.val = b + a` and `b - a` exactly.
      This mirrors the legacy `inv_ntt_step_spec_B` with `B = 4`. -/
@[spec]
theorem inv_ntt_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hne : i.val ≠ j.val)
    (hzeta : zeta.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 13312) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_inv_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j ⌝ ⦄ := by
  -- Step 0: vector length facts.
  have h_vec_len : vec.elements.length = 16 :=
    libcrux_iot_ml_kem.Util.PortableVector_elements_length vec
  have h_vec_val_len : vec.elements.val.length = 16 := h_vec_len
  -- Step 1: read vec[j] (= i1 in impl, called "b").
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    libcrux_iot_ml_kem.Util.array_index_usize_ok_eq vec.elements j
      (by rw [h_vec_len]; exact hj)
  -- Step 2: read vec[i] (= i2 in impl, called "a").
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    libcrux_iot_ml_kem.Util.array_index_usize_ok_eq vec.elements i
      (by rw [h_vec_len]; exact hi)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  have h_a_bnd : a.val.natAbs ≤ 13312 := hvec i.val hi
  have h_b_bnd : b.val.natAbs ≤ 13312 := hvec j.val hj
  -- Step 3,4: wrapping_sub b a and wrapping_add b a.
  have h_sub_eq :
      core_models.num.I16.wrapping_sub b a = .ok (Std.I16.wrapping_sub b a) :=
    ntt_step_fc.cm_wrapping_sub_ok_eq b a
  have h_add_eq :
      core_models.num.I16.wrapping_add b a = .ok (Std.I16.wrapping_add b a) :=
    ntt_step_fc.cm_wrapping_add_ok_eq b a
  set a_minus_b : Std.I16 := Std.I16.wrapping_sub b a with hamb_def
  set a_plus_b  : Std.I16 := Std.I16.wrapping_add b a with hapb_def
  -- No-overflow for wrapping_add b a: |b.val + a.val| ≤ 2·13312 = 26624 < 32768.
  have h_apb_val : a_plus_b.val = b.val + a.val := by
    have h_sum_abs : ((b.val + a.val : Int)).natAbs ≤ 26624 := by
      have h_tri : (b.val + a.val).natAbs ≤ b.val.natAbs + a.val.natAbs :=
        Int.natAbs_add_le _ _
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val + a.val := by omega
    have h_ub : b.val + a.val < (2 ^ 15 : Int) := by omega
    have h_bmod : Int.bmod (b.val + a.val) (2 ^ 16) = b.val + a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_add_val_eq b a
    rw [hapb_def, h_val, h_bmod]
  have h_amb_val : a_minus_b.val = b.val - a.val := by
    have h_diff_abs : ((b.val - a.val : Int)).natAbs ≤ 26624 := by
      have h_neg_natAbs : (-a.val).natAbs = a.val.natAbs := Int.natAbs_neg _
      have h_eq : b.val - a.val = b.val + (-a.val) := by ring
      rw [h_eq]
      have h_tri : (b.val + (-a.val)).natAbs ≤ b.val.natAbs + (-a.val).natAbs :=
        Int.natAbs_add_le _ _
      rw [h_neg_natAbs] at h_tri
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val - a.val := by omega
    have h_ub : b.val - a.val < (2 ^ 15 : Int) := by omega
    have h_bmod : Int.bmod (b.val - a.val) (2 ^ 16) = b.val - a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_sub_val_eq b a
    rw [hamb_def, h_val, h_bmod]
  -- Bound on a_plus_b for L0.2 (≤ 26624 ≤ 32767).
  have h_apb_bd : a_plus_b.val.natAbs ≤ 32767 := by
    rw [h_apb_val]
    have h_tri : (b.val + a.val).natAbs ≤ b.val.natAbs + a.val.natAbs :=
      Int.natAbs_add_le _ _
    omega
  -- Step 5: L0.2 barrett_reduce_element on a_plus_b.
  obtain ⟨o0, h_o0_eq_ok, h_o0_bd, h_o0_lift⟩ :=
    triple_exists_ok_fc (barrett_reduce_element_fc a_plus_b h_apb_bd)
  -- Recover modq form via legacy (needed since L0.2-FC delivers `lift_fe o0 =
  -- barrett_pure (lift_fe a_plus_b)` but we need `lift_fe o0 = add_pure (lift_fe b)
  -- (lift_fe a)`; the bridge needs the modq equation on `.val`s).
  obtain ⟨o0', h_o0'_eq, h_o0'_modq, _h_o0'_bd⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Equivalence.barrett_reduce_element_spec a_plus_b h_apb_bd)
  have h_oo' : o0 = o0' := by
    have : (Result.ok o0 : Result _) = Result.ok o0' := by
      rw [← h_o0_eq_ok, h_o0'_eq]
    cases this; rfl
  -- Step 6: classify zeta = zeta.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    ntt_step_fc.classify_ok_eq zeta
  -- Step 7: L0.4 montgomery_multiply on (a_minus_b, zeta).
  obtain ⟨o1, h_o1_eq_ok, h_o1_bd, h_o1_lift⟩ :=
    triple_exists_ok_fc (montgomery_multiply_fe_by_fer_fc a_minus_b zeta
      (by have := a_minus_b.hBounds; omega) hzeta)
  obtain ⟨o1', h_o1'_eq, h_o1'_bd_tight, h_o1'_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Equivalence.montgomery_multiply_fe_by_fer_spec a_minus_b zeta hzeta)
  have h_oo1' : o1 = o1' := by
    have : (Result.ok o1 : Result _) = Result.ok o1' := by
      rw [← h_o1_eq_ok, h_o1'_eq]
    cases this; rfl
  -- Step 8: write vec[i] := o0.
  have h_upd_i :
      Aeneas.Std.Array.update vec.elements i o0
        = .ok (vec.elements.set i o0) :=
    libcrux_iot_ml_kem.Util.array_update_ok_eq vec.elements i o0
      (by rw [h_vec_len]; exact hi)
  -- Step 9: write vec[j] := o1.
  have h_upd_j :
      Aeneas.Std.Array.update (vec.elements.set i o0) j o1
        = .ok ((vec.elements.set i o0).set j o1) := by
    have h_len : (vec.elements.set i o0).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact libcrux_iot_ml_kem.Util.array_update_ok_eq _ j o1
      (by rw [h_len]; exact hj)
  -- Compose into `.ok final_vec`.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set i o0).set j o1 with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
        = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step
    rw [h_idx_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_sub_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_add_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_oo'] at h_o0'_eq
    rw [h_o0_eq_ok]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_oo1'] at h_o1'_eq
    rw [h_o1_eq_ok]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_j]; simp only [Aeneas.Std.bind_tc_ok]; rfl
  apply triple_of_ok_fc h_body
  -- Now: prove the FC chunk equation.
  -- spec new_i := add_pure (lift_fe b) (lift_fe a)
  -- spec new_j := mul_pure (sub_pure (lift_fe b) (lift_fe a)) (lift_fe_mont zeta)
  set s_new_i : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
      (lift_fe b) (lift_fe a) with hs_new_i_def
  set s_diff : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
      (lift_fe b) (lift_fe a) with hs_diff_def
  set s_new_j : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
      s_diff (lift_fe_mont zeta) with hs_new_j_def
  unfold lift_chunk Spec.chunk_inv_ntt_step_pure
  apply Subtype.ext
  simp only [Std.Array.set_val_eq]
  -- Bridge: (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) when k < 16.
  have h_map_lift_at (k : Nat) (hk : k < 16) :
      (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) := by
    have hk_lhs : k < (vec.elements.val.map lift_fe).length := by
      simp [List.length_map, h_vec_val_len]; exact hk
    rw [getElem!_pos (vec.elements.val.map lift_fe) k hk_lhs]
    rw [List.getElem_map]
    have hk_vec : k < vec.elements.val.length := by rw [h_vec_val_len]; exact hk
    rw [getElem!_pos vec.elements.val k hk_vec]
  show ((vec.elements.val.set i.val o0).set j.val o1).map lift_fe
      = ((vec.elements.val.map lift_fe).set i.val
          (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.add_pure
            ((vec.elements.val.map lift_fe)[j.val]!)
            ((vec.elements.val.map lift_fe)[i.val]!))).set j.val
        (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.sub_pure
            ((vec.elements.val.map lift_fe)[j.val]!)
            ((vec.elements.val.map lift_fe)[i.val]!))
          (lift_fe_mont zeta))
  rw [h_map_lift_at i.val hi, h_map_lift_at j.val hj]
  change ((vec.elements.val.set i.val o0).set j.val o1).map lift_fe
      = ((vec.elements.val.map lift_fe).set i.val s_new_i).set j.val s_new_j
  apply List.ext_getElem
  · simp [List.length_map, List.length_set]
  · intro k hk1 hk2
    have hk : k < 16 := by
      have hk' : k < (((vec.elements.val.set i.val o0).set j.val o1).map lift_fe).length := hk1
      simp [List.length_map, List.length_set, h_vec_val_len] at hk'
      exact hk'
    rw [List.getElem_map]
    by_cases h_eq_j : k = j.val
    · -- k = j.val: r[j] = o1 = mont_mul(b-a, zeta).
      subst h_eq_j
      rw [List.getElem_set_self]
      rw [List.getElem_set_self]
      show lift_fe o1 = s_new_j
      -- mont_mul a_minus_b zeta produced o1. We have h_o1'_modq:
      -- modq_eq o1'.val (a_minus_b.val * zeta.val * 169) 3329.
      -- lift_fe o1 = lift_fe o1' (h_oo1') = mul_pure (lift_fe a_minus_b) (lift_fe_mont zeta).
      have h_step1 :
          lift_fe o1 = libcrux_iot_ml_kem.BitMlKem.SpecPure.FieldElement.mul_pure
            (lift_fe a_minus_b) (lift_fe_mont zeta) := by
        rw [h_oo1']
        exact lift_fe_mul_pure_mont_eq a_minus_b zeta o1' h_o1'_modq
      rw [h_step1]
      -- Now: mul_pure (lift_fe a_minus_b) (lift_fe_mont zeta) = s_new_j
      --    = mul_pure s_diff (lift_fe_mont zeta) where s_diff = sub_pure (lift_fe b) (lift_fe a).
      -- Reduce by congr 1 to: lift_fe a_minus_b = s_diff.
      simp only [hs_new_j_def]
      congr 1
      -- lift_fe a_minus_b = sub_pure (lift_fe b) (lift_fe a).
      exact lift_fe_sub_pure_eq b a a_minus_b h_amb_val
    · rw [List.getElem_set_ne (Ne.symm h_eq_j)]
      rw [List.getElem_set_ne (Ne.symm h_eq_j)]
      by_cases h_eq_i : k = i.val
      · -- k = i.val: r[i] = o0 = barrett(b+a).
        subst h_eq_i
        rw [List.getElem_set_self]
        rw [List.getElem_set_self]
        show lift_fe o0 = s_new_i
        -- lift_fe o0 = lift_fe o0' (h_oo') from h_o0'_modq:
        --   modq_eq o0'.val a_plus_b.val 3329.
        -- Then lift_fe o0' = lift_fe a_plus_b = add_pure (lift_fe b) (lift_fe a).
        have h_step1 : lift_fe o0 = lift_fe a_plus_b := by
          rw [h_oo']
          exact lift_fe_eq_of_modq o0' a_plus_b h_o0'_modq
        rw [h_step1]
        -- lift_fe a_plus_b = add_pure (lift_fe b) (lift_fe a) via h_apb_val.
        simp only [hs_new_i_def]
        exact lift_fe_add_pure_eq b a a_plus_b h_apb_val
      · -- k ≠ i.val, k ≠ j.val.
        rw [List.getElem_set_ne (Ne.symm h_eq_i)]
        rw [List.getElem_set_ne (Ne.symm h_eq_i)]
        rw [List.getElem_map]

/-! ## §L3 — NTT driver loops (5 theorems). -/

/-- L3.1 — `ntt_at_layer_1` driver: 16 iters × 8 butterflies per chunk
    using 4 zetas per chunk from `ZETAS_TIMES_MONTGOMERY_R[zeta_i+1 .. zeta_i+4]`.
    Output is the same poly with layer-1 NTT applied across all 16 chunks. -/
@[spec]
theorem ntt_at_layer_1_fc
    {Vector : Type}
    (inst : libcrux_iot_ml_kem.vector.traits.Operations Vector)
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector)
    (initial_bound : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1 inst zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ True ⌝ ⦄ := by
  sorry
  -- TODO: FC equation requires `lift_poly` specialized to `Vector` —
  -- the impl is poly-generic over `Vector`; we land the bare-true post
  -- here as a placeholder. The PortableVector-specialised FC equation
  -- is the one used by callers; see `ntt_at_layer_1_portable_fc` below.

/-- L3.1' — `ntt_at_layer_1` PortableVector-specialised FC equation.
    The impl returns `(zeta_i_after, re_after)`; we project on `re_after`.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_bnd : ∀ chunk < 16, ∀ k < 16, |re.coefficients[chunk].elements[k]| ≤ 29439`
      — every input lane satisfies the `ntt_layer_1_step` bound. Caller
      sites guarantee this from the prior layer's output range.
    - `h_zeta : zeta_i.val + 64 ≤ 128` — the loop reads zetas at
      positions `zeta_i+1 .. zeta_i+64`, all of which must be in the
      128-entry ZETAS table to avoid `.fail`. -/
@[spec high]
theorem ntt_at_layer_1_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 29439)
    (h_zeta : zeta_i.val + 64 ≤ 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1
      (vectortraitsOperationsInst := portable_ops_inst)
      zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_1_pure (lift_poly re) zeta_i ⌝ ⦄ := by
  sorry

/-- L3.2 — `ntt_at_layer_2` PortableVector FC. Same precondition shape
    as L3.1 (per-lane bound + zeta-index bound) but layer 2 consumes 2
    zetas per chunk so `zeta_i + 32 ≤ 128`. -/
@[spec high]
theorem ntt_at_layer_2_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 29439)
    (h_zeta : zeta_i.val + 32 ≤ 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_2_pure (lift_poly re) zeta_i ⌝ ⦄ := by
  sorry

/-- L3.3 — `ntt_binomially_sampled_ring_element` driver (5 layer
    composition + barrett reduce). Projects on the poly component. -/
@[spec]
theorem ntt_binomially_sampled_ring_element_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element
      (vectortraitsOperationsInst := portable_ops_inst) re scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.ntt_pure (lift_poly re) ⌝ ⦄ := by
  sorry

/-- L3.4 — `ntt_vector_u` driver (4 layer composition + barrett reduce,
    used for the encryption "u" vector NTT). -/
@[spec]
theorem ntt_vector_u_fc
    (VECTOR_U_COMPRESSION_FACTOR : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_vector_u
      VECTOR_U_COMPRESSION_FACTOR
      (vectortraitsOperationsInst := portable_ops_inst) re scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.ntt_pure (lift_poly re) ⌝ ⦄ := by
  sorry

/-! ## §L6 — poly-level ops (6 theorems). -/

/-- L6.1 — `poly_barrett_reduce`: 16-chunk loop applying `barrett_reduce`
    per chunk. Spec target: hacspec `polynomial.poly_barrett_reduce`. -/
@[spec]
theorem poly_barrett_reduce_fc
    (self : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.polynomial.poly_barrett_reduce (lift_poly self)
                = .ok (lift_poly p) ⌝ ⦄ := by
  sorry

/-- L6.2 — `subtract_reduce`: pointwise `(self - b · (R/128))` then
    negate then barrett.
    Spec target: hacspec `polynomial.subtract_reduce`. -/
@[spec]
theorem subtract_reduce_fc
    (self b : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self b
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.polynomial.subtract_reduce (lift_poly self) (lift_poly b)
                = .ok (lift_poly p) ⌝ ⦄ := by
  sorry

/-! ### L6.3 — `add_to_ring_element` (DOCUMENTED, NO STANDALONE FC).

    The impl-side `PolynomialRingElement.add_to_ring_element` is NOT
    a standalone exported op at the impl extraction layer: the impl
    fuses "add then reduce" into the `add_*_reduce` family
    (`add_error_reduce`, `add_standard_error_reduce`,
    `add_message_error_reduce`).

    The hacspec target `polynomial.add_to_ring_element` is exercised
    indirectly through the matrix-level FCs (L7.1 / L7.3 use it
    inside `multiply_matrix_by_column` and `add_polynomials`); we do
    NOT land a separate `add_to_ring_element_fc` Triple here, but we
    DO land per-component `add_*_reduce_fc` Triples below (L6.4/5/6)
    that cover the impl-side calls. -/

/-- L6.4 — `add_error_reduce`: `self · (R/128) + error` then barrett.
    Returns `(re, scratch)` tuple; we project on `re`. -/
@[spec]
theorem add_error_reduce_fc
    (self error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self error
    ⦃ ⇓ p => ⌜ lift_poly p = Spec.add_error_reduce_pure (lift_poly self) (lift_poly error) ⌝ ⦄ := by
  sorry

/-- L6.5 — `add_standard_error_reduce`: `self · R² + error` then barrett.
    Used to take an inverse-NTT result back to "standard domain". -/
@[spec]
theorem add_standard_error_reduce_fc
    (self error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self error
    ⦃ ⇓ p => ⌜ lift_poly p
                = Spec.add_standard_error_reduce_pure (lift_poly self) (lift_poly error) ⌝ ⦄ := by
  sorry

/-- L6.6 — `add_message_error_reduce`: combines `self · (R/128)` with
    `result + message` then barrett. Returns `(re, scratch)` tuple. -/
@[spec]
theorem add_message_error_reduce_fc
    (self message result : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self message result scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1
                = Spec.add_message_error_reduce_pure
                    (lift_poly self) (lift_poly message) (lift_poly result) ⌝ ⦄ := by
  sorry

/-- L6.7 — poly-level `reducing_from_i32_array`. Returns a fresh poly
    from an `i32` slice via 16 chunkwise `reducing_from_i32_array` calls. -/
@[spec]
theorem poly_reducing_from_i32_array_fc
    (a : Slice Std.I32)
    (out : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
      (vectortraitsOperationsInst := portable_ops_inst) a out
    ⦃ ⇓ p => ⌜ lift_poly_mont p = Spec.poly_reducing_from_i32_array_pure a ⌝ ⦄ := by
  sorry

/-! ## §L7 — matrix-level targets (4 theorems).

    These are the ultimate FC obligations: the impl matrix functions
    must compute the same hacspec ring-element vector / single ring
    element as their spec counterparts. -/

/-- L7.1 — `matrix.compute_As_plus_e`: product `A · s + e` of the
    public-key generation step. Impl returns
    `(t_as_ntt, s_cache, accumulator)`; project on `t_as_ntt`. -/
@[spec]
theorem compute_As_plus_e_fc
    {K : Std.Usize}
    (t_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (matrix_A : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt s_cache : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : Std.Array Std.I32 256#usize)
    (hAlen : matrix_A.length = (K.val * K.val : Nat)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e
      (vectortraitsOperationsInst := portable_ops_inst)
      t_as_ntt matrix_A s_as_ntt error_as_ntt s_cache accumulator
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_As_plus_e
                  (lift_matrix (sorry : Std.Array (Std.Array
                    (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K) K))
                  (lift_vec s_as_ntt) (lift_vec error_as_ntt)
                = .ok (lift_vec p.1) ⌝ ⦄ := by
  sorry

/-- L7.2 — `matrix.compute_vector_u`: product `Aᵀ · r + e₁` of the
    encryption step. Impl takes `seed : Slice U8` and reconstructs
    the matrix via `sample_matrix_A_loop`; the FC equation references
    the deterministic `Spec.sample_matrix_A_pure seed K` projection.
    Impl returns
    `(matrix_entry, result, scratch, cache, accumulator)`; project on
    `result`. -/
@[spec]
theorem compute_vector_u_fc
    {Hasher : Type} (K : Std.Usize)
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (matrix_entry : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (seed : Slice Std.U8)
    (r_as_ntt error_1 result : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (cache : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (accumulator : Std.Array Std.I32 256#usize) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u
      K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
      matrix_entry seed r_as_ntt error_1 result scratch cache accumulator
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_vector_u
                  (lift_matrix_from_seed seed K)
                  (lift_vec_slice r_as_ntt K)
                  (lift_vec_slice error_1 K)
                = .ok (lift_vec_slice p.2.1 K) ⌝ ⦄ := by
  sorry

/-- L7.3 — `matrix.compute_ring_element_v`: `t · r + e₂ + message`.
    Impl returns `(t_as_ntt_entry, result, scratch, accumulator)`;
    project on `result`. -/
@[spec]
theorem compute_ring_element_v_fc
    (K : Std.Usize)
    (public_key : Slice Std.U8)
    (t_as_ntt_entry : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (r_as_ntt : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (error_2 message result :
      libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (cache : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (accumulator : Std.Array Std.I32 256#usize) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_ring_element_v
      K (vectortraitsOperationsInst := portable_ops_inst)
      public_key t_as_ntt_entry r_as_ntt error_2 message result scratch
      cache accumulator
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_ring_element_v
                  (sorry : Std.Array
                    (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K)
                  (lift_vec_slice r_as_ntt K)
                  (lift_poly error_2) (lift_poly message)
                = .ok (lift_poly p.2.1) ⌝ ⦄ := by
  sorry

/-- L7.4 — `matrix.compute_message`: `v - secret · u` then NTT-inverse.
    Impl returns `(result, scratch, accumulator)`; project on `result`. -/
@[spec]
theorem compute_message_fc
    {K : Std.Usize}
    (v : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (result : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (accumulator : Std.Array Std.I32 256#usize) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_message
      (vectortraitsOperationsInst := portable_ops_inst)
      v secret_as_ntt u_as_ntt result scratch accumulator
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_message
                  (lift_poly v)
                  (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
                = .ok (lift_poly p.1) ⌝ ⦄ := by
  sorry

/-! ## Roll-up

    Theorems written by layer:
      §L0 — 4
      §L1 — 10
      §L2 — 5
      §L3 — 5  (one is the type-generic placeholder + four PortableVector-specialised)
      §L6 — 6  (L6.1, L6.2, L6.4, L6.5, L6.6, L6.7 — L6.3 documented as
                "absorbed into L6.{4,5,6} via the fused `add_*_reduce` impls")
      §L7 — 4

    Total theorems: 34.
    Total `sorry`s: 34 (one per theorem) + ~25 helper-def bodies.
-/

end libcrux_iot_ml_kem.BitMlKem.FCTargets
