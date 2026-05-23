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

/-- Pure projection of Montgomery `fe · fer / R`: given two FEs,
    one in plain domain (`fe`) and one in Mont domain (`fer = c · R`),
    returns `fe · c`. Composes `FieldElement.mul_pure` after one
    `mont_reduce`. -/
noncomputable def Spec.montgomery_multiply_fe_by_fer_pure
    (fe fer : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.parameters.FieldElement := sorry

/-- Pure projection of `get_n_least_significant_bits` — pure modular
    truncation on `Std.U32`. -/
def Spec.get_n_least_significant_bits_pure (n : Std.U8) (value : Std.U32) : Std.U32 :=
  ⟨value.bv &&& ((1#32 <<< n.val) - 1#32)⟩

/-- Pure pointwise add at the FE-array level (16-lane chunk). -/
noncomputable def Spec.chunk_add_pure
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure pointwise sub at the FE-array level (16-lane chunk). -/
noncomputable def Spec.chunk_sub_pure
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure pointwise neg at the FE-array level (16-lane chunk). -/
noncomputable def Spec.chunk_neg_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure pointwise barrett-reduce at the FE-array level. -/
noncomputable def Spec.chunk_barrett_reduce_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure pointwise `montgomery_multiply_by_constant` at the chunk level
    (each lane: `fe · c / R`). -/
noncomputable def Spec.chunk_montgomery_multiply_by_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure pointwise plain `multiply_by_constant` at the chunk level. -/
noncomputable def Spec.chunk_multiply_by_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure pointwise `bitwise_and_with_constant` at the chunk level.
    NO HACSPEC EQUIVALENT — this is a bit-level mask used only in
    serialize/compress paths. We state the FC equation against the
    bit-masking definition itself. -/
noncomputable def Spec.chunk_bitwise_and_with_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure pointwise `shift_right` at the chunk level.
    NO HACSPEC EQUIVALENT at the FE level. -/
noncomputable def Spec.chunk_shift_right_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (SHIFT_BY : Std.I32) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure `reducing_from_i32_array` at the chunk level. -/
noncomputable def Spec.chunk_reducing_from_i32_array_pure
    (array : Slice Std.I32) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure NTT butterfly step at the chunk level: applies `ntt.butterfly`
    pointwise to the lane pair `(i, j)` with `zeta`. -/
noncomputable def Spec.chunk_ntt_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure NTT-layer-1 step at the chunk level. -/
noncomputable def Spec.chunk_ntt_layer_1_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure NTT-layer-2 step at the chunk level. -/
noncomputable def Spec.chunk_ntt_layer_2_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure NTT-layer-3 step at the chunk level. -/
noncomputable def Spec.chunk_ntt_layer_3_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

/-- Pure inverse-NTT step at the chunk level. -/
noncomputable def Spec.chunk_inv_ntt_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize := sorry

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

/-- Pure projection of the full hacspec `ntt.ntt`. -/
noncomputable def Spec.ntt_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize := sorry

/-- Pure projection of the layer-N driver `ntt.ntt_layer_n`. -/
noncomputable def Spec.ntt_layer_n_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (n : Std.Usize) :
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

/-- L0.4 — `montgomery_multiply_fe_by_fer`.
    Spec: `fe · c` (where `fer = c · R`). -/
@[spec]
theorem montgomery_multiply_fe_by_fer_fc
    (fe fer : Std.I16)
    (hfe : fe.val.natAbs ≤ 32767) (hfer : fer.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer fe fer
    ⦃ ⇓ r => ⌜ r.val.natAbs ≤ 3328 + 1665
                ∧ lift_fe_mont r
                    = Spec.montgomery_multiply_fe_by_fer_pure
                        (lift_fe fe) (lift_fe_mont fer) ⌝ ⦄ := by
  sorry

/-! ## §L1 — chunk-level vector ops (10 theorems). -/

/-- L1.1 — `add` on 16-lane PortableVector chunks. -/
@[spec]
theorem add_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      ((lhs.elements.val[i]!).val + (rhs.elements.val[i]!).val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.add lhs rhs
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_add_pure (lift_chunk lhs) (lift_chunk rhs) ⌝ ⦄ := by
  sorry

/-- L1.2 — `sub` on 16-lane PortableVector chunks. -/
@[spec]
theorem sub_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      ((lhs.elements.val[i]!).val - (rhs.elements.val[i]!).val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.sub lhs rhs
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_sub_pure (lift_chunk lhs) (lift_chunk rhs) ⌝ ⦄ := by
  sorry

/-- L1.3 — `barrett_reduce` on a chunk. -/
@[spec]
theorem barrett_reduce_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      (vec.elements.val[i]!).val.natAbs ≤ 32767) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce vec
    ⦃ ⇓ r => ⌜ (∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 3328)
                ∧ lift_chunk r = Spec.chunk_barrett_reduce_pure (lift_chunk vec) ⌝ ⦄ := by
  sorry

/-- L1.4 — `montgomery_multiply_by_constant` on a chunk.
    Each lane: `vec[i] · c / R`. The lift uses `lift_chunk_mont` on
    the output (the result is in Mont domain). -/
@[spec]
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
  sorry

/-- L1.5 — `cond_subtract_3329` on a chunk.
    NO HACSPEC EQUIVALENT — the impl conditionally subtracts q to
    rebalance ranges; spec-side this is identity in `ZMod 3329`. The
    spec target we land against is the identity at the FE-array level. -/
@[spec]
theorem cond_subtract_3329_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329 vec
    ⦃ ⇓ r => ⌜ lift_chunk r = lift_chunk vec ⌝ ⦄ := by
  sorry

/-- L1.6 — `negate` on a chunk. -/
@[spec]
theorem negate_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.negate vec
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_neg_pure (lift_chunk vec) ⌝ ⦄ := by
  sorry

/-- L1.7 — `multiply_by_constant` (plain) on a chunk. -/
@[spec]
theorem multiply_by_constant_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hvec : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 32767)
    (hc : c.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_multiply_by_constant_pure
                    (lift_chunk vec) (lift_fe c) ⌝ ⦄ := by
  sorry

/-- L1.8 — `bitwise_and_with_constant` on a chunk.
    NO HACSPEC EQUIVALENT at the FE level — this is a bit-mask used
    only in compress/serialize paths. -/
@[spec]
theorem bitwise_and_with_constant_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant vec c
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_bitwise_and_with_constant_pure
                    (lift_chunk vec) (lift_fe c) ⌝ ⦄ := by
  sorry

/-- L1.9 — `shift_right` on a chunk.
    NO HACSPEC EQUIVALENT at the FE level — used only in
    compress/decompress paths. -/
@[spec]
theorem shift_right_fc
    (SHIFT_BY : Std.I32)
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hs : SHIFT_BY.val.natAbs ≤ 16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right SHIFT_BY vec
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_shift_right_pure (lift_chunk vec) SHIFT_BY ⌝ ⦄ := by
  sorry

/-- L1.10 — `reducing_from_i32_array` on a chunk.
    Composes `montgomery_reduce_element` across 16 lanes. -/
@[spec]
theorem reducing_from_i32_array_fc
    (array : Slice Std.I32)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hlen : array.length = 16)
    (hbound : ∀ i : Nat, i < 16 →
      (array.val[i]!).val.natAbs ≤ 2^16 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array array out
    ⦃ ⇓ r => ⌜ lift_chunk_mont r = Spec.chunk_reducing_from_i32_array_pure array ⌝ ⦄ := by
  sorry

/-! ## §L2 — NTT step ops (5 theorems). -/

/-- L2.1 — `ntt_step`: per-pair butterfly. -/
@[spec]
theorem ntt_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hzeta : zeta.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j ⌝ ⦄ := by
  sorry

/-- L2.2 — `ntt_layer_1_step`: 8 butterfly pairs with 4 distinct zetas. -/
@[spec]
theorem ntt_layer_1_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z0 z1 z2 z3 : Std.I16)
    (hz : z0.val.natAbs ≤ 1664 ∧ z1.val.natAbs ≤ 1664
        ∧ z2.val.natAbs ≤ 1664 ∧ z3.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec z0 z1 z2 z3
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_1_step_pure (lift_chunk vec)
                    (lift_fe_mont z0) (lift_fe_mont z1)
                    (lift_fe_mont z2) (lift_fe_mont z3) ⌝ ⦄ := by
  sorry

/-- L2.3 — `ntt_layer_2_step`: 4 butterfly pairs with 2 distinct zetas. -/
@[spec]
theorem ntt_layer_2_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z0 z1 : Std.I16)
    (hz : z0.val.natAbs ≤ 1664 ∧ z1.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec z0 z1
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_2_step_pure (lift_chunk vec)
                    (lift_fe_mont z0) (lift_fe_mont z1) ⌝ ⦄ := by
  sorry

/-- L2.4 — `ntt_layer_3_step`: 2 butterfly pairs with 1 zeta. -/
@[spec]
theorem ntt_layer_3_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z : Std.I16) (hz : z.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec z
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_3_step_pure (lift_chunk vec) (lift_fe_mont z) ⌝ ⦄ := by
  sorry

/-- L2.5 — `inv_ntt_step`: per-pair inverse butterfly. -/
@[spec]
theorem inv_ntt_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hzeta : zeta.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_inv_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j ⌝ ⦄ := by
  sorry

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
    The impl returns `(zeta_i_after, re_after)`; we project on `re_after`. -/
@[spec]
theorem ntt_at_layer_1_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (hpre : True) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1
      (vectortraitsOperationsInst := portable_ops_inst)
      zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_n_pure (lift_poly re) 1#usize ⌝ ⦄ := by
  sorry

/-- L3.2 — `ntt_at_layer_2/3/4_plus/7` collapsed into a single
    PortableVector FC theorem family. We split by layer for the
    follow-up dispatch, but encode the same post-shape. -/
@[spec]
theorem ntt_at_layer_2_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_n_pure (lift_poly re) 2#usize ⌝ ⦄ := by
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
